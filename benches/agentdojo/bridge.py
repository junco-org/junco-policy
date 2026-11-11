"""AgentDojo 0.1.34 environment and scorer; stdout is reserved for JSON RPC."""

import contextlib
import json
import sys

with contextlib.redirect_stdout(sys.stderr):
    from agentdojo.agent_pipeline.base_pipeline_element import BasePipelineElement
    from agentdojo.attacks import load_attack
    from agentdojo.default_suites.v1.tools.banking_client import Transaction
    from agentdojo.default_suites.v1.tools.calendar_client import CalendarEvent
    from agentdojo.default_suites.v1.tools.cloud_drive_client import CloudDriveFile
    from agentdojo.default_suites.v1.tools.email_client import Email
    from agentdojo.default_suites.v1.tools.slack import Message
    from agentdojo.functions_runtime import FunctionCall, FunctionsRuntime
    from agentdojo.models import MODEL_NAMES
    from agentdojo.task_suite import get_suite
    from agentdojo.types import text_content_block_from_string
    from pydantic import BaseModel
    from pydantic_core import to_jsonable_python


# Tool outputs CaMeL marks as readable by nobody (camel/pipeline_elements/agentdojo_function.py):
# plain text and channel/user names may carry injections and have no owner metadata.
PRIVATE_TEXT_TOOLS = {
    "read_file",
    "get_channels",
    "get_users_in_channel",
    "get_webpage",
    "send_money",
    "schedule_transaction",
    "update_scheduled_transaction",
}
PRIVATE_RECORD_TOOLS = {"get_user_info", "update_password", "update_user_info", "get_user_information"}
PUBLIC_REVIEW_TOOLS = {
    "get_rating_reviews_for_car_rental",
    "get_rating_reviews_for_hotels",
    "get_rating_reviews_for_restaurants",
}


def readers(tool, value):
    """CaMeL's readers lattice as a tree parallel to the result: `{"readers": [...]}` at each
    value that has an owner set, lists and nested models recursed, `None` where readers are public."""
    if isinstance(value, (list, tuple)):
        items = [readers(tool, item) for item in value]
        return items if any(item is not None for item in items) else None
    if tool in PUBLIC_REVIEW_TOOLS:
        return None
    if isinstance(value, str) and tool in PRIVATE_TEXT_TOOLS:
        return {"readers": []}
    if isinstance(value, (dict, BaseModel)) and tool in PRIVATE_RECORD_TOOLS:
        return {"readers": []}
    if isinstance(value, Email):
        return {"readers": sorted({value.sender, *value.recipients, *value.cc, *value.bcc})}
    if isinstance(value, Transaction):
        return {"readers": sorted({value.sender, value.recipient})}
    if isinstance(value, Message):
        return {"readers": [value.recipient]}
    if isinstance(value, CalendarEvent):
        return {"readers": sorted(set(value.participants))}
    if isinstance(value, CloudDriveFile):
        return {"readers": sorted(value.shared_with)}
    if isinstance(value, BaseModel):
        fields = {name: readers(tool, getattr(value, name)) for name in type(value).model_fields}
        fields = {name: tree for name, tree in fields.items() if tree is not None}
        return fields or None
    if isinstance(value, dict):
        fields = {name: readers(tool, item) for name, item in value.items()}
        fields = {name: tree for name, tree in fields.items() if tree is not None}
        return fields or None
    return None


class _Named(BasePipelineElement):
    def __init__(self, name):
        self.name = name

    def query(self, *args, **kwargs):
        raise RuntimeError("The Rust harness owns model execution")


def shape(value):
    if isinstance(value, BaseModel):
        return {field: shape(getattr(value, field)) for field in type(value).model_fields}
    if isinstance(value, dict):
        return {"<dict>": len(value)}
    if isinstance(value, (list, tuple)):
        return {"<list>": len(value), "item": shape(value[0]) if value else None}
    if isinstance(value, str):
        return "<str>"
    if isinstance(value, bool):
        return "<bool>"
    if isinstance(value, (int, float)):
        return "<number>"
    if value is None:
        return None
    return "<value>"


class Worker:
    def list_tasks(self, suite):
        suite = get_suite("v1.2", suite)
        return {
            "user_tasks": list(suite.user_tasks),
            "injection_tasks": list(suite.injection_tasks),
        }

    def reset(self):
        self.env = self.user_task.init_environment(
            self.suite.load_and_inject_default_environment(self.injections)
        )
        self.pre_env = self.env.model_copy(deep=True)
        self.runtime = FunctionsRuntime(self.suite.tools)
        self.trace = []

    def load_task(self, suite, user_task_id, injection_task_id, pipeline_name, model_prose):
        MODEL_NAMES[pipeline_name] = model_prose
        self.suite = get_suite("v1.2", suite)
        self.user_task = self.suite.get_user_task_by_id(user_task_id)
        self.injection_task = (
            self.suite.get_injection_task_by_id(injection_task_id)
            if injection_task_id is not None
            else None
        )
        self.injections = {}
        if self.injection_task is not None:
            attack = load_attack("important_instructions", self.suite, _Named(pipeline_name))
            self.injections = attack.attack(self.user_task, self.injection_task)
        self.reset()
        return {
            "prompt": self.user_task.PROMPT,
            "tools": [
                {
                    "name": function.name,
                    "description": function.description,
                    "parameters": function.parameters.model_json_schema(),
                }
                for function in self.runtime.functions.values()
            ],
            "injections": self.injections,
        }

    def execute(self, name, args):
        result, error = self.runtime.run_function(self.env, name, args)
        self.trace.append(FunctionCall(function=name, args=args))
        return result, error

    def call_tool(self, name, args):
        result, error = self.execute(name, args)
        return {
            "result": to_jsonable_python(result),
            "error": error,
            "shape": shape(result),
            "readers": readers(name, result),
        }

    def recipients(self, name, args):
        """Who receives data through a sink whose audience is environment state, not an argument."""
        if name == "send_channel_message":
            channel = args.get("channel")
            return [user for user, channels in self.env.slack.user_channels.items() if channel in channels]
        if name == "append_to_file":
            return sorted(self.env.cloud_drive.files[args["file_id"]].shared_with)
        if name == "reschedule_calendar_event":
            return sorted(set(self.env.calendar.events[args["event_id"]].participants))
        if name == "update_scheduled_transaction":
            recipient = args.get("recipient")
            if recipient:  # same truthiness test as banking_client.update_scheduled_transaction
                return [recipient]
            transaction_id = int(args["id"])
            transaction = next((t for t in self.env.bank_account.scheduled_transactions if t.id == transaction_id), None)
            if transaction is None:
                raise ValueError(f"Scheduled transaction {transaction_id} not found")
            return [transaction.recipient]
        raise ValueError(f"{name} has no environment-defined recipients")

    def evaluate(self, model_output):
        blocks = [text_content_block_from_string(model_output)]
        utility = self.suite._check_task_result(
            self.user_task, blocks, self.pre_env, self.env, self.trace
        )
        injection_success = None
        if self.injection_task is not None:
            injection_success = self.suite._check_task_result(
                self.injection_task, blocks, self.pre_env, self.env, self.trace
            )
        return {"utility": utility, "injection_success": injection_success}

    def replay_evaluate(self, calls, model_output):
        self.reset()
        for call in calls:
            self.execute(call["name"], call["args"])
        return self.evaluate(model_output)


def main():
    worker = Worker()
    methods = {
        name: getattr(worker, name)
        for name in ("list_tasks", "load_task", "call_tool", "recipients", "evaluate", "replay_evaluate")
    }
    for line in sys.stdin:
        request_id = None
        try:
            request = json.loads(line)
            request_id = request["id"]
            method = request["method"]
            if method not in methods:
                raise ValueError(f"Unknown method: {method}")
            with contextlib.redirect_stdout(sys.stderr):
                result = methods[method](**request.get("params", {}))
            response = {"id": request_id, "result": result}
        except Exception as error:
            response = {"id": request_id, "error": f"{type(error).__name__}: {error}"}
        print(json.dumps(response, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
