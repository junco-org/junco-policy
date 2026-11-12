#!/usr/bin/env python3
"""Translate recorded three-coordinate AgentDojo logs to principal-aware flow events.

Usage: python3 benches/agentdojo/translate_events.py SRC_RUN_DIR OUT_DIR
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys


EVENT = re.compile(r"\$(\d+) (Read|Receive|Contact) (trusted|untrusted|private|sink|peer)", re.ASCII)
REFERENCE = re.compile(r"\$(\d+)", re.ASCII)
FIELDS = (
    "suite", "user_task_id", "injection_task_id", "attack_type",
    "utility", "injection_success", "error",
)


def extraction_handles(messages):
    """Find Q outputs by matching provider call IDs, not event actions or labels."""
    calls = set()
    for message in messages:
        if message["role"] != "assistant":
            continue
        for block in message["content"]:
            if block["type"] == "toolcall" and block["function"]["name"] == "query_ai_assistant":
                calls.add(block["id"]["provider"])

    handles = set()
    for message in messages:
        if message["role"] != "user":
            continue
        for block in message["content"]:
            if block["type"] != "toolresult" or block["call"]["provider"] not in calls:
                continue
            for content in block["content"]:
                value = content.get("value")
                if not isinstance(value, dict) or "$ref" not in value:
                    continue
                reference = value["$ref"]
                match = REFERENCE.fullmatch(reference) if isinstance(reference, str) else None
                if match is None:
                    raise ValueError(f"invalid extraction reference: {reference!r}")
                handles.add(int(match[1]))
    return handles


def translate(source):
    """Translate one task, rejecting malformed events and misaligned contact records."""
    handles = extraction_handles(source["messages"])
    if not isinstance(source["events"], list) or not isinstance(source["policy_decisions"], list):
        raise ValueError("events and policy_decisions must be arrays")
    events = []
    contacts = []
    for event in source["events"]:
        match = EVENT.fullmatch(event) if isinstance(event, str) else None
        if match is None:
            raise ValueError(f"invalid event: {event!r}")
        handle, action, label = int(match[1]), match[2], match[3]
        reference = f"${handle}"
        if action == "Contact":
            events.append(["P", reference, "contact", label])
            contacts.append((handle, label))
        elif handle in handles:
            events.append(["Q", reference, action.lower(), label])
            events.append(["P", reference, "receive", label])
        else:
            events.append(["P", reference, action.lower(), label])

    decisions = source["policy_decisions"]
    if len(contacts) != len(decisions):
        raise ValueError(f"{len(contacts)} contacts but {len(decisions)} policy decisions")
    translated_decisions = []
    for index, ((handle, label), decision) in enumerate(zip(contacts, decisions)):
        if (
            not isinstance(decision, dict)
            or type(decision.get("handle")) is not int
            or decision["handle"] != handle
            or decision.get("class") != label
        ):
            raise ValueError(f"contact {index} (${handle}, {label}) does not match decision {decision!r}")
        translated_decisions.append({**decision, "principal": "P"})

    return {
        **{field: source[field] for field in FIELDS},
        "events": events,
        "policy_decisions": translated_decisions,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="directory of recorded three-coordinate task logs")
    parser.add_argument("output", type=Path, help="directory for translated four-coordinate task logs")
    args = parser.parse_args()
    source_root = args.source.resolve()
    output_root = args.output.resolve()
    if not source_root.is_dir():
        parser.error(f"not a source directory: {source_root}")
    if source_root == output_root or source_root in output_root.parents or output_root in source_root.parents:
        parser.error("source and output directories must not overlap")
    paths = sorted(source_root.glob("*/*/*/*.json"))
    if not paths:
        print(f"{source_root}: no canonical task logs", file=sys.stderr)
        return 1
    suites = Counter()
    event_count = 0
    contact_count = 0
    for path in paths:
        try:
            with path.open(encoding="utf-8") as stream:
                translated = translate(json.load(stream))
            relative = path.relative_to(source_root)
            output = output_root / relative
            output.parent.mkdir(parents=True, exist_ok=True)
            with output.open("w", encoding="utf-8") as stream:
                json.dump(translated, stream, indent=2, ensure_ascii=False)
                stream.write("\n")
            suites[relative.parts[0]] += 1
            event_count += len(translated["events"])
            contact_count += len(translated["policy_decisions"])
        except (OSError, ValueError, TypeError, KeyError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            return 1
    print(f"Translated {sum(suites.values())} tasks, {event_count} events, {contact_count} contacts")
    for suite, count in sorted(suites.items()):
        print(f"  {suite}: {count} tasks")
    return 0


if __name__ == "__main__":
    sys.exit(main())
