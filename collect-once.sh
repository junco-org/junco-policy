#!/usr/bin/env bash
# usage: ./collect.sh <pass-number>   — one pass over missing.tsv, skipping tasks that are now error-free
set -u
root=benches/agentdojo/runs/gpt-4.1+camel
consecutive=0
while IFS=$'\t' read -r suite user inj kind; do
  if [ "$inj" = "-" ]; then path="$root/$suite/$user/none/none.json"; sel="--clean-only"
  else path="$root/$suite/$user/important_instructions/$inj.json"; sel="--injection-task $inj"; fi
  err=$("$AGENTDOJO_PYTHON" -c 'import json,sys; print(json.load(open(sys.argv[1])).get("error") or "")' "$path")
  [ -z "$err" ] && continue
  echo "[pass $1] $suite/$user/$inj ($kind) start $(date -u +%T)" | tee -a collect.log
  cargo +1.98.1 bench --bench agentdojo -- --suite "$suite" --user-task "$user" $sel --concurrency 1 2>&1 | grep -E "^(workspace|banking|travel|slack)/" | tee -a collect.log
  err=$("$AGENTDOJO_PYTHON" -c 'import json,sys; print(json.load(open(sys.argv[1])).get("error") or "")' "$path")
  case "$err" in
    *"failed after provider retries"*) consecutive=$((consecutive+1)) ;;
    *) consecutive=0 ;;
  esac
  if [ "$consecutive" -ge 3 ]; then
    echo "[pass $1] 3 consecutive provider failures; quota wall, stopping $(date -u +%T)" | tee -a collect.log
    exit 2
  fi
done < missing.tsv
