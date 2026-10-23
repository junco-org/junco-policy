#!/usr/bin/env python3
"""Downloads the AgentDojo and AgentDyn trace pipelines the replay examples read into
traces/<benchmark> (gitignored), pinned to the commits below so the tables stay reproducible.
Sparse, blob-less checkouts: only the selected pipeline's JSON is fetched (plus the repo's
top-level files, which cone mode always includes).

Refetch by deleting traces/<benchmark>; add a pipeline with
`git -C traces/<benchmark> sparse-checkout add runs/<pipeline>`.
"""

import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# (benchmark, url, commit, pipeline)
TRACES = [
    (
        "agentdojo",
        "https://github.com/ethz-spylab/agentdojo.git",
        "089ed468cf3ed0322acc66b0211f26d9d90dbf60",
        "gpt-4o-2024-05-13",
    ),
    (
        "agentdyn",
        "https://github.com/SaFo-Lab/AgentDyn.git",
        "5353cf7615b135cace8d07c8f12dac53a16b6db3",
        "gpt-4o-2024-08-06",
    ),
]


def git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True)


def fetch(benchmark, url, commit, pipeline):
    repo = ROOT / "traces" / benchmark
    shown = repo.relative_to(ROOT).as_posix()
    if repo.exists():
        print(f"{shown} exists, skipping")
        return
    try:
        subprocess.run(["git", "init", "-q", str(repo)], check=True)
        git(repo, "remote", "add", "origin", url)
        git(repo, "sparse-checkout", "set", "--cone", f"runs/{pipeline}")
        git(repo, "fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", commit)
        git(repo, "checkout", "-q", commit)
    except BaseException:
        # a half-fetched directory would be skipped as "exists" on the next run
        shutil.rmtree(repo, ignore_errors=True)
        raise
    print(f"{shown}/runs/{pipeline}")


if __name__ == "__main__":
    for trace in TRACES:
        fetch(*trace)
