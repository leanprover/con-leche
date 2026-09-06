#!/usr/bin/env python3
"""Print the lech column of an arena run as a table.

Usage: scripts/arena/table.py <arena-clone> [checker-name] [results-dir] [results-dir]

Reads <results-dir>/<checker>_*.json (what `lka.py run` writes into
<arena-clone>/_results) and joins it with the expected outcome from
<arena-clone>/_build/tests/*.stats.json.
"""
import json
import sys
from pathlib import Path

STATUS = {"accepted": "accept", "rejected": "reject", "declined": "decline",
          "error": "ERROR"}


def human(n):
    if not n:
        return "-"
    for unit in ("B", "K", "M", "G"):
        if n < 1024 or unit == "G":
            return f"{n:.0f}{unit}" if unit == "B" else f"{n:.1f}{unit}"
        n /= 1024.0


def main():
    arena = Path(sys.argv[1])
    checker = sys.argv[2] if len(sys.argv) > 2 else "lech"
    results = Path(sys.argv[3]) if len(sys.argv) > 3 else arena / "_results"

    expected = {}
    for s in (arena / "_build" / "tests").rglob("*.stats.json"):
        d = json.load(open(s))
        expected[d["name"]] = d.get("outcome", "?")

    rows = []
    for r in sorted(results.glob(f"{checker}_*.json")):
        d = json.load(open(r))
        name = d["test"]
        exp = expected.get(name, "?")
        got = STATUS.get(d["status"], d["status"])
        rows.append((name, exp, got, d["correctness"], d["exit_code"],
                     d["wall_time"], d["max_rss"],
                     (d.get("stderr") or d.get("stdout") or "").strip().replace("\n", " ")[:100]))

    w = max((len(r[0]) for r in rows), default=10)
    print(f"{'test'.ljust(w)}  {'expect':7} {'got':7} {'ok':9} {'exit':>4} "
          f"{'wall':>9} {'rss':>8}  message")
    print("-" * (w + 60))
    counts = {}
    for name, exp, got, corr, ec, wall, rss, msg in rows:
        counts[corr] = counts.get(corr, 0) + 1
        print(f"{name.ljust(w)}  {exp:7} {got:7} {corr:9} {ec:>4} "
              f"{wall:>8.2f}s {human(rss):>8}  {msg if corr != 'correct' else ''}")
    print("-" * (w + 60))
    print(f"{len(rows)} results: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
