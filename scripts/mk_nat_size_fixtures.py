#!/usr/bin/env python3
"""Derive the numeral-budget e2e fixtures (task #519) from two raw exports.

The elaborator cannot state the theorems these fixtures are about (it
would compute `1 ^ 4000000000` or `2 ^ 4294967296` itself), so the
sources carry small placeholder exponents and this script replaces each
placeholder literal (a `natVal` record that occurs exactly once) by the
value the fixture is about:

  tests/e2e/nat_size.ndjson (tests/e2e/src/nat_size.lean):
    nat_size_ok.ndjson            201,202 -> 4000000000, 203 -> 4294967295,
                                  204 -> 16777216, 205 -> 100000000
    nat_pow_over_budget.ndjson    204 -> 16777217
    nat_pow_exp_32bit.ndjson      203 -> 4294967296
    nat_shift_over_budget.ndjson  205 -> 1073741760
    nat_shift_exp_32bit.ndjson    205 -> 4294967296
  tests/e2e/nat_size_limit_pow_huge_exp.ndjson:
    nat_size_limit_pow_32bit.ndjson  206 -> 4294967296

Usage: scripts/mk_nat_size_fixtures.py   (from the repository root)
"""
import json

E2E = "tests/e2e/"

FIXTURES = {
    "nat_size_ok": ("nat_size", {201: 4000000000, 202: 4000000000, 203: 4294967295,
                                 204: 16777216, 205: 100000000}),
    "nat_pow_over_budget": ("nat_size", {204: 16777217}),
    "nat_pow_exp_32bit": ("nat_size", {203: 4294967296}),
    "nat_shift_over_budget": ("nat_size", {205: 1073741760}),
    "nat_shift_exp_32bit": ("nat_size", {205: 4294967296}),
    "nat_size_limit_pow_32bit": ("nat_size_limit_pow_huge_exp", {206: 4294967296}),
}


def derive(base: str, patch: dict) -> str:
    lines = open(E2E + base + ".ndjson").read().splitlines()
    seen = {k: 0 for k in patch}
    out = []
    for line in lines:
        rec = json.loads(line)
        if "natVal" in rec and int(rec["natVal"]) in patch:
            k = int(rec["natVal"])
            seen[k] += 1
            rec["natVal"] = str(patch[k])
            line = json.dumps(rec, separators=(",", ":"), ensure_ascii=False)
        out.append(line)
    for k, n in seen.items():
        if n != 1:
            raise SystemExit(f"{base}: placeholder {k} occurs {n} times, expected once")
    return "\n".join(out) + "\n"


def main() -> None:
    for name, (base, patch) in FIXTURES.items():
        with open(E2E + name + ".ndjson", "w") as f:
            f.write(derive(base, patch))


if __name__ == "__main__":
    main()
