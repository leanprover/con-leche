#!/usr/bin/env python3
"""The line-placement fixtures (task #488, issue #15): `prop_proj.ndjson`
with its `meta` header missing, moved, or with other contents, or with a
blank line where a lean4export stream has none.

The format's first line is its `meta` header, and every later line is a
record; Lean's reader skips the first line and parses every later one as
a record.  The checker takes the header exactly as the first line,
whatever object it holds, and refuses a blank line anywhere:

* `meta_line_absent.ndjson`  — no header, the first line a record (exit 3);
* `meta_line_second.ndjson`  — the header again as line 2 (exit 3);
* `meta_line_late.ndjson`    — the header again in the middle (exit 3);
* `blank_line_mid.ndjson`    — an empty line in the middle (exit 3);
* `blank_line_final.ndjson`  — an empty line after the last record,
  the file ending in two newlines (exit 3);
* `meta_line_free.ndjson`    — a header with other contents than
  lean4export's (exit 0: what is in it is not read);
* `empty_file.ndjson`        — no lines at all (exit 0, no declarations,
  as Lean's reader).

Usage: scripts/mk_meta_line_fixtures.py   (reads and writes under tests/e2e/)
"""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E2E = os.path.join(ROOT, "tests/e2e")

with open(os.path.join(E2E, "prop_proj.ndjson"), "rb") as f:
    lines = f.read().split(b"\n")
assert lines[-1] == b"", "the source ends with a newline"
lines = lines[:-1]
assert lines[0].startswith(b'{"meta":'), "the source's first line is its header"
meta, recs = lines[0], lines[1:]
mid = len(recs) // 2
free = b'{"meta":{"exporter":"someone else","extra":[1,2.5,{"x":"y\\n"},null,true]}}'


def dump(name, ls, tail=b"\n"):
    with open(os.path.join(E2E, name), "wb") as f:
        f.write(b"\n".join(ls) + tail if ls else b"")
    print(f"{name}: {len(ls)} lines")


dump("meta_line_absent.ndjson", recs)
dump("meta_line_second.ndjson", [meta, meta] + recs)
dump("meta_line_late.ndjson", [meta] + recs[:mid] + [meta] + recs[mid:])
dump("blank_line_mid.ndjson", [meta] + recs[:mid] + [b""] + recs[mid:])
dump("blank_line_final.ndjson", [meta] + recs, tail=b"\n\n")
dump("meta_line_free.ndjson", [free] + recs)
dump("empty_file.ndjson", [])
