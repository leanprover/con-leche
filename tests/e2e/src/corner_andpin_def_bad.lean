prelude
--#export And.self

/- Corner case (lane ANDPIN, 2026-09-30): `And` is pinned, whatever kind
   of record claims the name.  This stream declares `And` as a
   DEFINITION (`And a b := a`) and uses it.  The fold rejects the record
   (`andPinOk`).  Official 0 (no pins).  Today 1; that is the target. -/

def And (a _b : Prop) : Prop := a

theorem And.self {a b : Prop} (h : a) : And a b := h
