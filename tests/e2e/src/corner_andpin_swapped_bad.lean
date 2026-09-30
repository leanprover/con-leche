prelude
--#export And.swap

/- Corner case (lane ANDPIN, 2026-09-30): `And` is pinned.  This stream
   declares its OWN `And`, a valid structure with the two fields in the
   other order (`intro (right : b) (left : a)`).  The stuck-proof rescue
   (`majorToCtor`'s `And` branch) is code for the toolchain's `And`, so
   the fold rejects the block (`andPinOk`: "`And` must be the standard
   `And`") rather than accept the stream with the rescue silently
   unavailable.  Official 0 (no pins).  Today 1; that is the target. -/

structure And (a b : Prop) : Prop where
  intro ::
  right : b
  left : a

theorem And.swap {a b : Prop} (h : And a b) : And b a :=
  And.intro h.left h.right
