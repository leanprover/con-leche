#import "../lib.typ": *

= The fragment without an environment

This section presents the core of the argument on a fragment of Lean
without an environment: first the terms, the levels and the three
relations that say what the checker does; then the set theory, the
interpretation, the semantic invariant that replaces a typing
judgement, and the three soundness claims with their proofs.
Everything here is verified in the fragment's own Lean development
and linked, alongside its counterpart in the real proof.

#include "02a-syntax-rules.typ"
#include "02b-model-proof.typ"
