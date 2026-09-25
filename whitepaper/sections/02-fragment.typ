#import "../lib.typ": *

= The env-free fragment

This section presents the core of the argument on a fragment of Lean
without an environment: terms with the annotation, universe levels,
and the three relations that say what the checker does; then the set
theory the model is built in, the interpretation, the invariant that
replaces a typing judgement, and the three soundness claims with their
proofs.  Everything here is verified in the fragment's own Lean
development and linked, alongside its counterpart in the real proof.

#include "02a-syntax-rules.typ"
#include "02b-model-proof.typ"
