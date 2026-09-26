module

public import ConLeche.Semantics.DeclEta


import ConLeche.Verify.Denote.Rename

public import ConLeche.Verify.Extend.Recs

import ConLeche.Semantics.DeclRun
import ConLeche.Kernel.Checker
import ConLeche.Verify.Abstract
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst

@[expose] public section
/-!
# The inductive block's **relation-level** residue (task #161 S5,
THE SEPARATION — the C4 refutation's bill, paid)

S3's stop-and-name refuted the design census's C4 at the `indDecl`
kind: `declStepS`'s ind branch takes its η-closure from the whole
`DeclIndS` obligation, whose discharge reads `hEC₁`/`hBP₁` off
`indMembersS` and `hnonrecUp` off `indRecsS` — both **model-carrying**
installs.  The S3 seal sized the repair at "two ~800-line inductions
re-run η-only".

**MEASURED, THE SIZING IS WRONG, AND THAT IS THE FINDING.**  Nothing
of the two folds' model content is needed.  Every ingredient of
`declIndS`'s second component was already relation-level and V-free —
`indMembersR_mono`/`_indNew`/`_ctorEntry`, `indRecsR_noInd`,
`projInstallR_ext` — and the *one* ingredient that
was not, `indRecsS`'s `hnonrecUp`, is not a consequence of the install
at all: the group's install fold accumulates on the **base**
environment (`IndRecsFoldR`'s `acc` starts at `env₂`, not at the
provisional `envSelf`), and every name it conses was checked fresh
against that base.  So the preservation is `indRecsR_keep` below —
an eight-line `find?` walk, *stronger* than `hnonrecUp` (it needs no
"not a recursor" side condition and returns an equation), and the
recursor swap never enters.

This module is model-free by construction: no `V`, no `SetTheory`, no
`EnvS`.  It holds the relation-level lemmas the block folds' syntactic
residue consists of, moved here verbatim from
`SetR/Install/{IndRecsS,IndMembersS,DeclIndS}.lean`, plus the three new
lemmas the keep-fact needs and `declIndEtaClosed`, the ind kind's
η-closure proved from `DeclIndRun` alone.  `declIndS` routes its own
second component through it (one source of truth), and the P fold
consumes it instead of `declIndS memberKeyS mp.base`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## The provisioning's syntactic residue -/

/-! ## The group phase's keep-fact (task #161 S5 — the C4 bill)

`indRecsS` reports a *non-recursor* transport (`hnonrecUp`) and proves
it through the `EnvS` swap.  At the relation level the fact is both
simpler and stronger, and needs no install: `IndRecsFoldR` accumulates
on the group's **base** environment (`IndRecsR` starts the fold at
`env₂`, handing `envSelf` over only as the environment the *rules* are
checked against), and every name it conses was checked fresh against
that base by `MemberValR`.  So a base lookup that succeeds is
untouched — recursor or not. -/

/-! ## `declIndEtaClosed` — the ind kind's η-closure, model-free -/

/-- The reserved-name side condition of the group swap: a genuinely
swapped entry never sits at a pinned basis name. -/
def SwapNResS (env₀ env₃ : Env) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env₀.find? n = some (.recInfo cv mI rP []) →
    env₃.find? n = some (.recInfo cv mI rP rules) →
    rules = [] ∨ reservedBasisNames.contains n = false

end ConLeche.Semantics
