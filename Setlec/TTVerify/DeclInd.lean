import Setlec.TTVerify.DeclBasis
import Setlec.Verify.Extend.Iota

/-!
# `DeclIndTT`: the modeled-inductive install

The tentpole, opened.  §14.3 names five obligations; this module holds
the pieces they share, and `EtaFoldTT`/`UnitFoldTT` first, because they
are the smallest and they close `CapsOkTT` — which `majorToCtor`'s
rescues already consume.

**What the scouting settled** (§14.1's gate, discharged): the whole
*syntactic* layer of the install — `EtaPins`, `checkEtaThm_inv`,
`checkUnitThm_inv`, `EtaPins.step`, `EtaPins.transport` — is already
`V`-free and lives in `Setlec/Verify/Extend/Iota.lean`, so the bridge
imports it rather than duplicating it.  Only the *assembly* of
`EtaPins` from a successful `checkIndDecl` exists solely inside the
model's proof (`Setlec/Model/Extend/Decl.lean:150`), and it is nine
lines; `etaPinsT_of_caps` below re-derives it.  It is `V`-free and a
candidate for sharing under #123's criterion — recorded here rather
than moved, because moving it would be a change to a file the model
path is mid-flight in.

**The counting that matters for the two folds.**  The model's
`unit_rule_fold` (`Setlec/Model/EtaInstall.lean:581`) has 21
hypotheses: **12 `V`-free syntactic** (find?s, `stripPis` shapes,
telescope-domain matches, `hasFvar = false`) and **9 semantic**
(`RenameOk`, `ConstValParams`, the `Eq` former's value, the theorem's
`∈ˢ` membership, `AnnotOk`, and the use site's `TeleFit`).  The bridge
inherits all twelve syntactic ones unchanged and replaces the nine:
`interpClosed`/`∈ˢ` become `denote`/`HasType`, `TeleFit` becomes
`VTeleTyped`, the `Eq` former's value becomes `EnvTT.eq_law`, and
`AnnotOk` — as everywhere in this hierarchy — disappears.  `RenameOk`
and `ConstValParams` have transposes in `EnvTT`'s own fields.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The shared final step

Both folds, and `ProjBottomTT` after them, end the same way: a
*checked theorem* is a closed term whose type is a Π-telescope ending
in the pinned `Eq` former applied to three arguments.  Fit the
telescope with the use site's spine, and the theorem's inhabitant
becomes a proof of that spine's equation — which §11's law turns into
a `Deq`.

This is the transpose of `eta_rule_fold`'s "the theorem's inhabitant is
eliminated through the statement, and the equality collapses to the
value identity", and it is *short* where the model's is not, for a
reason worth naming: the model has to produce a set-theoretic
inhabitant of an interpreted equality and then read equality of
*values* off it, while the layer's equality is a syntactic former and
`Deq.intro` is the whole elimination. -/

/-- **A checked equality theorem, fired at a use site.**  The last step
of `EtaFoldTT`, `UnitFoldTT` and `ProjBottomTT`. -/
theorem Deq.ofEqThm {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Δ : List VExpr} {v Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType Δ v Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (m.cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.intro (Setlec.TT.Deq.conv (hfit.appN hv)
    (m.eq_law hE ψ Δ A a b hA ha hb))

/-- The same, when the theorem is a *closed* constant's valuation —
which is how every checked `_model.*` theorem reaches a use site. -/
theorem Deq.ofEqThmClosed {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) {n : Name}
    {Δ : List VExpr} {Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType [] (m.cval n ψ) Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (m.cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.ofEqThm m hE ψ (HasType.weakenNil hv Δ) hfit hA ha hb

/-! ## The install's syntactic pins, assembled

`EtaPins` (`Setlec/Verify/Extend/Iota.lean:917`) is the conjunction of
both capability pins, each guarded by its flag.  The model builds it
inline; here it is a lemma, so that the two folds can take it as a
hypothesis and `DeclIndTT` can supply it once. -/

/-- **`EtaPins` from the stored capabilities.**  `indBlockCaps` sets
`eta` and `unitlike` from `checkEtaThm`/`checkUnitThm`, so the flags
holding *is* the checks having passed, and the two inversions do the
rest.  Nine lines, and the only part of the install's syntactic layer
the bridge has to write for itself. -/
theorem etaPinsT_of_caps {env : Env} {cvT cvC : ConstantVal} {nP nF : Nat} :
    EtaPins env cvT.name cvT.levelParams (indBlockCaps env cvT cvC nP nF) := by
  refine ⟨fun hcape => ?_, fun hcapu => ?_⟩
  · refine checkEtaThm_inv ?_
    simp only [indBlockCaps, Bool.and_eq_true] at hcape
    exact hcape.2
  · refine checkUnitThm_inv ?_
    simp only [indBlockCaps] at hcapu
    exact hcapu

/-! ## The phase's block-independent half

Each phase of this bridge has needed exactly one shared spine lemma
before any of its cases could be written: the basis blocks needed
`BetaSpine` (fire a λ-tower at a spine) and then `inst_chain₁₋₄`
(collapse what firing leaves behind).  This phase needs a third, and
it is worth naming the pattern: **the shared piece is always the one
that moves a spine between two descriptions of the same telescope.**

Here the two descriptions are the *public* type former's telescope,
which the use site's `VTeleTyped` is stated against, and the *checked
theorem's* statement telescope, which the fold has to apply the
theorem along.  The install's pins say the two agree binder for binder
(`sbinders[k].2.1 = tbindersM[k].2.1`, and the public-vs-model half by
`checkMemberVal_inv`'s `eqUpToNames`, which `denote_erasedEq`
(`Setlec/TTVerify/Inst.lean:265`) turns into equal denotations).  What
is missing is the step that *uses* that agreement: a spine that fits
one telescope fits the other.

That the domains agree while the *bodies* do not is the whole reason
this cannot be a rewrite — the public type former ends in a sort and
the statement ends in an equation, so only the fitting transfers, not
the residual.

**The pattern predicts the next phase's piece, and the prediction is
worth cashing early.**  If the shared piece is always the spine-mover
between two descriptions of a telescope, then the *bottoms*' shared
piece is whatever moves the **constructor** spine between the rule's
description of it and the fired redex's — and that is exactly where
§8.2's index premise lives (`ruleLhsAux` fills the recursor's index
slots with the constructor's canonical tuple; the fired form leaves
them free).  So the index-premise plumbing is not a *second* cost on
top of the bottoms' spine lemma: **it is that spine lemma.**  Two
anticipated pieces collapse into one, which is the first time this
bridge's pattern-noticing has bought a schedule change rather than an
explanation. -/

/-- Two `VExpr` telescopes met by the same spine, agreeing binder for
binder — **and both residuals named**.  Only the domains are
constrained, and only at the positions the spine reaches.

Naming the second residual is not decoration: a fold has to *continue*
past the retarget (the statement's telescope does not end where the
type former's does), so "some residual exists" is exactly the fact it
cannot use. -/
inductive TeleAlign : VExpr → VExpr → List VExpr → VExpr → VExpr → Prop
  | nil {T T' : VExpr} : TeleAlign T T' [] T T'
  | cons {A B B' x r r' : VExpr} {xs : List VExpr} :
      TeleAlign (B.inst x) (B'.inst x) xs r r' →
      TeleAlign (.pi A B) (.pi A B') (x :: xs) r r'

/-- **Retargeting a fitted spine.**  A spine that fits one telescope
fits any telescope aligned with it — at the residual the alignment
names.  The argument typings are *reused*, not re-derived, which is the
point: at a fold's use site they are hypotheses, not things the proof
can rebuild. -/
theorem VTeleTyped.retarget {Δ : List VExpr} :
    ∀ {T T' : VExpr} {xs : List VExpr} {rest rest' : VExpr},
      VTeleTyped Δ T xs rest → TeleAlign T T' xs rest rest' →
      VTeleTyped Δ T' xs rest' := by
  intro T T' xs rest rest' h
  induction h generalizing T' with
  | nil => intro ha; cases ha with | nil => exact .nil
  | @cons A B x xs rest hx _ ih =>
    intro ha
    cases ha with
    | cons ha' => exact .cons hx (ih ha')

/-- The alignment a fitting already carries: every telescope is aligned
with itself along any spine that fits it.  Note this is *not*
reflexivity of `TeleAlign` — a non-`∀` type has no domains to agree
about, so the relation is genuinely partial and the witness has to come
from a fitting. -/
theorem VTeleTyped.teleAlign {Δ : List VExpr} :
    ∀ {T rest : VExpr} {ys : List VExpr},
      VTeleTyped Δ T ys rest → TeleAlign T T ys rest rest := by
  intro T rest ys h
  induction h with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ih

end Setlec.TTVerify
