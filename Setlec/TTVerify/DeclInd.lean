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

end Setlec.TTVerify
