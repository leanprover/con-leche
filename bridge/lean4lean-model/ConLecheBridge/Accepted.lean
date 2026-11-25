import ConLecheBridge.StandardNat
import ConLeche.Verify.IsModelRecords
import ConLeche.Model.PureChecker

/-!
# Accepted streams: `Nat` is the standard naturals in Carneiro's set theory

`carneiro_nat_standard` (`ConLecheBridge/StandardNat.lean`) is about every model of a stream
that declares the prelude's `Nat` and `Eq` (`DeclaresNat`, `DeclaresEq`).  This module ties
those two hypotheses to what the checker accepts:

* `checkDecls_declaresNat`: an accepted stream that stores `Nat` declares the prelude's `Nat`.
  The checker compares a block with the pinned names against the pin (`natBasis`), up to the
  records' level-parameter names; this is `Cached.checkDecls_declaresFalse` and
  `Cached.checkDecls_declaresEq` (`ConLeche/Verify/IsModelRecords.lean`) for `Nat`.
* `carneiro_accepted_nat_standard`: under Carneiro's hypothesis, every stream the checker
  accepts that stores `Nat` and `Eq` has a model, in `setTheoryOfCarneiro`, in which the
  literals' values are exactly the members of what `Nat` denotes, each once.
-/

universe u

open ConLeche

namespace ConLecheBridge

/-- **An accepted stream that stores `Nat` declares the prelude's `Nat`.** -/
theorem checkDecls_declaresNat {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env} {env : Env}
    (h : Cached.checkDeclsWith mode pins maxNatSize ds justify = .ok env)
    (hs : (env.find? natName).isSome = true) : DeclaresNat (· ∈ constantsOf ds.toList) := by
  obtain ⟨block, nP, hmem, hok⟩ := Cached.checkDecls_pinned h (kind := .natK) (by decide)
    (n := natName) (by decide) hs
  match block, hok with
  | [b1, b2, b3, b4], hok =>
    simp only [BasisKind.decls, natBasis, listBeqBy, Bool.and_eq_true] at hok
    obtain ⟨hcv1, -, hl1⟩ := Cached.pinCopyOk_cv hok.1 rfl
    obtain ⟨hcv2, -, hl2⟩ := Cached.pinCopyOk_cv hok.2.1 rfl
    obtain ⟨hcv3, -, hl3⟩ := Cached.pinCopyOk_cv hok.2.2.1 rfl
    obtain ⟨-, -, hl4⟩ := Cached.pinCopyOk_cv hok.2.2.2.1 rfl
    have hd4 := pinCopyOk_dropCaps hok.2.2.2.1 rfl
    match hq1 : b1.toConstantVal.levelParams, hl1, hq2 : b2.toConstantVal.levelParams, hl2,
      hq3 : b3.toConstantVal.levelParams, hl3, hq4 : b4.toConstantVal.levelParams, hl4 with
    | [], _, [], _, [], _, [p], _ =>
      have hb : ∀ b ∈ ([b1, b2, b3, b4] : List ConstantInfo), b ∈ constantsOf ds.toList :=
        fun b hb => mem_constantsOf.2 ⟨_, hmem, hb⟩
      refine ⟨⟨b1, hb _ (by simp), ?_⟩, ⟨b2, hb _ (by simp), ?_⟩, ⟨b3, hb _ (by simp), ?_⟩, p, ?_⟩
      · rw [hcv1, hq1]; rfl
      · rw [hcv2, hq2]; rfl
      · rw [hcv3, hq3]; rfl
      · rw [hq4] at hd4
        have h4 : b4 = natRecA.atLps [p] := by
          rw [natRecA_atLps] at hd4 ⊢
          cases b4 with
          | indInfo cv caps => exact nomatch hd4
          | _ => exact hd4
        exact h4 ▸ hb b4 (by simp)
  | [], hok | [_], hok | [_, _], hok | [_, _, _], hok | _ :: _ :: _ :: _ :: _ :: _, hok =>
    simp [BasisKind.decls, natBasis, listBeqBy] at hok

/-- **Under Carneiro's hypothesis, an accepted stream that stores `Nat` and `Eq` has a model in
which `Nat` is the standard naturals**: a model, in the set theory `setTheoryOfCarneiro` builds,
in which the literals' values `natLitVal model : ℕ → ZFSet` are exactly the members of what
`Nat` denotes, each once.  The same holds of every model of the stream there
(`carneiro_nat_standard`). -/
theorem carneiro_accepted_nat_standard (hO : OmegaInaccessibles.{u}) (pins : List NatOpPinSet)
    (maxNatSize : Nat) (ds : Array Declaration) {env : Env}
    (accepted : Cached.checkDecls .verified pins maxNatSize ds = .ok env)
    (hNat : (env.find? natName).isSome = true) (hEq : (env.find? eqName).isSome = true) :
    ∃ model : Name → List ℕ → ZFSet.{u},
      @IsModel ZFSet.{u} (setTheoryOfCarneiro hO) model (· ∈ constantsOf ds.toList) ∧
      (∀ x : ZFSet.{u}, x ∈ model natName [] ↔
        ∃ k : ℕ, x = @natLitVal ZFSet.{u} (setTheoryOfCarneiro hO) model k) ∧
      Function.Injective (@natLitVal ZFSet.{u} (setTheoryOfCarneiro hO) model) := by
  obtain ⟨model, hm⟩ := @model_exists ZFSet.{u} (setTheoryOfCarneiro hO) pins maxNatSize ds
    (by rw [accepted]; rfl)
  exact ⟨model, hm, carneiro_nat_standard hO hm (checkDecls_declaresNat accepted hNat)
    (Cached.checkDecls_declaresEq accepted hEq)⟩

/--
info: 'ConLecheBridge.carneiro_accepted_nat_standard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms carneiro_accepted_nat_standard

end ConLecheBridge
