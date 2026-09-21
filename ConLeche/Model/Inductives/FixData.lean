module

public import ConLeche.Model.Inductives.BlockData
public section

/-!
# The recursive constructor's data at ONE member (task #188, #315 M3)

`BlockData.lean` at a single family: `FixOpened` and `FixCtorDataI`
are the block forms with every recursive or reflexive field targeting
the family itself (`Tof = fun _ => T`, `nIdxOf = fun _ => nIdx`), and
`fixCtorData_of` is `blockCtorData_of` with the opened-form guard read
off `nativeOpenedOk` instead of `blockOpenedOk`.  Everything the
one-member route consumes — `opened`, `domRead`, `eisRead`,
`recEntry`, `reflEntry`, the telescopes — keeps its statement, because
at a single family `Tof i` IS `T`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The opened-form guard, positionally -/

/-- `nativeOpenedOk`, read positionally — `BlockOpened` with every
field targeting the family. -/
abbrev FixOpened (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx nF : Nat)
    (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr) : Prop :=
  BlockOpened env₀ (fun _ => T) (fun _ => nIdx) lps nP nF ks fvsP xFvs xrest

theorem fixOpened_of {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx : Nat} {cty : Expr}
    {nF : Nat} {ks : List RecFieldKind}
    (h : ConLeche.nativeOpenedOk env₀ T lps nP nIdx cty nF ks = true) :
    ∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
      openPisAtFvars nP cty 0 = some (fvsP, crest) ∧
      openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
      FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest := by
  unfold ConLeche.nativeOpenedOk at h
  split at h
  · next fvsP crest hop =>
    split at h
    · next xFvs xrest hox =>
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      obtain ⟨hres, hall⟩ := h
      have hlenX : xFvs.length = nF := openPisAtFvars_length _ hox
      refine ⟨fvsP, crest, xFvs, xrest, hop, hox, ⟨hres, ?_, ?_, ?_, ?_⟩⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        exact this
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, List.any_eq_false] at this
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
        exact ⟨h1, h2, h3, h4, fun y hy => by simpa using h5 y hy, h6⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        dsimp only at this
        cases hopA : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
        | none => rw [hopA] at this; exact nomatch this
        | some q =>
          obtain ⟨afvs, body⟩ := q
          rw [hopA] at this
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, List.any_eq_false, bne_iff_ne, ne_eq] at this
          obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
          exact ⟨afvs, body, rfl, h1, h2, h3, h4, h5, h6, fun y hy => by simpa using h7 y hy, h8⟩
      · intro i hi
        have := hall i hi
        cases hx : xFvs[i]? with
        | none => rw [hx] at this; exact nomatch this
        | some x =>
          rw [hx] at this
          cases hk : ks.getD i .ordinary with
          | ordinary => exact Or.inl rfl
          | recursive => exact Or.inr (Or.inl rfl)
          | reflexive => exact Or.inr (Or.inr rfl)
          | negative => rw [hk] at this; exact nomatch this
          | unsupported => rw [hk] at this; exact nomatch this
    · exact nomatch h
  · exact nomatch h

/-! ## The constructor's data -/

/-- **A recursive constructor's data** at a carrier storing the former
— `BlockCtorDataI` with every field targeting the family. -/
abbrev FixCtorDataI {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (Eiss : (Name → Nat) → List (List AnnotTerm))
    (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop :=
  BlockCtorDataI m env₀ T (fun _ => T) (fun _ => nIdx) lps cvC nP nF nIdx resSort isProp large
    idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss

/-- **The recursive constructor's data**, from its stage run at the
environment holding the former and the opened-form guard. -/
theorem fixCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ks : List RecFieldKind}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hks : ks.length = nF)
    (hopened : ConLeche.nativeOpenedOk env₀ T lps nP nIdx cvCa.type nF ks = true) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat))
      (fvsP xFvs : List Expr) (xrest : Expr) (Eiss : (Name → Nat) → List (List AnnotTerm))
      (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs
        ks fvsP xFvs xrest Eiss tss :=
  blockCtorData_of hμ mp hCtor hfT hlpsT hstripT hks
    (fun _ => ⟨cvTa, caps, resSort, bs, hfT, hlpsT, hstripT, fun _ => rfl⟩)
    (by
      intro fvsP crest xFvs xrest hp hx
      obtain ⟨fvsP', crest', xFvs', xrest', hp', hx', hO⟩ := fixOpened_of hopened
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans hp'))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hx'))
      exact hO)

end ConLeche.Model
