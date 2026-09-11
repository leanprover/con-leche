module

public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualRecPre2
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The mutual block's former stage (task #278, M2.5b)

`stageMutualFormer`: the P step at ONE member's cons — the member's
leaf `mutualTyAVI` (`Semantics/Tower/MutualLeafI.lean`) consed with the
block's EMPTY capability record, `stageFixFormer` with the fibre leaf
in place of the fixpoint one.  `mutualLeafWalks` is `fixLeafWalks` at
that leaf: the member's hereditary premise (`ParamsOkMI`) and the
tower's validity are walked from the former's binder data
(`FormerData`) down to the frame below the parameters and the member's
index variables, where the block's chain facts at the parameter frame
(the tag `TagOk`, the auxiliary family's `FixChainsOkI`, the chains'
validity) are the base.

`stageMutualFormers` folds it over the formers' loop
(`mutualFormers`): `k` conses, member `t`'s leaf at tag `t`, with the
members' binder data and the block's chain data given.  Its two
conclusions are the ones the constructor and recursor stages read: the
positional leaf equation at every member, and the agreement off the
block.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps MutualFormerA)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The member leaf's closedness, grading and validity -/

omit [SetTheory V] in
/-- **The member's leaf is closed**: its body is the auxiliary family
(closed at the parameters) applied to the auxiliary tupler at the
member's tagged tuple of its own index variables. -/
theorem mutualTyAVI_below {W w nP nIdx t : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess',
      FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow 0 (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss₀ Ess' t).erase := by
  have hauxB : FieldsBelow nP (auxIds W Idss) := ⟨tagTyAV_below hIds, trivial⟩
  unfold mutualTyAVI
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN nIdx
      (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess').erase nP 0
      (fixBodyAVI_below (w := w) (nIdx := 1) hauxB hchains)
    exact this
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN nIdx _ _ _ (tuplerAV_below hauxB)
    · intro a ha
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton] at hE
      subst hE
      refine tagTupleAV_below hIds ?_
      intro E hE
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hE
      rw [List.mem_range] at hj
      show Term.bvarsBelow (nP + nIdx) (Term.bvar (nIdx - 1 - j))
      show nIdx - 1 - j < nP + nIdx
      omega

/-- **The auxiliary family's functor is bit-valid** at the parameter
frame — `fixBody_validV`'s function half at the tag telescope, read
off a fitting one-element index spine. -/
theorem auxBodyAV_validV {W w : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss₀ Ess' : List (List AnnotTerm)}
    (hI : IdxOk W ρp (auxIds W Idss)) (hIV : FieldsValid ρp (auxIds W Idss))
    (hchains : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) →
      ∀ t, t ∈ˢ idxSet W ρp (auxIds W Idss) →
      SumFieldsValid (cons t (cons X ρp))
        (chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess'))
    {z : V} (hsp : SpineFit ρp (auxIds W Idss) [z]) :
    AnnotValid V ρp (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess') := by
  have h := fixBody_validV (u := W) (w := w) (Ids := auxIds W Idss) (rss := rss)
    (tlss := tlss) (Eiss := Eiss') (Fss := Fss₀) (Ess := Ess') hI hIV hchains hsp
  rw [AnnotValid_app] at h
  have hf := h.1
  rw [AnnotValid_liftN] at hf
  have hsh : shiftE (auxIds W Idss).length 0 (consList [z] ρp) = ρp := by
    rw [show (auxIds W Idss).length = [z].length from rfl]
    exact shiftE_consList _ ρp
  rw [hsh] at hf
  exact hf

