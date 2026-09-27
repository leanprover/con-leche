module

public import ConLeche.Model.Inductives.HoleRelK
public import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# A node's base, instantiated at a use (PRIMREC / NESTKN-M3)

At a use of a key-named node, the user's layout `L` (depth `d`, valuation
`ρ`) instantiates the node's BASE — its flexible families over the block's
parameters and members, depth `hc = hiAt0 + nF` — by the match's bindings:
the members and parameters are the user's (`dropV (d - hiAt0) ρ`), family
`j` holds the value of its binding `xs[j]` at `ρ` (`useVal`).  Along the
image of a hole relation of the user (`useRel`):

* `holeRelK_use`: the image is a hole relation at the node's base, given
  that the bindings' values inhabit the families' types (`hsat`) and that
  every family the node MET is bound to a value growing along the user's
  relation (`HoleOnVal`);
* `keyFrame_useVal`: the node's key frame at the image is the user's key
  frame, given the parameters read the same (the match's check).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey LayoutK)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **A value's order along a relation**, at every spine of `n` arguments
(a family's order at its index count). -/
@[expose] def HoleOnVal (R : FrameRel V) (a : AnnotTerm) (n : Nat) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ as : List V, as.length = n →
    as.foldl app (interp V ρ a) ⊆ˢ as.foldl app (interp V ρ' a)

/-- **The node's base valuation at a use**: the bindings' values `xs` over
the user's valuation seen `k = d - hiAt0` positions down. -/
@[expose] noncomputable def useVal (xs : List AnnotTerm) (k : Nat) (ρ : Nat → V) : Nat → V :=
  consList (xs.map (interp V ρ)) (dropV k ρ)

/-- **The image of the user's relation** at the node's base. -/
@[expose] def useRel (R : FrameRel V) (xs : List AnnotTerm) (k : Nat) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ', R ρ ρ' ∧ σ = useVal xs k ρ ∧ σ' = useVal xs k ρ'

theorem useVal_base {xs : List AnnotTerm} {k : Nat} (ρ : Nat → V) (i : Nat) :
    useVal xs k ρ (i + xs.length) = ρ (i + k) := by
  unfold useVal
  have := consList_apply_add (xs.map (interp V ρ)) (dropV k ρ) i
  rw [List.length_map] at this
  rw [this]; rfl

theorem useVal_fam {xs : List AnnotTerm} {k : Nat} (ρ : Nat → V) {j : Nat} (hj : j < xs.length) :
    useVal xs k ρ (xs.length - 1 - j) = interp V ρ xs[j] := by
  unfold useVal
  have := consList_getElem_pos (xs := xs.map (interp V ρ)) (ρ := dropV k ρ)
    (by rw [List.length_map]) hj
  rw [this, List.getElem_map]

/-- **The image of a user's hole relation is a hole relation at the node's
base** (see the module docstring). -/
theorem holeRelK_use {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (hR : HoleRelK m φ ctx L met d Δa R)
    (hd : L.hi ≤ d) {L' : LayoutK} {metc : List Nat} {xs tya : List AnnotTerm}
    (hxl : xs.length = L'.nF)
    (hsat : ∀ ρ, Sat V Δa ρ →
      SpineFit (dropV (d - ctx.hiAt 0) ρ) tya (xs.map (interp V ρ)))
    (hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < L'.nF → L'.fams[j]? = some (key, nI) →
      j ∈ metc → ∀ hj : j < xs.length, HoleOnVal R xs[j] nI)
    (hdsw : ∀ x ∈ L'.dsF, Expr.WScoped (ctx.hiAt 0 + L'.nF) x) :
    HoleRelK m φ ctx (layoutBaseK ctx L') metc (ctx.hiAt 0 + L'.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) (useRel R xs (d - ctx.hiAt 0)) := by
  have h0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- dom
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨sat_of_spineFit (Sat_drop h1 _) (hsat ρ h1), sat_of_spineFit (Sat_drop h2 _) (hsat ρ' h2)⟩
  · -- agree: off the holes the image is the user's valuation, off the user's holes
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    simp only [layoutBaseK_hi] at hi
    by_cases hin : i < xs.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, by omega⟩
      simp only [NestCtx.hiAt] at hxl ⊢; omega
    obtain ⟨q, rfl⟩ : ∃ q, i = q + xs.length := ⟨i - xs.length, by omega⟩
    rw [useVal_base, useVal_base]
    refine hR.agree ρ ρ' hr (q + (d - ctx.hiAt 0)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, by omega⟩
    omega
  · -- member
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
    have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.nP + t) = (ctx.hiAt 0 - 1 - (ctx.nP + t)) + xs.length := by
      omega
    rw [e, useVal_base, useVal_base,
      show ctx.hiAt 0 - 1 - (ctx.nP + t) + (d - ctx.hiAt 0) = d - 1 - (ctx.nP + t) by omega]
    exact hR.member t ht ρ ρ' hr as has
  · -- the met families: their bindings grow
    rintro j key nI hj hk hmet' _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    simp only [layoutBaseK_nF, layoutBaseK_fams] at hj hk
    have hjx : j < xs.length := by omega
    have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.hiAt 0 + j) = xs.length - 1 - j := by omega
    rw [e, useVal_fam ρ hjx, useVal_fam ρ' hjx]
    exact hmet j key nI hj hk hmet' hjx ρ ρ' hr as has
  · -- no own group at the base
    intro g n hg; simp at hg
  · exact hdsw

/-- **The node's key frame at the image is the user's key frame**, where
the node's parameters read at the image as the user's at `ρ`. -/
theorem keyFrame_useVal {xs dsa psa : List AnnotTerm} {h0 d : Nat} (hd : h0 ≤ d) (ρ : Nat → V)
    (hpos : dsa.map (interp V (useVal xs (d - h0) ρ)) = psa.map (interp V ρ)) :
    keyFrame dsa (h0 + xs.length) (useVal xs (d - h0) ρ) = keyFrame psa d ρ := by
  unfold keyFrame
  rw [hpos]
  congr 1
  funext j
  rw [show j + (h0 + xs.length) = (j + h0) + xs.length by omega, useVal_base]
  congr 1; omega

/-! ## The match's substitution, read -/

/-- **The match's substitution as a parallel one** (`substFvars` at
`h0 + |bs|`): the parameters and members kept, family `j` its binding. -/
@[expose] def useSubst (h0 : Nat) (bs : List Expr) : Nat → Expr :=
  fun v => if v < h0 then .fvar v (.sort .zero) else bs.getD (v - h0) (.sort .zero)

/-- Its readings at the user's depth `d`. -/
@[expose] def useX (h0 d : Nat) (xs : List AnnotTerm) : Nat → AnnotTerm :=
  fun v => if v < h0 then .bvar (d - 1 - v) else xs.getD (v - h0) default

/-- The valuation the substituted reading is read at is the node's base
valuation at the use. -/
theorem substE_useX {h0 d : Nat} (hd : h0 ≤ d) (xs : List AnnotTerm) (ρ : Nat → V) :
    substE V (substTau (h0 + xs.length) d (useX h0 d xs)) 0 ρ = useVal xs (d - h0) ρ := by
  rw [substE_substTau]
  unfold useVal
  congr 1
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, useX, if_neg (show ¬ h0 + i < h0 by omega),
      show h0 + i - h0 = i by omega]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂)]
    rfl
  · funext q
    unfold dropV
    by_cases hq : q < h0
    · rw [if_pos hq]
      simp only [useX, if_pos (show h0 - 1 - q < h0 by omega), interp_bvar]
      congr 1; omega
    · rw [if_neg hq]; congr 1; omega

/-- **The match's substitution, read** (`replaceFVars` at bindings `bs` of
the families `h0 ..< h0 + |bs|`, nothing below `h0`): the reading of the
substituted parameter at the user's depth is the parameter's reading at the
node's base depth, substituted by the bindings' readings. -/
theorem denoteMeta_replaceFVars_use {h0 d : Nat} (hd : h0 ≤ d) {θ : Nat → Option Expr}
    {bs : List Expr} {xs : List AnnotTerm}
    (hθlo : ∀ v, v < h0 → θ v = none)
    (hθ : ∀ j (hj : j < bs.length), θ (h0 + j) = some bs[j])
    (hbs : ∀ b ∈ bs, Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true)
    (hxs : DenoteMetaSpine m.acval env φ d bs xs) {p : Expr}
    (hp : p.fvarsBelow (h0 + bs.length)) :
    denoteMeta m.acval env φ d (p.replaceFVars θ)
      = (denoteMeta m.acval env φ (h0 + bs.length) p).map
          (AnnotTerm.substAV (substTau (h0 + bs.length) d (useX h0 d xs)) · 0) := by
  have hl : bs.length = xs.length := DenoteMetaSpine.length_eq hxs
  have hE := ConLeche.Expr.replaceFVars_erasedEq_substFvars (g := θ) (b := h0 + bs.length) (D := d)
    (s := useSubst h0 bs) (fun v hv ty => by
      unfold useSubst
      by_cases hv0 : v < h0
      · rw [hθlo v hv0, if_pos hv0]; rfl
      · obtain ⟨j, rfl⟩ : ∃ j, v = h0 + j := ⟨v - h0, by omega⟩
        have hj : j < bs.length := by omega
        rw [hθ j hj, if_neg hv0, show h0 + j - h0 = j by omega, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj]
        exact ConLeche.Expr.ErasedEq.rfl _) p hp
  rw [denoteMeta_erasedEq hE d]
  have h := denoteMeta_substFvars (φ := φ) m (b := h0 + bs.length) (D := d) (s := useSubst h0 bs)
    (x := useX h0 d xs) (fun i hi => by
      unfold useSubst useX
      by_cases hi0 : i < h0
      · rw [if_pos hi0, if_pos hi0]
        refine ⟨by simp only [Expr.WScoped]; exact ⟨by omega, trivial⟩, rfl, denoteMeta_fvar _ _ _ _⟩
      · rw [if_neg hi0, if_neg hi0]
        have hj : i - h0 < bs.length := by omega
        have hmem : bs.getD (i - h0) (.sort .zero) ∈ bs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _
        refine ⟨(hbs _ hmem).1, (hbs _ hmem).2, ?_⟩
        rw [DenoteMetaSpine.getD hxs _ _ hj]) p 0 (by simpa using hp)
  simpa using h

/-- **A parameter matched syntactically reads, at the node's base
valuation, as its spelling at the user**. -/
theorem interp_of_replaceFVars_use {h0 d : Nat} (hd : h0 ≤ d) {θ : Nat → Option Expr}
    {bs : List Expr} {xs : List AnnotTerm}
    (hθlo : ∀ v, v < h0 → θ v = none)
    (hθ : ∀ j (hj : j < bs.length), θ (h0 + j) = some bs[j])
    (hbs : ∀ b ∈ bs, Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true)
    (hxs : DenoteMetaSpine m.acval env φ d bs xs) {p : Expr}
    (hp : p.fvarsBelow (h0 + bs.length)) {pa qa : AnnotTerm}
    (hpa : denoteMeta m.acval env φ (h0 + bs.length) p = some pa)
    (hqa : denoteMeta m.acval env φ d (p.replaceFVars θ) = some qa) (ρ : Nat → V) :
    interp V ρ qa = interp V (useVal xs (d - h0) ρ) pa := by
  rw [denoteMeta_replaceFVars_use hd hθlo hθ hbs hxs hp, hpa, Option.map_some] at hqa
  cases hqa
  rw [interp_substAV, ← substE_useX hd xs ρ, DenoteMetaSpine.length_eq hxs]

/-- The same, the parameter's own reading OBTAINED from its spelling's. -/
theorem reads_of_replaceFVars_use {h0 d : Nat} (hd : h0 ≤ d) {θ : Nat → Option Expr}
    {bs : List Expr} {xs : List AnnotTerm}
    (hθlo : ∀ v, v < h0 → θ v = none)
    (hθ : ∀ j (hj : j < bs.length), θ (h0 + j) = some bs[j])
    (hbs : ∀ b ∈ bs, Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true)
    (hxs : DenoteMetaSpine m.acval env φ d bs xs) {p : Expr}
    (hp : p.fvarsBelow (h0 + bs.length)) {qa : AnnotTerm}
    (hqa : denoteMeta m.acval env φ d (p.replaceFVars θ) = some qa) :
    ∃ pa, denoteMeta m.acval env φ (h0 + bs.length) p = some pa ∧
      ∀ ρ : Nat → V, interp V ρ qa = interp V (useVal xs (d - h0) ρ) pa := by
  have h := denoteMeta_replaceFVars_use hd hθlo hθ hbs hxs hp
  rw [hqa] at h
  rcases hpa : denoteMeta m.acval env φ (h0 + bs.length) p with _ | pa
  · rw [hpa] at h; simp at h
  exact ⟨pa, rfl, interp_of_replaceFVars_use hd hθlo hθ hbs hxs hp hpa hqa⟩

end ConLeche.Model
