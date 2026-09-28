module

public import ConLeche.Model.Inductives.ClassN2
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.NatEqs
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# A container instance, read at its leaf

The container case's reading: `C.{us} ds is` is the container's former
applied, which the clause's `leaf` reads as the carrier at the key's
parameter frame (`keyFrame`), at the index tuple.  The application's
grading (the walked field domain is graded) makes the key's parameters
fit the container's parameter telescope and the indices its index
telescope (`keyFit_of_wd`: the former inhabits its type's Π-tower, M4,
and a graded application of a Π-tower's inhabitant fits it); so the
instance grows along a hole relation as soon as the carrier does at the
two key frames (`monoOn_of_famLe`) — the index sets being the same there
(N2, `n2_link`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **The key's arguments fit the container's former telescope** (the
former's reading, M4, at the key's levels), at every valuation where the
application is graded. -/
theorem keyFit_of_wd {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep : Nat}
    {args : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const (D.member mm) us) args)
      = some wa)
    (hlen : args.length = (D.pars mm (Level.substFn φ cv.levelParams us)).length
      + (D.ids mm (Level.substFn φ cv.levelParams us)).length) :
    us.length = cv.levelParams.length ∧ ∃ vs, DenoteMetaSpine mp.base2.acval env φ dep args vs ∧
      wa = AnnotTerm.mkAppN (mp.base2.acval (D.member mm) (Level.substFn φ cv.levelParams us)) vs ∧
      ∀ ρ : Nat → V, WellDenoted V ρ wa → ∀ σ : Nat → V,
        SpineFit σ (D.pars mm (Level.substFn φ cv.levelParams us)
          ++ D.ids mm (Level.substFn φ cv.levelParams us)) (vs.map (interp V ρ)) := by
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, rfl⟩ := Rules.denoteMeta_const_arityK hf hfa
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hul ⊢
  refine ⟨hul, vs, hsp, rfl, fun ρ hwd σ => ?_⟩
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlen hwd ⊢
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨ab, hta, hmap, hbits⟩ := hab ψ
  have hmem := ConLeche.Semantics.Env.find?_mem hf
  have hname := ConLeche.Semantics.Env.find?_name hf
  have hin := mp.mem_type _ hmem ψ _ hta ρ
  rw [hname] at hin
  have hwf := mp.base2.wf _ hmem
  have hcl : Term.bvarsBelow 0 (mkPisAV ab (.sort (D.w ψ))).erase :=
    ConLeche.Verify.denote_bvarsBelow mp.base2.cval_closedL 0 _
      (ConLeche.Expr.WScoped.of_not_hasFvar hwf.1) hwf.2.2.2.1
      (denoteMeta_erase mp.base2.acval_erase 0 _ hta)
  rw [interp_closed V hcl ρ σ] at hin
  have hsp' := spineFit_of_wellDenoted_mkAppN_pi hbits hwd hin
    (by rw [← DenoteMetaSpine.length_eq hsp, hlen, ← List.length_append, ← hmap, List.length_map])
  rwa [hmap] at hsp'

/-- The valuation `n` positions down. -/
@[expose] def dropV (n : Nat) (ρ : Nat → V) : Nat → V := fun i => ρ (i + n)

/-- **The container instance at its leaf** (see the module docstring): at
every valuation where `C.{us} (ds ++ is)` is graded, the key frame
satisfies the container's parameter telescope, the indices fit its index
telescope there, and the instance is the carrier's component at the
index tuple.  `ds` are scoped at `b ≤ dep` (the walk's hole bound) and
read there as `dsa`. -/
theorem keyLeafW {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ b ds dsa) :
    us.length = cv.levelParams.length ∧ ∃ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa ∧
      ∀ ρ : Nat → V, WellDenoted V ρ wa →
        Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
            (keyFrame dsa b (dropV (dep - b) ρ)) ∧
        SpineFit (keyFrame dsa b (dropV (dep - b) ρ)) (D.ids mm (Level.substFn φ cv.levelParams us))
            (isa.map (interp V ρ)) ∧
        interp V ρ wa = app (D.carrier (Level.substFn φ cv.levelParams us)
            (keyFrame dsa b (dropV (dep - b) ρ)) mm)
          (tupW (D.u mm (Level.substFn φ cv.levelParams us)) (isa.map (interp V ρ))) := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hpl := h.parsLen mm hmm (Level.substFn φ cv.levelParams us)
  obtain ⟨hul, vs, hsp, rfl, hfit⟩ := keyFit_of_wd mp hD hmm hf hwa
    (by rw [List.length_append, hlenP, hlenI, hpl])
  refine ⟨hul, ?_⟩
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
  refine ⟨vs₂, hsp₂, fun ρ hwd => ?_⟩
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hpl hlenP hlenI hfit hwd ⊢
  have hlift := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hbd hdsw hdsa
  obtain rfl := DenoteMetaSpine.unique hsp₁ hlift
  have has : (dsa.map (AnnotTerm.liftN (dep - b) · 0)).map (interp V ρ)
      = dsa.map (interp V (dropV (dep - b) ρ)) := by
    rw [List.map_map]
    exact List.map_congr_left fun a _ => interp_liftN_drop _ ρ a
  generalize hτ : (fun j => dropV (dep - b) ρ (j + b)) = τ
  have hkf : keyFrame dsa b (dropV (dep - b) ρ) = consList (dsa.map (interp V (dropV (dep - b) ρ))) τ := by
    rw [← hτ]; rfl
  rw [hkf]
  generalize hasd : dsa.map (interp V (dropV (dep - b) ρ)) = as at has
  have hfτ := hfit ρ hwd τ
  rw [List.map_append, has] at hfτ
  obtain ⟨as₁, as₂, heq, hs₁, hs₂⟩ := spineFit_append_inv hfτ
  have hl₁ : as₁.length = as.length := by
    rw [hs₁.length_eq, hpl, ← hlenP, ← hasd, List.length_map, ← DenoteMetaSpine.length_eq hdsa]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl₁.symm
  have hsatP : Sat V (D.pars mm ψ).reverse (consList as τ) := by
    have := sat_of_spineFit (Sat_nil V τ) hs₁
    simpa using this
  have hsat := h.parsSatInv mm hmm ψ _ hsatP
  refine ⟨hsat, hs₂, ?_⟩
  have hsa : SpineFit τ (D.params ψ) as :=
    spineFit_of_sat_consList (by rw [← hasd, List.length_map,
      ← DenoteMetaSpine.length_eq hdsa, hlenP]) hsat
  rw [interp_mkAppN_foldl, List.map_append, has,
    acval_interp_closed mp.base2 _ ψ ρ τ]
  exact h.leaf mm hmm ψ τ as _ hsa hs₂

/-- **The container instance at its leaf** (`keyLeafW` at a graded instance). -/
theorem keyLeaf {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ b ds dsa) :
    us.length = cv.levelParams.length ∧ ∃ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ wa →
        Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
            (keyFrame dsa b (dropV (dep - b) ρ)) ∧
        SpineFit (keyFrame dsa b (dropV (dep - b) ρ)) (D.ids mm (Level.substFn φ cv.levelParams us))
            (isa.map (interp V ρ)) ∧
        interp V ρ wa = app (D.carrier (Level.substFn φ cv.levelParams us)
            (keyFrame dsa b (dropV (dep - b) ρ)) mm)
          (tupW (D.u mm (Level.substFn φ cv.levelParams us)) (isa.map (interp V ρ))) := by
  obtain ⟨hul, isa, hisa, h⟩ := keyLeafW mp hD hmm hf hbd hwa hlenP hlenI hdsw hdsa
  exact ⟨hul, isa, hisa, fun ρ hwd => h ρ hwd.1⟩

/-- **A container instance grows along a relation** at whose pairs the
application is graded and its indices are the same, as soon as the
carrier grows at the two key frames. -/
theorem monoOn_of_famLe {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ b ds dsa)
    {Δa : List AnnotTerm} {R : FrameRel V} (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (hgr : Rules.Graded V Δa wa)
    (his : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hle : ∀ ρ ρ', R ρ ρ' →
      FamLe (D.idx (Level.substFn φ cv.levelParams us) (keyFrame dsa b (dropV (dep - b) ρ)) mm)
        (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame dsa b (dropV (dep - b) ρ)) mm)
        (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame dsa b (dropV (dep - b) ρ')) mm)) :
    MonoOn R wa := by
  obtain ⟨-, isa, hisa, hk⟩ := keyLeaf mp hD hmm hf hbd hwa hlenP hlenI hdsw hdsa
  intro ρ ρ' hR
  obtain ⟨h1, h2⟩ := hdom ρ ρ' hR
  obtain ⟨-, hfit, heq⟩ := hk ρ (hgr ρ h1)
  obtain ⟨-, -, heq'⟩ := hk ρ' (hgr ρ' h2)
  have hmap : isa.map (interp V ρ) = isa.map (interp V ρ') :=
    List.map_congr_left fun v hv => his isa hisa v hv ρ ρ' hR
  rw [heq, heq', ← hmap]
  exact hle ρ ρ' hR _ (tupW_mem hfit)

/-- **The key's parameters fit the container's parameter telescope** at
every valuation where the instance is graded (the index count not yet
known: only the parameter prefix of the former's tower is read). -/
theorem keyParamsFit {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ b ds dsa) :
    ∀ ρ : Nat → V, WellDenotedV V ρ wa →
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
        (keyFrame dsa b (dropV (dep - b) ρ)) := by
  intro ρ hwd
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hf hfa
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hwd ⊢
  obtain ⟨vs₁, vs₂, rfl, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
  have hlift := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hbd hdsw hdsa
  obtain rfl := DenoteMetaSpine.unique hsp₁ hlift
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP hwd ⊢
  obtain ⟨h, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨ab, hta, hmap, hbits⟩ := hab ψ
  have hpl := h.parsLen mm hmm ψ
  have hmem := ConLeche.Semantics.Env.find?_mem hf
  have hname := ConLeche.Semantics.Env.find?_name hf
  have hin := mp.mem_type _ hmem ψ _ hta ρ
  rw [hname] at hin
  have hwf := mp.base2.wf _ hmem
  have hcl : Term.bvarsBelow 0 (mkPisAV ab (.sort (D.w ψ))).erase :=
    ConLeche.Verify.denote_bvarsBelow mp.base2.cval_closedL 0 _
      (ConLeche.Expr.WScoped.of_not_hasFvar hwf.1) hwf.2.2.2.1
      (denoteMeta_erase mp.base2.acval_erase 0 _ hta)
  generalize hτ : (fun j => dropV (dep - b) ρ (j + b)) = τ
  rw [interp_closed V hcl ρ τ, ← List.take_append_drop ds.length ab, mkPisAV_append'] at hin
  rw [annotMkAppN_append] at hwd
  have hwd₁ := WellDenoted_mkAppN_head _ hwd.1
  have hlab : (ab.take ds.length).length = ds.length := by
    rw [List.length_take]
    have := congrArg List.length hmap
    simp only [List.length_map, List.length_append] at this
    omega
  have hsp' := spineFit_of_wellDenoted_mkAppN_pi
    (fun d hd => hbits d (List.mem_of_mem_take hd)) hwd₁ hin
    (by rw [List.length_map, ← DenoteMetaSpine.length_eq hdsa, hlab])
  have hmap₁ : (ab.take ds.length).map (·.2.2) = D.pars mm ψ := by
    rw [List.map_take, hmap, hlenP, ← hpl, List.take_left' rfl]
  rw [hmap₁] at hsp'
  have has : (dsa.map (AnnotTerm.liftN (dep - b) · 0)).map (interp V ρ)
      = dsa.map (interp V (dropV (dep - b) ρ)) := by
    rw [List.map_map]
    exact List.map_congr_left fun a _ => interp_liftN_drop _ ρ a
  rw [has] at hsp'
  have hkf : keyFrame dsa b (dropV (dep - b) ρ) = consList (dsa.map (interp V (dropV (dep - b) ρ))) τ := by
    rw [← hτ]; rfl
  rw [hkf]
  have hsatP : Sat V (D.pars mm ψ).reverse (consList (dsa.map (interp V (dropV (dep - b) ρ))) τ) := by
    have := sat_of_spineFit (Sat_nil V τ) hsp'
    simpa using this
  exact h.parsSatInv mm hmm ψ _ hsatP

end ConLeche.Model
