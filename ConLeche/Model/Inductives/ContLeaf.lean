module

public import ConLeche.Model.Inductives.ContN2
import ConLeche.Verify.Rules.RedVal
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.Sound
import ConLeche.Model.IndStageKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Reading.Levels
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.NatEqs
import ConLeche.Model.Env.LfpFormer
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.Inst
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

open ConLeche (Env Expr Name Level ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- A fitting spine, from the satisfaction of the reversed list at its
own frame. -/
theorem spineFit_of_sat_consList {Ds : List Term} {as : List V} {ρ : Nat → V}
    (hlen : as.length = Ds.length) (h : Sat V Ds.reverse (consList as ρ)) :
    SpineFit ρ Ds as := by
  have := spineFit_frameIdx_of_sat h
  rwa [← hlen, shiftE_consList, frameIdx_consList'] at this

/-- **The key's arguments fit the container's former telescope** (the
former's reading, M4, at the key's levels), at every valuation where the
application is graded. -/
theorem keyFit_of_wd {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep : Nat}
    {args : List Expr} {wa : Term}
    (hwa : denote mp.base2.acval env φ dep (Expr.mkAppN (.const (D.member mm) us) args)
      = some wa)
    (hlen : args.length = (D.pars mm (Level.substFn φ cv.levelParams us)).length
      + (D.ids mm (Level.substFn φ cv.levelParams us)).length) :
    us.length = cv.levelParams.length ∧ ∃ vs, DenoteSpine mp.base2.acval env φ dep args vs ∧
      wa = Term.mkAppN (mp.base2.acval (D.member mm) (Level.substFn φ cv.levelParams us)) vs ∧
      ∀ ρ : Nat → V, WellDenotedTy V ρ wa → ∀ σ : Nat → V,
        SpineFit σ (D.pars mm (Level.substFn φ cv.levelParams us)
          ++ D.ids mm (Level.substFn φ cv.levelParams us)) (vs.map (interp V ρ)) := by
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denote_mkAppN_inv hwa
  obtain ⟨hul, rfl⟩ := Rules.denote_const_arityK hf hfa
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hul ⊢
  refine ⟨hul, vs, hsp, rfl, fun ρ hwd σ => ?_⟩
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlen hwd ⊢
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨ab, hta, hmap⟩ := hab ψ
  have hmem := ConLeche.Env.find?_mem hf
  have hname := ConLeche.Env.find?_name hf
  have hin := mp.mem_type _ hmem ψ _ hta ρ
  rw [hname] at hin
  have hwf := mp.base2.wf.consts _ hmem
  have hcl : Term.bvarsBelow 0 (mkPisAV ab (.sort (D.w ψ))) :=
    ConLeche.Verify.denote_bvarsBelow mp.base2.cval_closed 0 _
      (ConLeche.Expr.WScoped.of_not_hasFvar hwf.1) hwf.2.2.2.1
      hta
  rw [interp_closed V hcl ρ σ] at hin
  -- "not pt" source (1): the family instance is a type
  have hsp' := spineFit_of_wellDenoted_mkAppN_pi hwd.2.ne_pt hwd.1 hin
    (by rw [← DenoteSpine.length_eq hsp, hlen, ← List.length_append, ← hmap])
  rwa [hmap] at hsp'

/-- The valuation `n` positions down. -/
@[expose] def dropV (n : Nat) (ρ : Nat → V) : Nat → V := fun i => ρ (i + n)

/-- **The container instance at its leaf** (see the module docstring): at
every valuation where `C.{us} (ds ++ is)` is graded, the key frame
satisfies the container's parameter telescope, the indices fit its index
telescope there, and the instance is the carrier's component at the
index tuple.  `ds` are scoped at `b ≤ dep` (the walk's hole bound) and
read there as `dsa`. -/
theorem keyLeaf {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : Term}
    (hwa : denote mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List Term}
    (hdsa : DenoteSpine mp.base2.acval env φ b ds dsa) :
    us.length = cv.levelParams.length ∧ ∃ isa, DenoteSpine mp.base2.acval env φ dep is isa ∧
      ∀ ρ : Nat → V, WellDenotedTy V ρ wa →
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
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteSpine.split _ hsp
  refine ⟨vs₂, hsp₂, fun ρ hwd => ?_⟩
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hpl hlenP hlenI hfit hwd ⊢
  have hlift := DenoteSpine.lift (m := mp.base2) (φ := φ) hbd hdsw hdsa
  obtain rfl := DenoteSpine.unique hsp₁ hlift
  have has : (dsa.map (Term.liftN (dep - b) · 0)).map (interp V ρ)
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
    rw [hs₁.length_eq, hpl, ← hlenP, ← hasd, List.length_map, ← DenoteSpine.length_eq hdsa]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl₁.symm
  have hsatP : Sat V (D.pars mm ψ).reverse (consList as τ) := by
    have := sat_of_spineFit (Sat_nil V τ) hs₁
    simpa using this
  have hsat := h.parsSatInv mm hmm ψ _ hsatP
  refine ⟨hsat, hs₂, ?_⟩
  have hsa : SpineFit τ (D.params ψ) as :=
    spineFit_of_sat_consList (by rw [← hasd, List.length_map,
      ← DenoteSpine.length_eq hdsa, hlenP]) hsat
  rw [interp_mkAppN_foldl, List.map_append, has,
    acval_interp_closed mp.base2 _ ψ ρ τ]
  exact h.leaf mm hmm ψ τ as _ hsa hs₂

/-- **A container instance grows along a relation** at whose pairs the
application is graded and its indices are the same, as soon as the
carrier grows at the two key frames. -/
theorem monoOn_of_famLe {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {dep b : Nat}
    (hbd : b ≤ dep) {ds is : List Expr} {wa : Term}
    (hwa : denote mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List Term}
    (hdsa : DenoteSpine mp.base2.acval env φ b ds dsa)
    {Δa : List Term} {R : FrameRel V} (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (hgr : Rules.GradedTy V Δa wa)
    (his : ∀ isa, DenoteSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
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

/-! ## A constant's spine, typed: its arguments' certificates

A key `C.{us} ds` is a parameter prefix — a family over the indices, no
type — and over an empty index set it reads the point, which fixes no
domain.  Its parameters' fit comes from its INFERENCE: at the full grade
every argument of an application is inferred and its type compared with
the head type's domain, and a stored former's type is a literal
Π-telescope over the parameters, so the inference of the spine is a
full-grade certificate of the arguments against that telescope
(`certsF_of_infer_spine`), whose soundness is the fit (`certsF_sound`). -/

/-- Peeling an application spine down to its head: the head is inferred. -/
theorem infer_mkAppN_head {env : Env} {g : ConLeche.Rules.Grade} {d : Nat} :
    ∀ (as : List Expr) {f T : Expr}, ConLeche.Rules.Infer env g d (Expr.mkAppN f as) T →
      ∃ Tf, ConLeche.Rules.Infer env g d f Tf
  | [], _, T, h => ⟨T, h⟩
  | a :: as, f, _, h => by
    obtain ⟨_, h1⟩ := infer_mkAppN_head as (f := .app f a) h
    cases h1 with
    | app hf _ _ _ => exact ⟨_, hf⟩
    | bvUnsat hf _ _ _ _ _ _ _ => exact ⟨_, hf⟩

/-- **An inferred spine over a literal Π-telescope is a full-grade
certificate**: the head's type is determined (`hf`), a Π reduces only to
itself (`Red.eq_of_redVal`), so each argument was inferred and compared
with the telescope's own domain. -/
theorem certsF_of_infer_spine {env : Env} {d : Nat} :
    ∀ (ds : List Expr) {f T0 r : Expr},
      -- Task #368: the head is a stored inductive
      -- former, so no application in the spine is `Infer.bvUnsat`'s
      (∀ c us', f.getAppFn = .const c us' → ∃ cv caps, env.find? c = some (.indInfo cv caps)) →
      (∀ T', ConLeche.Rules.Infer env .full d f T' → T' = T0) →
      ConLeche.instPisWith ds T0 = some r →
      (∃ T, ConLeche.Rules.Infer env .full d (Expr.mkAppN f ds) T) →
      ConLeche.Rules.CertsF env d T0 ds
  | [], _, _, _, _, _, _, _ => .nil
  | a :: as, f, T0, r, hhd, hf, hpi, ⟨T, hT⟩ => by
    have hU : ∀ {E C : Expr}, f = .app (.app (.const unsatThmName []) E) C → ∀ {a' : Expr},
        bvUnsatHit env.find? env.findProj? (.app (.app (.const unsatThmName []) E) C) a' = true → False := by
      intro E C hfe a' hhit
      obtain ⟨cv, caps, hfi⟩ := hhd unsatThmName [] (by rw [hfe]; rfl)
      exact bvUnsatHit_U_notInd hhit cv caps hfi
    match T0, hpi with
    | .forallE A B, hpi =>
      have hpi' : ConLeche.instPisWith as (B.instantiate1 a) = some r := hpi
      obtain ⟨_, h1⟩ := infer_mkAppN_head as (f := .app f a) hT
      cases h1 with
      | app htf hred hta hdef =>
        obtain rfl := hf _ htf
        have heq := ConLeche.Rules.Red.eq_of_redVal hred trivial
        cases heq
        refine .cert (hta rfl) (hdef rfl)
          (certsF_of_infer_spine as (f := .app f a) (fun c us' h => hhd c us' h) ?_ hpi' ⟨T, hT⟩)
        intro T' hT'
        cases hT' with
        | app htf' hred' _ _ =>
          obtain rfl := hf _ htf'
          have heq' := ConLeche.Rules.Red.eq_of_redVal hred' trivial
          cases heq'
          rfl
        | bvUnsat _ _ hskip _ _ _ _ _ => exact (hU rfl (bvUnsatSkip_hit hskip)).elim
      | bvUnsat _ _ hskip _ _ _ _ _ => exact (hU rfl (bvUnsatSkip_hit hskip)).elim

/-- **The key's parameters fit the container's parameter telescope**, at
every valuation of the key's context: the key `C.{us} ds` was inferred
at the full grade over the former's literal parameter telescope
(`hpi`), so its arguments carry full-grade certificates
(`certsF_of_infer_spine`) whose soundness is the fit against the
former's stored type reading.  (The key's VALUE cannot give it: a
parameter prefix over an empty index set reads the point.)  The
certificates' `DefEq`/`Red` claims are used only between types, never
the point ("not pt" source (1), inside `certsF_sound`). -/
theorem keyParamsFit {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : Rules.RulesInputs V mp.base2 φ) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level}
    (hul : us.length = cv.levelParams.length) {d F : Nat} {ds : List Expr} {ty r : Expr}
    (hty : ConLeche.inferTypeCore .verified env F d (Expr.mkAppN (.const (D.member mm) us) ds)
      = .ok ty)
    (hpi : ConLeche.instPisWith ds (cv.type.instantiateLevelParams cv.levelParams us) = some r)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    {Δa : List Term} (hΔ : Δa.length = d)
    (hfr : ∀ x ∈ ds, Rules.Frame d x ∧ CtxOkS mp.base2 φ d Δa x) {dsa : List Term}
    (hdsa : DenoteSpine mp.base2.acval env φ d ds dsa) :
    ∀ ρ : Nat → V, Sat V Δa ρ → (∀ x ∈ ds, LeavesGr mp.base2 φ d x ρ) →
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse (keyFrame dsa d ρ) := by
  intro ρ hρ hL
  -- the certificates
  have hI := ConLeche.Rules.inferTypeCore_bridge hty
  have hhead : ∀ T', ConLeche.Rules.Infer env .full d (.const (D.member mm) us) T' →
      T' = cv.type.instantiateLevelParams cv.levelParams us := by
    intro T' h
    cases h with
    | const hf' _ =>
      rw [hf] at hf'
      cases hf'
      rfl
  have hcerts := certsF_of_infer_spine ds
    (fun c us' h => by cases h; exact ⟨cv, caps, hf⟩) hhead hpi ⟨ty, hI⟩
  have hsem := Rules.certsF_sound hin hcerts
  -- the former's stored type, read
  obtain ⟨Ta, hTaD, hokTa, -, hnf, hbd⟩ := Rules.constTy_pkg hin.const_ty hf hul
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTaD hokTa hnf hbd
  obtain ⟨hfT, hCT⟩ := Rules.frame_of_not_hasFvar (m := mp.base2) (φ := φ) (Δa := Δa) hnf hbd hΔ
  obtain ⟨resta, hfit⟩ := hsem hfT hCT (hTaD d) hfr hdsa
  obtain ⟨-, hTF, -⟩ := hfit ρ hρ
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl
      exact nomatch hl) hL (hokTa ρ)
  -- the reading is the former's telescope over the parameters and indices
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP ⊢
  obtain ⟨h, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨ab, hta, hmap⟩ := hab ψ
  have hpl := h.parsLen mm hmm ψ
  have hT0 := hTaD 0
  rw [denotePInstLevels, hψ, hta] at hT0
  obtain rfl := Option.some.inj hT0
  have hlab : (ab.take ds.length).length = ds.length := by
    rw [List.length_take]
    have := congrArg List.length hmap
    simp only [List.length_append] at this
    omega
  have hsplit : mkPisAV ab (.sort (D.w ψ))
      = mkPisAV (ab.take ds.length) (mkPisAV (ab.drop ds.length) (.sort (D.w ψ))) := by
    have := mkPisAV_append' (.sort (D.w ψ)) (ab.take ds.length) (ab.drop ds.length)
    rwa [List.take_append_drop] at this
  rw [hsplit] at hTF
  have hdl := DenoteSpine.length_eq hdsa
  -- a fit of a Π-tower prefix is a `SpineFit` of its domains
  have hsp : SpineFit ρ (ab.take ds.length) (dsa.map (interp V ρ)) := by
    have hle : dsa.length = (ab.take ds.length).length := by rw [hlab, hdl]
    have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV (ab.take ds.length)
      (mkPisAV (ab.drop ds.length) (.sort (D.w ψ))))
    refine spineFit_of_chain (by simpa using hle) ?_
    intro n hn
    have := teleFitPA_to_chain (ab.take ds.length).length htele hle hTF n (by simpa using hn)
    simpa using this
  -- the former's telescope is closed, so the fit holds at the key frame's base
  have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
  have hcl : Term.bvarsBelow 0 (mkPisAV ab (.sort (D.w ψ))) :=
    ConLeche.Verify.denote_bvarsBelow mp.base2.cval_closed 0 _
      (ConLeche.Expr.WScoped.of_not_hasFvar hwf.1) hwf.2.2.2.1
      hta
  rw [hsplit] at hcl
  have hsp := spineFit_congr_below (ρ' := fun j => ρ (j + d))
    (bvarsBelow_mkPisAV_inv hcl).1 (fun i hi => absurd hi (Nat.not_lt_zero i)) hsp
  have hmap₁ : (ab.take ds.length) = D.pars mm ψ := by
    rw [hmap, hlenP, ← hpl, List.take_left' rfl]
  rw [hmap₁] at hsp
  have hsatP : Sat V (D.pars mm ψ).reverse (keyFrame dsa d ρ) := by
    have := sat_of_spineFit (Sat_nil V (fun j => ρ (j + d))) hsp
    simpa [keyFrame] using this
  exact h.parsSatInv mm hmm ψ _ hsatP

end ConLeche.Model
