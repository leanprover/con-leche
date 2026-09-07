import ConLeche.SetP.Direct.DirectStageFormerP

/-!
# The constructor's stage data (task #175 W4c, P3 module 6, part 3)

`CtorData`: the constructor type's peeled reading — the binder data
`ds` (parameters then fields), whose codomain bits are zero exactly at
a squash instance, ending in the family applied to the parameter
variables — with its gradings, bounds and level dependence; derived
from the constructor's `checkConstantVal` run at the environment
holding the former (`ctorData_of`), crossed to later stages
(`CtorData.cross`).

`ctorFrames`: the field chain graded at the constructor's parameter
frame (from the field-sort runs), and the two parameter frames
identified (from the binder pins) — the semantic content the former's
real leaf and the constructor's leaf consume.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A spine of position-indexed variables reads to the frame's own
`bvar`s. -/
theorem denoteSpineP_indexed {acval : Name → (Name → Nat) → AVExpr} {d : Nat} :
    ∀ (fvs : List Expr) (off : Nat),
      (∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (off + j) ty) →
      DenoteSpineP acval env φ d fvs
        ((List.range fvs.length).map fun j => AVExpr.bvar (d - 1 - (off + j)))
  | [], _, _ => .nil
  | x :: fvs, off, h => by
    obtain ⟨nm, ty, rfl⟩ := h 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteP_fvar]) ?_
    have hmap : (List.range fvs.length).map
          ((fun j => AVExpr.bvar (d - 1 - (off + j))) ∘ Nat.succ)
        = (List.range fvs.length).map fun j => AVExpr.bvar (d - 1 - (off + 1 + j)) := by
      apply List.map_congr_left
      intro j _
      show AVExpr.bvar (d - 1 - (off + (j + 1))) = AVExpr.bvar (d - 1 - (off + 1 + j))
      congr 1; omega
    rw [hmap]
    exact denoteSpineP_indexed fvs (off + 1) fun j y hy => by
        obtain ⟨ty', hy'⟩ := h (j + 1) y (by simpa using hy)
        exact ⟨ty', by rw [hy']; congr 1; omega⟩

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
def paramBvars (nP nF : Nat) : List AVExpr :=
  (List.range nP).map fun k => AVExpr.bvar (nP + nF - 1 - k)

/-- The family applied to the parameter variables, read at the
constructor's full frame. -/
def ctorBodyAV {env : Env} (m : EnvS2Core V env) (T : Name) (nP nF : Nat)
    (ψ : Name → Nat) : AVExpr :=
  AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF)

omit [SetTheory V] in
theorem consList_range_reverse :
    ∀ (n : Nat) (ρ : Nat → V),
      consList ((List.range n).reverse.map ρ) (fun j => ρ (j + n)) = ρ := by
  intro n
  induction n with
  | zero => intro ρ; funext j; simp
  | succ n ih =>
    intro ρ
    rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have hcons : cons (ρ n) (fun j => ρ (j + (n + 1))) = fun j => ρ (j + n) := by
      funext j
      cases j with
      | zero => rw [cons_zero, Nat.zero_add]
      | succ j => rw [cons_succ]; congr 1; omega
    rw [hcons]
    exact ih ρ

/-- The prefix and suffix of a peeled binder list, as the reversed
context's parts. -/
theorem reverse_map_take_drop (ds : List (Nat × Nat × AVExpr)) (nP : Nat) :
    ((ds.map (·.2.2)).reverse)
      = (((ds.drop nP).map (·.2.2)).reverse) ++ (((ds.take nP).map (·.2.2)).reverse) := by
  rw [← List.reverse_append, ← List.map_append, List.take_append_drop]

/-! ## The constructor's data -/

/-- **The constructor type's reading, peeled.** -/
structure CtorData {env : Env} (m : EnvS2Core V env) (T : Name)
    (cvC : ConstantVal) (nP nF : Nat) (resSort : Level)
    (ds : (Name → Nat) → List (Nat × Nat × AVExpr)) : Prop where
  read : ∀ ψ : Name → Nat, denoteP m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAV m T nP nF ψ))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AVExpr), d ∈ ds ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkP V ρ (mkPisAV (ds ψ) (ctorBodyAV m T nP nF ψ))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) →
    ds ψ₁ = ds ψ₂

/-- The constructor's data, from its stage run at the environment
holding the former. -/
theorem ctorData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa : ConstantVal} {env₀ envC : Env}
    {sorts : List Level} {caps : IndCaps}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hCtor : ConLeche.checkDirectCtor (ConLeche.fueledOps μ F) env₀ env p cvTa
      = .ok (envC, cvCa, sorts))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hstripT : cvTa.type.stripPis p.nP = some (bs, .sort p.resSort)) :
    ∃ ds : (Name → Nat) → List (Nat × Nat × AVExpr),
      CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds := by
  obtain ⟨hccv, -, -, fvsP, crest, tfvs, trest, xFvs, hopC, -, -, hopX, -, -⟩ :=
    ConLeche.checkDirectCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', -, hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hopC
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = p.nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add p.nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index p.nP type' 0 hopC
  -- the bits: the opened body is the family at the parameters, of
  -- sort `resSort`
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (p.nP + p.nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv fvsP hib
  obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : ConLeche.inferTypeCore μ env F' (p.nP + p.nF)
      (.const p.cvT.name (p.cvT.levelParams.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort fvsP htfT (by rw [hlenP]; exact hstripT) hib
  obtain rfl := ensureSortCore_sort_eq hensb
  -- per assignment
  have hper : ∀ ψ : Name → Nat, ∃ ds : List (Nat × Nat × AVExpr),
      denoteP mp.base2.acval env ψ 0 type'
        = some (mkPisAV ds (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ)) ∧
      ds.length = p.nP + p.nF ∧
      (∀ d ∈ ds, (p.resSort.eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V,
        AnnotOkP V ρ (mkPisAV ds (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ))) ∧
      DomsBelow 0 ds := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReadsP_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOkP.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, AnnotOkP V ρ Ta := fun ρ =>
      hokT ρ (Sat2_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := openedP_of hopAll htf' hbt' hTa hokT'
    -- the core reads as the family at the parameter variables
    have hR : R = ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ := by
      have hb := hop'.body
      have hsp := denoteSpineP_indexed (acval := mp.base2.acval) (env := env)
        (φ := ψ) (d := p.nP + p.nF) fvsP 0 hidx
      have hconst := denoteP_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := p.nP + p.nF) hfT
        (show (p.cvT.levelParams.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (p.cvT.levelParams.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      rw [denoteP_mkAppN hsp hconst] at hb
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (p.cvT.levelParams.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (p.cvT.levelParams.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hsubst, hlenP] at hb
      have : ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ
          = AVExpr.mkAppN (mp.base2.acval p.cvT.name ψ)
            ((List.range p.nP).map fun j => AVExpr.bvar (p.nP + p.nF - 1 - (0 + j))) := by
        unfold ctorBodyAV paramBvars
        congr 1
        apply List.map_congr_left
        intro k _
        rw [Nat.zero_add]
      rw [this]
      exact (Option.some.inj hb).symm
    subst hR
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleP htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨ds, hTa, hlen, ?_, hokT', ?_⟩
    · intro d hd
      exact (stripPisAV_bits (p.nP + p.nF) (hbits ψ) hTa hst' d hd).symm
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
  refine ⟨fun ψ => Classical.choose (hper ψ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteP mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ₁)) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 type' htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    exact (mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))).1

/-- The constructor's data crosses a cons that is neither the former
nor mentions the stored type's slot. -/
theorem CtorData.cross {m : EnvS2Core V env} {T : Name} {cvC : ConstantVal}
    {nP nF : Nat} {resSort : Level}
    {ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (h : CtorData m T cvC nP nF resSort ds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ConsCrossAt c₀ cvC.type) (hcb : ConstsBound env cvC.type)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorData m₂ T cvC nP nF resSort ds := by
  have hbody : ∀ ψ, ctorBodyAV m₂ T nP nF ψ = ctorBodyAV m T nP nF ψ := by
    intro ψ
    unfold ctorBodyAV
    rw [hac, acvalWith_ne hT]
  refine ⟨fun ψ => ?_, h.len, h.bits, fun ψ ρ => ?_, h.below, h.params⟩
  · rw [hac, hbody]
    exact denoteP_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  · rw [hbody]; exact h.okTy ψ ρ

end ConLeche.SetP
