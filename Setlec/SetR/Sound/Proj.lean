import Setlec.SetR.Sound.Rigidity
import Setlec.Verify.Denote.SubstAlgebra

/-!
# Soundness cases — the projection rules (task #148, T4, batch e)

I9 (`Infer.proj`) and R6 (`Red.projRed`) — the campaign's R2 hot
spots, discharged per the T4 architecture record:

* the pinned entries are identified through `EnvSHyp.proj_ok` and the
  stored-name injection (`Model/Core/Infer.lean`'s `hidx` move);
* the entry/constructor types are *pinned closed expressions*, so
  their denotations and `piResidualV` walks are concrete computations
  (`denote_pairFstTy_eq` etc. — the transposes of the TT lane's
  `denote_projEntryTy` computation and of the model's Expr-side
  residual computation);
* I9's sigma package comes from `mem_psigmaV_app` (rigidity: the
  membership self-certifies the domains — the #129-replacement) and
  `sfst_mem`/`ssnd_mem`;
* R6's component memberships come from its `Tele` premise over the
  denoted constructor type (the amendment's exposure of the infer
  run's own argument re-checks), walked concretely; the equality is
  `psigmaMkV_app`'s fold (`spair` + `sfst_spair`/`ssnd_spair`), with
  the `Nat.max = 0` collapse branch closed by the field certificate's
  sort chain (`mem_univ_zero` + `sfst_pt`/`ssnd_pt`) — the
  `whnfCore_claims` proj-case re-hang.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ### Entry identification -/

/-- A native table entry is one of the two pinned pair entries, its
stored name pins the struct name and index, and the pair block is
stored.  (`Model/Core/Whnf.lean:317-326`'s moves, packaged.) -/
theorem projEntry_pins (hpo : ProjOkT env) {sn : Name} {i : Nat}
    {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    sn = psigmaName ∧ entry.idx = i ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA := by
  obtain ⟨hpin, hpsig, hpsigMk⟩ :=
    hpo.1 _ _ (Env.findProj?_some hf) hnat
  have h1 := List.find?_some (Env.findProj?_some hf)
  have h2 : (ConstantInfo.projInfo entry).name = projFnName sn i :=
    eq_of_beq (by simpa using h1)
  simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
  refine ⟨hpin, ?_, (projFnName_inj h2).2, hpsig, hpsigMk⟩
  have hsn : entry.structName = sn := (projFnName_inj h2).1
  rw [← hsn]
  rcases hpin with rfl | rfl <;> rfl

/-! ### The pinned types' denotations (concrete computations) -/

/-- The instantiated first-projection entry type denotes to its
concrete `VExpr`. -/
theorem denote_pairFstTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (pairFstEntry.ty.instantiateLevelParams pairFstEntry.levelParams
        [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.app (.app (cval psigmaName
                  (Level.substFn φ psigmaA.toConstantVal.levelParams
                    [l0, l1]))
                (.bvar 1)) (.bvar 0))
              (.bvar 2)))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, pairFstEntry, pairFstTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-- The instantiated second-projection entry type denotes to its
concrete `VExpr`. -/
theorem denote_pairSndTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (pairSndEntry.ty.instantiateLevelParams pairSndEntry.levelParams
        [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.app (.app (cval psigmaName
                  (Level.substFn φ psigmaA.toConstantVal.levelParams
                    [l0, l1]))
                (.bvar 1)) (.bvar 0))
              (.app (.bvar 1) (.proj 0 (.bvar 0)))))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, pairSndEntry, pairSndTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app, denote_proj,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-- The instantiated pinned constructor type denotes to its concrete
`VExpr`. -/
theorem denote_psigmaMkTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (psigmaMkA.toConstantVal.type.instantiateLevelParams
        psigmaMkA.toConstantVal.levelParams [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.bvar 1)
              (.pi (.app (.bvar 1) (.bvar 0))
                (.app (.app (cval psigmaName
                    (Level.substFn φ psigmaA.toConstantVal.levelParams
                      [l0, l1]))
                  (.bvar 3)) (.bvar 2)))))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, psigmaMkA,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-! ### The concrete residual walks -/

/-- The first entry's residual at a full spine is the type argument. -/
theorem piResidualV_pairFst {K : VExpr} (hK : VExpr.Closed K)
    (u₀ v₀ : Nat) (X Y p : VExpr) :
    piResidualV
      (.pi (.sort u₀) (.pi (.pi (.bvar 0) (.sort v₀))
        (.pi (.app (.app K (.bvar 1)) (.bvar 0)) (.bvar 2))))
      [X, Y, p] = some X := by
  have e1 : ((VExpr.liftN 2 X).inst Y 1) = VExpr.liftN 1 X := by
    simpa using VExpr.inst_liftN_absorb X (j := 0) (k := 1) (m := 1)
      (by omega) (by omega) Y
  have e2 : ((VExpr.liftN 1 X).inst p) = X := by
    simpa [VExpr.liftN_zero] using
      VExpr.inst_liftN_absorb X (j := 0) (k := 0) (m := 0)
        (by omega) (by omega) p
  simp +decide only [piResidualV, VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_sort, VExpr.inst_bvar,
    VExpr.inst_eq_self_of_closed hK, if_true, if_false,
    Nat.reduceAdd, Nat.reduceSub, e1, e2]

/-- The second entry's residual at a full spine is the fibre at the
first projection. -/
theorem piResidualV_pairSnd {K : VExpr} (hK : VExpr.Closed K)
    (u₀ v₀ : Nat) (X Y p : VExpr) :
    piResidualV
      (.pi (.sort u₀) (.pi (.pi (.bvar 0) (.sort v₀))
        (.pi (.app (.app K (.bvar 1)) (.bvar 0))
          (.app (.bvar 1) (.proj 0 (.bvar 0))))))
      [X, Y, p] = some (.app Y (.proj 0 p)) := by
  have e3 : ((VExpr.liftN 1 Y).inst p) = Y := by
    simpa [VExpr.liftN_zero] using
      VExpr.inst_liftN_absorb Y (j := 0) (k := 0) (m := 0)
        (by omega) (by omega) p
  simp +decide only [piResidualV, VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_sort, VExpr.inst_bvar, VExpr.inst_proj,
    VExpr.inst_eq_self_of_closed hK, if_true, if_false,
    Nat.reduceAdd, Nat.reduceSub, e3, VExpr.liftN_zero]

/-- Destructure the telescope certificate over the pinned constructor
type: the four component memberships, at the assigned levels. -/
theorem TeleFitV_psigmaMk {ρ : Nat → V} {K : VExpr}
    (hK : VExpr.Closed K) {u₀ v₀ : Nat} {α β x y restC : VExpr}
    (h : TeleFitV V ρ
      (.pi (.sort u₀) (.pi (.pi (.bvar 0) (.sort v₀))
        (.pi (.bvar 1) (.pi (.app (.bvar 1) (.bvar 0))
          (.app (.app K (.bvar 3)) (.bvar 2))))))
      [α, β, x, y] restC) :
    interp V ρ α ∈ˢ (univ u₀ : V) ∧
    interp V ρ β ∈ˢ piC (interp V ρ α) (fun _ => (univ v₀ : V)) ∧
    interp V ρ x ∈ˢ interp V ρ α ∧
    interp V ρ y ∈ˢ SetTheory.app (interp V ρ β) (interp V ρ x) := by
  have habs1 : ∀ e a : VExpr, (VExpr.liftN 1 e).inst a = e := by
    intro e a
    simpa [VExpr.liftN_zero] using
      VExpr.inst_liftN_absorb e (j := 0) (k := 0) (m := 0)
        (by omega) (by omega) a
  have habs2 : ∀ e a : VExpr,
      (VExpr.liftN 2 e).inst a 1 = VExpr.liftN 1 e := by
    intro e a
    simpa using VExpr.inst_liftN_absorb e (j := 0) (k := 1) (m := 1)
      (by omega) (by omega) a
  have habs3 : ∀ e a : VExpr,
      (VExpr.liftN 3 e).inst a 2 = VExpr.liftN 2 e := by
    intro e a
    simpa using VExpr.inst_liftN_absorb e (j := 0) (k := 2) (m := 2)
      (by omega) (by omega) a
  cases h with
  | cons hm1 h =>
  simp +decide only [VExpr.inst_pi, VExpr.inst_app, VExpr.inst_sort,
    VExpr.inst_bvar, if_true, if_false, Nat.reduceAdd,
    VExpr.inst_eq_self_of_closed hK, VExpr.liftN_zero] at h
  cases h with
  | cons hm2 h =>
  simp +decide only [VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_bvar, if_true, if_false, Nat.reduceAdd,
    VExpr.inst_eq_self_of_closed hK, habs1, habs3] at h
  cases h with
  | cons hm3 h =>
  simp +decide only [VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_bvar, if_true, if_false, Nat.reduceAdd,
    VExpr.inst_eq_self_of_closed hK,
    VExpr.liftN_zero, habs1, habs2] at h
  cases h with
  | cons hm4 h =>
  exact ⟨hm1, hm2, hm3, hm4⟩

/-! ### I9: projection inference -/

theorem sndInfProj (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {p tp TP resV : VExpr} {i : Nat} {T : Name}
    {entry : ProjEntry} {ciT : ConstantInfo} {us : List Level}
    {ps : List VExpr}
    (h1 : env.findProj? T i = some entry)
    (h2 : entry.native = true)
    (h3 : ps.length = entry.numParams)
    (h4 : us.length = entry.levelParams.length)
    (h5 : env.find? T = some ciT)
    (_ : us.length = ciT.toConstantVal.levelParams.length)
    (h7 : denoteClosed cval env φ
      (entry.ty.instantiateLevelParams entry.levelParams us) = some TP)
    (_ : VExpr.Closed TP)
    (h8 : piResidualV TP (ps ++ [p]) = some resV)
    (_ : Infer μ env cval φ Δ p tp)
    (_ : DefEq μ env cval φ Δ tp
      (VExpr.mkAppN
        (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps))
    (ihp : InfS V Δ p tp)
    (ihr : DeqS V Δ tp
      (VExpr.mkAppN
        (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps)) :
    InfS V Δ (.proj i p) resV := by
  intro ρ hΔ
  obtain ⟨hpin, hT, hidx, hpsig, -⟩ := projEntry_pins henv.proj_ok h1 h2
  subst hT
  obtain rfl : ciT = psigmaA := Option.some.inj (h5.symm.trans hpsig)
  obtain ⟨l0, l1, rfl⟩ : ∃ l0 l1, us = [l0, l1] := by
    rcases hpin with rfl | rfl <;>
      (simp only [pairFstEntry, pairSndEntry, List.length_cons,
        List.length_nil] at h4
       match us, h4 with
       | [l0, l1], _ => exact ⟨l0, l1, rfl⟩)
  obtain ⟨X, Y, rfl⟩ : ∃ X Y, ps = [X, Y] := by
    rcases hpin with rfl | rfl <;>
      (simp only [pairFstEntry, pairSndEntry] at h3
       match ps, h3 with
       | [X, Y], _ => exact ⟨X, Y, rfl⟩)
  have hval : cval psigmaName
      (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])
      = .const .psigma
          [Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1] uN,
           Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1] vN] :=
    (henv.basis_pinned _ _ hpsig (by decide)).2 _ _ rfl
  have hmem2 : interp V ρ p ∈ˢ
      SetTheory.app (SetTheory.app
        (psigmaV V
          (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1] uN)
          (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1] vN))
        (interp V ρ X)) (interp V ρ Y) := by
    have h := (ihr ρ hΔ) ▸ (ihp ρ hΔ).2
    simp only [VExpr.mkAppN_cons, VExpr.mkAppN_nil, interp_app, hval]
      at h
    exact h
  obtain ⟨hXu, hYpi, hsig⟩ := mem_psigmaV_app hmem2
  have hfib : ∀ x, x ∈ˢ interp V ρ X →
      SetTheory.app (interp V ρ Y) x ∈ˢ
        (univ (Level.substFn φ psigmaA.toConstantVal.levelParams
          [l0, l1] vN) : V) :=
    fun x hx => app_mem_piC hYpi hx
  rcases hpin with rfl | rfl
  · -- first projection
    obtain rfl : i = 0 := hidx.symm
    rw [denote_pairFstTy_eq hpsig] at h7
    obtain rfl := (Option.some.inj h7).symm
    rw [show ([X, Y] ++ [p]) = [X, Y, p] from rfl,
      piResidualV_pairFst (henv.cval_closed _ _)] at h8
    obtain rfl := (Option.some.inj h8).symm
    refine ⟨?_, ?_⟩
    · rw [AnnotOkV_proj]
      exact ⟨(ihp ρ hΔ).1, by omega, _, _, _, _, hsig, hXu, hfib⟩
    · rw [interp_proj, if_pos rfl]
      exact sfst_mem V hXu hsig
  · -- second projection
    obtain rfl : i = 1 := hidx.symm
    rw [denote_pairSndTy_eq hpsig] at h7
    obtain rfl := (Option.some.inj h7).symm
    rw [show ([X, Y] ++ [p]) = [X, Y, p] from rfl,
      piResidualV_pairSnd (henv.cval_closed _ _)] at h8
    obtain rfl := (Option.some.inj h8).symm
    refine ⟨?_, ?_⟩
    · rw [AnnotOkV_proj]
      exact ⟨(ihp ρ hΔ).1, by omega, _, _, _, _, hsig, hXu, hfib⟩
    · rw [interp_app, interp_proj, if_neg (by omega), interp_proj,
        if_pos rfl]
      exact ssnd_mem V hXu hYpi hsig

/-! ### R6: native projection reduction -/

theorem sndRedProjRed (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {p P fv ta tta te tte TC restC : VExpr}
    {i : Nat} {sn : Name} {entry : ProjEntry} {ci : ConstantInfo}
    {us : List Level} {vs : List VExpr}
    (h1 : env.findProj? sn i = some entry) (h2 : entry.native = true)
    (_ : i < entry.numFields)
    (h4 : vs.length = entry.numParams + entry.numFields)
    (_ : us.length = entry.levelParams.length)
    (h6 : env.find? entry.ctor = some ci)
    (h7 : us.length = ci.toConstantVal.levelParams.length)
    (h8 : P = VExpr.mkAppN
      (cval entry.ctor
        (Level.substFn φ ci.toConstantVal.levelParams us)) vs)
    (h9 : vs[entry.numParams + i]? = some fv)
    (hTC : denoteClosed cval env φ
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some TC)
    (_ : VExpr.Closed TC)
    (_ : Red μ env cval φ Δ p P)
    (_ : Tele μ env cval φ Δ TC vs restC)
    (_ : Infer μ env cval φ Δ fv ta) (_ : Infer μ env cval φ Δ ta tta)
    (_ : DefEq μ env cval φ Δ tta
      (.sort ((Level.subst entry.levelParams us entry.fieldSort).eval φ)))
    (_ : Infer μ env cval φ Δ P te) (_ : Infer μ env cval φ Δ te tte)
    (_ : DefEq μ env cval φ Δ tte
      (.sort ((Level.subst entry.levelParams us entry.structSort).eval φ)))
    (ihp : RedS V Δ p P)
    (ihTele : TeleS V Δ TC vs restC)
    (ihfv : InfS V Δ fv ta)
    (ihta : InfS V Δ ta tta)
    (ihtta : DeqS V Δ tta
      (.sort ((Level.subst entry.levelParams us entry.fieldSort).eval φ)))
    (_ : InfS V Δ P te) (_ : InfS V Δ te tte)
    (_ : DeqS V Δ tte
      (.sort ((Level.subst entry.levelParams us entry.structSort).eval φ))) :
    RedS V Δ (.proj i p) fv := by
  intro ρ hΔ
  obtain ⟨hpin, hT, hidx, hpsig, hpsigMk⟩ :=
    projEntry_pins henv.proj_ok h1 h2
  have hctor : entry.ctor = psigmaMkName := by
    rcases hpin with rfl | rfl <;> rfl
  rw [hctor] at h6
  obtain rfl : ci = psigmaMkA := Option.some.inj (h6.symm.trans hpsigMk)
  obtain ⟨l0, l1, rfl⟩ : ∃ l0 l1, us = [l0, l1] := by
    simp only [psigmaMkA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil] at h7
    match us, h7 with
    | [l0, l1], _ => exact ⟨l0, l1, rfl⟩
  obtain ⟨α, β, x, y, rfl⟩ : ∃ α β x y, vs = [α, β, x, y] := by
    rcases hpin with rfl | rfl <;>
      (simp only [pairFstEntry, pairSndEntry] at h4
       match vs, h4 with
       | [α, β, x, y], _ => exact ⟨α, β, x, y, rfl⟩)
  -- the two pinned blocks share their level-parameter list
  have hlp : psigmaA.toConstantVal.levelParams
      = psigmaMkA.toConstantVal.levelParams := rfl
  -- the head's pinned valuation and the spine's interpretation
  have hvalMk : cval psigmaMkName
      (Level.substFn φ psigmaMkA.toConstantVal.levelParams [l0, l1])
      = .const .psigmaMk
          [Level.substFn φ psigmaMkA.toConstantVal.levelParams [l0, l1] uN,
           Level.substFn φ psigmaMkA.toConstantVal.levelParams [l0, l1] vN] :=
    (henv.basis_pinned _ _ hpsigMk (by decide)).2 _ _ rfl
  -- the telescope certificates: the four component memberships
  rw [denote_psigmaMkTy_eq hpsig, hlp] at hTC
  obtain rfl := (Option.some.inj hTC).symm
  obtain ⟨hfit, hargs, -⟩ := ihTele ρ hΔ
  obtain ⟨hm1, hm2, hm3, hm4⟩ :=
    TeleFitV_psigmaMk (henv.cval_closed _ _) hfit
  have hψu : Level.substFn φ psigmaMkA.toConstantVal.levelParams
      [l0, l1] uN = Level.eval φ l0 := by
    simp +decide [psigmaMkA, ConstantInfo.toConstantVal, Level.substFn,
      uN]
  have hψv : Level.substFn φ psigmaMkA.toConstantVal.levelParams
      [l0, l1] vN = Level.eval φ l1 := by
    simp +decide [psigmaMkA, ConstantInfo.toConstantVal, Level.substFn,
      vN]
  have hm1' : interp V ρ α ∈ˢ (univ (Level.eval φ l0) : V) := hm1
  have hm2' : interp V ρ β ∈ˢ
      piC (interp V ρ α) (fun _ => (univ (Level.eval φ l1) : V)) := hm2
  have hm4' : interp V ρ y ∈ˢ
      SetTheory.app (interp V ρ β) (interp V ρ x) := hm4
  -- the subject's interpretation
  have hPv : interp V ρ P =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkV V (Level.eval φ l0) (Level.eval φ l1))
        (interp V ρ α)) (interp V ρ β)) (interp V ρ x)) (interp V ρ y) := by
    rw [h8]
    simp only [VExpr.mkAppN_cons, VExpr.mkAppN_nil, interp_app, hctor,
      hvalMk, hψu, hψv]
    rfl
  have hp_eq : interp V ρ p = interp V ρ P := (ihp ρ hΔ).1
  -- the field's identity and truthfulness
  have hfv : (i = 0 ∧ fv = x) ∨ (i = 1 ∧ fv = y) := by
    rcases hpin with rfl | rfl
    · obtain rfl : i = 0 := hidx.symm
      exact Or.inl ⟨rfl, by simpa using (Option.some.inj h9).symm⟩
    · obtain rfl : i = 1 := hidx.symm
      exact Or.inr ⟨rfl, by simpa using (Option.some.inj h9).symm⟩
  have hfvA : AnnotOkV V ρ fv := by
    rcases hfv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hargs _ (by simp)
  -- the field certificate's sort, computed off the pin
  have hfsort : (Level.subst entry.levelParams [l0, l1]
      entry.fieldSort).eval φ
      = (if i = 0 then Level.eval φ l0 else Level.eval φ l1) := by
    rcases hpin with rfl | rfl
    · obtain rfl : i = 0 := hidx.symm
      simp [pairFstEntry, Level.subst, Level.subst.go]
    · obtain rfl : i = 1 := hidx.symm
      have hne : uN ≠ vN := by decide
      simp [pairSndEntry, Level.subst, Level.subst.go]
  refine ⟨?_, fun _ => hfvA⟩
  by_cases hw : Nat.max (Level.eval φ l0) (Level.eval φ l1) = 0
  · -- the Prop collapse: everything is the proof point
    have hPpt : interp V ρ P = pt := by
      rw [hPv, psigmaMkV_zero hw, app_pt, app_pt, app_pt, app_pt]
    have hfpt : interp V ρ fv = pt := by
      have hta : interp V ρ ta ∈ˢ (univ 0 : V) := by
        have h := ihtta ρ hΔ
        rw [interp_sort, hfsort] at h
        have h0 : (if i = 0 then Level.eval φ l0 else Level.eval φ l1)
            = 0 := by
          have h1 : Level.eval φ l0 = 0 :=
            Nat.le_zero.mp
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw))
          have h2 : Level.eval φ l1 = 0 :=
            Nat.le_zero.mp
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw))
          split <;> assumption
        rw [h0] at h
        exact h ▸ (ihta ρ hΔ).2
      exact mem_univ_zero hta (ihfv ρ hΔ).2
    rw [hfpt]
    rcases hfv with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [interp_proj, if_pos rfl, hp_eq, hPpt, sfst_pt]
    · rw [interp_proj, if_neg (by omega), hp_eq, hPpt, ssnd_pt]
  · -- no collapse: the constructor value folds to the pair
    have hm3' : interp V ρ x ∈ˢ interp V ρ α := hm3
    have hPfold : interp V ρ P = spair (interp V ρ x) (interp V ρ y) := by
      rw [hPv, psigmaMkV_app V hm1' hm2' hm3' hm4', if_neg hw]
    rcases hfv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [interp_proj, if_pos rfl, hp_eq, hPfold, sfst_spair]
    · rw [interp_proj, if_neg (by omega), hp_eq, hPfold, ssnd_spair]

end Cases

end Setlec.SetR
