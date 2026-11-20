module

public import ConLeche.Model.IsModelBridge
import ConLeche.Model.OfEnvModelM
import ConLeche.Denotes

public section

/-!
# A constant holds at other level-parameter names (task #619)

`ModelOf` reads a constant's level parameters positionally (`Level.assign`), so a constant
whose statement (and, for a definition, value) is a stored constant's at other names of its level
parameters (`RenamedAs`: as many, neither list with a repeat) holds wherever the stored one does
(`modelOf_renamed`).  The two readings meet through `Expr.eval`'s substitution lemma
(`eval_instantiateLevelParams`) and the stored constant's scoping (`EnvWF`: its level parameters
are all among its names, `eval_congr_levels`).
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- **`Expr.eval` across a level instantiation**: the instantiated term at `φ` is the term at the
substitution's assignment. -/
theorem eval_instantiateLevelParams (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (ρ : BVarIdx → V), Expr.eval model φ ρ (e.instantiateLevelParams ks us) =
      Expr.eval model (Level.substFn φ ks us) ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ; rfl
  | fvar i t _ => intro ρ; rfl
  | sort u => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, Level.eval_subst]
  | const n us' =>
    intro ρ
    simp [Expr.instantiateLevelParams, Expr.eval, List.map_map, Function.comp_def,
      Level.eval_subst]
  | app f a ihf iha => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, ihf, iha]
  | lam t b iht ihb => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, iht, ihb]
  | forallE t b iht ihb => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, iht, ihb]
  | letE t v b iht ihv ihb => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, ihv, ihb]
  | lit l => intro ρ; cases l <;> rfl
  | proj s i e ih => intro ρ; simp [Expr.instantiateLevelParams, Expr.eval, ih]

/-- A level reads its parameters only. -/
theorem Level.eval_congr_params {φ φ' : LevelParam → Nat} {ps : List Name}
    (h : ∀ p ∈ ps, φ p = φ' p) :
    ∀ (l : Level), l.allParamsDefined ps = true → Level.eval φ l = Level.eval φ' l
  | .zero, _ => rfl
  | .succ l, hl => by
    simp only [Level.allParamsDefined] at hl
    simp [Level.eval, Level.eval_congr_params h l hl]
  | .max l r, hl => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at hl
    simp [Level.eval, Level.eval_congr_params h l hl.1, Level.eval_congr_params h r hl.2]
  | .imax l r, hl => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at hl
    simp [Level.eval, Level.eval_congr_params h l hl.1, Level.eval_congr_params h r hl.2]
  | .param n, hl => by
    simp only [Level.allParamsDefined, List.contains_iff_mem] at hl
    exact h n hl

/-- **A term reads its level parameters only**: two assignments agreeing on `ps` read a term
whose level parameters are all among `ps` alike. -/
theorem eval_congr_levels (model : Name → List Nat → V) {φ φ' : LevelParam → Nat}
    {ps : List Name} (h : ∀ p ∈ ps, φ p = φ' p) :
    ∀ (e : Expr) (ρ : BVarIdx → V), e.allLevelParamsDefined ps = true →
      Expr.eval model φ ρ e = Expr.eval model φ' ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ _; rfl
  | fvar i t _ => intro ρ _; rfl
  | sort u =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined] at hd
    simp [Expr.eval, Level.eval_congr_params h u hd]
  | const n us =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    simp only [Expr.eval]
    congr 1
    exact List.map_congr_left fun u hu => Level.eval_congr_params h u (hd u hu)
  | app f a ihf iha =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp [Expr.eval, ihf ρ hd.1, iha ρ hd.2]
  | lam t b iht ihb =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.eval, iht ρ hd.1]
    congr 1; funext x; exact ihb _ hd.2
  | forallE t b iht ihb =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.eval, iht ρ hd.1]
    congr 1; funext x; exact ihb _ hd.2
  | letE t v b iht ihv ihb =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.eval, ihv ρ hd.1.2]
    exact ihb _ hd.2
  | lit l => intro ρ _; cases l <;> rfl
  | proj s i e ih =>
    intro ρ hd
    simp only [Expr.allLevelParamsDefined] at hd
    simp [Expr.eval, ih ρ hd]

/-- A substitution by parameters reads the assignment on those parameters only. -/
theorem substFn_params_congr {φ φ' : LevelParam → Nat} :
    ∀ {ps qs : List Name}, ps.length = qs.length → (∀ q ∈ qs, φ q = φ' q) → ∀ p ∈ ps,
      Level.substFn φ ps (qs.map Level.param) p = Level.substFn φ' ps (qs.map Level.param) p
  | [], _, _, _, p, hp => by simp at hp
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: ps, b :: qs, hl, h, p, hp => by
    simp only [List.map_cons, Level.substFn]
    by_cases hap : a = p
    · simp [hap, Level.eval, h b List.mem_cons_self]
    · simp only [hap, ↓reduceIte]
      exact substFn_params_congr (Nat.succ.inj hl) (fun q hq => h q (List.mem_cons_of_mem _ hq))
        p ((List.mem_cons.mp hp).resolve_left (Ne.symm hap))

/-- **Positional level assignments, renamed**: at `qs`'s values, the substitution of `ps` by
`qs`'s parameters reads every name of `ps` as `ps`'s own assignment does. -/
theorem substFn_assign_rename :
    ∀ {ps qs : List Name} {vals : List Nat}, ps.Nodup → qs.Nodup → ps.length = qs.length →
      vals.length = qs.length → ∀ p ∈ ps,
        Level.substFn (Level.assign qs vals) ps (qs.map Level.param) p = Level.assign ps vals p
  | [], _, _, _, _, _, _, p, hp => by simp at hp
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, hv, _, _ => by simp at hv
  | a :: ps, b :: qs, v :: vals, hps, hqs, hl, hv, p, hp => by
    obtain ⟨-, hps'⟩ := List.nodup_cons.mp hps
    obtain ⟨hb, hqs'⟩ := List.nodup_cons.mp hqs
    simp only [List.map_cons, Level.substFn, Level.assign]
    by_cases hap : a = p
    · subst hap
      simp [Level.eval]
    · simp only [hap, ↓reduceIte]
      have hp' : p ∈ ps := (List.mem_cons.mp hp).resolve_left (Ne.symm hap)
      rw [← substFn_assign_rename hps' hqs' (Nat.succ.inj hl) (Nat.succ.inj hv) p hp']
      refine substFn_params_congr (Nat.succ.inj hl) (fun q hq => ?_) p hp'
      have hbq : b ≠ q := fun e => hb (e ▸ hq)
      simp [hbq]

/-- **A constant holds where a stored constant it renames holds** (see the module docstring). -/
theorem modelOf_renamed {env : Env} (m : Model.EnvModelM V env)
    {model : Name → List Nat → V} (hag : AgreesOn model (Model.cvalOf m.base2.acval) env)
    {ci c : ConstantInfo} (hf : env.find? c.name = some ci)
    (hr : RenamedAs ci c) : ModelOf model c := by
  obtain ⟨hks, hps, hlen, hname, hty, hdef, hrec, -⟩ := hr
  let M := Model.Model.ofEnvModelM m
  have hloc := cvalLocal_ofEnvModelM m
  rw [← Model.Model.ofEnvModelM_cval m] at hloc hag
  have hmem : ci ∈ env.consts := Env.find?_mem hf
  obtain ⟨-, hdefd, -, -, hdv, -⟩ := m.base2.wf.consts ci hmem
  intro vals hl
  let φS := Level.assign ci.toConstantVal.levelParams vals
  have hval : model c.name vals = M.cval c.name φS := by
    rw [hag c.name ci hf, posModel_of_find hf]
  have hren : ∀ e : Expr, e.allLevelParamsDefined ci.toConstantVal.levelParams = true →
      Expr.eval model (Level.assign c.toConstantVal.levelParams vals) ρ₀
        (e.instantiateLevelParams ci.toConstantVal.levelParams
          (c.toConstantVal.levelParams.map Level.param)) = Expr.eval model φS ρ₀ e := by
    intro e he
    rw [eval_instantiateLevelParams]
    exact eval_congr_levels model
      (substFn_assign_rename hks hps hlen hl) e ρ₀ he
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT, hmT⟩ := M.mem ci hmem φS ρ₀
    show model c.name vals ∈ˢ Expr.eval model _ ρ₀ c.toConstantVal.type
    rw [hval, hty, hren _ hdefd, eval_of_Denotes hloc hag hT, hname]
    exact hmT
  · cases c with
    | defnInfo cv value hint =>
      obtain ⟨cv', v', rfl, hv⟩ := hdef cv value hint rfl
      obtain ⟨-, hvd, -⟩ := hdv cv' v' hint rfl
      have hD := M.defn_eq cv' v' hint hmem φS ρ₀
      show model cv.name vals = Expr.eval model (Level.assign cv.levelParams vals) ρ₀ value
      have hv' : value = v'.instantiateLevelParams cv'.levelParams
          (cv.levelParams.map Level.param) := hv
      rw [hv']
      exact hval.trans (((congrArg (M.cval · φS) hname).trans
        (eval_of_Denotes hloc hag hD).symm).trans (hren v' hvd).symm)
    | recInfo cv mI rP isK rules => exact absurd rfl (hrec cv mI rP isK rules)
    | _ => trivial

end ConLeche
