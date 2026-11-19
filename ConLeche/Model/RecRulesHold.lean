module

public import ConLeche.Model.Denotes
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Denote.Lemmas

public section

/-!
# The recursor rules in the model the invariant carries (task #610 spike)

`ConLeche.RecRulesHold` (`ConLeche/Denotes.lean`) states the ι equations of every stored
recursor over `Denotes`.  This module derives them, at the model `Model.ofEnvModelM` reads off
the invariant, from the invariant's `rec_rules` field (`RecRuleLaw`'s fired equation):

* `teleFit_of_Fits`: a fit of sets against a stored type (`Fits`, over `Denotes`) is a fit
  against the type's reading (`TeleFit`, over `interp`);
* `TeleFit.transfer`: a fit against a closed reading holds under every variable environment;
* `recRule_of_envModelM_ne_pt`: the ι equation where the major is not the point.

What is not here: where the major is the point, the law needs `IotaIndexPin` on the reading
of the constructor type's conclusion, from the spec's `IndexPin` on the conclusion itself.
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Term
open ConLeche.Model.Rules (PiChain teleFitPA_of_teleFit)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule Fits appList)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-- **A fit against a stored type is a fit against its reading.** -/
theorem teleFit_of_Fits {acval : Name → (Name → Nat) → Term}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ)) {env : Env} {φ : Name → Nat} :
    ∀ (xs : List V) (d : Nat) (e : Expr) {ta : Term} {ρ ρ' : Nat → V} {R : Expr},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e →
      e.looseBVarsBounded 0 = true →
      Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) xs ρ' R →
      ∃ rest, TeleFit V ρ ta xs rest
  | [], _, _, _, _, _, _, _, _, _, _ => ⟨_, .nil⟩
  | x :: xs, d, e, ta, ρ, ρ', R, h, hfb, hlb, hfit => by
    cases e with
    | forallE ty body =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denote_forallE_inv h
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      have hc : closeN d (.forallE ty body) = .forallE (closeN d ty 0) (closeN d body 1) := rfl
      rw [hc] at hfit
      cases hfit with
      | cons hA hx hrest =>
        have hA' := Denotes_of_denote (V := V) hcl d ty hta hfb'.1 hlb'.1 ρ
        obtain rfl := ConLeche.Denotes_functional hA hA'
        rw [← Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, push_eq_cons] at hrest
        obtain ⟨rest, hr⟩ := teleFit_of_Fits hcl xs (d + 1) _ hba
          (Expr.fvarsBelow_instantiate1 0 hfb'.2)
          (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) hrest
        exact ⟨rest, .cons hx hr⟩
    | _ => cases hfit

/-- A fit makes its term a Π-chain of the fit's length. -/
theorem piChain_of_teleFit {ρ : Nat → V} {T : Term} {vs : List V} {rest : V}
    (h : TeleFit V ρ T vs rest) : PiChain vs.length T := by
  induction h with
  | nil => trivial
  | cons _ _ ih => exact ih

/-- **A fit against a term scoped below `k` transfers** to an environment agreeing below `k`. -/
theorem TeleFit.transfer :
    ∀ {ρ σ : Nat → V} {T : Term} {vs : List V} {rest : V} {k : Nat},
      TeleFit V ρ T vs rest → Term.bvarsBelow k T → (∀ i, i < k → ρ i = σ i) →
      ∃ rest', TeleFit V σ T vs rest'
  | _, _, _, [], _, _, _, _, _ => ⟨_, .nil⟩
  | ρ, σ, _, _ :: _, _, k, .cons (A := A) (B := B) hm h, hb, hag => by
    have hb' : Term.bvarsBelow k A ∧ Term.bvarsBelow (k + 1) B := hb
    rw [interp_congr_below V A k ρ σ hb'.1 hag] at hm
    obtain ⟨r, hr⟩ := TeleFit.transfer (σ := Semantics.cons _ σ) h hb'.2 fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    exact ⟨r, .cons hm hr⟩

/-- Levels read alike at `φ` give one composed assignment. -/
theorem substFn_map_subst_self (φ : Name → Nat) (lps : List Name) :
    ∀ (ks : List Name) (vs : List Level),
      Level.substFn φ ks (vs.map (Level.subst lps (lps.map Level.param)))
        = Level.substFn φ ks vs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | k :: ks, v :: vs => by
    funext q
    simp only [List.map_cons, Level.substFn]
    rw [Level.eval_subst, Level.substFn_param_self, substFn_map_subst_self φ lps ks vs]

/-- **The spec's constructor levels are the fired comparands** at the recursor's own levels. -/
theorem substFn_ctorLevels (φ : Name → Nat) (rl : RecRule) (cnP : Nat) (lps cvjLps : List Name)
    (rP : Nat) :
    Level.substFn φ cvjLps (rl.ctorLevels cvjLps)
      = Level.substFn φ cvjLps
          (ConLeche.recFireComparands rl cnP lps (lps.map Level.param) cvjLps [] rP).1 := by
  unfold RecRule.ctorLevels ConLeche.recFireComparands
  split <;> rename_i h <;> simp only [h]
  · exact (substFn_map_subst_self φ lps cvjLps _).symm
  · exact (substFn_map_subst_self φ lps cvjLps _).symm
  · rw [show cvjLps.map (fun p => Level.subst lps (lps.map Level.param) (.param p))
        = (cvjLps.map Level.param).map (Level.subst lps (lps.map Level.param)) by
      rw [List.map_map]; rfl]
    exact (substFn_map_subst_self φ lps cvjLps _).symm

/-- A list of variables read in an environment holding a list. -/
theorem map_interp_bvars (σ : Nat → V) (o : Nat) (zs : List V)
    (hσ : ∀ i (h : i < zs.length), σ (o + i) = zs[i]) :
    ((List.range zs.length).map fun i => Term.bvar (o + i)).map (interp V σ) = zs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, interp_bvar]
  exact hσ i (by simpa using h1)

/-- A reading at a recursor's own levels is the uninstantiated reading. -/
theorem denote_inst_self {acval : Name → (Name → Nat) → Term} {env : Env} (m : EnvModel V env)
    (hm : m.acval = acval) (φ : Name → Nat) (lps : List Name) (e : Expr) :
    denote acval env φ 0 (e.instantiateLevelParams lps (lps.map Level.param))
      = denote acval env φ 0 e := by
  subst hm
  rw [denotePInstLevels m φ lps _ 0 e, Level.substFn_param_self]

/-- **The ι equation where the major is not the point**, in the model the invariant carries. -/
theorem recRule_of_envModelM_ne_pt {env : Env} (m : EnvModelM V env)
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hf : env.find? n = some (.recInfo cv mI rP isK rules)) {rl : RecRule} (hrl : rl ∈ rules)
    {cvj : ConstantVal} {cnP cnF : Nat} {iT : Name}
    (hc : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF iT))
    {φ : Name → Nat} {ρ : Nat → V} {C R : V} {xs ys : List V} {ρr ρc : Nat → V} {Tr Tc : Expr}
    (hC : ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ
      (.const rl.ctor (rl.ctorLevels cvj.levelParams)) C)
    (hR : ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ rl.rhs R)
    (hxs : xs.length = mI) (hys : ys.length = cnP + rl.nfields)
    (hfr : Fits (cvalOf m.base2.acval) env φ ρ cv.type (xs ++ [appList C ys]) ρr Tr)
    (hfc : Fits (cvalOf m.base2.acval) env φ ρ
      (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams))
      ys ρc Tc)
    (hpt : appList C ys ≠ pt) :
    appList (cvalOf m.base2.acval n φ) (xs ++ [appList C ys])
      = appList R (xs.take rP ++ ys.drop cnP) := by
  have hcl := m.base2.cval_closed
  -- the constructor's levels and value
  cases hC with
  | const hf' hlen =>
  rw [hc] at hf'
  obtain rfl := Option.some.inj hf'
  simp only [ConstantInfo.toConstantVal] at hlen hfr hpt ⊢
  -- the variable environment holding the arguments
  let σ : Nat → V := fun i => (xs ++ ys).getD i pt
  let xsT : List Term := (List.range xs.length).map fun i => .bvar (0 + i)
  let ysT : List Term := (List.range ys.length).map fun i => .bvar (xs.length + i)
  have hxsI : xsT.map (interp V σ) = xs := map_interp_bvars σ 0 xs fun i h => by
    simp [σ, List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getElem?_eq_getElem h]
  have hysI : ysT.map (interp V σ) = ys := map_interp_bvars σ xs.length ys fun i h => by
    show (xs ++ ys).getD (xs.length + i) pt = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [List.getElem?_eq_getElem h]
  let ψc := Level.substFn φ cvj.levelParams (rl.ctorLevels cvj.levelParams)
  let majT : Term := Term.mkAppN (m.base2.acval rl.ctor ψc) ysT
  have hmaj : interp V σ majT = appList (cvalOf m.base2.acval rl.ctor ψc) ys := by
    show interp V σ (Term.mkAppN _ ysT) = _
    rw [interp_mkAppN, interp_cvalOf hcl, appList, ← hysI]
    simp only [ysT, List.foldl_map]
  -- the recursor's law at its own levels
  have hmemR := ConLeche.Env.find?_mem hf
  have hmemC := ConLeche.Env.find?_mem hc
  obtain ⟨-, hus, -⟩ := m.rec_rules φ n cv mI rP isK rules hf rl hrl
  obtain ⟨Ra, hRa, -, -, hlaw⟩ := hus (cv.levelParams.map Level.param) (by simp)
  rw [denote_inst_self m.base2 rfl] at hRa
  obtain ⟨TVa, hTVa⟩ := m.type_reads _ hmemR φ
  obtain ⟨TVja, hTVja⟩ := m.type_reads _ hmemC ψc
  have hTVa' : denote m.base2.acval env φ 0
      (cv.type.instantiateLevelParams cv.levelParams (cv.levelParams.map Level.param))
        = some TVa := by
    rw [denote_inst_self m.base2 rfl]; exact hTVa
  have hTVja' : denote m.base2.acval env φ 0
      (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)) = some TVja := by
    rw [denotePInstLevels m.base2 φ]; exact hTVja
  -- the scoping facts
  have hwfR := m.base2.wf.consts _ hmemR
  have hwfC := m.base2.wf.consts _ hmemC
  have hrhs := (hwfR.2.2.2.2.2 cv mI rP isK rules rfl rl hrl)
  have hwfR1 : cv.type.hasFvar = false := hwfR.1
  have hwfR4 : cv.type.looseBVarsBounded 0 = true := hwfR.2.2.2.1
  have hwfC1 : cvj.type.hasFvar = false := hwfC.1
  have hwfC4 : cvj.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hnfC' : (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)).hasFvar = false := by
    simpa [Expr.hasFvar_instantiateLevelParams] using hwfC1
  have hlbC' : (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)).looseBVarsBounded 0 = true := by
    simpa [Expr.looseBVarsBounded_instantiateLevelParams] using hwfC4
  -- the fits, at the readings, at `σ`
  rw [← Expr.closeN_of_hasFvar _ 0 0 hwfR1] at hfr
  rw [← Expr.closeN_of_hasFvar _ 0 0 hnfC'] at hfc
  obtain ⟨_, hfr'⟩ := teleFit_of_Fits hcl _ 0 _ hTVa
    (fvarsBelow_zero_of_not_hasFvar hwfR1) hwfR4 hfr
  obtain ⟨_, hfc'⟩ := teleFit_of_Fits hcl _ 0 _ hTVja'
    (fvarsBelow_zero_of_not_hasFvar hnfC') hlbC' hfc
  have hclA := denote_closed hcl hwfR1 hwfR4 hTVa
  have hclC := denote_closed hcl hnfC' hlbC' hTVja'
  obtain ⟨_, hfr''⟩ := hfr'.transfer (σ := σ) hclA (fun _ h => absurd h (Nat.not_lt_zero _))
  obtain ⟨_, hfc''⟩ := hfc'.transfer (σ := σ) hclC (fun _ h => absurd h (Nat.not_lt_zero _))
  have hC' : ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ
      (.const rl.ctor (rl.ctorLevels cvj.levelParams)) (cvalOf m.base2.acval rl.ctor ψc) := .const hc hlen
  have hvals : (xsT ++ [majT]).map (interp V σ) = xs ++ [appList (cvalOf m.base2.acval rl.ctor ψc) ys] := by
    rw [List.map_append, hxsI, List.map_singleton, hmaj]
  rw [← hvals] at hfr''
  rw [← hysI] at hfc''
  obtain ⟨restR, hPA⟩ := teleFitPA_of_teleFit _ (by simpa using piChain_of_teleFit hfr'') hfr''
  obtain ⟨restC, hPC⟩ := teleFitPA_of_teleFit _ (by simpa using piChain_of_teleFit hfc'') hfc''
  have hlenx : xsT.length = mI := by simp [xsT, hxs]
  have hleny : ysT.length = cnP + rl.nfields := by simp [ysT, hys]
  obtain ⟨heq, -⟩ := hlaw cvj cnP cnF iT hc (rl.ctorLevels cvj.levelParams) σ xsT ysT TVa TVja restR restC hlenx hleny hlen
    (substFn_ctorLevels φ rl cnP cv.levelParams cvj.levelParams rP)
    (fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      simp)
    (fun h => absurd (hmaj ▸ h) hpt) hTVa' hTVja' hPA hPC
  -- read the equation back
  rw [Level.substFn_param_self] at heq
  have hL : interp V σ (Term.mkAppN (m.base2.acval n φ) (xsT ++ [majT]))
      = appList (cvalOf m.base2.acval n φ) (xs ++ [appList (cvalOf m.base2.acval rl.ctor ψc) ys]) := by
    rw [interp_mkAppN, interp_cvalOf hcl, appList, ← hvals, List.foldl_map]
  have hRr : interp V σ (Term.mkAppN Ra (xsT.take rP ++ ysT.drop cnP))
      = appList (interp V σ Ra) (xs.take rP ++ ys.drop cnP) := by
    rw [interp_mkAppN, ← List.foldl_map (f := interp V σ) (g := SetTheory.app),
      List.map_append, List.map_take, List.map_drop, hxsI, hysI]
    rfl
  rw [hL, hRr] at heq
  -- the right-hand side's value
  have hRd := Denotes_of_denote (V := V) hcl 0 rl.rhs hRa
    (fvarsBelow_zero_of_not_hasFvar hrhs.1) hrhs.2.2.2.1 ρ
  rw [Expr.closeN_of_hasFvar _ 0 0 hrhs.1] at hRd
  obtain rfl := ConLeche.Denotes_functional hR hRd
  rw [interp_closed (V := V) (denote_closed hcl hrhs.1 hrhs.2.2.2.1 hRa) σ ρ] at heq
  exact heq

end ConLeche.Model
