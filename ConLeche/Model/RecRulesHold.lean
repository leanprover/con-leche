module

public import ConLeche.Model.Denotes
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Denote.Lemmas

public section

/-!
# The recursor rules in the model the invariant carries (task #610 spikes)

`ConLeche.RuleEqsHold` (`ConLeche/Denotes.lean`) states every stored recursor rule's ι equation
as a proposition (`iotaEq`: `∀ prefix fields, @Eq (motive indices major) (rec prefix indices
major) (rhs prefix fields)`) that must be inhabited.  This module holds what a derivation of it
from the invariant has so far:

* the semantic equation, from the invariant's `rec_rules` (`RecRuleLaw`'s fired equation), where
  the major is not the point and the arguments fit the recursor's whole telescope
  (`recRule_of_envModelM_ne_pt`, over `Fits`, the telescope fit over `Denotes`;
  `teleFit_of_Fits` and `TeleFit.transfer` carry it to the readings);
* substitution over `Denotes` (`Denotes_liftLooseBVars`, `Denotes_instantiateLift`): the
  constructor's fields at the parameters, the indices and the equation's type are such
  substitutions;
* the telescope (`TeleOk`, `tele_inhabited`, `teleOk_eq`, `RuleEqsHold_of`): the equation
  holds where, at every fit of the prefix and the fields, the type is a member of the motive's
  universe and both sides denote the same member of it.

What is not here (task #610 spike 2 record in DESIGN.md): that the constructor's indices and
the constructor application fit the recursor's index and major binders (typing), the point case
of the law, and the readability of the pieces at every fit.
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Term
open ConLeche.Model.Rules (PiChain teleFitPA_of_teleFit)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-- A set applied to a list of sets, left to right. -/
noncomputable def appList (F : V) (xs : List V) : V := xs.foldl app F

/-- `Fits cval env φ ρ T xs ρ' R`: the sets `xs` fit the leading `∀`
binders of `T` read at `ρ` — each a member of what its domain denotes,
the domain read with the earlier sets pushed — and `R` is the rest of
`T`, to be read at `ρ'`, which is `ρ` with `xs` pushed. -/
inductive Fits (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    (Nat → V) → Expr → List V → (Nat → V) → Expr → Prop
  | nil {ρ : Nat → V} {T : Expr} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : Nat → V} {A B R : Expr} {A' x : V} {xs : List V}
      (hA : ConLeche.Denotes cval env φ ρ A A') (hx : x ∈ˢ A')
      (h : Fits cval env φ (ConLeche.push x ρ) B xs ρ' R) :
      Fits cval env φ ρ (.forallE A B) (x :: xs) ρ' R

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

/-! ### Reading the ι equations: substitution and telescopes over `Denotes` -/

section Subst

variable {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}

/-- The environment a lift by `k` at cutoff `c` reads its source in. -/
def skipAt (c k : Nat) (ρ : Nat → V) : Nat → V := fun i => if i < c then ρ i else ρ (i + k)

omit [SetTheory V] in
theorem push_skipAt (x : V) (c k : Nat) (ρ : Nat → V) :
    ConLeche.push x (skipAt c k ρ) = skipAt (c + 1) k (ConLeche.push x ρ) := by
  funext i
  cases i with
  | zero => simp [skipAt, ConLeche.push]
  | succ i =>
    by_cases h : i < c
    · have h' : i + 1 < c + 1 := by omega
      simp [skipAt, ConLeche.push, h, h']
    · have h' : ¬ i + 1 < c + 1 := by omega
      simp [skipAt, ConLeche.push, h, h', show i + 1 + k = i + k + 1 by omega]

theorem strLitToConstructor_looseBVarsBounded (s : String) (c : Nat) :
    (ConLeche.strLitToConstructor s).looseBVarsBounded c = true := by
  unfold ConLeche.strLitToConstructor
  simp only [Expr.looseBVarsBounded, Bool.true_and]
  induction s.toList with
  | nil => simp [Expr.looseBVarsBounded]
  | cons a l ih => simp [Expr.looseBVarsBounded, ih]

theorem natLitToConstructor_looseBVarsBounded' (n c : Nat) :
    (ConLeche.natLitToConstructor n).looseBVarsBounded c = true := by
  cases n <;> simp [ConLeche.natLitToConstructor, Expr.looseBVarsBounded]

/-- Instantiating variables no loose variable reaches is the identity. -/
theorem instantiateLift_eq_self (vs : List Expr) :
    ∀ {e : Expr} {d : Nat}, e.looseBVarsBounded d = true → e.instantiateLift vs d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp [Expr.instantiateLift, hb]
  | _ =>
    intro d hb
    simp_all [Expr.looseBVarsBounded, Expr.instantiateLift]

/-- **Lifting**: a term read where a lift by `k` at cutoff `c` skips `k`
variables denotes what its lift denotes. -/
theorem Denotes_liftLooseBVars {k : Nat} :
    ∀ {σ : Nat → V} {e : Expr} {X : V}, ConLeche.Denotes cval env φ σ e X →
    ∀ {c : Nat} {ρ : Nat → V}, σ = skipAt c k ρ →
      ConLeche.Denotes cval env φ ρ (e.liftLooseBVars k c) X := by
  intro σ e X h
  induction h with
  | bvar =>
    rename_i i
    intro c ρ hσ
    subst hσ
    by_cases hi : c ≤ i
    · have hi' : ¬ i < c := Nat.not_lt.mpr hi
      simp only [Expr.liftLooseBVars, skipAt, ge_iff_le, hi, hi', ↓reduceIte]
      exact .bvar
    · have hi' : i < c := Nat.lt_of_not_le hi
      simp only [Expr.liftLooseBVars, skipAt, ge_iff_le, hi, hi', ↓reduceIte]
      exact .bvar
  | sort => intro c ρ _; exact .sort
  | const hf hlen => intro c ρ _; exact .const hf hlen
  | app _ _ ihf iha => intro c ρ hσ; exact .app (ihf hσ) (iha hσ)
  | lam _ _ ihA ihF =>
    intro c ρ hσ
    subst hσ
    exact .lam (ihA rfl) fun x hx => ihF x hx (push_skipAt x c k ρ)
  | pi _ _ ihA ihB =>
    intro c ρ hσ
    subst hσ
    exact .pi (ihA rfl) fun x hx => ihB x hx (push_skipAt x c k ρ)
  | letE _ _ ihv ihb =>
    intro c ρ hσ
    subst hσ
    exact .letE (ihv rfl) (ihb (push_skipAt _ c k ρ))
  | proj_table ht _ ih => intro c ρ hσ; exact .proj_table ht (ih hσ)
  | natLit _ ih =>
    rename_i n _ _
    intro c ρ hσ
    have h := ih hσ
    rw [Expr.liftLooseBVars_eq_self (natLitToConstructor_looseBVarsBounded' n c)] at h
    exact .natLit h
  | strLit _ ih =>
    rename_i s _ _
    intro c ρ hσ
    have h := ih hσ
    rw [Expr.liftLooseBVars_eq_self (strLitToConstructor_looseBVarsBounded s c)] at h
    exact .strLit h

/-- The environment an instantiation at depth `d` reads its source in:
`ρ` below `d`, the values' denotations `Ys` next, `ρ` lowered above. -/
def insAt (d : Nat) (Ys : List V) (ρ : Nat → V) : Nat → V := fun i =>
  if i < d then ρ i else if h : i - d < Ys.length then Ys[i - d] else ρ (i - Ys.length)

omit [SetTheory V] in
theorem push_insAt (x : V) (d : Nat) (Ys : List V) (ρ : Nat → V) :
    ConLeche.push x (insAt d Ys ρ) = insAt (d + 1) Ys (ConLeche.push x ρ) := by
  funext i
  cases i with
  | zero => simp [insAt, ConLeche.push]
  | succ i =>
    by_cases h : i < d
    · have h1 : i + 1 < d + 1 := by omega
      simp [insAt, ConLeche.push, h, h1]
    · have h1 : ¬ i + 1 < d + 1 := by omega
      have h2 : i + 1 - (d + 1) = i - d := by omega
      by_cases h' : i - d < Ys.length
      · simp [insAt, ConLeche.push, h, h1, h2, h']
      · have h3 : i + 1 - Ys.length = (i - Ys.length) + 1 := by omega
        simp [insAt, ConLeche.push, h, h1, h2, h', h3]

/-- **Instantiation**: substituting values for `bvar d, bvar (d+1), …`
(`instantiateLift`, the values read at `σ`, the environment outside the
`d` crossed binders) denotes what the term denotes with the values'
denotations in their place. -/
theorem Denotes_instantiateLift {vs : List Expr} {Ys : List V} {σ : Nat → V}
    (hlen : Ys.length = vs.length)
    (hvs : ∀ j (h : j < vs.length), ConLeche.Denotes cval env φ σ vs[j] (Ys[j]'(hlen ▸ h))) :
    ∀ {τ : Nat → V} {e : Expr} {X : V}, ConLeche.Denotes cval env φ τ e X →
    ∀ {d : Nat} {ρ : Nat → V}, τ = insAt d Ys ρ → (∀ i, ρ (i + d) = σ i) →
      ConLeche.Denotes cval env φ ρ (e.instantiateLift vs d) X := by
  intro τ e X h
  induction h with
  | bvar =>
    rename_i i
    intro d ρ hτ hσ
    subst hτ
    by_cases hi : i < d
    · simp only [Expr.instantiateLift, insAt, hi, ↓reduceIte]
      exact .bvar
    · by_cases hj : i - d < vs.length
      · have hj' : i - d < Ys.length := by rw [hlen]; exact hj
        simp only [Expr.instantiateLift, insAt, hi, ↓reduceIte, hj, hj', dite_true]
        refine Denotes_liftLooseBVars (hvs _ hj) ?_
        funext q
        simp [skipAt, ← hσ q]
      · have hj' : ¬ i - d < Ys.length := by rw [hlen]; exact hj
        simp only [Expr.instantiateLift, insAt, hi, ↓reduceIte, hj, dite_false, hlen]
        exact .bvar
  | sort => intro d ρ _ _; exact .sort
  | const hf hl => intro d ρ _ _; exact .const hf hl
  | app _ _ ihf iha => intro d ρ hτ hσ; exact .app (ihf hτ hσ) (iha hτ hσ)
  | lam _ _ ihA ihF =>
    intro d ρ hτ hσ
    subst hτ
    exact .lam (ihA rfl hσ) fun x hx => ihF x hx (push_insAt x d Ys ρ)
      fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i
  | pi _ _ ihA ihB =>
    intro d ρ hτ hσ
    subst hτ
    exact .pi (ihA rfl hσ) fun x hx => ihB x hx (push_insAt x d Ys ρ)
      fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i
  | letE _ _ ihv ihb =>
    intro d ρ hτ hσ
    subst hτ
    exact .letE (ihv rfl hσ) (ihb (push_insAt _ d Ys ρ)
      fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i)
  | proj_table ht _ ih => intro d ρ hτ hσ; exact .proj_table ht (ih hτ hσ)
  | natLit _ ih =>
    rename_i n _ _
    intro d ρ hτ hσ
    have h := ih hτ hσ
    rw [instantiateLift_eq_self vs (natLitToConstructor_looseBVarsBounded' n d)] at h
    exact .natLit h
  | strLit _ ih =>
    rename_i s _ _
    intro d ρ hτ hσ
    have h := ih hτ hσ
    rw [instantiateLift_eq_self vs (strLitToConstructor_looseBVarsBounded s d)] at h
    exact .strLit h

/-- **A telescope over a truth value, inhabited at every fit**: the
`∀`s read (each domain denotes, at every fit of the earlier ones), and
at every fit of all of them the body denotes an inhabited truth value. -/
def TeleOk (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    (Nat → V) → List Expr → Expr → Prop
  | ρ, [], body => ∃ Y, ConLeche.Denotes cval env φ ρ body Y ∧ Y ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ Y
  | ρ, d :: ds, body => ∃ A, ConLeche.Denotes cval env φ ρ d A ∧
      ∀ x, x ∈ˢ A → TeleOk cval env φ (ConLeche.push x ρ) ds body

/-- **An inhabited telescope**: where `TeleOk` holds, the `∀`-telescope
denotes an inhabited truth value. -/
theorem tele_inhabited : ∀ (ds : List Expr) {ρ : Nat → V} {body : Expr},
    TeleOk cval env φ ρ ds body →
    ∃ P, ConLeche.Denotes cval env φ ρ (ds.foldr .forallE body) P ∧
      P ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ P
  | [], _, _, h => h
  | d :: ds, ρ, body, ⟨A, hA, h⟩ => by
    classical
    have hc : ∀ x, x ∈ˢ A → ∃ P, ConLeche.Denotes cval env φ (ConLeche.push x ρ)
        (ds.foldr .forallE body) P ∧ P ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ P :=
      fun x hx => tele_inhabited ds (h x hx)
    let B : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (hc x hx) else empty
    have hB : ∀ x (hx : x ∈ˢ A), B x = Classical.choose (hc x hx) := fun x hx => by
      simp only [B, hx, dite_true]
    have hz : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) := fun x hx => by
      rw [hB x hx]; exact (Classical.choose_spec (hc x hx)).2.1
    refine ⟨piV A B, .pi hA fun x hx => ?_, ?_, ?_⟩
    · rw [hB x hx]; exact (Classical.choose_spec (hc x hx)).1
    · rw [piV_eq_zero hz]; exact piR_zero_mem_univZero
    · refine (pt_mem_piV_iff fun x hx => Or.inl (hz x hx)).mpr fun x hx => ?_
      rw [hB x hx]; exact (Classical.choose_spec (hc x hx)).2.2

/-- **The equation at the end of the telescope**: in a model, where the
type denotes a member of its universe and both sides denote the same
member of it, the equation is an inhabited truth value. -/
theorem teleOk_eq {env : Env} (M : ConLeche.Model V env) {φ : Name → Nat} {ρ : Nat → V}
    {u : Level} {ty l r : Expr} {E T L : V}
    (hE : ConLeche.Denotes M.cval env φ ρ (.const ConLeche.eqName [u]) E)
    (hT : ConLeche.Denotes M.cval env φ ρ ty T) (hL : ConLeche.Denotes M.cval env φ ρ l L)
    (hR : ConLeche.Denotes M.cval env φ ρ r L)
    (hTu : T ∈ˢ (univ (Level.eval φ u) : V)) (hLm : L ∈ˢ T) :
    TeleOk M.cval env φ ρ [] (.app (.app (.app (.const ConLeche.eqName [u]) ty) l) r) := by
  refine ⟨_, .app (.app (.app hE hT) hL) hR, ?_, ?_⟩ <;>
    rw [M.eq_equality u φ ρ E T L L hE hTu hLm hLm]
  · exact eqv_mem_univZero L L
  · exact pt_mem_eqv_self L

/-- **The ι equations hold where their telescopes are inhabited.** -/
theorem RuleEqsHold_of {cval : Name → (Name → Nat) → V} {env : Env}
    (h : ∀ e ∈ ConLeche.ruleEqs env, ∃ ds body, e = ds.foldr .forallE body ∧
      ∀ φ ρ, TeleOk cval env φ ρ ds body) :
    ConLeche.RuleEqsHold cval env := by
  intro e he φ ρ
  obtain ⟨ds, body, rfl, hok⟩ := h e he
  obtain ⟨P, hP, -, hpt⟩ := tele_inhabited ds (hok φ ρ)
  exact ⟨P, hP, pt, hpt⟩

end Subst

end ConLeche.Model
