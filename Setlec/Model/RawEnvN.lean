import Setlec.Model.Norm

/-!
# The raw model at the twin relation (task #100, stage 4d)

`Setlec/Model/RawEnv.lean` states the raw-storage model and its
constant-install combinators at the *plain erasure* twin
(`fun a e => a.eraseCod = e`).  The end state stores the **parsed**
record untouched, so the twin relation is `Env.TwinAt O f`
(`aenv.eraseCodS = Env.norm O f env`, `Setlec/Model/Norm.lean`) and
those combinators need re-proving there.  This module is that
re-proof; nothing else in the tower moves, because `RawEnvModelE` was
already parametric in the relation.

Two differences from the erasure instantiation drive the work:

* **the shallow erasure**, not the hereditary one.  `eraseCodS` leaves
  `fvar` type annotations alone (it is the erasure a decoration pass
  inverts), so its `hasFvar` / `looseBVarsBounded` / `constsResolve`
  invariances are the `fvar`-clause-trivial versions of stage 1's;
* **`norm` is not an invariance.**  Zeta expansion duplicates the let
  value, so each certificate transfer rests on the stage-4d-prep
  congruences (`Expr.norm_hasFvar`, `Expr.norm_looseBVarsBounded`,
  `Expr.norm_constsResolve`), each of which carries an **oracle**
  hypothesis: the projection rewrite emits a term built from the
  environment, so only the annotation pass knows it is well-formed.
  `NormOracleOk` bundles the three; the flip discharges it from what
  the annotation pass established, exactly as `CodAgree` is
  discharged.

The environment side additionally needs that *both* maps preserve
names (`Env.find?_eraseCodS`, `Env.find?_norm`), which is what makes a
raw-side freshness certificate a witness-side one and lets
`constsResolve` cross between the two environments.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory

/-! ## Shallow-erasure invariances

The `eraseCodS` counterparts of `Expr.hasFvar_eraseCod` &co.  Each
`fvar` clause is `rfl` rather than a recursive call — the shallow
erasure does not descend into annotations. -/

/-- `hasFvar` is shallow-erasure-invariant. -/
theorem Expr.hasFvar_eraseCodS : ∀ e : Expr, e.eraseCodS.hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const .. | .lit _ => rfl
  | .fvar _ _ _ => rfl
  | .app f a => by
    simp [Expr.eraseCodS, Expr.hasFvar, Expr.hasFvar_eraseCodS f,
      Expr.hasFvar_eraseCodS a]
  | .lam _ ty b _ => by
    simp [Expr.eraseCodS, Expr.hasFvar, Expr.hasFvar_eraseCodS ty,
      Expr.hasFvar_eraseCodS b]
  | .forallE _ ty b _ => by
    simp [Expr.eraseCodS, Expr.hasFvar, Expr.hasFvar_eraseCodS ty,
      Expr.hasFvar_eraseCodS b]
  | .letE _ ty v b => by
    simp [Expr.eraseCodS, Expr.hasFvar, Expr.hasFvar_eraseCodS ty,
      Expr.hasFvar_eraseCodS v, Expr.hasFvar_eraseCodS b]
  | .proj _ _ e => by
    simp [Expr.eraseCodS, Expr.hasFvar, Expr.hasFvar_eraseCodS e]

/-- `looseBVarsBounded` is shallow-erasure-invariant. -/
theorem Expr.looseBVarsBounded_eraseCodS :
    ∀ (e : Expr) (k : Nat),
      e.eraseCodS.looseBVarsBounded k = e.looseBVarsBounded k
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl
  | .fvar _ _ _, _ => rfl
  | .app f a, k => by
    simp [Expr.eraseCodS, Expr.looseBVarsBounded,
      Expr.looseBVarsBounded_eraseCodS f k,
      Expr.looseBVarsBounded_eraseCodS a k]
  | .lam _ ty b _, k => by
    simp [Expr.eraseCodS, Expr.looseBVarsBounded,
      Expr.looseBVarsBounded_eraseCodS ty k,
      Expr.looseBVarsBounded_eraseCodS b (k + 1)]
  | .forallE _ ty b _, k => by
    simp [Expr.eraseCodS, Expr.looseBVarsBounded,
      Expr.looseBVarsBounded_eraseCodS ty k,
      Expr.looseBVarsBounded_eraseCodS b (k + 1)]
  | .letE _ ty v b, k => by
    simp [Expr.eraseCodS, Expr.looseBVarsBounded,
      Expr.looseBVarsBounded_eraseCodS ty k,
      Expr.looseBVarsBounded_eraseCodS v k,
      Expr.looseBVarsBounded_eraseCodS b (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.eraseCodS, Expr.looseBVarsBounded,
      Expr.looseBVarsBounded_eraseCodS e k]

/-- `constsResolve` is shallow-erasure-invariant (at a fixed
environment — the environment map is handled separately). -/
theorem Expr.constsResolve_eraseCodS (env : Env) :
    ∀ e : Expr, e.eraseCodS.constsResolve env = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) | .lit (.strVal _) => rfl
  | .const _ _ => rfl
  | .fvar _ _ _ => rfl
  | .app f a => by
    simp [Expr.eraseCodS, Expr.constsResolve,
      Expr.constsResolve_eraseCodS env f, Expr.constsResolve_eraseCodS env a]
  | .lam _ ty b _ => by
    simp [Expr.eraseCodS, Expr.constsResolve,
      Expr.constsResolve_eraseCodS env ty, Expr.constsResolve_eraseCodS env b]
  | .forallE _ ty b _ => by
    simp [Expr.eraseCodS, Expr.constsResolve,
      Expr.constsResolve_eraseCodS env ty, Expr.constsResolve_eraseCodS env b]
  | .letE _ ty v b => by
    simp [Expr.eraseCodS, Expr.constsResolve,
      Expr.constsResolve_eraseCodS env ty, Expr.constsResolve_eraseCodS env v,
      Expr.constsResolve_eraseCodS env b]
  | .proj _ _ e => by
    simp [Expr.eraseCodS, Expr.constsResolve,
      Expr.constsResolve_eraseCodS env e]

/-! ## Both maps preserve names -/

theorem ConstantInfo.name_eraseCodS (ci : ConstantInfo) :
    ci.eraseCodS.name = ci.name := by
  cases ci <;> rfl

theorem ConstantInfo.name_norm (O : NormOracle) (f : Nat)
    (ci : ConstantInfo) : (ci.norm O f).name = ci.name := by
  cases ci <;> rfl

theorem Env.find?_eraseCodS (env : Env) (n : Name) :
    env.eraseCodS.find? n = (env.find? n).map ConstantInfo.eraseCodS := by
  show (env.consts.map ConstantInfo.eraseCodS).find? _ = _
  have hp : ((fun x : ConstantInfo => x.name == n) ∘ ConstantInfo.eraseCodS) =
      (fun x : ConstantInfo => x.name == n) := by
    funext ci
    simp [Function.comp, ConstantInfo.name_eraseCodS]
  rw [Env.find?, List.find?_map, hp]

theorem Env.find?_norm (O : NormOracle) (f : Nat) (env : Env) (n : Name) :
    (Env.norm O f env).find? n =
      (env.find? n).map (ConstantInfo.norm O f) := by
  show (env.consts.map (ConstantInfo.norm O f)).find? _ = _
  have hp : ((fun x : ConstantInfo => x.name == n) ∘ ConstantInfo.norm O f) =
      (fun x : ConstantInfo => x.name == n) := by
    funext ci
    simp [Function.comp, ConstantInfo.name_norm]
  rw [Env.find?, List.find?_map, hp]

/-! ## The oracle's obligations

The projection-rewrite oracle emits a term the expression alone does
not determine (it is built from the environment's projection table), so
every raw-side certificate transfer needs the oracle to respect that
certificate.  These are exactly the three hypotheses of the
stage-4d-prep congruences, bundled. -/

/-- The projection oracle preserves the three raw-side syntactic
certificates.  Discharged at the flip from what the annotation pass
established about the term it emits — the same shape of obligation as
`CodAgree`. -/
structure NormOracleOk (O : NormOracle) (env : Env) : Prop where
  /-- The rewrite introduces no free variable. -/
  hasFvar : ∀ d n r, O d n = some r → n.hasFvar = false → r.hasFvar = false
  /-- The rewrite preserves the loose-`bvar` bound. -/
  bounded : ∀ d n r k, O d n = some r → n.looseBVarsBounded k = true →
    r.looseBVarsBounded k = true
  /-- The rewrite mentions no unresolved constant. -/
  consts : ∀ d n r, O d n = some r → n.constsResolve env = true →
    r.constsResolve env = true

/-! ## Certificate transfer across the twin relation -/

variable {O : NormOracle} {f d : Nat} {env : Env}

/-- A raw-side `hasFvar` certificate transfers to the twin. -/
theorem Expr.hasFvar_witnessN (hO : NormOracleOk O env) {ea e : Expr}
    (hw : Expr.TwinAt O f d ea e) (h : e.hasFvar = false) :
    ea.hasFvar = false := by
  have h1 := Expr.norm_hasFvar O hO.hasFvar f d e h
  rw [← hw, Expr.hasFvar_eraseCodS] at h1
  exact h1

/-- A raw-side `looseBVarsBounded` certificate transfers to the twin. -/
theorem Expr.looseBVarsBounded_witnessN (hO : NormOracleOk O env)
    {ea e : Expr} {k : Nat} (hw : Expr.TwinAt O f d ea e)
    (h : e.looseBVarsBounded k = true) : ea.looseBVarsBounded k = true := by
  have h1 := Expr.norm_looseBVarsBounded O hO.bounded f d e k h
  rw [← hw, Expr.looseBVarsBounded_eraseCodS] at h1
  exact h1

namespace RawEnvModelE

variable {env : Env} (M : RawEnvModelN V O f env)

/-- Constant lists correspond, each side under its own map. -/
theorem consts_twin :
    M.aenv.consts.map ConstantInfo.eraseCodS =
      env.consts.map (ConstantInfo.norm O f) := by
  simpa [Env.eraseCodS, Env.norm] using congrArg Env.consts M.erase_eq

/-- The witness and the stored environment have the same names. -/
theorem find?_isSome_twin (n : Name) :
    (M.aenv.find? n).isSome = (env.find? n).isSome := by
  have h := congrArg (fun e => (Env.find? e n).isSome) M.erase_eq
  simpa [Env.find?_eraseCodS, Env.find?_norm] using h

/-- A raw-side freshness certificate is one about the witness. -/
theorem find?_witness_eq_noneN {n : Name} (h : env.find? n = none) :
    M.aenv.find? n = none := by
  have := M.find?_isSome_twin n
  rw [h] at this
  cases hh : M.aenv.find? n with
  | none => rfl
  | some ci => rw [hh] at this; simp at this

/-- A raw-side `constsResolve` certificate transfers to the twin (and
across to the witness environment, which has the same names). -/
theorem constsResolve_witnessN (hO : NormOracleOk O env) {ea e : Expr}
    (hw : Expr.TwinAt O f d ea e) (h : e.constsResolve env = true) :
    ea.constsResolve M.aenv = true := by
  have h1 := Expr.norm_constsResolve (env := env) O hO.consts f d e h
  rw [← hw, Expr.constsResolve_eraseCodS] at h1
  rw [Expr.constsResolve_congr (M.find?_isSome_twin) ea]
  exact h1

/-! ### The generic raw-install combinator, at the twin relation -/

/-- Any extension of the witness environment is an extension of the
stored environment it is a twin of. -/
theorem extendN {cs csR : List ConstantInfo}
    (hcw : cs.map ConstantInfo.eraseCodS = csR.map (ConstantInfo.norm O f))
    (hm : Nonempty (EnvModel V ⟨cs ++ M.aenv.consts⟩)) :
    Nonempty (RawEnvModelN V O f ⟨csR ++ env.consts⟩) := by
  obtain ⟨m'⟩ := hm
  exact ⟨⟨⟨cs ++ M.aenv.consts⟩, by
    simp [Env.TwinAt, Env.eraseCodS, Env.norm, List.map_append, hcw,
      M.consts_twin], m'⟩⟩

/-- The single-record case (the shape of every constant install). -/
theorem extend_oneN {c cR : ConstantInfo}
    (hcw : c.eraseCodS = ConstantInfo.norm O f cR)
    (hm : Nonempty (EnvModel V ⟨c :: M.aenv.consts⟩)) :
    Nonempty (RawEnvModelN V O f ⟨cR :: env.consts⟩) := by
  obtain ⟨m'⟩ := hm
  exact ⟨⟨⟨c :: M.aenv.consts⟩, by
    simp [Env.TwinAt, Env.eraseCodS, Env.norm, hcw, M.consts_twin], m'⟩⟩

end RawEnvModelE

/-! ## Raw constant install, at the twin relation

`extend_model_raw` verbatim, with the erasure twin replaced by
`Expr.TwinAt` and the certificate transfers routed through the `norm`
congruences.  The hypothesis split is unchanged: raw-side certificates
on the stored (parsed) trees, witness-side obligations on the
annotated shadow. -/

/-- Install a constant into a raw environment whose witness is a
`Env.TwinAt` twin: the stored record is the parsed one, the shadow is
extended with its annotated twin. -/
theorem extend_model_rawN {envR : Env} (M : RawEnvModelN V O f envR)
    (hO : NormOracleOk O envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    -- the witnesses
    (htw : Expr.TwinAt O f 0 type typeR)
    (hvw : Expr.TwinAt O f 0 value valueR)
    -- raw-side syntactic certificates
    (hfindR : envR.find? name = none)
    (htfR : typeR.hasFvar = false)
    (htrR : typeR.constsResolve envR = true)
    (htbR : typeR.looseBVarsBounded 0 = true)
    (hvfR : valueR.hasFvar = false)
    (hvrR : valueR.constsResolve envR = true)
    (hvbR : valueR.looseBVarsBounded 0 = true)
    -- witness-side semantic obligations, over the shadow environment
    (htp : type.allLevelParamsDefined lps = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V M.model.val M.aenv ψ value = some v ∧
      interpClosed V M.model.val M.aenv ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) value)
    -- the stored record and its twin
    (c₀ c₀R : ConstantInfo) (hcw : c₀.eraseCodS = ConstantInfo.norm O f c₀R)
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hc₀val : ∀ cv2 value2 h2, c₀ = ConstantInfo.defnInfo cv2 value2 h2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀thm : ∀ cv2 value2, c₀ = ConstantInfo.thmInfo cv2 value2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀nb : c₀.isBasis = false)
    (hc₀nres : reservedBasisNames.contains name = false)
    (hc₀pshape : name.isProjFnShape = false)
    (hnatop : natOpNames.contains name = true →
      (∃ cv₀ v₀ h₀, c₀ = ConstantInfo.defnInfo cv₀ v₀ h₀) →
      natOpGuard (⟨c₀ :: M.aenv.consts⟩ : Env) name = true ∧
      ∀ eq ∈ natOpEquations 0 name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V M.model.val M.aenv ψ 2 (rho0 V) (.const natName []) =
          some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V M.model.val M.aenv ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.1) =
        interpExpr V M.model.val M.aenv ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.2))
    (hdivmod : natDivModNames.contains name = true →
      (∃ cv₀ v₀ h₀, c₀ = ConstantInfo.defnInfo cv₀ v₀ h₀) →
      natOpGuard (⟨c₀ :: M.aenv.consts⟩ : Env) name = true ∧
      ∀ val' : ConstVal V,
        (∀ ψ : Name → Nat,
          interpClosed V M.model.val M.aenv ψ value = some (val' name ψ)) →
        (∀ n, n ≠ name → ∀ ψ' : Name → Nat, val' n ψ' = M.model.val n ψ') →
        DivModEqs V val' name)
    (hreduce : reduceOpNames.contains name = true →
      (∃ cv₀, c₀ = ConstantInfo.axiomInfo cv₀ ∧
        ConstantVal.matchesPin cv₀ (reduceOpCvA name) = true) →
      ((⟨c₀ :: M.aenv.consts⟩ : Env).find? (reduceElemName name)).isSome = true ∧
      ∀ val' : ConstVal V,
        (∀ ψ : Name → Nat,
          interpClosed V M.model.val M.aenv ψ value = some (val' name ψ)) →
        (∀ n, n ≠ name → ∀ ψ' : Name → Nat, val' n ψ' = M.model.val n ψ') →
        ∀ (ψ : Name → Nat) (x : V),
          x ∈ˢ val' (reduceElemName name) ψ →
          SetTheory.app (val' name ψ) x = x) :
    Nonempty (RawEnvModelN V O f ⟨c₀R :: envR.consts⟩) := by
  have hfindA := M.find?_witness_eq_noneN hfindR
  have htf := Expr.hasFvar_witnessN hO htw htfR
  have hvf := Expr.hasFvar_witnessN hO hvw hvfR
  have htb := Expr.looseBVarsBounded_witnessN hO htw htbR
  have hvb := Expr.looseBVarsBounded_witnessN hO hvw hvbR
  have htr := M.constsResolve_witnessN hO htw htrR
  have hvr := M.constsResolve_witnessN hO hvw hvrR
  refine M.extend_oneN hcw ?_
  obtain ⟨aenv, herase, m⟩ := M
  exact
    extend_model (V := V) m (name := name) (lps := lps)
      (type := type) (value := value) hfindA htp htf htr htb hvp hvf hvr hvb
      hkey hAty hAval c₀ hc₀cv hc₀name hc₀val hc₀thm hc₀nb hc₀nres hc₀pshape
      hnatop hdivmod hreduce

/-- The plain-definition instance. -/
theorem extend_model_rawN_defn {envR : Env} (M : RawEnvModelN V O f envR)
    (hO : NormOracleOk O envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    (hint : ReducibilityHint)
    (htw : Expr.TwinAt O f 0 type typeR)
    (hvw : Expr.TwinAt O f 0 value valueR)
    (hfindR : envR.find? name = none)
    (htfR : typeR.hasFvar = false)
    (htrR : typeR.constsResolve envR = true)
    (htbR : typeR.looseBVarsBounded 0 = true)
    (hvfR : valueR.hasFvar = false)
    (hvrR : valueR.constsResolve envR = true)
    (hvbR : valueR.looseBVarsBounded 0 = true)
    (hnres : reservedBasisNames.contains name = false)
    (hpshape : name.isProjFnShape = false)
    (hnop : natOpNames.contains name = false)
    (hndm : natDivModNames.contains name = false)
    (htp : type.allLevelParamsDefined lps = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V M.model.val M.aenv ψ value = some v ∧
      interpClosed V M.model.val M.aenv ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) value) :
    Nonempty (RawEnvModelN V O f
      ⟨.defnInfo ⟨name, lps, typeR⟩ valueR hint :: envR.consts⟩) :=
  extend_model_rawN M hO htw hvw hfindR htfR htrR htbR hvfR hvrR hvbR
    htp hvp hkey hAty hAval
    (ConstantInfo.defnInfo ⟨name, lps, type⟩ value hint)
    (ConstantInfo.defnInfo ⟨name, lps, typeR⟩ valueR hint)
    (by
      have htw' : type.eraseCodS = Expr.norm O f 0 typeR := htw
      have hvw' : value.eraseCodS = Expr.norm O f 0 valueR := hvw
      simp [ConstantInfo.eraseCodS, ConstantVal.eraseCodS,
        ConstantInfo.norm, ConstantVal.norm, htw', hvw'])
    rfl rfl
    (fun cv2 value2 h2 heq => by
      injection heq with h1 h2' h3
      exact ⟨h1.symm, h2'.symm⟩)
    (fun cv2 value2 heq => by exact nomatch heq)
    rfl hnres hpshape
    (fun hc _ => nomatch hnop.symm.trans hc)
    (fun hc _ => nomatch hndm.symm.trans hc)
    (fun _ hex => absurd hex (by rintro ⟨cv₀, h, -⟩; cases h))

/-- The axiom instance (the value slot is the type itself, as
`checkDecl` does at an axiom record). -/
theorem extend_model_rawN_axiom {envR : Env} (M : RawEnvModelN V O f envR)
    (hO : NormOracleOk O envR)
    {name : Name} {lps : List Name} {typeR type : Expr}
    (htw : Expr.TwinAt O f 0 type typeR)
    (hfindR : envR.find? name = none)
    (htfR : typeR.hasFvar = false)
    (htrR : typeR.constsResolve envR = true)
    (htbR : typeR.looseBVarsBounded 0 = true)
    (hnres : reservedBasisNames.contains name = false)
    (hpshape : name.isProjFnShape = false)
    (hnop : natOpNames.contains name = false)
    (hndm : natDivModNames.contains name = false)
    (hnred : reduceOpNames.contains name = false)
    (htp : type.allLevelParamsDefined lps = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V M.model.val M.aenv ψ type = some v ∧
      interpClosed V M.model.val M.aenv ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) type) :
    Nonempty (RawEnvModelN V O f
      ⟨.axiomInfo ⟨name, lps, typeR⟩ :: envR.consts⟩) :=
  extend_model_rawN M hO htw htw hfindR htfR htrR htbR htfR htrR htbR
    htp htp hkey hAty hAty
    (ConstantInfo.axiomInfo ⟨name, lps, type⟩)
    (ConstantInfo.axiomInfo ⟨name, lps, typeR⟩)
    (by
      have htw' : type.eraseCodS = Expr.norm O f 0 typeR := htw
      simp [ConstantInfo.eraseCodS, ConstantVal.eraseCodS,
        ConstantInfo.norm, ConstantVal.norm, htw'])
    rfl rfl
    (fun cv2 value2 h2 heq => by exact nomatch heq)
    (fun cv2 value2 heq => by exact nomatch heq)
    rfl hnres hpshape
    (fun hc _ => nomatch hnop.symm.trans hc)
    (fun hc _ => nomatch hndm.symm.trans hc)
    (fun hc _ => nomatch hnred.symm.trans hc)

/-- The theorem instance. -/
theorem extend_model_rawN_thm {envR : Env} (M : RawEnvModelN V O f envR)
    (hO : NormOracleOk O envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    (htw : Expr.TwinAt O f 0 type typeR)
    (hvw : Expr.TwinAt O f 0 value valueR)
    (hfindR : envR.find? name = none)
    (htfR : typeR.hasFvar = false)
    (htrR : typeR.constsResolve envR = true)
    (htbR : typeR.looseBVarsBounded 0 = true)
    (hvfR : valueR.hasFvar = false)
    (hvrR : valueR.constsResolve envR = true)
    (hvbR : valueR.looseBVarsBounded 0 = true)
    (hnres : reservedBasisNames.contains name = false)
    (hpshape : name.isProjFnShape = false)
    (hnop : natOpNames.contains name = false)
    (hndm : natDivModNames.contains name = false)
    (htp : type.allLevelParamsDefined lps = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V M.model.val M.aenv ψ value = some v ∧
      interpClosed V M.model.val M.aenv ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) value) :
    Nonempty (RawEnvModelN V O f
      ⟨.thmInfo ⟨name, lps, typeR⟩ valueR :: envR.consts⟩) :=
  extend_model_rawN M hO htw hvw hfindR htfR htrR htbR hvfR hvrR hvbR
    htp hvp hkey hAty hAval
    (ConstantInfo.thmInfo ⟨name, lps, type⟩ value)
    (ConstantInfo.thmInfo ⟨name, lps, typeR⟩ valueR)
    (by
      have htw' : type.eraseCodS = Expr.norm O f 0 typeR := htw
      have hvw' : value.eraseCodS = Expr.norm O f 0 valueR := hvw
      simp [ConstantInfo.eraseCodS, ConstantVal.eraseCodS,
        ConstantInfo.norm, ConstantVal.norm, htw', hvw'])
    rfl rfl
    (fun cv2 value2 h2 heq => by exact nomatch heq)
    (fun cv2 value2 heq => by
      injection heq with h1 h2'
      exact ⟨h1.symm, h2'.symm⟩)
    rfl hnres hpshape
    (fun hc _ => nomatch hnop.symm.trans hc)
    (fun hc _ => nomatch hndm.symm.trans hc)
    (fun _ hex => absurd hex (by rintro ⟨cv₀, h, -⟩; cases h))

end Setlec
