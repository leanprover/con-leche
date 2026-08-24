import Setlec.Model.Erasure
import Setlec.Model.Extend.Model
import Setlec.Model.Subst

/-!
# The witness-shaped environment model (task #100, stage 1)

`RawEnvModel V env` is what a *raw* (annotation-free) stored
environment has instead of an `EnvModel`: an annotated **shadow
environment** `aenv` — the per-declaration annotation witnesses,
packaged coherently — that erases to what the kernel stores, together
with the unchanged `EnvModel` of the shadow.

Everything the model layer says stays a statement about `aenv`:
`interpExpr`, `AnnotOk`, `EnvModel` and the whole `Extend*` tower
survive verbatim.  Only the env-facing seam changes, and it splits the
per-install obligations in two:

* **raw side** — freshness, `hasFvar`, `constsResolve`,
  `looseBVarsBounded`: certificates a raw-storage kernel checks on the
  stored trees, transferred to the witness by the erasure-invariance
  lemmas of `Setlec/Model/Erasure.lean`;
* **witness side** — `AnnotOk`, the interpretations, and
  `allLevelParamsDefined` (which reads annotation levels, so it is
  deliberately *not* raw-derivable): discharged by the retargeted
  annotation certificates.

`extend_model_raw` is that split in miniature, for the simplest
constant install: the conclusion stores the **raw** trees and extends
the shadow with the twins, and every `EnvModel` clause rides
`extend_model` unchanged.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory

/-- A model of a stored environment relative to an **erasure** `er`
(see the module docstring): the annotated shadow environment `aenv` —
the annotation witness — together with the unchanged `EnvModel` of the
shadow, and the requirement that the shadow erases to what the kernel
stores.  All existing model clauses — `mem_type`, `defn_eq`,
`annot_ok`, `rec_rules`, … — are consumed through `model` verbatim;
`erase_eq` is the one new proof obligation per install step.

The erasure is a parameter so the switch can be staged: at `er := id`
the witness *is* the stored environment (the transitional
instantiation, while annotations are still stored), at
`er := Env.eraseCod` it is the real thing.  `Expr.eraseCod_idem`
characterizes the fixed points for the flip. -/
structure RawEnvModelE (V : Type u) [SetTheory V] (er : Env → Env)
    (env : Env) where
  /-- The annotated shadow environment (the witness). -/
  aenv : Env
  /-- The witness erases to what the kernel stores. -/
  erase_eq : er aenv = env
  /-- The unchanged model, over the shadow. -/
  model : EnvModel V aenv

/-- The codomain-erasure instantiation: the end state of task #100. -/
abbrev RawEnvModel (V : Type u) [SetTheory V] (env : Env) :=
  RawEnvModelE V Env.eraseCod env

/-- The identity-erasure instantiation: the transitional state, in
which the stored environment is its own witness. -/
abbrev RawEnvModelId (V : Type u) [SetTheory V] (env : Env) :=
  RawEnvModelE V id env

namespace RawEnvModelE

/-- At the identity erasure an environment model *is* a raw model. -/
def ofEnvModel {env : Env} (m : EnvModel V env) : RawEnvModelId V env :=
  ⟨env, rfl, m⟩

/-- … and conversely, so the transitional switch is a restatement. -/
def toEnvModel {env : Env} (M : RawEnvModelId V env) : EnvModel V env :=
  M.erase_eq ▸ M.model

end RawEnvModelE

/-- A raw-side `hasFvar` certificate transfers to any twin. -/
theorem Expr.hasFvar_witness {e eR : Expr} (hw : e.eraseCod = eR)
    (h : eR.hasFvar = false) : e.hasFvar = false := by
  rw [← hw, Expr.hasFvar_eraseCod] at h; exact h

/-- A raw-side `looseBVarsBounded` certificate transfers to any twin. -/
theorem Expr.looseBVarsBounded_witness {e eR : Expr} {k : Nat}
    (hw : e.eraseCod = eR) (h : eR.looseBVarsBounded k = true) :
    e.looseBVarsBounded k = true := by
  rw [← hw, Expr.looseBVarsBounded_eraseCod] at h; exact h

namespace RawEnvModelE

variable {env : Env} (M : RawEnvModel V env)

/-- Constant lists correspond. -/
theorem consts_eraseCod : M.aenv.consts.map ConstantInfo.eraseCod = env.consts := by
  simpa [Env.eraseCod] using congrArg Env.consts M.erase_eq

/-- A raw-side freshness certificate is one about the witness. -/
theorem find?_witness_eq_none {n : Name} (h : env.find? n = none) :
    M.aenv.find? n = none :=
  Env.find?_eq_none_of_eraseCod (by rw [M.erase_eq]; exact h)

/-- A raw-side `constsResolve` certificate transfers to any twin. -/
theorem constsResolve_witness {e eR : Expr} (hw : e.eraseCod = eR)
    (h : eR.constsResolve env = true) : e.constsResolve M.aenv = true := by
  rw [← hw, ← M.erase_eq, Expr.constsResolve_eraseCod] at h; exact h

/-! ### The generic raw-install combinator

Every install path's `_raw` sibling is the same two moves: run the
existing shadow extension unchanged, then discharge `erase_eq`.  This
combinator is that second move, once and for all — so the inductive
block, projection, direct-structure and basis-pin paths do **not** need
their 60-line signatures restated; each is `RawEnvModelE.extend`
applied to the `extend_*` lemma it already uses, with the one new
obligation being that the installed records erase to what the kernel
stores. -/

/-- Any extension of the witness environment is an extension of the raw
environment it erases to. -/
theorem extend {cs csR : List ConstantInfo}
    (hcw : cs.map ConstantInfo.eraseCod = csR)
    (hm : Nonempty (EnvModel V ⟨cs ++ M.aenv.consts⟩)) :
    Nonempty (RawEnvModel V ⟨csR ++ env.consts⟩) := by
  obtain ⟨m'⟩ := hm
  exact ⟨⟨⟨cs ++ M.aenv.consts⟩, by
    simp [Env.eraseCod, List.map_append, hcw, M.consts_eraseCod], m'⟩⟩

/-- The single-record case (the shape of every constant install). -/
theorem extend_one {c cR : ConstantInfo} (hcw : c.eraseCod = cR)
    (hm : Nonempty (EnvModel V ⟨c :: M.aenv.consts⟩)) :
    Nonempty (RawEnvModel V ⟨cR :: env.consts⟩) := by
  obtain ⟨m'⟩ := hm
  exact ⟨⟨⟨c :: M.aenv.consts⟩, by
    simp [Env.eraseCod, hcw, M.consts_eraseCod], m'⟩⟩

end RawEnvModelE

/-! ## Raw constant install

The witness-shaped restatement of `extend_model` — the single
constant-install extension behind *every* non-inductive install path
(axioms, definitions, theorems, opaques, and the pinned `Nat`-operation
/ `Nat.div`-`Nat.mod` / `reduce` families, whose extra obligations ride
through unchanged).  The split of hypotheses is the design's claim in
miniature:

* **raw side** — freshness, `hasFvar`, `constsResolve`,
  `looseBVarsBounded` on the stored raw trees, transferred to the
  witness by the erasure-invariance lemmas;
* **witness side** — the annotated twins, their `AnnotOk`, their
  interpretations, and `allLevelParamsDefined` (which reads annotation
  levels, hence is deliberately *not* raw-derivable), plus the
  name-keyed pin obligations, all phrased over the shadow.

The conclusion stores the **raw** constant and extends the shadow with
its twin; every `EnvModel` clause rides `extend_model` unchanged. -/

/-- Install a constant into a raw environment: the stored record is
raw, the shadow is extended with its annotated twin. -/
theorem extend_model_raw {envR : Env} (M : RawEnvModel V envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    -- the witnesses
    (htw : type.eraseCod = typeR) (hvw : value.eraseCod = valueR)
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
    (c₀ c₀R : ConstantInfo) (hcw : c₀.eraseCod = c₀R)
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
    Nonempty (RawEnvModel V ⟨c₀R :: envR.consts⟩) := by
  have hfindA := M.find?_witness_eq_none hfindR
  have htf := Expr.hasFvar_witness htw htfR
  have hvf := Expr.hasFvar_witness hvw hvfR
  have htb := Expr.looseBVarsBounded_witness htw htbR
  have hvb := Expr.looseBVarsBounded_witness hvw hvbR
  have htr := M.constsResolve_witness htw htrR
  have hvr := M.constsResolve_witness hvw hvrR
  refine M.extend_one hcw ?_
  obtain ⟨aenv, herase, m⟩ := M
  -- extend the shadow with the annotated twin, via `extend_model` verbatim
  exact
    extend_model (V := V) m (name := name) (lps := lps)
      (type := type) (value := value) hfindA htp htf htr htb hvp hvf hvr hvb
      hkey hAty hAval c₀ hc₀cv hc₀name hc₀val hc₀thm hc₀nb hc₀nres hc₀pshape
      hnatop hdivmod hreduce

/-- The plain-definition instance: the shape every ordinary `def`
install takes (no pinned machinery on the name). -/
theorem extend_model_raw_defn {envR : Env} (M : RawEnvModel V envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    (hint : ReducibilityHint)
    (htw : type.eraseCod = typeR) (hvw : value.eraseCod = valueR)
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
    Nonempty (RawEnvModel V
      ⟨.defnInfo ⟨name, lps, typeR⟩ valueR hint :: envR.consts⟩) :=
  extend_model_raw M htw hvw hfindR htfR htrR htbR hvfR hvrR hvbR
    htp hvp hkey hAty hAval
    (ConstantInfo.defnInfo ⟨name, lps, type⟩ value hint)
    (ConstantInfo.defnInfo ⟨name, lps, typeR⟩ valueR hint)
    (by simp [ConstantInfo.eraseCod, ConstantVal.eraseCod, htw, hvw])
    rfl rfl
    (fun cv2 value2 h2 heq => by
      injection heq with h1 h2' h3
      exact ⟨h1.symm, h2'.symm⟩)
    (fun cv2 value2 heq => by exact nomatch heq)
    rfl hnres hpshape
    (fun hc _ => nomatch hnop.symm.trans hc)
    (fun hc _ => nomatch hndm.symm.trans hc)
    (fun _ hex => absurd hex (by rintro ⟨cv₀, h, -⟩; cases h))

/-- The axiom instance: no value to speak of, so the value slot is the
type itself (as `checkDecl` does at an axiom record). -/
theorem extend_model_raw_axiom {envR : Env} (M : RawEnvModel V envR)
    {name : Name} {lps : List Name} {typeR type : Expr}
    (htw : type.eraseCod = typeR)
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
    Nonempty (RawEnvModel V ⟨.axiomInfo ⟨name, lps, typeR⟩ :: envR.consts⟩) :=
  extend_model_raw M htw htw hfindR htfR htrR htbR htfR htrR htbR
    htp htp hkey hAty hAty
    (ConstantInfo.axiomInfo ⟨name, lps, type⟩)
    (ConstantInfo.axiomInfo ⟨name, lps, typeR⟩)
    (by simp [ConstantInfo.eraseCod, ConstantVal.eraseCod, htw])
    rfl rfl
    (fun cv2 value2 h2 heq => by exact nomatch heq)
    (fun cv2 value2 heq => by exact nomatch heq)
    rfl hnres hpshape
    (fun hc _ => nomatch hnop.symm.trans hc)
    (fun hc _ => nomatch hndm.symm.trans hc)
    (fun hc _ => nomatch hnred.symm.trans hc)

/-- The theorem instance. -/
theorem extend_model_raw_thm {envR : Env} (M : RawEnvModel V envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    (htw : type.eraseCod = typeR) (hvw : value.eraseCod = valueR)
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
    Nonempty (RawEnvModel V
      ⟨.thmInfo ⟨name, lps, typeR⟩ valueR :: envR.consts⟩) :=
  extend_model_raw M htw hvw hfindR htfR htrR htbR hvfR hvrR hvbR
    htp hvp hkey hAty hAval
    (ConstantInfo.thmInfo ⟨name, lps, type⟩ value)
    (ConstantInfo.thmInfo ⟨name, lps, typeR⟩ valueR)
    (by simp [ConstantInfo.eraseCod, ConstantVal.eraseCod, htw, hvw])
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
