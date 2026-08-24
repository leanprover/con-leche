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

/-- A model of a *raw* environment (see the module docstring).  All
existing model clauses — `mem_type`, `defn_eq`, `annot_ok`,
`rec_rules`, … — are consumed through `model` verbatim; `erase_eq` is
the one new proof obligation per install step. -/
structure RawEnvModel (V : Type u) [SetTheory V] (env : Env) where
  /-- The annotated shadow environment (the witness). -/
  aenv : Env
  /-- The witness erases to what the kernel stores. -/
  erase_eq : aenv.eraseCod = env
  /-- The unchanged model, over the shadow. -/
  model : EnvModel V aenv

/-- A raw-side `hasFvar` certificate transfers to any twin. -/
theorem Expr.hasFvar_witness {e eR : Expr} (hw : e.eraseCod = eR)
    (h : eR.hasFvar = false) : e.hasFvar = false := by
  rw [← hw, Expr.hasFvar_eraseCod] at h; exact h

/-- A raw-side `looseBVarsBounded` certificate transfers to any twin. -/
theorem Expr.looseBVarsBounded_witness {e eR : Expr} {k : Nat}
    (hw : e.eraseCod = eR) (h : eR.looseBVarsBounded k = true) :
    e.looseBVarsBounded k = true := by
  rw [← hw, Expr.looseBVarsBounded_eraseCod] at h; exact h

namespace RawEnvModel

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

end RawEnvModel

/-! ## Raw constant install

The witness-shaped restatement of the simplest constant-install
extension (`extend_model`, specialized to a plain definition whose name
touches no pinned machinery). -/

/-- Install a plain definition into a raw environment: the stored trees
are raw, the shadow is extended with the annotated twins. -/
theorem extend_model_raw {envR : Env} (M : RawEnvModel V envR)
    {name : Name} {lps : List Name} {typeR valueR type value : Expr}
    (hint : ReducibilityHint)
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
    -- name-only side conditions (a plain definition)
    (hnres : reservedBasisNames.contains name = false)
    (hpshape : name.isProjFnShape = false)
    (hnop : natOpNames.contains name = false)
    (hndm : natDivModNames.contains name = false)
    -- witness-side semantic obligations, over the shadow environment
    (htp : type.allLevelParamsDefined lps = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V M.model.val M.aenv ψ value = some v ∧
      interpClosed V M.model.val M.aenv ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V M.model.val M.aenv ψ 0 (rho0 V) value) :
    Nonempty (RawEnvModel V
      ⟨.defnInfo ⟨name, lps, typeR⟩ valueR hint :: envR.consts⟩) := by
  have hconsts := M.consts_eraseCod
  have hfindA := M.find?_witness_eq_none hfindR
  have htf := Expr.hasFvar_witness htw htfR
  have hvf := Expr.hasFvar_witness hvw hvfR
  have htb := Expr.looseBVarsBounded_witness htw htbR
  have hvb := Expr.looseBVarsBounded_witness hvw hvbR
  have htr := M.constsResolve_witness htw htrR
  have hvr := M.constsResolve_witness hvw hvrR
  obtain ⟨aenv, herase, m⟩ := M
  -- extend the shadow with the annotated twins, via `extend_model` verbatim
  obtain ⟨m'⟩ :=
    extend_model (V := V) m (name := name) (lps := lps)
      (type := type) (value := value) hfindA htp htf htr htb hvp hvf hvr hvb
      hkey hAty hAval
      (ConstantInfo.defnInfo ⟨name, lps, type⟩ value hint) rfl rfl
      (fun cv2 value2 h2 heq => by
        injection heq with h1 h2' h3
        exact ⟨h1.symm, h2'.symm⟩)
      (fun cv2 value2 heq => by exact nomatch heq)
      rfl hnres hpshape
      (fun hc _ => nomatch hnop.symm.trans hc)
      (fun hc _ => nomatch hndm.symm.trans hc)
      (fun _ hex => absurd hex (by rintro ⟨cv₀, h, -⟩; cases h))
  -- the stored environment is the erasure of the extended shadow
  refine ⟨⟨⟨ConstantInfo.defnInfo ⟨name, lps, type⟩ value hint :: aenv.consts⟩,
    ?_, m'⟩⟩
  simp [Env.eraseCod, ConstantInfo.eraseCod, ConstantVal.eraseCod, htw, hvw,
    hconsts]

end Setlec
