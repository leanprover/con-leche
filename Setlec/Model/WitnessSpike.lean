import Setlec.Model.Extend.Model
import Setlec.Model.Subst

/-!
# DESIGN SPIKE — witness-shaped model plumbing for raw (annotation-free) storage

**Do not merge.**  Feasibility skeleton for the planned "install/check
split + annotation removal" refactor: the environment stores *raw*
expression trees (no binder codomain-sort annotations), and the level
source for the model's structural `∀`/`λ` interpretation moves to the
proof side as a per-declaration *annotation witness*.

Representation chosen: the **erasure view**.  A witness for a raw tree
`e` is an annotated twin `ê` with `ê.eraseCod = e`; the witness for a
whole environment is an annotated *shadow environment* `aenv` with
`aenv.eraseCod = env`.  `interpExpr`, `AnnotOk`, `EnvModel` and the
entire `Extend*` tower then survive **verbatim** as statements about
`aenv`; only the env-facing seam changes:

* `RawEnvModel env` packages `(aenv, aenv.eraseCod = env, EnvModel aenv)`;
* raw-side syntactic certificates (freshness, `constsResolve`,
  `hasFvar`, `looseBVarsBounded`) transfer across erasure by the
  congruence lemmas below; semantic obligations (`AnnotOk`,
  interpretations, `allLevelParamsDefined` — which reads annotation
  levels and is *not* erasure-invariant raw→annotated) stay phrased on
  the witness and are discharged by the retargeted annotation certs;
* twin tracking through reduction rests on erasure being *structural*
  (constructor-wise inversion) and commuting with `instantiate1`
  (`Expr.eraseCod_instantiate1`), so the existing substitution lemmas
  (`interp_beta`, …) apply to the twin unchanged (`interp_twin_beta`).

The two end-to-end proofs required by the spike are sorry-free:
`interp_twin_beta` (interp side) and `extend_model_raw` (extend side).
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory

/-! ## Erasure -/

/-- Drop the codomain-sort annotation of one binder. -/
def BinderMeta.eraseCod (m : BinderMeta) : BinderMeta := ⟨m.bi, none⟩

/-- Erase all binder codomain-sort annotations, hereditarily (including
inside `fvar` type annotations, so that twins survive binder opening).
A *raw* tree — what the refactored kernel stores and computes with — is
a fixed point of this map; an annotation witness for a raw tree `e` is
an annotated twin `ê` with `ê.eraseCod = e`. -/
def Expr.eraseCod : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n ty.eraseCod
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.eraseCod a.eraseCod
  | .lam n ty b m => .lam n ty.eraseCod b.eraseCod m.eraseCod
  | .forallE n ty b m => .forallE n ty.eraseCod b.eraseCod m.eraseCod
  | .letE n ty v b => .letE n ty.eraseCod v.eraseCod b.eraseCod
  | .lit l => .lit l
  | .proj s i e => .proj s i e.eraseCod

def ConstantVal.eraseCod (cv : ConstantVal) : ConstantVal :=
  { cv with type := cv.type.eraseCod }

def RecRuleFire.eraseCod : RecRuleFire → RecRuleFire
  | .nested lvls pins => .nested lvls (pins.map Expr.eraseCod)
  | f => f

def RecRule.eraseCod (r : RecRule) : RecRule :=
  { r with fire := r.fire.eraseCod, rhs := r.rhs.eraseCod }

def ProjEntry.eraseCod (p : ProjEntry) : ProjEntry :=
  { p with ty := p.ty.eraseCod }

def ConstantInfo.eraseCod : ConstantInfo → ConstantInfo
  | .axiomInfo cv => .axiomInfo cv.eraseCod
  | .defnInfo cv v h => .defnInfo cv.eraseCod v.eraseCod h
  | .thmInfo cv v => .thmInfo cv.eraseCod v.eraseCod
  | .indInfo cv caps => .indInfo cv.eraseCod caps
  | .ctorInfo cv nP nF => .ctorInfo cv.eraseCod nP nF
  | .recInfo cv mI rP rules => .recInfo cv.eraseCod mI rP (rules.map RecRule.eraseCod)
  | .projInfo e => .projInfo e.eraseCod

/-- Erase a whole stored environment (the shadow env's projection back
to what the refactored kernel actually stores). -/
def Env.eraseCod (env : Env) : Env := ⟨env.consts.map ConstantInfo.eraseCod⟩

/-! ## Erasure congruences (the seam library) -/

theorem ConstantInfo.name_eraseCod (ci : ConstantInfo) : ci.eraseCod.name = ci.name := by
  cases ci <;> rfl

theorem Env.find?_eraseCod (env : Env) (n : Name) :
    env.eraseCod.find? n = (env.find? n).map ConstantInfo.eraseCod := by
  show (env.consts.map ConstantInfo.eraseCod).find? _ = _
  have hp : ((fun x : ConstantInfo => x.name == n) ∘ ConstantInfo.eraseCod) =
      (fun x : ConstantInfo => x.name == n) := by
    funext ci
    simp [Function.comp, ConstantInfo.name_eraseCod]
  rw [Env.find?, List.find?_map, hp]

/-- Erasure commutes with binder-body opening: the danger zone of any
position-based annotation oracle (substitution moves positions) is a
one-line structural fact in the erasure view.  The `forallE`/`lam`
cases are the ∀-clause of the port. -/
theorem Expr.eraseCod_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).eraseCod = e.eraseCod.instantiate1 v.eraseCod d
  | .bvar i, d => by
    simp only [Expr.instantiate1, Expr.eraseCod]
    by_cases h1 : i = d
    · simp [h1]
    · by_cases h2 : i > d <;> simp [h1, h2, Expr.eraseCod]
  | .fvar idx n ty, d => by simp [Expr.instantiate1, Expr.eraseCod]
  | .sort u, d => by simp [Expr.instantiate1, Expr.eraseCod]
  | .const n us, d => by simp [Expr.instantiate1, Expr.eraseCod]
  | .app f a, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v f d,
      Expr.eraseCod_instantiate1 v a d]
  | .lam n ty b m, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v b (d + 1)]
  | .forallE n ty b m, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v b (d + 1)]
  | .letE n ty vl b, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v vl d, Expr.eraseCod_instantiate1 v b (d + 1)]
  | .lit l, d => by simp [Expr.instantiate1, Expr.eraseCod]
  | .proj s i e, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v e d]

/-- `hasFvar` is erasure-invariant (a raw-side input-closedness
certificate transfers to the witness). -/
theorem Expr.hasFvar_eraseCod : ∀ e : Expr, e.eraseCod.hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const .. | .lit _ => rfl
  | .fvar idx n ty => rfl
  | .app f a => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod f, Expr.hasFvar_eraseCod a]
  | .lam n ty b m => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty, Expr.hasFvar_eraseCod b]
  | .forallE n ty b m => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty, Expr.hasFvar_eraseCod b]
  | .letE n ty v b => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty,
      Expr.hasFvar_eraseCod v, Expr.hasFvar_eraseCod b]
  | .proj s i e => by simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod e]

/-- `looseBVarsBounded` is erasure-invariant. -/
theorem Expr.looseBVarsBounded_eraseCod :
    ∀ (e : Expr) (k : Nat), e.eraseCod.looseBVarsBounded k = e.looseBVarsBounded k
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl
  | .fvar idx n ty, k => rfl
  | .app f a, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod f k,
      Expr.looseBVarsBounded_eraseCod a k]
  | .lam n ty b m, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .forallE n ty b m, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .letE n ty v b, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod v k, Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .proj s i e, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod e k]

/-- `constsResolve` is erasure-invariant on both the expression and the
environment (it reads only lookup success, which erasure preserves). -/
theorem Expr.constsResolve_eraseCod (env : Env) :
    ∀ e : Expr, e.eraseCod.constsResolve env.eraseCod = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .lit (.strVal _) => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .const n us => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .fvar idx n ty => by
    simpa [Expr.eraseCod, Expr.constsResolve] using
      Expr.constsResolve_eraseCod env ty
  | .app f a => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env f,
      Expr.constsResolve_eraseCod env a]
  | .lam n ty b m => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env b]
  | .forallE n ty b m => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env b]
  | .letE n ty v b => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env v, Expr.constsResolve_eraseCod env b]
  | .proj s i e => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map, Expr.constsResolve_eraseCod env e]

/-! ## The witness-shaped environment model -/

/-- A model of a *raw* environment: an annotated shadow environment
`aenv` (the per-declaration annotation witnesses, packaged coherently)
that erases to it, together with the unchanged `EnvModel` of the
shadow.  All existing model clauses — `mem_type`, `defn_eq`,
`annot_ok`, `rec_rules`, … — are consumed through `model` verbatim;
`erase_eq` is the one new proof obligation per install step. -/
structure RawEnvModel (V : Type u) [SetTheory V] (env : Env) where
  /-- The annotated shadow environment (the witness). -/
  aenv : Env
  /-- The witness erases to what the kernel stores. -/
  erase_eq : aenv.eraseCod = env
  /-- The unchanged model, over the shadow. -/
  model : EnvModel V aenv

/-! ## Representative proof 1 (interp side): twin transport across beta

The raw checker beta-reduces `(fun x : tyR => bR) aR` to
`bR.instantiate1 aR` without ever seeing an annotation.  On the proof
side, any twin of the redex decomposes structurally (erasure is
constructor-wise), its own beta reduct is a twin of the raw reduct
(`eraseCod_instantiate1`), and the *existing* substitution lemma
`interp_beta` applies to the twin verbatim.  This is the shape every
reduction-simulation case takes under the witness design. -/

/-- Twin transport across a raw beta step. -/
theorem interp_twin_beta {t : Expr} {n : Name} {tyR bR aR : Expr} {mR : BinderMeta}
    {d : Nat} {ρ : Nat → V}
    (htwin : t.eraseCod = .app (.lam n tyR bR mR) aR) :
    ∃ ty b m a, t = .app (.lam n ty b m) a ∧
      ty.eraseCod = tyR ∧ b.eraseCod = bR ∧ a.eraseCod = aR ∧
      -- the twin's beta reduct is a twin of the raw beta reduct …
      (b.instantiate1 a).eraseCod = bR.instantiate1 aR ∧
      -- … and the existing `interp_beta` applies to it unchanged
      ∀ {va : V}, Expr.fvarsBelow d b → Expr.WScoped d a →
        a.looseBVarsBounded 0 = true →
        interpExpr V cval env φ d ρ a = some va →
        interpExpr V cval env φ d ρ (b.instantiate1 a) =
          interpExpr V cval env φ (d + 1) (updV V ρ d va)
            (b.instantiate1 (.fvar d n ty)) := by
  cases t with
  | app f a' =>
    rw [show (Expr.app f a').eraseCod = .app f.eraseCod a'.eraseCod from rfl] at htwin
    injection htwin with hf ha
    cases f with
    | lam n' ty b m =>
      rw [show (Expr.lam n' ty b m).eraseCod =
        .lam n' ty.eraseCod b.eraseCod m.eraseCod from rfl] at hf
      injection hf with hn hty hb hm
      subst hn
      refine ⟨ty, b, m, a', rfl, hty, hb, ha, ?_, ?_⟩
      · rw [Expr.eraseCod_instantiate1, hb, ha]
      · intro va hfb hwa hba hai
        exact interp_beta hfb hwa hba hai 0
    | bvar i => exact absurd hf (by simp [Expr.eraseCod])
    | fvar idx nm ty => exact absurd hf (by simp [Expr.eraseCod])
    | sort u => exact absurd hf (by simp [Expr.eraseCod])
    | const nm us => exact absurd hf (by simp [Expr.eraseCod])
    | app g b => exact absurd hf (by simp [Expr.eraseCod])
    | forallE nm ty b m => exact absurd hf (by simp [Expr.eraseCod])
    | letE nm ty v b => exact absurd hf (by simp [Expr.eraseCod])
    | lit l => exact absurd hf (by simp [Expr.eraseCod])
    | proj s i e => exact absurd hf (by simp [Expr.eraseCod])
  | bvar i => exact absurd htwin (by simp [Expr.eraseCod])
  | fvar idx nm ty => exact absurd htwin (by simp [Expr.eraseCod])
  | sort u => exact absurd htwin (by simp [Expr.eraseCod])
  | const nm us => exact absurd htwin (by simp [Expr.eraseCod])
  | lam nm ty b m => exact absurd htwin (by simp [Expr.eraseCod])
  | forallE nm ty b m => exact absurd htwin (by simp [Expr.eraseCod])
  | letE nm ty v b => exact absurd htwin (by simp [Expr.eraseCod])
  | lit l => exact absurd htwin (by simp [Expr.eraseCod])
  | proj s i e => exact absurd htwin (by simp [Expr.eraseCod])

/-! ## Representative proof 2 (extend side): raw constant install

The witness-shaped restatement of the simplest constant-install
extension (`extend_model`, specialized to a plain definition whose name
touches no pinned machinery).  The split of hypotheses is the design's
claim in miniature:

* **raw side** (what the refactored kernel certifies at install):
  freshness, `hasFvar`, `constsResolve`, `looseBVarsBounded` — all on
  the stored raw trees, transferred across erasure by the congruence
  library;
* **witness side** (what the retargeted annotation certs deliver):
  the annotated twins, their `AnnotOk`, their interpretations, and
  `allLevelParamsDefined` — the latter deliberately, because annotation
  levels contribute parameters, so it is *not* raw-derivable.

The conclusion stores the **raw** trees and extends the shadow with the
twins; every `EnvModel` clause rides `extend_model` unchanged. -/
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
    -- name-only side conditions (spike scope: a plain definition)
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
  obtain ⟨aenv, herase, m⟩ := M
  -- the seam: transfer the raw-side certificates onto the shadow
  have hconsts : aenv.consts.map ConstantInfo.eraseCod = envR.consts := by
    simpa [Env.eraseCod] using congrArg Env.consts herase
  have hfindA : aenv.find? name = none := by
    have h := Env.find?_eraseCod aenv name
    rw [herase, hfindR] at h
    cases hh : aenv.find? name with
    | none => rfl
    | some ci => rw [hh] at h; simp at h
  have htf : type.hasFvar = false := by
    rw [← htw, Expr.hasFvar_eraseCod] at htfR; exact htfR
  have hvf : value.hasFvar = false := by
    rw [← hvw, Expr.hasFvar_eraseCod] at hvfR; exact hvfR
  have htb : type.looseBVarsBounded 0 = true := by
    rw [← htw, Expr.looseBVarsBounded_eraseCod] at htbR; exact htbR
  have hvb : value.looseBVarsBounded 0 = true := by
    rw [← hvw, Expr.looseBVarsBounded_eraseCod] at hvbR; exact hvbR
  have htr : type.constsResolve aenv = true := by
    rw [← htw, ← herase, Expr.constsResolve_eraseCod] at htrR; exact htrR
  have hvr : value.constsResolve aenv = true := by
    rw [← hvw, ← herase, Expr.constsResolve_eraseCod] at hvrR; exact hvrR
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
  refine ⟨⟨⟨ConstantInfo.defnInfo ⟨name, lps, type⟩ value hint :: aenv.consts⟩, ?_, m'⟩⟩
  simp [Env.eraseCod, ConstantInfo.eraseCod, ConstantVal.eraseCod, htw, hvw, hconsts]

end Setlec
