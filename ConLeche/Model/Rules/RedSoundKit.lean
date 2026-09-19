module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.BitClosed
public import ConLeche.Model.Annot.BitInstall
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.InstLevels
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.StrLit

public section

/-!
# The reduction lane's transplanted kit (task #305, lane S-red)

The rules tier may not import `Model/Steps/*` (the proof-term pin turns
such an import into a door, and the deletion lane removes those files
altogether), so the semantic facts the reduction rules' soundness needs
are **transplanted** here, argument for argument, from the rows the
DESIGN record names.  Nothing in this file mentions a run.

Sections, in the order the rules consume them:

* the level crossing and the assignment-independent literal slots
  (`Model/Steps/BitLevels.lean`'s `acval_*`/`denotePInstLevels`, renamed
  so that the two spellings can coexist while `Model/Steps` lives);
* the two `Nat` constructor readings (`Steps/DefEq.lean:99`, `:119`)
  and the literal expansions' blindness (`Steps/Major.lean:66`,
  `Steps/Stuck.lean:540`);
* the δ identity (`delta_of`, `Steps/Whnf.lean:329`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The level crossing (`Steps/BitLevels.lean`, transplanted) -/

/-- A parameter-free slot is valued independently of the assignment. -/
theorem acvalIsEmpty (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval n ψ₁ = m.acval n ψ₂ := by
  refine m.acval_params n ci hf ψ₁ ψ₂ fun p hpm => ?_
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment. -/
theorem acvalOneParam (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval n (Level.substFn ψ₁ ci.toConstantVal.levelParams [.zero])
      = m.acval n
        (Level.substFn ψ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine m.acval_params n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p
    hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- The scalar literal-support slots, read off their shape guards. -/
theorem acvalScalar (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval nm ψ₁ = m.acval nm ψ₂ := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    rw [hx] at hfok
    exact acvalIsEmpty m hx (hshape ci hfok) _ _

/-- The two one-parameter literal-support slots. -/
theorem acvalOne (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval nm (Level.substFn ψ₁ (levelParamsAt env nm) [.zero])
      = m.acval nm
        (Level.substFn ψ₂ (levelParamsAt env nm) [.zero]) := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    have hlp : levelParamsAt env nm = ci.toConstantVal.levelParams := by
      simp [levelParamsAt, hx]
    rw [hx] at hfok
    rw [hlp]
    exact acvalOneParam m hx (hshape ci hfok) _ _

/-- The `Nat`-literal leaves are assignment-independent. -/
theorem acvalNatPair (m : EnvModel V env)
    (hg : ConLeche.natLitSupported env = true) (ψ₁ ψ₂ : Name → Nat) :
    m.acval natZeroName ψ₁ = m.acval natZeroName ψ₂ ∧
      m.acval natSuccName ψ₁ = m.acval natSuccName ψ₂ := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hz⟩, hs⟩ := hg
  refine ⟨acvalScalar m natZeroName natZeroOk hz rfl ?_ _ _,
    acvalScalar m natSuccName natSuccOk hs rfl ?_ _ _⟩
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natZeroOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natZeroOk] at h
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natSuccOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natSuccOk] at h

/-- **The level crossing for `denoteMeta`, unconditional and exact**:
reading an instantiated term at `φ` is reading the term at the
composed valuation `Level.substFn φ ks us`.  The binder step is
`pwBit_substPW` (i.e. `PropWhen.holds_substPW`); the constant step is
`EnvModel.acval_params` + `Level.substFn_map_subst`, as in the canonical
walk. -/
theorem denoteMetaInstLevels (m : EnvModel V env)
    (φ : Name → Nat) (ks : List Name) (us : List Level) :
    ∀ (d : Nat) (e : Expr),
      denoteMeta m.acval env φ d (e.instantiateLevelParams ks us)
        = denoteMeta m.acval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, Level.eval_subst]
  | case2 d idx ty =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta]
  | case3 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_pos hlen, if_pos (by simpa using hlen)]
    exact congrArg some
      (m.acval_params n ci hf _ _ fun p hp =>
        Level.substFn_map_subst hlen hp)
  | case4 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_neg hlen, if_neg (by simpa using hlen)]
  | case5 d n vs hf =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
  | case6 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case7 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case8 d fe a ihf iha =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, ihf, iha]
  | case9 d ty val body =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, ihe]
  | case11 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acvalNatPair m hsup
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acvalNatPair m h0
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have esol := acvalScalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have echar := acvalScalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have eofn := acvalScalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have enil := acvalOne m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    have econs := acvalOne m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i =>
      rw [Expr.instantiateLevelParams, denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)
/-! ## The two `Nat` constructor readings and the literal expansions -/

theorem denoteMetaNatZeroConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natZeroName [])
      = some (acval ConLeche.natZeroName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? ConLeche.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h2
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [ConLeche.natZeroOk] at h2
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

theorem denoteMetaNatSuccConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natSuccName [])
      = some (acval ConLeche.natSuccName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? ConLeche.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h3
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [ConLeche.natSuccOk] at h3
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- `denoteMeta` is blind to the `Nat`-literal constructor expansion. -/
theorem denoteMeta_natLitToConstructor
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) (d n : Nat) :
    denoteMeta acval env φ d (ConLeche.natLitToConstructor n)
      = denoteMeta acval env φ d (.lit (.natVal n)) := by
  match n with
  | 0 =>
    rw [ConLeche.natLitToConstructor, denoteMetaNatZeroConst hg,
      denoteMeta_natLit hg]
    rfl
  | k + 1 =>
    rw [ConLeche.natLitToConstructor, denoteMeta_app, denoteMetaNatSuccConst hg,
      denoteMeta_natLit hg, denoteMeta_natLit hg]
    rfl

theorem denoteMetaConstNolevels
    {acval : Name → (Name → Nat) → AnnotTerm} {c : Name}
    {ci : ConLeche.ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denoteMeta acval env φ d (.const c [])
      = some (acval c (Level.substFn φ [] [])) := by
  rw [denoteMeta_const hf (by simp [hlp]), hlp]

theorem denoteMetaNilTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listNilName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciN, p, mb, hfN, hlpN, -⟩ := listNil_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciN.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listNilName := by
    simp [levelParamsAt, hfN]
  rw [denoteMeta, denoteMeta_const hfN (by simp [hlpN]),
    denoteMetaConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteMetaConsTerm {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denoteMeta acval env φ d
        (.app (.const ConLeche.listConsName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciC', p, -, -, -, hfC', hlpC', -⟩ := listCons_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciC'.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listConsName := by
    simp [levelParamsAt, hfC']
  rw [denoteMeta, denoteMeta_const hfC' (by simp [hlpC']),
    denoteMetaConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteMetaStrLitList
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denoteMeta acval env φ d (ConLeche.strLitList cs)
        = some (charListAV
          (.app (acval ConLeche.listNilName
            (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (.app (acval ConLeche.listConsName
            (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (acval ConLeche.charOfNatName (Level.substFn φ [] []))
          (acval ConLeche.natZeroName (Level.substFn φ [] []))
          (acval ConLeche.natSuccName (Level.substFn φ [] []))
          cs) := by
  have hnat : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciF, mb, hfF, hlpF, -⟩ := charOfNat_shape hg
  intro cs
  induction cs with
  | nil =>
    rw [ConLeche.strLitList, charListAV]; exact denoteMetaNilTerm hg d
  | cons c cs ih =>
    rw [ConLeche.strLitList, charListAV, denoteMeta, denoteMeta,
      denoteMetaConsTerm hg d, denoteMeta,
      denoteMetaConstNolevels hfF hlpF d, denoteMeta_natLit hnat, ih]
    rfl

/-- `denoteMeta` is blind to the string-literal constructor expansion. -/
theorem denoteMeta_strLitToConstructor
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) (s : String) :
    denoteMeta acval env φ d (ConLeche.strLitToConstructor s)
      = denoteMeta acval env φ d (.lit (.strVal s)) := by
  obtain ⟨ciO, mb, hfO, hlpO, -⟩ := stringOfList_shape hg
  rw [ConLeche.strLitToConstructor_eq, denoteMeta,
    denoteMetaConstNolevels hfO hlpO d, denoteMetaStrLitList hg d,
    denoteMeta, if_pos hg]
  rfl


/-! ## The application congruence at the reading -/

/-- The frame of a closed atom. -/
theorem frame_atom {d : Nat} {e : Expr} (h : e.fvarLeaves = [])
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true) :
    Frame d e ∧ ∀ (x : Expr), LeavesSub e x :=
  ⟨⟨hw, hb, fun l hl => by rw [h] at hl; exact nomatch hl⟩,
   fun _ l hl => by rw [h] at hl; exact nomatch hl⟩

/-- The two components of a graded application are graded. -/
theorem graded_app {Δa : List AnnotTerm} {f x : AnnotTerm}
    (h : Graded V Δa (.app f x)) : Graded V Δa f ∧ Graded V Δa x :=
  ⟨fun σ hσ =>
      ⟨by have h1 := (h σ hσ).1; rw [WellDenoted_app] at h1; exact h1.1,
        by have h2 := (h σ hσ).2; rw [AnnotValid_app] at h2; exact h2.1⟩,
   fun σ hσ =>
      ⟨by have h1 := (h σ hσ).1; rw [WellDenoted_app] at h1; exact h1.2.1,
        by have h2 := (h σ hσ).2; rw [AnnotValid_app] at h2; exact h2.2⟩⟩


/-- An application's grading depends on its two components only through
their VALUES, so it transfers along equal-valued graded replacements
(the content `whnfCore_app_claim` (`Steps/Whnf.lean:509`) writes inline
at its head slot; stated once, for either slot). -/
theorem appCongrV {σ : Nat → V} {f a f' a' : AnnotTerm}
    (heqf : interp V σ f = interp V σ f')
    (heqa : interp V σ a = interp V σ a')
    (hgf' : WellDenotedV V σ f') (hga' : WellDenotedV V σ a')
    (h : WellDenotedV V σ (.app f a)) : WellDenotedV V σ (.app f' a') := by
  refine ⟨?_, by rw [AnnotValid_app]; exact ⟨hgf'.2, hga'.2⟩⟩
  have h1 := h.1
  rw [WellDenoted_app] at h1 ⊢
  obtain ⟨-, -, v, A, B, h2, h3, h4⟩ := h1
  exact ⟨hgf'.1, hga'.1, v, A, B, heqf ▸ h2, heqa ▸ h3, h4⟩


/-! ## `projAV`'s grading under equal-valued subjects
(`Model/Steps/ProjAVKit.lean` and `projAV_validV`, transplanted) -/

namespace ProjAV

/-- The subject of a graded projection spine is graded. -/
theorem hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (projAV i e) → WellDenoted V σ e
  | 0, e, σ, h => ((WellDenoted_fst V σ e) ▸ h).1
  | i + 1, e, σ, h =>
    ((WellDenoted_snd V σ e) ▸ (hoist (i := i) (e := .snd e) h)).1

/-- The subject of a bit-valid projection spine is bit-valid. -/
theorem validHoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ (projAV i e) → AnnotValid V σ e
  | 0, e, σ, h => (AnnotValid_fst V σ e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValid_snd V σ e) ▸ (validHoist (i := i) (e := .snd e) h)

/-- The uniform projection spelling is bit-valid whenever its subject
is (`projAV_validV`, `Model/Inductives/StructIntro.lean:90`). -/
theorem validV :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ e → AnnotValid V σ (projAV i e)
  | 0, e, σ, h => by
    show AnnotValid V σ (.fst e)
    rw [AnnotValid_fst]
    exact h
  | i + 1, e, σ, h => by
    show AnnotValid V σ (projAV i (.snd e))
    exact validV (by rw [AnnotValid_snd]; exact h)

/-- **`projAV`'s truthfulness transfers to an equal-valued graded
subject.** -/
theorem congr :
    ∀ {i : Nat} {e e' : AnnotTerm} {σ : Nat → V},
      interp V σ e = interp V σ e' → WellDenoted V σ e' →
      WellDenoted V σ (projAV i e) → WellDenoted V σ (projAV i e')
  | 0, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (.fst e')
    have h : WellDenoted V σ (.fst e) := hok
    rw [WellDenoted_fst] at h ⊢
    obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := h
    exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩
  | i + 1, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (projAV i (.snd e'))
    have hok1 : WellDenoted V σ (.snd e) :=
      hoist (i := i) (e := .snd e) hok
    refine congr (i := i) (e := .snd e) (e' := .snd e') ?_ ?_ hok
    · simp only [interp_snd, heq]
    · rw [WellDenoted_snd] at hok1 ⊢
      obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := hok1
      exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩

/-- `WellDenotedV` form of the congruence. -/
theorem congrV {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') (hok' : WellDenotedV V σ e')
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ (projAV i e') :=
  ⟨congr heq hok'.1 hok.1, validV hok'.2⟩

/-- `WellDenotedV` of the subject, off the spine's. -/
theorem hoistV {i : Nat} {e : AnnotTerm} {σ : Nat → V}
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ e :=
  ⟨hoist hok.1, validHoist hok.2⟩

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp_congr {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') :
    interp V σ (projAV i e) = interp V σ (projAV i e') := by
  rw [projAV_interp, projAV_interp, heq]

end ProjAV


/-! ## The δ identity (`delta_of`, `Steps/Whnf.lean:329`, transplanted) -/

/-- The instantiated form of `DefnReads`, by the level crossing
(`acvalDefnInst_subst`, `Steps/Whnf.lean:277`). -/
theorem denoteMetaDefnInst {m : EnvModel V env} (hdi : DefnReads m)
    (φ : Name → Nat) {cv : ConstantVal} {value : Expr} {us : List Level}
    (hmem : ∃ hint : ConLeche.ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) :
    denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval cv.name (Level.substFn φ cv.levelParams us)) := by
  rw [denoteMetaInstLevels m φ cv.levelParams us 0 value]
  exact hdi _ cv value hmem

/-- `delta_core` (`Steps/Whnf.lean:289`), transplanted. -/
private theorem deltaCore (m : EnvModel V env)
    {d : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea : AnnotTerm}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval ci.name (Level.substFn φ cv.levelParams us)))
    (hea : denoteMeta m.acval env φ d e = some ea) :
    denoteMeta m.acval env φ d
        (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs) = some ea := by
  obtain rfl : ci.name = n := by
    rw [ConLeche.Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    ConLeche.Expr.mkAppN_getApp e
  rw [← he] at hea
  refine denoteMeta_mkAppN_swap e.getAppArgs ?_ hea
  intro fa hfa
  rw [hfn, denoteMeta, hfind] at hfa
  simp only [hcvt] at hfa
  rw [if_pos hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  exact denoteMeta_depth_of_closed m.acval_closed
    (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hnofv)
    (fun k => m.acval_closed _ _ k) hval d

/-- **The δ step is invisible to the reading** (`delta_of`,
`Steps/Whnf.lean:329`): the unfolding has the subject's own
annotation. -/
theorem denoteMeta_unfoldDefinition {m : EnvModel V env} (hdi : DefnReads m)
    {d : Nat} {e e' : Expr} {ea : AnnotTerm}
    (hud : ConLeche.unfoldDefinition env e = some e')
    (hea : denoteMeta m.acval env φ d e = some ea) :
    denoteMeta m.acval env φ d e' = some ea := by
  rw [ConLeche.unfoldDefinition] at hud
  split at hud
  · next n us hfn =>
    split at hud
    · next cv value hint hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact deltaCore m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ :=
                m.wf _ (ConLeche.find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (denoteMetaDefnInst hdi φ ⟨hint, ConLeche.find?_mem hfind⟩) hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud


end ConLeche.Model.Rules
