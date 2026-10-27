module

public import ConLeche.Model.Modular.Scope
public import ConLeche.Model.Fold
public import ConLeche.Verify.Denote.Agree
public import ConLeche.Verify.EnvBound
import ConLeche.Model.Env.CanonCrest

public section

/-!
# A context's model, read from its sources' models

The first step of the modular theorem (`ConLeche/Modular.lean`): a
module's context is an environment each of whose constants is read from
an earlier module's own environment — its **source**, which has a model.
`CtxSrc` is what the local checks give about that, stated without
modules: per stored name `n`, the source environment `E n` with its
model `m n`, and the part `R n` of it the context reads as the source
does (stored in both, resolved alike, so with one leaf); the context's
constant refines the source's, and what its laws read lies in `R n`.
`ctxModel` builds the context's model at the leaves `aC`, every law of a
context constant read off its source's law.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Semantics ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

universe w

/-- An inductive type former, constructor or recursor: the kinds no
context presents as an assumption. -/
@[expose] def _root_.ConLeche.ConstantInfo.isIndKind : ConstantInfo → Bool
  | .indInfo .. | .ctorInfo .. | .recInfo .. => true
  | _ => false

/-- An inductive type former. -/
@[expose] def _root_.ConLeche.ConstantInfo.isFormer : ConstantInfo → Bool
  | .indInfo .. => true
  | _ => false

/-- **A constructor's result family is a type former** of the environment. -/
@[expose] def CtorFam (E : Env) : Prop :=
  ∀ x cv nP nF, E.find? x = some (.ctorInfo cv nP nF) → ∀ T us,
    cv.type.piResult.getAppFn = .const T us → ∃ cvT capsT, E.find? T = some (.indInfo cvT capsT)

/-- A type former of `C`. -/
@[expose] def FormerIn (C : Env) (n : Name) : Prop := ∃ cv caps, C.find? n = some (.indInfo cv caps)

/-- **A context, read from its sources** (see the module docstring). -/
structure CtxSrc (V : Type w) [SetTheory V] (μ : CheckMode) (C : Env)
    (aC : Name → (Name → Nat) → Term) where
  /-- the source environment of each name -/
  E : Name → Env
  /-- its model -/
  m : (n : Name) → EnvModelM V μ (E n)
  /-- the part of it the context reads as the source does -/
  R : Name → Env
  R_sub : ∀ n d ci, (R n).find? d = some ci → (E n).find? d = some ci ∧ (C.find? d).isSome = true
  agree : ∀ n, (C.find? n).isSome = true → ReadAgree (R n) C (E n) aC (m n).base2.acval
  entry : ∀ n ci, C.find? n = some ci → ∃ ci', (E n).find? n = some ci' ∧ Refines n ci ci'
  self : ∀ n, (C.find? n).isSome = true → ((R n).find? n).isSome = true
  scope : ∀ n ci, C.find? n = some ci → EntryScoped (R n) C n ci
  /-- a name read alike is stored alike where the context stores an
  inductive kind, the source a constructor or recursor, or it is pinned -/
  same : ∀ n d, ((R n).find? d).isSome = true →
    (((∃ ci, C.find? d = some ci ∧ ci.isIndKind = true) ∧
      ∃ ci, (E n).find? d = some ci ∧ ci.isIndKind = true) ∨ d ∈ pinnedNames) →
    C.find? d = (E n).find? d
  /-- in a source, a constructor's result family is a type former -/
  ctorFam : ∀ n, CtorFam (E n)
  /-- what an inductive kind read alike reads is read alike, where it is stored -/
  deep : ∀ n c ci, ((R n).find? c).isSome = true → C.find? c = some ci → ci.isIndKind = true →
    EntryScopedP (fun d => (C.find? d).isSome = true → ((E n).find? d).isSome = true →
      ((R n).find? d).isSome = true) C c ci
  cover : ∀ n, LfpCover (m n) []
  eta : ∀ n, ConLeche.EtaFamiliesClosed (E n)
  tables : ∀ T ci, C.find? T = some ci → C.findTable? T =
    match ci with
    | .indInfo .. => (E T).findTable? T
    | _ => none
  projs : ∀ n ci, C.find? n = some ci → EntryProjs C n ci
  blocks : ∀ n ci, C.find? n = some ci → BlockIn C n ci
  tables_mem : ∀ t ∈ C.tables, C.findTable? t.structName = some t
  nodup : NodupNames C
  closed : ∀ n ψ, Term.Closed (aC n ψ)
  wd : ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (aC n ψ)

variable {V : Type w} [SetTheory V] {μ : CheckMode} {C : Env}
  {aC : Name → (Name → Nat) → Term}

/-! ## Refinement -/

theorem _root_.ConLeche.Modular.Refines.cv {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci') :
    ci.toConstantVal = ci'.toConstantVal := by
  rcases h with rfl | ⟨-, rfl⟩ <;> rfl

theorem _root_.ConLeche.Modular.Refines.eq_of_not_axiom {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hn : ∀ cv, ci ≠ .axiomInfo cv) : ci = ci' := by
  rcases h with h | ⟨-, rfl⟩
  · exact h
  · exact absurd rfl (hn _)

theorem _root_.ConLeche.Modular.Refines.eq_of_indKind {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hk : ci.isIndKind = true) : ci = ci' :=
  h.eq_of_not_axiom fun _ he => by rw [he] at hk; simp [ConstantInfo.isIndKind] at hk

theorem _root_.ConLeche.Modular.Refines.eq_of_pinned {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hp : n ∈ pinnedNames) : ci = ci' := by
  rcases h with h | ⟨hn, -⟩
  · exact h
  · exact absurd hp hn

theorem _root_.ConLeche.Modular.Refines.trans {n : Name} {a b c : ConstantInfo}
    (h₁ : Refines n a b) (h₂ : Refines n b c) : Refines n a c := by
  rcases h₁ with rfl | ⟨hn, rfl⟩
  · exact h₂
  · exact Or.inr ⟨hn, by rw [h₂.cv]⟩

theorem _root_.ConLeche.Modular.Refines.refl (n : Name) (ci : ConstantInfo) : Refines n ci ci := Or.inl rfl

/-! ## Lookups -/

/-- A stored constant of a name-unique environment is its name's lookup. -/
theorem find?_of_mem {env : Env} (hnd : NodupNames env) {c : ConstantInfo}
    (hc : c ∈ env.consts) : env.find? c.name = some c := by
  unfold NodupNames at hnd
  unfold Env.find?
  obtain ⟨cs⟩ := env
  simp only at hc hnd ⊢
  induction cs with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hc'
    · simp
    · have hne : x.name ≠ c.name := fun h =>
        hnd.1 (h ▸ List.mem_map_of_mem hc')
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 hc'


/-! ## Projections of formers, kept by the term operations -/

theorem projsFormer_instantiate1_any {E : Env} {a : Expr}
    (ha : Expr.projsFormer E a = true) :
    ∀ (e : Expr) (k : Nat), Expr.projsFormer E e = true →
      Expr.projsFormer E (e.instantiate1 a k) = true := by
  intro e
  induction e <;> intro k h <;> simp_all [ConLeche.Expr.instantiate1, Expr.projsFormer]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [Expr.projsFormer]

theorem projsFormer_instantiateLevelParams {E : Env} (ks : List Name) (us : List Level) :
    ∀ (e : Expr), Expr.projsFormer E (e.instantiateLevelParams ks us) = Expr.projsFormer E e := by
  intro e
  induction e <;> simp_all [ConLeche.Expr.instantiateLevelParams, Expr.projsFormer]

theorem projsFormer_projTele {E : Env} :
    ∀ (k : Nat) (body : Expr), Expr.projsFormer E (ConLeche.projTele k body) = Expr.projsFormer E body
  | 0, _ => rfl
  | k + 1, body => by
    simp [ConLeche.projTele, Expr.projsFormer, projsFormer_projTele k body]

theorem projsFormer_openRev {E : Env} {e : Expr} (h : Expr.projsFormer E e = true) :
    ∀ d n : Nat, Expr.projsFormer E (ConLeche.Verify.openRev d n e) = true := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show Expr.projsFormer E ((ConLeche.Verify.openRev d n e).instantiate1 (.fvar (d + n) (.sort .zero)) 0)
      = true
    exact projsFormer_instantiate1_any (by simp [Expr.projsFormer]) _ 0 ih

theorem projsFormer_instPisWith {E : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, Expr.projsFormer E a = true) →
      Expr.projsFormer E e = true → ConLeche.instPisWith as e = some r →
      Expr.projsFormer E r = true
  | [], e, r, _, he, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b, h =>
      have h' : ConLeche.instPisWith as (b.instantiate1 a) = some r := h
      simp only [Expr.projsFormer, Bool.and_eq_true] at he
      exact projsFormer_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (projsFormer_instantiate1_any (has a List.mem_cons_self) b 0 he.2) h'

theorem projsFormer_replaceApps {E : Env} {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us e, f c us = some e → Expr.projsFormer E e = true) :
    ∀ (e : Expr), Expr.projsFormer E e = true →
      Expr.projsFormer E (e.replaceApps f b n) = true := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceApps, Expr.projsFormer]
  | fvar i ty ih => intro h; simpa [ConLeche.Expr.replaceApps] using h
  | sort u => intro _; simp [ConLeche.Expr.replaceApps, Expr.projsFormer]
  | const c us =>
    intro h
    rw [ConLeche.Expr.replaceApps_const]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · exact h
  | lit l => intro h; simpa [ConLeche.Expr.replaceApps] using h
  | app a x iha ihx =>
    intro h
    rw [ConLeche.Expr.replaceApps_app]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := ConLeche.Expr.appHole?_some hr
      exact hf _ _ _ hc
    · simp only [Expr.projsFormer, Bool.and_eq_true] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, Expr.projsFormer, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, Expr.projsFormer, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceApps, Expr.projsFormer, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceApps, Expr.projsFormer, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

theorem projsFormer_canonOf {E : Env} {ty A : Expr} (he : Expr.projsFormer E ty = true)
    (hA : CanonOf ty A) : Expr.projsFormer E A = true := by
  have hp : ∀ n, ∀ x ∈ canonParams n, Expr.projsFormer E x = true := fun _ x hx => by
    obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp [Expr.projsFormer]
  rcases hA with ⟨names, us, n, hA⟩ | ⟨n, hA⟩
  · unfold ConLeche.nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    refine projsFormer_replaceApps (fun c us' r hr => ?_) _ (projsFormer_instPisWith (hp _) he ht)
    obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
    simp [Expr.projsFormer]
  · exact projsFormer_instPisWith (hp _) he hA

/-- A fragment term has no projections. -/
theorem projsFormer_of_natFragOk {E E' : Env} {c : Name} :
    ∀ {e : Expr}, ConLeche.Verify.natFragOk E' c e = true → Expr.projsFormer E e = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | fvar idx ty =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true, beq_iff_eq] at h
    simp [Expr.projsFormer, h.2]
  | proj _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | lam _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | forallE _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | letE _ _ _ => intro h; simp [ConLeche.Verify.natFragOk] at h
  | _ => intro _; simp [Expr.projsFormer]

namespace CtxSrc

variable (S : CtxSrc V μ C aC)

theorem storedC {n d : Name} (h : ((S.R n).find? d).isSome = true) : (C.find? d).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  exact (S.R_sub n d ci hci).2

theorem storedE {n d : Name} (h : ((S.R n).find? d).isSome = true) :
    ((S.E n).find? d).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  rw [(S.R_sub n d ci hci).1]; rfl

/-- A name read alike has one leaf. -/
theorem leaf {n d : Name} (hn : (C.find? n).isSome = true)
    (h : ((S.R n).find? d).isSome = true) : aC d = (S.m n).base2.acval d := by
  obtain ⟨-, -, -, -, -, hl⟩ := (S.agree n hn).find d h (S.storedE h)
  exact hl

/-- An expression read alike reads alike. -/
theorem denote_eq {n : Name} (hn : (C.find? n).isSome = true) {e : Expr}
    (hR : e.constsResolve (S.R n) = true) (hE : e.constsResolve (S.E n) = true)
    (hP : Expr.projsFormer C e = true) (hQ : Expr.projsFormer (S.E n) e = true)
    (ψ : Name → Nat) (d : Nat) :
    denote aC C ψ d e = denote (S.m n).base2.acval (S.E n) ψ d e :=
  denote_agree (S.agree n hn) d e hR hE hP hQ

/-- The source's reading names projections of its formers only. -/
theorem projsE {n : Name} {e : Expr} {ψ : Name → Nat} {d : Nat} {t : Term}
    (h : denote (S.m n).base2.acval (S.E n) ψ d e = some t) :
    Expr.projsFormer (S.E n) e = true :=
  projsFormer_of_denote (S.m n).base2.proj_ok d e h

/-- A source constant's type names projections of its formers only. -/
theorem typeE_projs {n d : Name} {ci : ConstantInfo} (hf : (S.E n).find? d = some ci) :
    Expr.projsFormer (S.E n) ci.toConstantVal.type = true := by
  obtain ⟨ta, hta⟩ := (S.m n).type_reads ci (ConLeche.Env.find?_mem hf) (fun _ => 0)
  exact S.projsE hta

/-- A resolution in the context, from one in the part read alike. -/
theorem resolveC {n : Name} {e : Expr} (hR : e.constsResolve (S.R n) = true) :
    e.constsResolve C = true :=
  Expr.constsResolve_of_find (fun _ h => S.storedC h) hR

/-- A resolution in the source, from one in the part read alike. -/
theorem resolveE {n : Name} {e : Expr} (hR : e.constsResolve (S.R n) = true) :
    e.constsResolve (S.E n) = true :=
  Expr.constsResolve_of_find (fun _ h => S.storedE h) hR

/-- The context's constant and its source's, with the source's
well-formedness. -/
theorem src_entry {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ∃ ci', (S.E n).find? n = some ci' ∧ Refines n ci ci' ∧
      ConLeche.ConstWF (S.E n) ci' := by
  obtain ⟨ci', hf', hr⟩ := S.entry n ci hf
  exact ⟨ci', hf', hr, (S.m n).base2.wf.consts _ (ConLeche.Env.find?_mem hf')⟩

/-- **A stored type reads as its source's.** -/
theorem type_eq {n : Name} {ci ci' : ConstantInfo} (hf : C.find? n = some ci)
    (hf' : (S.E n).find? n = some ci') (hr : Refines n ci ci')
    (ψ : Name → Nat) (d : Nat) (us : List Level) (ks : List Name) :
    denote aC C ψ d (ci.toConstantVal.type.instantiateLevelParams ks us)
      = denote (S.m n).base2.acval (S.E n) ψ d
          (ci'.toConstantVal.type.instantiateLevelParams ks us) := by
  have hn : (C.find? n).isSome = true := by rw [hf]; rfl
  have hwf := (S.m n).base2.wf.consts _ (ConLeche.Env.find?_mem hf')
  rw [← hr.cv]
  refine S.denote_eq hn ?_ ?_ ?_ ?_ ψ d
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact (S.scope n ci hf).1
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams, hr.cv]; exact hwf.2.2.1
  · rw [projsFormer_instantiateLevelParams]; exact (S.projs n ci hf).1
  · rw [projsFormer_instantiateLevelParams, hr.cv]; exact S.typeE_projs hf'

end CtxSrc

theorem _root_.ConLeche.NestedRead.mono_resolves {p q : Expr → Bool} {lps : List Name}
    {tyA : Expr} {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr}
    (h : ConLeche.NestedRead p lps tyA mI rP cnP lvls pins)
    (hq : ∀ pin ∈ pins, q pin = true) : ConLeche.NestedRead q lps tyA mI rP cnP lvls pins := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun pin hp => ⟨(h3 pin hp).1, (h3 pin hp).2.1, hq pin hp, (h3 pin hp).2.2.2⟩, h4⟩

/-- A pinned name: a reserved basis name is one. -/
theorem mem_pinned_of_reserved {n : Name} (h : reservedBasisNames.contains n = true) :
    n ∈ pinnedNames := by
  unfold pinnedNames
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.contains_iff_mem.mp h)))

/-- **The rule bits cross a lookup that agrees at the constructor and,
where the source stores it, at its result family.** -/
theorem recRuleKOf_of {f g : Name → Option ConstantInfo} {ctor : Name}
    (hc : f ctor = g ctor)
    (hT : ∀ cvj nP nF, g ctor = some (.ctorInfo cvj nP nF) →
      ∀ T us, cvj.type.piResult.getAppFn = .const T us →
        ∀ cvT caps, g T = some (.indInfo cvT caps) → f T = g T)
    (h : ConLeche.recRuleKOf g ctor = true) : ConLeche.recRuleKOf f ctor = true := by
  unfold ConLeche.recRuleKOf at h ⊢
  rw [hc]
  match hg : g ctor, h with
  | some (.ctorInfo cvj nP nF), h =>
    dsimp only at h ⊢
    match hh : cvj.type.piResult.getAppFn, h with
    | .const T us, h =>
      dsimp only at h ⊢
      match hgT : g T, h with
      | some (.indInfo cvT caps), h =>
        rw [hT cvj nP nF hg T us hh cvT caps hgT, hgT]; exact h

theorem recRuleEtaOf_of {f g : Name → Option ConstantInfo} {ctor : Name}
    (hc : f ctor = g ctor)
    (hT : ∀ cvj nP nF, g ctor = some (.ctorInfo cvj nP nF) →
      ∀ T us, cvj.type.piResult.getAppFn = .const T us →
        ∀ cvT caps, g T = some (.indInfo cvT caps) → f T = g T)
    (h : ConLeche.recRuleEtaOf g ctor = true) : ConLeche.recRuleEtaOf f ctor = true := by
  unfold ConLeche.recRuleEtaOf at h ⊢
  rw [hc]
  match hg : g ctor, h with
  | some (.ctorInfo cvj nP nF), h =>
    dsimp only at h ⊢
    match hh : cvj.type.piResult.getAppFn, h with
    | .const T us, h =>
      dsimp only at h ⊢
      match hgT : g T, h with
      | some (.indInfo cvT caps), h =>
        rw [hT cvj nP nF hg T us hh cvT caps hgT, hgT]; exact h


/-- **The `Nat`-op guard reads the `Nat` basis and the dependencies'
lookups, and the `Bool` constructors' values.** -/
theorem natOpGuard_congr {E E' : Env} {c : Name}
    (h3 : ∀ n ∈ [natName, natZeroName, natSuccName] ++ natOpDeps c, E.find? n = E'.find? n)
    (hb : (decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true → ∀ n ∈ [boolTrueName, boolFalseName],
      (E.find? n).map (·.toConstantVal) = (E'.find? n).map (·.toConstantVal)) :
    natOpGuard E c = natOpGuard E' c := by
  have hN := h3 natName (by simp)
  have hZ := h3 natZeroName (by simp)
  have hS := h3 natSuccName (by simp)
  have hdep : ∀ n ∈ natOpDeps c, E.find? n = E'.find? n :=
    fun n hn => h3 n (List.mem_append_right _ hn)
  unfold natOpGuard natLitSupported
  rw [hN, hZ, hS]
  congr 1
  · congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun h n hn => by rw [← hdep n hn]; exact h n hn,
      fun h n hn => by rw [hdep n hn]; exact h n hn⟩
  · split
    · rename_i hcond
      have hT := hb hcond boolTrueName (by simp)
      have hF := hb hcond boolFalseName (by simp)
      cases hE1 : E.find? boolTrueName <;> cases hE1' : E'.find? boolTrueName <;>
        rw [hE1, hE1'] at hT <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at hT <;>
      cases hE2 : E.find? boolFalseName <;> cases hE2' : E'.find? boolFalseName <;>
        rw [hE2, hE2'] at hF <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at hF <;> simp only [hT, hF]
    · rfl

/-- `natOpTyPinned` reads `Bool`'s value only. -/
theorem natOpTyPinned_congr {E E' : Env} {c : Name} {ty : Expr}
    (hb : (decide (c = natBeqName) || decide (c = natBleName)) = true →
      (E.find? boolName).map (·.toConstantVal) = (E'.find? boolName).map (·.toConstantVal)) :
    ConLeche.natOpTyPinned E c ty = ConLeche.natOpTyPinned E' c ty := by
  have hcod : ∀ e, ConLeche.natOpCod E c e = ConLeche.natOpCod E' c e := by
    intro e
    unfold ConLeche.natOpCod
    split
    · rename_i hcond
      have hb' := hb hcond
      cases hE : E.find? boolName <;> cases hE' : E'.find? boolName <;> rw [hE, hE'] at hb' <;>
        simp at hb' <;> simp [hb']
    · rfl
  unfold ConLeche.natOpTyPinned
  split
  · split <;> simp [hcod]
  · split <;> simp [hcod]

/-- A fragment term resolves wherever the operation and `Nat` are stored. -/
theorem constsResolve_of_natFragOk {E : Env} {c : Name} (hc : (E.find? c).isSome = true)
    (hnat : (E.find? natName).isSome = true) :
    ∀ {e : Expr}, ConLeche.Verify.natFragOk E c e = true → e.constsResolve E = true := by
  intro e
  induction e with
  | sort u => intro _; rfl
  | fvar idx ty =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true, beq_iff_eq] at h
    simp only [ConLeche.Expr.constsResolve, h.2]
    exact hnat
  | const n us =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    simp only [ConLeche.Expr.constsResolve]
    rcases h with ⟨rfl, -⟩ | h
    · exact hc
    · revert h; cases E.find? n <;> simp
  | app f a ihf iha =>
    intro h
    simp only [ConLeche.Verify.natFragOk, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | _ => intro h; simp [ConLeche.Verify.natFragOk] at h

namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- A stored table's structure is an inductive type former of the
context, and the table its source's. -/
theorem table_of {T : Name} {t : ConLeche.ProjTable} (ht : C.findTable? T = some t) :
    ∃ cv caps, C.find? T = some (.indInfo cv caps) ∧ (S.E T).findTable? T = some t := by
  obtain ⟨-, -, hT⟩ := ConLeche.Env.findTable?_mem ht
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
  have h := S.tables T ci hci
  rw [ht] at h
  cases ci with
  | indInfo cv caps => exact ⟨cv, caps, hci, h.symm⟩
  | _ => exact nomatch h

/-- **The context is well formed.** -/
theorem wf : ConLeche.EnvWF C := by
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · have hf := find?_of_mem S.nodup hc
    obtain ⟨ci', hf', hr, hwf'⟩ := S.src_entry hf
    have hsc := S.scope _ c hf
    obtain ⟨h1, h2, -, h4, hdef, hrec, hcaps⟩ := hwf'
    refine ⟨by rw [hr.cv]; exact h1, by rw [hr.cv]; exact h2, S.resolveC hsc.1,
      by rw [hr.cv]; exact h4, fun cv v hint he => ?_, fun cv mI rP rules he r hrr => ?_,
      fun cv caps he => ?_⟩
    · have he' : ci' = .defnInfo cv v hint :=
        (hr.eq_of_not_axiom (by rw [he]; exact fun _ h => nomatch h)).symm.trans he
      obtain ⟨a, b, -, d⟩ := hdef cv v hint he'
      exact ⟨a, b, S.resolveC (hsc.2.1 cv v hint he), d⟩
    · have he' : ci' = .recInfo cv mI rP rules :=
        (hr.eq_of_indKind (by rw [he]; rfl)).symm.trans he
      obtain ⟨a, b, -, d, e⟩ := hrec cv mI rP rules he' r hrr
      obtain ⟨hrh, -, hpins⟩ := hsc.2.2.1 cv mI rP rules he r hrr
      exact ⟨a, b, S.resolveC hrh, d, fun lvls pins hn =>
        (e lvls pins hn).mono_resolves fun pin hp => S.resolveC (hpins lvls pins hn pin hp)⟩
    · have he' : ci' = .indInfo cv caps :=
        (hr.eq_of_indKind (by rw [he]; rfl)).symm.trans he
      exact hcaps cv caps he'
  · have hft := S.tables_mem t ht
    obtain ⟨-, -, hT⟩ := ConLeche.Env.findTable?_mem hft
    obtain ⟨cv, caps, hfT, htE⟩ := S.table_of hft
    obtain ⟨-, hsize, hbodies⟩ := (S.m t.structName).base2.wf.table htE
    refine ⟨hT, hsize, fun i b hb => ?_⟩
    obtain ⟨a, b', -, d⟩ := hbodies i b hb
    obtain ⟨-, -, -, hind, -⟩ := S.scope _ _ hfT
    obtain ⟨-, -, -, htab⟩ := hind cv caps rfl
    exact ⟨a, b', S.resolveC ((htab t hft).2 b (Array.mem_toList_iff.mpr
      (Array.mem_of_getElem? hb))), d⟩

/-- A name read alike, of an inductive kind or pinned, is stored alike
(either side's lookup given). -/
theorem same_of {n d : Name} (hd : ((S.R n).find? d).isSome = true)
    (hk : ((∃ ci, C.find? d = some ci ∧ ci.isIndKind = true) ∧
      ∃ ci, (S.E n).find? d = some ci ∧ ci.isIndKind = true) ∨ d ∈ pinnedNames) :
    C.find? d = (S.E n).find? d :=
  S.same n d hd hk

/-- A stored inductive kind is its source's. -/
theorem self_same {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci)
    (hk : ci.isIndKind = true) : C.find? n = (S.E n).find? n := by
  obtain ⟨ci', hf', hr⟩ := S.entry n ci hf
  rw [hf, hf', hr.eq_of_indKind hk]

/-- The name itself, read alike. -/
theorem selfR {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ((S.R n).find? n).isSome = true := S.self n (by rw [hf]; rfl)

/-- **The basis pins hold in the context.** -/
theorem basis_pinned : BasisPinnedTT C aC := by
  intro n ci hf hres
  have hsame := S.same_of (S.selfR hf) (Or.inr ((mem_pinned_of_reserved hres)))
  rw [hf] at hsame
  obtain ⟨h1, h2⟩ := (S.m n).base2.basis_pinned n ci hsame.symm hres
  refine ⟨h1, fun t ψ hp => ?_⟩
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  exact h2 t ψ hp

/-- **The context's tables are its sources'**, entry by entry. -/
theorem proj_ok : ProjOkT C := by
  intro T tbl ht i hi
  obtain ⟨-, hsn, hT⟩ := ConLeche.Env.findTable?_mem ht
  obtain ⟨cv, caps, hfI, htE⟩ := S.table_of ht
  obtain ⟨r1, r2, r3, r4, ⟨cvT, capsT, hfT, hlpT⟩, ⟨cvC, hfC, hlpC, hstrip⟩⟩ :=
    (S.m T).base2.proj_ok T tbl htE i hi
  have hsnT : (tbl.entry i).structName = T := hsn
  have hctor : (tbl.entry i).ctor = tbl.ctor := rfl
  obtain ⟨-, -, -, hind, -⟩ := S.scope _ _ hfI
  obtain ⟨-, -, -, htab⟩ := hind cv caps rfl
  have hcR := (htab tbl ht).1
  rw [hsnT] at hfT
  have hsameT := S.self_same hfI rfl
  rw [hctor] at hfC
  obtain ⟨-, -, -, htc⟩ := (S.blocks T _ hfI)
  obtain ⟨_, _, _, hcC⟩ := htc tbl ht
  have hsameC := S.same_of (n := T) hcR (Or.inl ⟨⟨_, hcC, rfl⟩, _, hfC, rfl⟩)
  refine ⟨r1, r2, r3, r4, ⟨cvT, capsT, by rw [hsnT, hsameT]; exact hfT, hlpT⟩,
    ⟨cvC, by rw [hctor, hsameC]; exact hfC, hlpC, hstrip⟩⟩

/-- **A constructor read alike reads its result family alike**, where
the source stores it. -/
theorem ctor_family {n c : Name} {cvj : ConstantVal} {nP nF : Nat}
    (hc : ((S.R n).find? c).isSome = true) (hfc : C.find? c = some (.ctorInfo cvj nP nF))
    {T : Name} {us : List Level} (hh : cvj.type.piResult.getAppFn = .const T us)
    (hTE : ((S.E n).find? T).isSome = true) : ((S.R n).find? T).isSome = true := by
  have hdeep := S.deep n c _ hc hfc rfl
  have hTC : (C.find? T).isSome = true := by
    have := (S.scope c _ hfc).1
    rw [Expr.constsResolve_iff] at this
    exact S.storedC (Expr.constsAll_piResult_head this hh)
  exact Expr.constsAll_piResult_head hdeep.1 hh hTC hTE

/-- **The rules' constructors are stored in the context**, with their
bits. -/
theorem rec_ctors : RecCtorsStored C := by
  intro n cv mI rP rules hf r hr
  obtain ⟨ci', hf', hrf, -⟩ := S.src_entry hf
  have he' : ci' = .recInfo cv mI rP rules := (hrf.eq_of_indKind rfl).symm
  rw [he'] at hf'
  obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hK, hEta⟩ := (S.m n).base2.rec_ctors n cv mI rP rules hf' r hr
  obtain ⟨-, hcR, -⟩ := (S.scope n _ hf).2.2.1 cv mI rP rules rfl r hr
  obtain ⟨_, _, _, hcC⟩ := (S.blocks n _ hf) r hr
  have hsame := S.same_of hcR (Or.inl ⟨⟨_, hcC, rfl⟩, _, hfc, rfl⟩)
  have hfcC : C.find? r.ctor = some (.ctorInfo cvj cnP cnF) := by rw [hsame]; exact hfc
  -- both bits read the constructor and its family alike
  have hT : ∀ cvj' nP nF, (S.E n).find? r.ctor = some (.ctorInfo cvj' nP nF) →
      ∀ T us, cvj'.type.piResult.getAppFn = .const T us →
        ∀ cvT caps, (S.E n).find? T = some (.indInfo cvT caps) →
          C.find? T = (S.E n).find? T := by
    intro cvj' nP nF hfc' T us hh cvT caps hgT
    rw [hfc] at hfc'
    obtain rfl : cvj = cvj' := by injection hfc' with h; injection h
    have hTR := S.ctor_family hcR hfcC hh (by rw [hgT]; rfl)
    obtain ⟨_, _, hTC⟩ := (S.blocks _ _ hfcC) T us hh
    exact S.same_of hTR (Or.inl ⟨⟨_, hTC, rfl⟩, _, hgT, rfl⟩)
  exact ⟨⟨cvj, cnP, cnF, hfcC⟩, fun hk => recRuleKOf_of hsame hT (hK hk),
    fun he => recRuleEtaOf_of hsame hT (hEta he)⟩


/-- **A leaf reads only its own level parameters.** -/
theorem acval_params : ∀ (n : Name) (ci : ConstantInfo), C.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      aC n ψ₁ = aC n ψ₂ := by
  intro n ci hf ψ₁ ψ₂ hp
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  exact (S.m n).base2.acval_params n ci' hf' ψ₁ ψ₂ (by rw [← hr.cv]; exact hp)

/-- **The context's carrier.** -/
@[expose] def base : EnvModel V C where
  wf := S.wf
  acval := aC
  cval_closed := S.closed
  basis_pinned := S.basis_pinned
  proj_ok := S.proj_ok
  rec_ctors := S.rec_ctors
  acval_params := S.acval_params
  acval_wellDenoted := S.wd

theorem base_acval : (S.base).acval = aC := rfl

/-- A stored type reads as its source's (uninstantiated). -/
theorem type_eq0 {n : Name} {ci ci' : ConstantInfo} (hf : C.find? n = some ci)
    (hf' : (S.E n).find? n = some ci') (hr : Refines n ci ci') (ψ : Name → Nat) (d : Nat) :
    denote aC C ψ d ci.toConstantVal.type
      = denote (S.m n).base2.acval (S.E n) ψ d ci'.toConstantVal.type := by
  have hn : (C.find? n).isSome = true := by rw [hf]; rfl
  have hwf := (S.m n).base2.wf.consts _ (ConLeche.Env.find?_mem hf')
  rw [← hr.cv]
  exact S.denote_eq hn (S.scope n ci hf).1 (by rw [hr.cv]; exact hwf.2.2.1)
    (S.projs n ci hf).1 (by rw [hr.cv]; exact S.typeE_projs hf') ψ d

theorem type_reads : ∀ c ∈ C.consts, ∀ ψ : Name → Nat,
    ∃ ta : Term, denote aC C ψ 0 c.toConstantVal.type = some ta := by
  intro c hc ψ
  have hf := find?_of_mem S.nodup hc
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  rw [S.type_eq0 hf hf' hr ψ 0]
  exact (S.m c.name).type_reads ci' (ConLeche.Env.find?_mem hf') ψ

theorem type_wellDenotedTy : ∀ c ∈ C.consts, ∀ (ψ : Name → Nat) (ta : Term),
    denote aC C ψ 0 c.toConstantVal.type = some ta → ∀ ρ : Nat → V, WellDenotedTy V ρ ta := by
  intro c hc ψ ta hta
  have hf := find?_of_mem S.nodup hc
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  rw [S.type_eq0 hf hf' hr ψ 0] at hta
  exact (S.m c.name).type_wellDenotedTy ci' (ConLeche.Env.find?_mem hf') ψ ta hta

theorem mem_type : ∀ c ∈ C.consts, ∀ (ψ : Name → Nat) (ta : Term),
    denote aC C ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp V ρ (aC c.name ψ) ∈ˢ interp V ρ ta := by
  intro c hc ψ ta hta ρ
  have hf := find?_of_mem S.nodup hc
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  rw [S.type_eq0 hf hf' hr ψ 0] at hta
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  have hname : ci'.name = c.name := ConLeche.Env.find?_name hf'
  have := (S.m c.name).mem_type ci' (ConLeche.Env.find?_mem hf') ψ ta hta ρ
  rwa [hname] at this

theorem defn_reads : AcvalDefnInst S.base := by
  intro ψ cv value ⟨hint, hmem⟩
  have hf := find?_of_mem S.nodup hmem
  obtain ⟨ci', hf', hr, hwf'⟩ := S.src_entry hf
  have he : ci' = .defnInfo cv value hint :=
    (hr.eq_of_not_axiom fun _ h => nomatch h).symm
  subst he
  have hname : (ConstantInfo.defnInfo cv value hint).name = cv.name := rfl
  rw [hname] at hf hf'
  obtain ⟨t, ht, hlr⟩ := (S.m cv.name).defn_reads ψ cv value ⟨hint, ConLeche.Env.find?_mem hf'⟩
  refine ⟨t, ?_, ?_⟩
  · show denote aC C ψ 0 value = some t
    rw [S.denote_eq (n := cv.name) (by rw [hf]; rfl) ((S.scope _ _ hf).2.1 cv value hint rfl)
      (hwf'.2.2.2.2.1 cv value hint rfl).2.2.1 ((S.projs _ _ hf).2.1 cv value hint rfl)
      (S.projsE ht)]
    exact ht
  · show LeafReads V (aC cv.name ψ) t
    rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
    exact hlr

theorem ind_strict : IndStrictOk (V := V) S.base := by
  intro I cv caps hf ψ ab n hread hn ρ vs hsp
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  have he : ci' = .indInfo cv caps := (hr.eq_of_indKind rfl).symm
  subst he
  have hread' := hread
  change denote aC C ψ 0 cv.type = _ at hread'
  rw [show cv.type = (ConstantInfo.indInfo cv caps).toConstantVal.type from rfl,
    S.type_eq0 hf hf' hr ψ 0] at hread'
  show Strict (vs.foldl SetTheory.app (interp V ρ (aC I ψ)))
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  exact (S.m I).ind_strict I cv caps hf' ψ ab n hread' hn ρ vs hsp

theorem eq_law : EqLaw S.base := by
  intro hf ψ
  have hsame := S.same_of (S.selfR hf)
    (Or.inr ((mem_pinned_of_reserved (by decide))))
  rw [hf] at hsame
  have h := (S.m eqName).eq_law hsame.symm ψ
  have hl : ∀ ψ', (S.base).acval eqName ψ' = (S.m eqName).base2.acval eqName ψ' := fun ψ' => by
    rw [base_acval, S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  simp only [hl]
  exact h

theorem reduce_ops : ReduceOps S.base := by
  intro c hc cv hf hpin
  have hpc : c ∈ pinnedNames := by
    unfold pinnedNames; simp only [List.mem_append]; exact Or.inr hc
  have hsame := S.same_of (S.selfR hf) (Or.inr (hpc))
  rw [hf] at hsame
  obtain ⟨hel, hlaw⟩ := (S.m c).reduce_ops c hc cv hsame.symm hpin
  have helR : ((S.R c).find? (ConLeche.reduceElemName c)).isSome = true :=
    (S.scope c _ hf).2.2.2.2 _ (by
      simp only [ConLeche.reduceOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> decide)
  refine ⟨S.storedC helR, fun ψ ρ x hx => ?_⟩
  change SetTheory.app (interp V ρ (aC c ψ)) x = x
  change x ∈ˢ interp V ρ (aC (ConLeche.reduceElemName c) ψ) at hx
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  rw [S.leaf (n := c) (by rw [hf]; rfl) helR] at hx
  exact hlaw ψ ρ x hx

theorem nat_heads (φ : Name → Nat) : NatHeads S.base φ := by
  intro hs ρ
  obtain ⟨cvN, capsN, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, -⟩ :=
    ConLeche.natLitSupported_inv hs
  have hNR := S.selfR hfN
  have hpinN := (S.basis_pinned natName _ hfN (by decide)).1
  have hNe : ConstantInfo.indInfo cvN capsN = natA := hpinN
  obtain ⟨-, -, -, hind, -⟩ := S.scope natName _ hfN
  obtain ⟨-, hctors, -, -⟩ := hind cvN capsN rfl
  have hcs : capsN.ctors = [natZeroName, natSuccName] := by
    have h' : ConstantInfo.indInfo cvN capsN = natRaw := hNe
    unfold natRaw at h'
    injection h' with _ hcaps
    rw [hcaps]
  have hZR := hctors natZeroName (by rw [hcs]; simp)
  have hSR := hctors natSuccName (by rw [hcs]; simp)
  have hag := S.agree natName (by rw [hfN]; rfl)
  have hsE : ConLeche.natLitSupported (S.E natName) = true := by
    rw [← hag.nat (by
      intro m hm
      simp only [natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨hNR, S.storedE hNR⟩
      · exact ⟨hZR, S.storedE hZR⟩
      · exact ⟨hSR, S.storedE hSR⟩)]
    exact hs
  have h := (S.m natName).nat_heads φ hsE ρ
  have e1 := S.leaf (n := natName) (by rw [hfN]; rfl) hNR
  have e2 := S.leaf (n := natName) (by rw [hfN]; rfl) hZR
  have e3 := S.leaf (n := natName) (by rw [hfN]; rfl) hSR
  have hl : ∀ d ψ', ((S.R natName).find? d).isSome = true →
      (S.base).acval d ψ' = (S.m natName).base2.acval d ψ' := fun d ψ' hd => by
    rw [base_acval, S.leaf (n := natName) (by rw [hfN]; rfl) hd]
  rw [hl _ _ hNR, hl _ _ hZR, hl _ _ hSR]
  exact h

end CtxSrc

/-- The certified `Nat` operations, their dependencies and the `Nat`
basis are pinned names; their footprint lists what their guard reads. -/
theorem natOp_facts {c : Name} (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    c ∈ pinnedNames ∧
    (∀ d ∈ [natName, natZeroName, natSuccName] ++ natOpDeps c,
      d ∈ pinnedNames ∧ d ∈ pinFootprint c) ∧
    ((decide (c = natBeqName) || decide (c = natBleName) || natDivModNames.contains c) = true →
      ∀ d ∈ [boolName, boolTrueName, boolFalseName], d ∈ pinFootprint c) := by
  simp only [natOpNames, natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- What a certified operation's guard reads is read alike. -/
theorem natOp_read {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci)
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    (∀ d ∈ [natName, natZeroName, natSuccName] ++ natOpDeps c,
      ((S.R c).find? d).isSome = true ∧ C.find? d = (S.E c).find? d ∧
        (S.R c).find? d = (S.E c).find? d) ∧
    ((decide (c = natBeqName) || decide (c = natBleName) || natDivModNames.contains c) = true →
      ∀ d ∈ [boolName, boolTrueName, boolFalseName], ((S.R c).find? d).isSome = true ∧
        (C.find? d).map (·.toConstantVal) = ((S.E c).find? d).map (·.toConstantVal) ∧
        (S.R c).find? d = (S.E c).find? d) := by
  obtain ⟨-, hdeps, hbool⟩ := natOp_facts hc
  have hfp := (S.scope c _ hf).2.2.2.2
  have hRE : ∀ d, ((S.R c).find? d).isSome = true → (S.R c).find? d = (S.E c).find? d := by
    intro d hd
    obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.mp hd
    rw [hci', (S.R_sub c d ci' hci').1]
  refine ⟨fun d hd => ?_, fun hcond d hd => ?_⟩
  · obtain ⟨hp, hfpd⟩ := hdeps d hd
    have hR := hfp d hfpd
    obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.mp hR
    exact ⟨hR, S.same_of hR (Or.inr (hp)), hRE d hR⟩
  · have hR := hfp d (hbool hcond d hd)
    obtain ⟨ciC, ciE, hC, hE, hcv, -⟩ := (S.agree c (by rw [hf]; rfl)).find d hR (S.storedE hR)
    exact ⟨hR, by rw [hC, hE]; simp [hcv], hRE d hR⟩

theorem natOpGuard_eq {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci)
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    natOpGuard C c = natOpGuard (S.E c) c := by
  obtain ⟨h1, h2⟩ := S.natOp_read hf hc
  exact natOpGuard_congr (fun d hd => (h1 d hd).2.1)
    (fun hcond d hd => (h2 hcond d (by simp at hd ⊢; rcases hd with rfl | rfl <;> simp)).2.1)

theorem natOpTyPinned_eq {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci)
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) (ty : Expr) :
    ConLeche.natOpTyPinned C c ty = ConLeche.natOpTyPinned (S.E c) c ty := by
  obtain ⟨-, h2⟩ := S.natOp_read hf hc
  refine natOpTyPinned_congr (fun hcond => (h2 ?_ boolName (by simp)).2.1)
  revert hcond; simp only [Bool.or_eq_true]; exact fun h => Or.inl h

theorem nat_ops (φ : Name → Nat) : NatOps S.base φ := by
  intro c hcN cv v hint hf
  have hc : c ∈ natOpNames ∨ c ∈ natDivModNames := Or.inl hcN
  obtain ⟨hpc, -, -⟩ := natOp_facts hc
  have hsame := S.same_of (S.selfR hf) (Or.inr (hpc))
  rw [hf] at hsame
  obtain ⟨hg, hpin, hlaws⟩ := (S.m c).nat_ops φ c hcN cv v hint hsame.symm
  obtain ⟨h1, h2⟩ := S.natOp_read hf hc
  have hcn : (C.find? c).isSome = true := by rw [hf]; rfl
  have hnatR := (h1 natName (by simp)).1
  -- the recurrences' terms resolve in the part read alike
  obtain ⟨hsN, hsZ, hsS, hsD, hsB⟩ := ConLeche.Verify.natOpGuard_stored hg
  have hst : ∀ d, ((S.R c).find? d).isSome = true → (S.R c).find? d = (S.E c).find? d →
      ConLeche.Verify.storedNoLevels (S.E c) d → ConLeche.Verify.storedNoLevels (S.R c) d := by
    intro d _ he h; unfold ConLeche.Verify.storedNoLevels at h ⊢; rw [he]; exact h
  have hfrag := ConLeche.Verify.natOpEquations_frag (env := S.R c) (c := c)
    (hst _ (h1 natZeroName (by simp)).1 (h1 natZeroName (by simp)).2.2 hsZ)
    (hst _ (h1 natSuccName (by simp)).1 (h1 natSuccName (by simp)).2.2 hsS)
    (fun n hn _ => hst _ (h1 n (List.mem_append_right _ hn)).1
      (h1 n (List.mem_append_right _ hn)).2.2 (hsD n hn))
    (fun hbq => by
      have hcond : (decide (c = natBeqName) || decide (c = natBleName) ||
          natDivModNames.contains c) = true := by
        rcases hbq with rfl | rfl <;> simp
      exact hst _ (h2 hcond boolTrueName (by simp)).1 (h2 hcond boolTrueName (by simp)).2.2
        (hsB hcond).1)
    (fun hbq => by
      have hcond : (decide (c = natBeqName) || decide (c = natBleName) ||
          natDivModNames.contains c) = true := by
        rcases hbq with rfl | rfl <;> simp
      exact hst _ (h2 hcond boolFalseName (by simp)).1 (h2 hcond boolFalseName (by simp)).2.2
        (hsB hcond).2)
  have hres : ∀ e, ConLeche.Verify.natFragOk (S.R c) c e = true → e.constsResolve (S.R c) = true :=
    fun e he => constsResolve_of_natFragOk (S.selfR hf) hnatR he
  refine ⟨by rw [S.natOpGuard_eq hf hc]; exact hg, by rw [S.natOpTyPinned_eq hf hc]; exact hpin,
    fun eq hq => ?_⟩
  obtain ⟨L, R, hL, hR, hlaw⟩ := hlaws eq hq
  obtain ⟨f1, f2⟩ := hfrag eq hq
  refine ⟨L, R, ?_, ?_, fun ρ x y hx hy => ?_⟩
  · show denote aC C φ 2 eq.1 = some L
    rw [S.denote_eq hcn (hres _ f1) (S.resolveE (hres _ f1)) (projsFormer_of_natFragOk f1)
      (S.projsE hL)]
    exact hL
  · show denote aC C φ 2 eq.2 = some R
    rw [S.denote_eq hcn (hres _ f2) (S.resolveE (hres _ f2)) (projsFormer_of_natFragOk f2)
      (S.projsE hR)]
    exact hR
  · change x ∈ˢ interp V ρ (aC natName φ) at hx
    change y ∈ˢ interp V ρ (aC natName φ) at hy
    rw [S.leaf hcn hnatR] at hx hy
    exact hlaw ρ x y hx hy

theorem div_mod (φ : Name → Nat) : DivMod S.base φ := by
  intro c hcN cv v hint hf
  have hc : c ∈ natOpNames ∨ c ∈ natDivModNames := Or.inr hcN
  obtain ⟨hpc, -, -⟩ := natOp_facts hc
  have hsame := S.same_of (S.selfR hf) (Or.inr (hpc))
  rw [hf] at hsame
  obtain ⟨hg, hpin, hlaw⟩ := (S.m c).div_mod φ c hcN cv v hint hsame.symm
  obtain ⟨h1, h2⟩ := S.natOp_read hf hc
  have hcn : (C.find? c).isSome = true := by rw [hf]; rfl
  have hcond : (decide (c = natBeqName) || decide (c = natBleName) ||
      natDivModNames.contains c) = true := by
    simp only [Bool.or_eq_true]; exact Or.inr (List.contains_iff_mem.mpr hcN)
  refine ⟨by rw [S.natOpGuard_eq hf hc]; exact hg, by rw [S.natOpTyPinned_eq hf hc]; exact hpin,
    fun ρ x y hx hy => ?_⟩
  have hleaf : ∀ n ∈ dmValNames c, interp V ρ (aC n φ) = interp V ρ ((S.m c).base2.acval n φ) := by
    intro n hn
    have hR : ((S.R c).find? n).isSome = true := by
      simp only [dmValNames, List.mem_cons] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
      · exact (h1 natName (by simp)).1
      · exact (h2 hcond boolTrueName (by simp)).1
      · exact (h2 hcond boolFalseName (by simp)).1
      · exact (h1 natZeroName (by simp)).1
      · exact (h1 natSuccName (by simp)).1
      · exact (h1 natBleName (List.mem_append_right _ (by
          simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hcN
          rcases hcN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))).1
      · exact S.selfR hf
      · exact (h1 n (List.mem_append_right _ hn)).1
    rw [S.leaf hcn hR]
  change x ∈ˢ interp V ρ (aC natName φ) at hx
  change y ∈ˢ interp V ρ (aC natName φ) at hy
  rw [hleaf natName (by simp [dmValNames])] at hx hy
  exact (divModClausesV_congr hcN (fun n hn => (hleaf n hn).symm)).mp (hlaw ρ x y hx hy)

end CtxSrc



namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- **An inductive kind read alike has its type read alike**, where the
source's entry resolves it. -/
theorem deep_type {n c : Name} {ci : ConstantInfo} (hc : ((S.R n).find? c).isSome = true)
    (hf : C.find? c = some ci) (hk : ci.isIndKind = true)
    (hE : ∃ ci', (S.E n).find? c = some ci' ∧ ci'.isIndKind = true) :
    ci.toConstantVal.type.constsResolve (S.R n) = true := by
  have hdeep := (S.deep n c ci hc hf hk).1
  have hsame := S.same_of hc (Or.inl ⟨⟨_, hf, hk⟩, hE⟩)
  rw [hf] at hsame
  have hE := ((S.m n).base2.wf.consts _ (ConLeche.Env.find?_mem hsame.symm)).2.2.1
  have hC := (S.scope c ci hf).1
  rw [Expr.constsResolve_iff] at hE hC ⊢
  exact Expr.constsAll_and3 (fun d h1 h2 h3 => h1 (S.storedC h2) h3) hdeep hC hE

/-- ... and its instantiated type reads as at the source. -/
theorem deep_type_eq {n c : Name} {ci : ConstantInfo} (hc : ((S.R n).find? c).isSome = true)
    (hf : C.find? c = some ci) (hk : ci.isIndKind = true)
    (hE : ∃ ci', (S.E n).find? c = some ci' ∧ ci'.isIndKind = true)
    (hn : (C.find? n).isSome = true)
    (ψ : Name → Nat) (d : Nat) (ks : List Name) (us : List Level) :
    denote aC C ψ d (ci.toConstantVal.type.instantiateLevelParams ks us)
      = denote (S.m n).base2.acval (S.E n) ψ d
          (ci.toConstantVal.type.instantiateLevelParams ks us) := by
  have hR := S.deep_type hc hf hk hE
  have hsame := S.same_of hc (Or.inl ⟨⟨_, hf, hk⟩, hE⟩)
  rw [hf] at hsame
  refine S.denote_eq hn ?_ ?_ ?_ ?_ ψ d
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hR
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact S.resolveE hR
  · rw [projsFormer_instantiateLevelParams]; exact (S.projs c ci hf).1
  · rw [projsFormer_instantiateLevelParams]; exact S.typeE_projs hsame.symm

/-- **The context's η families are closed.** -/
theorem etaClosed : ConLeche.EtaFamiliesClosed C := by
  intro T cvT caps hf he hr
  obtain ⟨ci', hf', hrf, -⟩ := S.src_entry hf
  have hci : ci' = .indInfo cvT caps := (hrf.eq_of_indKind rfl).symm
  rw [hci] at hf'
  obtain ⟨cvC, hfC⟩ := S.eta T T cvT caps hf' he hr
  obtain ⟨-, -, hetaR, -⟩ := (S.scope T _ hf).2.2.2.1 cvT caps rfl
  have hR := hetaR he
  obtain ⟨-, -, hetaC, -⟩ := S.blocks T _ hf
  obtain ⟨_, _, _, hcC⟩ := hetaC he
  exact ⟨cvC, by rw [S.same_of hR (Or.inl ⟨⟨_, hcC, rfl⟩, _, hfC, rfl⟩)]; exact hfC⟩

theorem caps_ok : CapsOk S.base := by
  refine ⟨fun T cvT caps hf he hr hst φ' us hus => ?_, fun T cvT caps hf hu hr φ' us hus => ?_⟩
  · obtain ⟨ci', hf', hrf, -⟩ := S.src_entry hf
    have hci : ci' = .indInfo cvT caps := (hrf.eq_of_indKind rfl).symm
    rw [hci] at hf'
    obtain ⟨hres, ⟨cvC, cnP, cnF, hfC⟩, hfl⟩ := hst
    obtain ⟨-, -, hetaR, -⟩ := (S.scope T _ hf).2.2.2.1 cvT caps rfl
    have hR := hetaR he
    obtain ⟨cvE, hfCE⟩ := S.eta T T cvT caps hf' he hr
    have hsameC := S.same_of hR (Or.inl ⟨⟨_, hfC, rfl⟩, _, hfCE, rfl⟩)
    have hTn : (C.find? T).isSome = true := by rw [hf]; rfl
    have hstE : ConLeche.EtaFamilyStored (S.E T) T caps :=
      ⟨hres, ⟨cvC, cnP, cnF, by rw [← hsameC]; exact hfC⟩, hfl⟩
    obtain ⟨TVa, hTVa, hwd, hlaw, hcoh⟩ := (S.m T).caps_ok.1 T cvT caps hf' he hr hstE φ' us hus
    have htyeq := S.type_eq hf hf' (Refines.refl _ _) φ' 0 us cvT.levelParams
    have hTVa' : denote aC C φ' 0 (cvT.type.instantiateLevelParams cvT.levelParams us)
        = some TVa := (htyeq.trans hTVa)
    refine ⟨TVa, hTVa', hwd, fun ρ ts rest x hlen hfit hmem => ?_, ?_⟩
    · change x = ts.foldl SetTheory.app (interp V ρ (aC caps.etaCtor _))
      change x ∈ˢ ts.foldl SetTheory.app (interp V ρ (aC T _)) at hmem
      rw [S.leaf hTn (S.selfR hf)] at hmem
      rw [S.leaf hTn hR]
      exact hlaw ρ ts rest x hlen hfit hmem
    · refine hcoh.transport (m₂ := S.base) (fun cvC' nPc nFc h₂ => ?_)
        (fun cvC' nPc nFc TCa h hTCa => ?_) ?_ (fun _ _ _ => rfl)
      · rw [← hsameC]; exact h₂
      · have hfC' : C.find? caps.etaCtor = some (.ctorInfo cvC' nPc nFc) := by
          rw [hsameC]; exact h
        have := S.deep_type_eq hR hfC' rfl ⟨_, h, rfl⟩ hTn φ' 0 cvC'.levelParams us
        exact this.trans hTCa
      · show aC T _ = _
        rw [S.leaf hTn (S.selfR hf)]
  · obtain ⟨ci', hf', hrf, -⟩ := S.src_entry hf
    have hci : ci' = .indInfo cvT caps := (hrf.eq_of_indKind rfl).symm
    rw [hci] at hf'
    have hTn : (C.find? T).isSome = true := by rw [hf]; rfl
    obtain ⟨TVa, hTVa, hwd, hlaw⟩ := (S.m T).caps_ok.2 T cvT caps hf' hu hr φ' us hus
    have htyeq := S.type_eq hf hf' (Refines.refl _ _) φ' 0 us cvT.levelParams
    have hTVa' : denote aC C φ' 0 (cvT.type.instantiateLevelParams cvT.levelParams us)
        = some TVa := (htyeq.trans hTVa)
    refine ⟨TVa, hTVa', hwd, fun ρ ts rest x y hlen hfit hx hy => ?_⟩
    change x ∈ˢ ts.foldl SetTheory.app (interp V ρ (aC T _)) at hx
    change y ∈ˢ ts.foldl SetTheory.app (interp V ρ (aC T _)) at hy
    rw [S.leaf hTn (S.selfR hf)] at hx hy
    exact hlaw ρ ts rest x y hlen hfit hx hy

end CtxSrc


/-- The reverse opening keeps resolution. -/
theorem constsResolve_openRev {E : Env} {e : Expr} (h : e.constsResolve E = true) :
    ∀ d n : Nat, (ConLeche.Verify.openRev d n e).constsResolve E = true := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show ((ConLeche.Verify.openRev d n e).instantiate1 (.fvar (d + n) (.sort .zero)) 0).constsResolve E
      = true
    exact ConLeche.Expr.constsResolve_instantiate1 (by simp [ConLeche.Expr.constsResolve]) 0 ih

/-- The case split's guard reads the constructor's result family only
where it is an inductive. -/
theorem iotaCtorNeverProp_congr {f g : Name → Option ConstantInfo} {cvj : ConstantVal}
    (hT : ∀ T us, cvj.type.piResult.getAppFn = .const T us →
      (∀ cvT caps, f T = some (.indInfo cvT caps) → f T = g T) ∧
      (∀ cvT caps, g T = some (.indInfo cvT caps) → f T = g T)) (lvs : List Level) :
    ConLeche.iotaCtorNeverProp f cvj lvs = ConLeche.iotaCtorNeverProp g cvj lvs := by
  unfold ConLeche.iotaCtorNeverProp
  match hh : cvj.type.piResult.getAppFn with
  | .const T us =>
    dsimp only
    obtain ⟨h1, h2⟩ := hT T us hh
    by_cases hfi : ∃ cvT caps, f T = some (.indInfo cvT caps)
    · obtain ⟨cvT, caps, hf⟩ := hfi; rw [h1 cvT caps hf]
    · by_cases hgi : ∃ cvT caps, g T = some (.indInfo cvT caps)
      · obtain ⟨cvT, caps, hg⟩ := hgi; rw [h2 cvT caps hg]
      · have hfn : ∀ cvT caps, f T ≠ some (.indInfo cvT caps) := fun a b h => hfi ⟨a, b, h⟩
        have hgn : ∀ cvT caps, g T ≠ some (.indInfo cvT caps) := fun a b h => hgi ⟨a, b, h⟩
        cases hfa : f T with
        | none =>
          cases hga : g T with
          | none => rfl
          | some c => cases c <;> first | rfl | exact absurd hga (hgn _ _)
        | some c =>
          cases c <;> first
            | exact absurd hfa (hfn _ _)
            | (cases hga : g T with
               | none => rfl
               | some c' => cases c' <;> first | rfl | exact absurd hga (hgn _ _))
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _
  | .lit _ | .proj _ _ _ => rfl

namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- **A recursor's rules are read alike** (`RuleExt` from the source). -/
theorem ruleExt {φ : Name → Nat} {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : C.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hrl : rl ∈ rules) :
    RuleExt (S.m n) C aC φ cv rP rl n := by
  have hn : (C.find? n).isSome = true := by rw [hf]; rfl
  obtain ⟨ci', hf', hr, hwf'⟩ := S.src_entry hf
  have he : ci' = .recInfo cv mI rP rules := (hr.eq_of_indKind rfl).symm
  rw [he] at hf' hwf'
  obtain ⟨hrhsR, hcR, hpinsR⟩ := (S.scope n _ hf).2.2.1 cv mI rP rules rfl rl hrl
  obtain ⟨-, -, -, -, -, hrecE, -⟩ := hwf'
  obtain ⟨-, -, hrhsE, -, hnest⟩ := hrecE cv mI rP rules rfl rl hrl
  obtain ⟨⟨cvj₀, cnP₀, cnF₀, hfcE⟩, -, -⟩ :=
    (S.m n).base2.rec_ctors n cv mI rP rules hf' rl hrl
  obtain ⟨_, _, _, hcC⟩ := (S.blocks n _ hf) rl hrl
  have hsameC := S.same_of hcR (Or.inl ⟨⟨_, hcC, rfl⟩, _, hfcE, rfl⟩)
  obtain ⟨hrhsP, hpinsP⟩ := (S.projs n _ hf).2.2.1 cv mI rP rules rfl rl hrl
  refine ⟨S.leaf hn (S.selfR hf), S.leaf hn hcR, fun ci h => by rw [← hsameC]; exact h,
    fun us TVa h => ?_, fun us Ra h => ?_, fun lvls pins hfr i us vpa h => ?_,
    fun cvj nP nF hfc usj TVja h => ?_, fun cvj nP nF hfc lvs => ?_⟩
  · have := S.type_eq hf hf' (Refines.refl _ _) φ 0 us cv.levelParams
    exact this.trans h
  · rw [S.denote_eq hn (by rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hrhsR)
      (by rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hrhsE)
      (by rw [projsFormer_instantiateLevelParams]; exact hrhsP) (S.projsE h)]
    exact h
  · have hpR : (pins.getD i default).constsResolve (S.R n) = true := by
      by_cases hilt : i < pins.length
      · exact hpinsR lvls pins hfr _ (ConLeche.getD_mem hilt)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hpP : Expr.projsFormer C (pins.getD i default) = true := by
      by_cases hilt : i < pins.length
      · exact hpinsP lvls pins hfr _ (ConLeche.getD_mem hilt)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [S.denote_eq hn (constsResolve_openRev
        (by rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hpR) 0 rP)
      (constsResolve_openRev
        (by rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact S.resolveE hpR) 0 rP)
      (projsFormer_openRev (by rw [projsFormer_instantiateLevelParams]; exact hpP) 0 rP)
      (S.projsE h)]
    exact h
  · have hfcC : C.find? rl.ctor = some (.ctorInfo cvj nP nF) := by rw [hsameC]; exact hfc
    exact (S.deep_type_eq hcR hfcC rfl ⟨_, hfc, rfl⟩ hn φ 0 cvj.levelParams usj).trans h
  · have hfcC : C.find? rl.ctor = some (.ctorInfo cvj nP nF) := by rw [hsameC]; exact hfc
    refine iotaCtorNeverProp_congr (fun T us hh => ?_) lvs
    have hTE : ((S.E n).find? T).isSome = true := by
      have hres := ((S.m n).base2.wf.consts _ (ConLeche.Env.find?_mem hfc)).2.2.1
      exact ConLeche.Expr.find?_isSome_of_piResult_getAppFn_const hres hh
    have hTR := S.ctor_family hcR hfcC hh hTE
    obtain ⟨_, _, hTC⟩ := (S.blocks _ _ hfcC) T us hh
    obtain ⟨_, _, hTE'⟩ := S.ctorFam n _ _ _ _ hfc T us hh
    have hsT := S.same_of hTR (Or.inl ⟨⟨_, hTC, rfl⟩, _, hTE', rfl⟩)
    exact ⟨fun _ _ _ => hsT, fun _ _ _ => hsT⟩

theorem rec_rules (φ : Name → Nat) : RecRules S.base φ := by
  intro n cv mI rP rules hf rl hrl
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  have he : ci' = .recInfo cv mI rP rules := (hr.eq_of_indKind rfl).symm
  rw [he] at hf'
  exact recRuleLaw_transport (S.m n) (m₂ := S.base) φ hf' hrl (S.ruleExt hf hrl)

theorem tower_ok (φ : Name → Nat) : TowerOk S.base φ := by
  intro T i entry hfP
  obtain ⟨tbl, ht, hi, rfl⟩ := ConLeche.Env.findProj?_some hfP
  obtain ⟨cvT, capsT, hfT, htE⟩ := S.table_of ht
  have hfPE : (S.E T).findProj? T i = some (tbl.entry i) := by
    unfold Env.findProj?; rw [htE]; simp [hi]
  have hn : (C.find? T).isSome = true := by rw [hfT]; rfl
  obtain ⟨-, -, -, hind, -⟩ := S.scope T _ hfT
  obtain ⟨-, -, -, htab⟩ := hind cvT capsT rfl
  obtain ⟨hcR, hbodies⟩ := htab tbl ht
  have hsameT := S.self_same hfT rfl
  obtain ⟨-, -, -, ⟨cvT', capsT', hfT', -⟩, -, cvC, hfCE, -, -, -⟩ :=
    (S.m T).tower_ok φ T i _ hfPE
  have hctor : (tbl.entry i).ctor = tbl.ctor := rfl
  rw [hctor] at hfCE
  obtain ⟨-, -, -, htc⟩ := (S.blocks T _ hfT)
  obtain ⟨_, _, _, hcC⟩ := htc tbl ht
  have hsameC := S.same_of hcR (Or.inl ⟨⟨_, hcC, rfl⟩, _, hfCE, rfl⟩)
  have hsz := ((S.m T).base2.wf.table htE).2.1
  have hbmem : tbl.bodies.getD i default ∈ tbl.bodies.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hi)]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
  have hbR : (tbl.entry i).body.constsResolve (S.R T) = true := hbodies _ hbmem
  have hbP : Expr.projsFormer C (tbl.entry i).body = true :=
    (S.projs T _ hfT).2.2.2 cvT capsT rfl tbl ht _ hbmem
  refine towerEntryLaw_transport (S.m T) (m₂ := S.base) φ hfPE
    ⟨S.leaf hn (S.selfR hfT), by rw [hctor]; exact S.leaf hn hcR,
      fun ci h => by rw [hsameT]; exact h, fun ci h => by rw [hctor, hsameC]; exact h,
      fun ci h => by rw [← hsameT]; exact h, fun ci h => by rw [hctor, ← hsameC]; exact h,
      fun us Ta h => ?_, fun cvC' nP nF hfc us TCa h => ?_, fun cvT'' caps hft us TVa h => ?_⟩
  · refine (S.denote_eq hn ?_ ?_ ?_ (S.projsE h) φ 0).trans h
    · rw [ConLeche.projTele_constsResolve, ConLeche.Expr.constsResolve_instantiateLevelParams]
      exact hbR
    · rw [ConLeche.projTele_constsResolve, ConLeche.Expr.constsResolve_instantiateLevelParams]
      exact S.resolveE hbR
    · rw [projsFormer_projTele, projsFormer_instantiateLevelParams]; exact hbP
  · rw [hctor] at hfc
    have hfcC : C.find? tbl.ctor = some (.ctorInfo cvC' nP nF) := by rw [hsameC]; exact hfc
    exact (S.deep_type_eq hcR hfcC rfl ⟨_, hfc, rfl⟩ hn φ 0 cvC'.levelParams us).trans h
  · have hftC : C.find? T = some (.indInfo cvT'' caps) := by rw [hsameT]; exact hft
    have := S.type_eq hftC hft (Refines.refl _ _) φ 0 us cvT''.levelParams
    exact this.trans h

end CtxSrc


theorem ctorEntry_some {C : Name} {ci : ConstantInfo} {t : ConstantVal × Nat × Nat}
    (h : ctorEntry C ci = some t) : ci = .ctorInfo t.1 t.2.1 t.2.2 := by
  unfold ctorEntry at h
  split at h
  · split at h
    · split at h
      · split at h
        · obtain rfl := Option.some.inj h; rfl
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **A container's constructor list comes from its member's record.** -/
theorem nestContainer_some {E : Env} {T : Name} {nP' : Nat} {L : List (ConstantVal × Nat)}
    (h : ConLeche.nestContainer (envCtx E) T = some (nP', L)) :
    ∃ cv caps, E.find? T = some (.indInfo cv caps) ∧
      ∀ e ∈ L, ∃ x ∈ caps.ctors, ∃ nPc, E.find? x = some (.ctorInfo e.1 nPc e.2) := by
  rw [nestContainer_eq] at h
  change (match E.find? T with
    | some (.indInfo _ caps) => nestPick caps (caps.ctors.filterMap (ctorLook E.find? T))
    | _ => none) = _ at h
  split at h
  · rename_i cv caps hf
    refine ⟨cv, caps, hf, fun e he => ?_⟩
    have key : ∀ c ∈ caps.ctors.filterMap (ctorLook E.find? T), ∃ x ∈ caps.ctors,
        E.find? x = some (.ctorInfo c.1 c.2.1 c.2.2) := by
      intro c hc
      obtain ⟨x, hx, hl⟩ := List.mem_filterMap.mp hc
      unfold ctorLook at hl
      cases hfx : E.find? x with
      | none => rw [hfx] at hl; exact nomatch hl
      | some ci =>
        rw [hfx] at hl
        have hci := ctorEntry_some hl
        exact ⟨x, hx, by rw [hfx, hci]⟩
    revert h
    generalize caps.ctors.filterMap (ctorLook E.find? T) = cs at key
    intro h
    cases cs with
    | nil =>
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2] at he; exact absurd he (List.not_mem_nil)
    | cons c cs' =>
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2] at he
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp he
      obtain ⟨x, hx, hfx⟩ := key c' hc'
      exact ⟨x, hx, c'.2.1, hfx⟩
  · exact nomatch h

namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- **The context's recorded blocks**: each stored type former's
source's blocks that list it. -/
@[expose] noncomputable def lfpList : List (LfpDatum V) :=
  C.consts.flatMap fun c =>
    (S.m c.name).lfpBlocks.filter fun D => c.isFormer && D.names.contains c.name

theorem mem_lfpList {D : LfpDatum V} (h : D ∈ S.lfpList) :
    ∃ n, FormerIn C n ∧ D ∈ (S.m n).lfpBlocks ∧ n ∈ D.names := by
  obtain ⟨c, hc, hD⟩ := List.mem_flatMap.mp h
  obtain ⟨hD, hn⟩ := List.mem_filter.mp hD
  simp only [Bool.and_eq_true] at hn
  have hf := find?_of_mem S.nodup hc
  refine ⟨c.name, ?_, hD, List.contains_iff_mem.mp hn.2⟩
  have hk := hn.1
  cases c with
  | indInfo cv caps => exact ⟨cv, caps, hf⟩
  | _ => simp [ConstantInfo.isFormer] at hk

theorem lfpList_of {D : LfpDatum V} {n : Name} {cv : ConstantVal} {caps : ConLeche.IndCaps}
    (hn : C.find? n = some (.indInfo cv caps))
    (hD : D ∈ (S.m n).lfpBlocks) (hmem : n ∈ D.names) : D ∈ S.lfpList := by
  have hname : (ConstantInfo.indInfo cv caps).name = n := ConLeche.Env.find?_name hn
  refine List.mem_flatMap.mpr ⟨_, ConLeche.Env.find?_mem hn, List.mem_filter.mpr ⟨?_, ?_⟩⟩
  · rw [hname]; exact hD
  · simp only [Bool.and_eq_true]
    exact ⟨rfl, by rw [hname]; exact List.contains_iff_mem.mpr hmem⟩

/-- **A recorded block's members are read alike**, stored alike, type
formers of the context. -/
theorem block_member {n : Name} (hn : FormerIn C n) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) (hmem : n ∈ D.names) {mm : Nat} (hmm : mm < D.k) :
    ((S.R n).find? (D.member mm)).isSome = true ∧
      C.find? (D.member mm) = (S.E n).find? (D.member mm) ∧ FormerIn C (D.member mm) := by
  have hcov := S.cover n
  obtain ⟨cvn, capsn, hfC⟩ := hn
  obtain ⟨mm₀, hmm₀, hn₀⟩ := List.getElem_of_mem hmem
  have hk : mm₀ < D.k := by rw [← hcov.len D hD]; exact hmm₀
  have hmem₀ : D.member mm₀ = n := by
    simp [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm₀, hn₀]
  have hsame := S.self_same hfC rfl
  have hfn : (S.E n).find? n = some (.indInfo cvn capsn) := by rw [← hsame]; exact hfC
  have hall := hcov.all D hD mm₀ hk cvn capsn (by rw [hmem₀]; exact hfn)
  obtain ⟨hallR, -⟩ := (S.scope n _ hfC).2.2.2.1 cvn capsn rfl
  have hin : D.member mm ∈ capsn.all := by
    rw [hall]
    simp only [LfpDatum.member, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show mm < D.names.length by rw [hcov.len D hD]; exact hmm),
      Option.getD_some]
    exact List.getElem_mem _
  have hmR := hallR _ hin
  obtain ⟨hallC, -⟩ := S.blocks n _ hfC
  obtain ⟨cvm, capsm, hfmC⟩ := hallC _ hin
  obtain ⟨cvE, capsE, hfmE⟩ := LfpCover.member_find hD hmm
  exact ⟨hmR, S.same_of hmR (Or.inl ⟨⟨_, hfmC, rfl⟩, _, hfmE, rfl⟩), cvm, capsm, hfmC⟩

/-- **A recorded block's constructors are read alike**, stored alike. -/
theorem block_ctor {n : Name} (hn : FormerIn C n) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) (hmem : n ∈ D.names) {c : Nat} (hc : c < D.k)
    {j : Nat} (hj : j < D.nctors c) :
    ((S.R n).find? (D.ctorName c j)).isSome = true ∧
      C.find? (D.ctorName c j) = (S.E n).find? (D.ctorName c j) := by
  have hcov := S.cover n
  obtain ⟨hmR, hmsame, -⟩ := S.block_member hn hD hmem hc
  obtain ⟨nP', L, hL, hlen, hfj⟩ := (hcov.own D hD).ctors c hc
  have hjL : j < L.length := by rw [hlen]; exact hj
  have hfx := hfj j hjL
  obtain ⟨cvm, capsm, hfm, hents⟩ := nestContainer_some hL
  obtain ⟨x, hx, nPc, hfxE⟩ := hents L[j] (List.getElem_mem _)
  have hxn : x = D.ctorName c j := by
    rw [← ConLeche.Env.find?_name hfxE, ← ConLeche.Env.find?_name hfx]; rfl
  subst hxn
  have hfmC : C.find? (D.member c) = some (.indInfo cvm capsm) := by rw [hmsame]; exact hfm
  have hdeep := S.deep n _ _ hmR hfmC rfl
  obtain ⟨-, hctC, -⟩ := S.blocks _ _ hfmC
  obtain ⟨_, _, _, hxC⟩ := hctC _ hx
  have hxR := (hdeep.2.2.2.1 cvm capsm rfl).2.1 _ hx (by rw [hxC]; rfl) (by rw [hfxE]; rfl)
  exact ⟨hxR, S.same_of hxR (Or.inl ⟨⟨_, hxC, rfl⟩, _, hfxE, rfl⟩)⟩

end CtxSrc


namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- The names of a recorded block, read alike and stored alike as
inductive kinds. -/
@[expose] def BlockName (n d : Name) : Prop :=
  ((S.R n).find? d).isSome = true ∧ C.find? d = (S.E n).find? d ∧
    ∃ ci, (S.E n).find? d = some ci ∧ ci.isIndKind = true

theorem blockName_of {n : Name} (hn : FormerIn C n) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) (hmem : n ∈ D.names) :
    (∀ mm, mm < D.k → S.BlockName n (D.member mm)) ∧
      ∀ c, c < D.k ∨ c < D.N → ∀ j, j < D.nctors c → S.BlockName n (D.ctorName c j) := by
  have hcov := S.cover n
  have hwid := hcov.wid D hD
  obtain ⟨hst, hstC⟩ := ((S.m n).lfp_ok D hD).2.1
  refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
  · obtain ⟨h1, h2, -⟩ := S.block_member hn hD hmem hmm
    obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨h1, h2, _, hf, rfl⟩
  · have hck : c < D.k := by rcases hc with hc | hc; exact hc; rw [← hwid]; exact hc
    obtain ⟨h1, h2⟩ := S.block_ctor hn hD hmem hck hj
    obtain ⟨cv, a, b, hf⟩ := hstC c (by rw [hwid]; exact hck) j hj
    exact ⟨h1, h2, _, hf, rfl⟩

theorem blockName_type {n d : Name} (h : S.BlockName n d)
    {ci : ConstantInfo} (hf : (S.E n).find? d = some ci) :
    ci.toConstantVal.type.constsResolve (S.R n) = true := by
  obtain ⟨hR, hsame, ci', hci', hk⟩ := h
  rw [hf] at hci'; obtain rfl := Option.some.inj hci'
  exact S.deep_type hR (by rw [hsame]; exact hf) hk ⟨_, hf, hk⟩

theorem blockName_projs {n d : Name} (h : S.BlockName n d)
    {ci : ConstantInfo} (hf : (S.E n).find? d = some ci) :
    Expr.projsFormer C ci.toConstantVal.type = true :=
  (S.projs d ci (by rw [h.2.1]; exact hf)).1

theorem lfp_ok : ∀ D ∈ S.lfpList, LfpClause aC D ∧ LfpStored C D ∧ LfpReads aC C D ∧
    LfpCtorReads aC C D ∧ LfpCaps C D := by
  intro D hD
  obtain ⟨n, hnF, hDn, hmem⟩ := S.mem_lfpList hD
  have hn : (C.find? n).isSome = true := by obtain ⟨_, _, h⟩ := hnF; rw [h]; rfl
  refine EnvModelM.lfpOne_transport (S.BlockName n) (S.blockName_of hnF hDn hmem)
    ((S.m n).lfp_ok D hDn)
    (fun d cv nPc nF _ hf ψ => (S.m n).type_reads _ (List.mem_of_find?_eq_some hf) ψ)
    (fun d ci hp hf => by rw [hp.2.1]; exact hf)
    (fun d ci hp hf => S.leaf hn hp.1)
    (fun d cv caps hp hf ψ ta h => ?_) (fun d cv nPc nF hp hf ψ ta h => ?_)
    (fun d ci hp hf A hA ψ k ta h => ?_)
  · have hR := S.blockName_type hp hf
    exact (S.denote_eq hn hR (S.resolveE hR) (S.blockName_projs hp hf) (S.projsE h) ψ 0).trans h
  · have hR := S.blockName_type hp hf
    exact (S.denote_eq hn hR (S.resolveE hR) (S.blockName_projs hp hf) (S.projsE h) ψ 0).trans h
  · have hR := canonOf_constsResolve (S.blockName_type hp hf) hA
    exact (S.denote_eq hn hR (S.resolveE hR)
      (projsFormer_canonOf (S.blockName_projs hp hf) hA) (S.projsE h) ψ k).trans h

/-- **The context owns its recorded blocks' constructors**, as the
source does. -/
theorem lfpOwn {D : LfpDatum V} (hD : D ∈ S.lfpList) : LfpOwn C D := by
  obtain ⟨n, hn, hDn, hmem⟩ := S.mem_lfpList hD
  have hcov := S.cover n
  have hown := hcov.own D hDn
  obtain ⟨hbm, hbc⟩ := S.blockName_of hn hDn hmem
  -- a member's container reads alike
  have hnc : ∀ c, c < D.k → ConLeche.nestContainer (envCtx C) (D.member c)
      = ConLeche.nestContainer (envCtx (S.E n)) (D.member c) ∧
      ∀ cv caps, (S.E n).find? (D.member c) = some (.indInfo cv caps) → ∀ x ∈ caps.ctors,
        ctorLook C.find? (D.member c) x = ctorLook (S.E n).find? (D.member c) x := by
    intro c hc
    obtain ⟨hmR, hmsame, -⟩ := hbm c hc
    obtain ⟨cvm, capsm, hfm⟩ := LfpCover.member_find hDn hc
    have hfmC : C.find? (D.member c) = some (.indInfo cvm capsm) := by rw [hmsame]; exact hfm
    have hpt : ∀ x ∈ capsm.ctors,
        ctorLook C.find? (D.member c) x = ctorLook (S.E n).find? (D.member c) x := by
      intro x hx
      obtain ⟨ci, hci, he⟩ := ctorLook_isSome (hown.ctorsAll c hc cvm capsm hfm x hx)
      obtain ⟨-, hctC, -⟩ := S.blocks _ _ hfmC
      obtain ⟨_, _, _, hxC⟩ := hctC _ hx
      have hxR := ((S.deep n _ _ hmR hfmC rfl).2.2.2.1 cvm capsm rfl).2.1 _ hx
        (by rw [hxC]; rfl) (by rw [hci]; rfl)
      unfold ctorLook
      have hk : ci.isIndKind = true := by
        cases ci <;> simp [ctorEntry, ConstantInfo.isIndKind] at he ⊢
      rw [S.same_of hxR (Or.inl ⟨⟨_, hxC, rfl⟩, _, hci, hk⟩)]
    refine ⟨?_, fun cv caps hf x hx => ?_⟩
    · rw [nestContainer_eq, nestContainer_eq]
      show (match C.find? (D.member c) with
          | some (.indInfo _ caps) =>
            nestPick caps (caps.ctors.filterMap (ctorLook C.find? (D.member c)))
          | _ => none) = (match (S.E n).find? (D.member c) with
          | some (.indInfo _ caps) =>
            nestPick caps (caps.ctors.filterMap (ctorLook (S.E n).find? (D.member c)))
          | _ => none)
      rw [hfmC, hfm]
      show nestPick capsm (capsm.ctors.filterMap (ctorLook C.find? (D.member c)))
        = nestPick capsm (capsm.ctors.filterMap (ctorLook (S.E n).find? (D.member c)))
      congr 1
      clear hfmC hfm hmsame hmR
      revert hpt
      generalize capsm.ctors = l
      intro hpt
      induction l with
      | nil => rfl
      | cons x xs ih =>
        rw [List.filterMap_cons, List.filterMap_cons, hpt x List.mem_cons_self,
          ih fun y hy => hpt y (List.mem_cons_of_mem _ hy)]
    · rw [hfm] at hf
      obtain rfl : capsm = caps := by injection hf with h1; injection h1
      exact hpt x hx
  have hfwd : ∀ d, S.BlockName n d → ∀ ci, (S.E n).find? d = some ci → C.find? d = some ci :=
    fun d hd ci hf => by rw [hd.2.1]; exact hf
  refine ⟨fun c hc => ?_, fun c hc nP' hL => ?_, fun c hc => ?_, fun c hc j hj => ?_,
    fun c hc cv caps hf x hx => ?_⟩
  · obtain ⟨nP', L, hL, hlen, hj⟩ := hown.ctors c hc
    refine ⟨nP', L, by rw [(hnc c hc).1]; exact hL, hlen, fun j hjL => ?_⟩
    exact hfwd _ (hbc c (Or.inl hc) j (by rw [← hlen]; exact hjL)) _ (hj j hjL)
  · obtain ⟨cv, caps, hf, hnd, hlen, hall⟩ := hown.noCtors c hc nP' (by rw [← (hnc c hc).1]; exact hL)
    refine ⟨cv, caps, hfwd _ (hbm c hc) _ hf, hnd, hlen, fun mm hmm => ?_⟩
    obtain ⟨cvm, capsm, hfm, hl⟩ := hall mm hmm
    exact ⟨cvm, capsm, hfwd _ (hbm mm hmm) _ hfm, hl⟩
  · obtain ⟨cv, caps, hf, hnd⟩ := hown.lvlNodup c hc
    exact ⟨cv, caps, hfwd _ (hbm c hc) _ hf, hnd⟩
  · obtain ⟨cv, nPc, nF, hf, hsh⟩ := hown.ctorConcl c hc j hj
    exact ⟨cv, nPc, nF, hfwd _ (hbc c (Or.inl hc) j hj) _ hf, hsh⟩
  · have hfE : (S.E n).find? (D.member c) = some (.indInfo cv caps) := by
      rw [← (hbm c hc).2.1]; exact hf
    rw [(hnc c hc).2 cv caps hfE x hx]
    exact hown.ctorsAll c hc cv caps hfE x hx

/-- **The context's model.** -/
@[expose] noncomputable def model : EnvModelM V μ C where
  base2 := S.base
  type_reads := S.type_reads
  type_wellDenotedTy := S.type_wellDenotedTy
  mem_type := S.mem_type
  defn_reads := S.defn_reads
  nat_heads := S.nat_heads
  nat_ops := S.nat_ops
  div_mod := S.div_mod
  eq_law := S.eq_law
  caps_ok := S.caps_ok
  rec_rules := S.rec_rules
  reduce_ops := S.reduce_ops
  tower_ok := S.tower_ok
  ind_strict := S.ind_strict
  lfpBlocks := S.lfpList
  lfp_ok := S.lfp_ok

theorem model_acval : S.model.base2.acval = aC := rfl

/-- **The context's model is covered.** -/
theorem model_cover : LfpCover S.model [] where
  cover := fun n cv caps hf _ hq => by
    obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
    have he : ci' = .indInfo cv caps := (hr.eq_of_indKind rfl).symm
    rw [he] at hf'
    obtain ⟨D, hD, mm, hmm, hmn⟩ := (S.cover n).cover n cv caps hf' (List.not_mem_nil) hq
    have hmem : n ∈ D.names := by
      rw [← hmn]
      simp only [LfpDatum.member, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show mm < D.names.length by
          rw [(S.cover n).len D hD]; exact hmm), Option.getD_some]
      exact List.getElem_mem _
    exact ⟨D, S.lfpList_of hf hD hmem, mm, hmm, hmn⟩
  nodup := fun D hD => by
    obtain ⟨n, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).nodup D hDn
  len := fun D hD => by
    obtain ⟨n, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).len D hDn
  all := fun D hD mm hmm cv caps hf => by
    obtain ⟨n, hn, hDn, hmem⟩ := S.mem_lfpList hD
    obtain ⟨-, hsame, -⟩ := (S.blockName_of hn hDn hmem).1 mm hmm
    exact (S.cover n).all D hDn mm hmm cv caps (by rw [← hsame]; exact hf)
  fresh := fun _ _ _ _ h => List.not_mem_nil h
  own := fun D hD => S.lfpOwn hD
  wid := fun D hD => by
    obtain ⟨n, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).wid D hDn

/-- **THE CONTEXT'S MODEL**: a context read from its sources' covered
models has a covered model at the leaves `aC`, and its η families are
closed. -/
theorem ctxModel : ∃ mc : EnvModelM V μ C, mc.base2.acval = aC ∧ LfpCover mc [] ∧
    ConLeche.EtaFamiliesClosed C :=
  ⟨S.model, rfl, S.model_cover, S.etaClosed⟩

end CtxSrc

end ConLeche.Model.Modular
