module

public import ConLeche.Model.Modular.Scope
public import ConLeche.Model.Fold
public import ConLeche.Verify.Denote.Agree
public import ConLeche.Verify.EnvBound

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
  /-- a name read alike is stored alike where it is an inductive kind or pinned -/
  same : ∀ n d ci, ((R n).find? d).isSome = true →
    (C.find? d = some ci ∨ (E n).find? d = some ci) →
    (ci.isIndKind = true ∨ d ∈ pinnedNames) → C.find? d = (E n).find? d
  /-- what an inductive kind read alike reads is read alike, where it is stored -/
  deep : ∀ n c ci, ((R n).find? c).isSome = true → C.find? c = some ci → ci.isIndKind = true →
    EntryScopedP (fun d => (C.find? d).isSome = true → ((E n).find? d).isSome = true →
      ((R n).find? d).isSome = true) C c ci
  cover : ∀ n, LfpCover (m n) []
  eta : ∀ n, ConLeche.EtaFamiliesClosed (E n)
  tables : ∀ T, (C.find? T).isSome = true → C.findTable? T = (E T).findTable? T
  tables_mem : ∀ t ∈ C.tables, C.findTable? t.structName = some t
  nodup : NodupNames C
  closed : ∀ n ψ, Term.Closed (aC n ψ)
  wd : ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (aC n ψ)

variable {V : Type w} [SetTheory V] {μ : CheckMode} {C : Env}
  {aC : Name → (Name → Nat) → Term}

/-! ## Refinement -/

theorem _root_.ConLeche.Modular.Refines.cv {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci') :
    ci.toConstantVal = ci'.toConstantVal := by
  rcases h with rfl | ⟨-, rfl, -⟩ <;> rfl

theorem _root_.ConLeche.Modular.Refines.eq_of_not_axiom {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hn : ∀ cv, ci ≠ .axiomInfo cv) : ci = ci' := by
  rcases h with h | ⟨-, rfl, -⟩
  · exact h
  · exact absurd rfl (hn _)

theorem _root_.ConLeche.Modular.Refines.eq_of_indKind {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hk : ci.isIndKind = true ∨ ci'.isIndKind = true) : ci = ci' := by
  rcases h with h | ⟨-, rfl, h3⟩
  · exact h
  · rcases hk with hk | hk
    · simp [ConstantInfo.isIndKind] at hk
    · rcases h3 with ⟨v, hh, he⟩ | he | he <;> rw [he] at hk <;>
        simp [ConstantInfo.isIndKind] at hk

theorem _root_.ConLeche.Modular.Refines.eq_of_pinned {n : Name} {ci ci' : ConstantInfo} (h : Refines n ci ci')
    (hp : n ∈ pinnedNames) : ci = ci' := by
  rcases h with h | ⟨hn, -, -⟩
  · exact h
  · exact absurd hp hn

theorem _root_.ConLeche.Modular.Refines.trans {n : Name} {a b c : ConstantInfo}
    (h₁ : Refines n a b) (h₂ : Refines n b c) : Refines n a c := by
  rcases h₁ with rfl | ⟨hn, rfl, hb⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨-, rfl, hc⟩
    · exact Or.inr ⟨hn, rfl, hb⟩
    · exact Or.inr ⟨hn, rfl, hc⟩

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
    (ψ : Name → Nat) (d : Nat) :
    denote aC C ψ d e = denote (S.m n).base2.acval (S.E n) ψ d e :=
  denote_agree (S.agree n hn) d e hR hE

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
  refine S.denote_eq hn ?_ ?_ ψ d
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact (S.scope n ci hf).1
  · rw [ConLeche.Expr.constsResolve_instantiateLevelParams, hr.cv]; exact hwf.2.2.1

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

namespace CtxSrc

variable (S : CtxSrc V μ C aC)
include S

/-- A stored table's structure is an inductive type former of its
source, hence of the context, unless the table has no fields. -/
theorem table_ind {T : Name} {t : ConLeche.ProjTable} (ht : C.findTable? T = some t)
    (hpos : 0 < t.numFields) :
    ∃ cv caps, C.find? T = some (.indInfo cv caps) := by
  obtain ⟨-, hsn, hT⟩ := ConLeche.Env.findTable?_mem ht
  have htE : (S.E T).findTable? T = some t := by rw [← S.tables T hT]; exact ht
  obtain ⟨-, -, -, -, ⟨cvT, capsT, hfT, -⟩, -⟩ := (S.m T).base2.proj_ok T t htE 0 hpos
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
  obtain ⟨ci', hf', hr⟩ := S.entry T ci hci
  have hsn' : (t.entry 0).structName = T := hsn
  rw [hsn', hf'] at hfT
  obtain rfl := Option.some.inj hfT
  rw [hr.eq_of_indKind (Or.inr rfl)] at hci
  exact ⟨cvT, capsT, hci⟩

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
        (hr.eq_of_indKind (Or.inl (by rw [he]; rfl))).symm.trans he
      obtain ⟨a, b, -, d, e⟩ := hrec cv mI rP rules he' r hrr
      obtain ⟨hrh, -, hpins⟩ := hsc.2.2.1 cv mI rP rules he r hrr
      exact ⟨a, b, S.resolveC hrh, d, fun lvls pins hn =>
        (e lvls pins hn).mono_resolves fun pin hp => S.resolveC (hpins lvls pins hn pin hp)⟩
    · have he' : ci' = .indInfo cv caps :=
        (hr.eq_of_indKind (Or.inl (by rw [he]; rfl))).symm.trans he
      exact hcaps cv caps he'
  · have hft := S.tables_mem t ht
    obtain ⟨-, -, hT⟩ := ConLeche.Env.findTable?_mem hft
    have htE : (S.E t.structName).findTable? t.structName = some t := by
      rw [← S.tables _ hT]; exact hft
    obtain ⟨-, hsize, hbodies⟩ := (S.m t.structName).base2.wf.table htE
    refine ⟨hT, hsize, fun i b hb => ?_⟩
    obtain ⟨a, b', -, d⟩ := hbodies i b hb
    have hpos : 0 < t.numFields := by
      rw [← hsize]
      exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ i)
        (Nat.succ_le_of_lt (Array.getElem?_eq_some_iff.mp hb).1)
    obtain ⟨cv, caps, hfT⟩ := S.table_ind hft hpos
    obtain ⟨-, -, -, hind, -⟩ := S.scope _ _ hfT
    obtain ⟨-, -, -, htab⟩ := hind cv caps rfl
    exact ⟨a, b', S.resolveC ((htab t hft).2 b (Array.mem_toList_iff.mpr
      (Array.mem_of_getElem? hb))), d⟩

/-- A name read alike, of an inductive kind or pinned, is stored alike
(either side's lookup given). -/
theorem same_of {n d : Name} {ci : ConstantInfo} (hd : ((S.R n).find? d).isSome = true)
    (hf : C.find? d = some ci ∨ (S.E n).find? d = some ci)
    (hk : ci.isIndKind = true ∨ d ∈ pinnedNames) : C.find? d = (S.E n).find? d :=
  S.same n d ci hd hf hk

/-- The name itself, read alike. -/
theorem selfR {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ((S.R n).find? n).isSome = true := S.self n (by rw [hf]; rfl)

/-- **The basis pins hold in the context.** -/
theorem basis_pinned : BasisPinnedTT C aC := by
  intro n ci hf hres
  have hsame := S.same_of (S.selfR hf) (Or.inl hf) (Or.inr (mem_pinned_of_reserved hres))
  rw [hf] at hsame
  obtain ⟨h1, h2⟩ := (S.m n).base2.basis_pinned n ci hsame.symm hres
  refine ⟨h1, fun t ψ hp => ?_⟩
  rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
  exact h2 t ψ hp

/-- **The context's tables are its sources'**, entry by entry. -/
theorem proj_ok : ProjOkT C := by
  intro T tbl ht i hi
  obtain ⟨-, hsn, hT⟩ := ConLeche.Env.findTable?_mem ht
  have htE : (S.E T).findTable? T = some tbl := by rw [← S.tables T hT]; exact ht
  obtain ⟨r1, r2, r3, r4, ⟨cvT, capsT, hfT, hlpT⟩, ⟨cvC, hfC, hlpC, hstrip⟩⟩ :=
    (S.m T).base2.proj_ok T tbl htE i hi
  obtain ⟨cv, caps, hfI⟩ := S.table_ind ht (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  have hsnT : (tbl.entry i).structName = T := hsn
  have hctor : (tbl.entry i).ctor = tbl.ctor := rfl
  obtain ⟨-, -, -, hind, -⟩ := S.scope _ _ hfI
  obtain ⟨-, -, -, htab⟩ := hind cv caps rfl
  have hcR := (htab tbl ht).1
  rw [hsnT] at hfT
  have hsameT := S.same_of (S.selfR hfI) (Or.inl hfI) (Or.inl rfl)
  rw [hctor] at hfC
  have hsameC := S.same_of (n := T) hcR (Or.inr hfC) (Or.inl rfl)
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
  have he' : ci' = .recInfo cv mI rP rules := (hrf.eq_of_indKind (Or.inl rfl)).symm
  rw [he'] at hf'
  obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hK, hEta⟩ := (S.m n).base2.rec_ctors n cv mI rP rules hf' r hr
  obtain ⟨-, hcR, -⟩ := (S.scope n _ hf).2.2.1 cv mI rP rules rfl r hr
  have hsame := S.same_of hcR (Or.inr hfc) (Or.inl rfl)
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
    exact S.same_of hTR (Or.inr hgT) (Or.inl rfl)
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
  exact S.denote_eq hn (S.scope n ci hf).1 (by rw [hr.cv]; exact hwf.2.2.1) ψ d

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
      (hwf'.2.2.2.2.1 cv value hint rfl).2.2.1]
    exact ht
  · show LeafReads V (aC cv.name ψ) t
    rw [S.leaf (by rw [hf]; rfl) (S.selfR hf)]
    exact hlr

theorem ind_strict : IndStrictOk (V := V) S.base := by
  intro I cv caps hf ψ ab n hread hn ρ vs hsp
  obtain ⟨ci', hf', hr, -⟩ := S.src_entry hf
  have he : ci' = .indInfo cv caps := (hr.eq_of_indKind (Or.inl rfl)).symm
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
  have hsame := S.same_of (S.selfR hf) (Or.inl hf)
    (Or.inr (mem_pinned_of_reserved (by decide)))
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
  have hsame := S.same_of (S.selfR hf) (Or.inl hf) (Or.inr hpc)
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

end ConLeche.Model.Modular
