module

public import ConLeche.Verify.InferIOLeaves
public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Verify.Inductives.UniformOcc
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.Knot
import ConLeche.Verify.EnvPreds

public section

/-!
# The walk's normal form names no member

The positivity walk (`nestPos`) classifies the WHNF of every field
domain; the Model reads the walk's normal form (`MemberCtorD`'s `tyN`)
and needs that it names no member constant.  Reduction may copy
material out of the environment and out of INFERRED types (the stuck
major's rescue fabricates a constructor application from the major's
inferred type, `majorToCtor`), so "no member constant in the input" is
not preserved when free-variable annotations are ignored: the
predicate carried through reduction is `Expr.occDeep` — no member
constant, annotations INCLUDED — and the environment hypothesis is
`WhnfNamesFree`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- Does a constant of `names` occur in `e`, free-variable annotations
included?  (`Expr.nestOcc names 0 0` without the annotation blind
spot; a `.proj` node's structure name is not an occurrence.) -/
@[expose] def Expr.occDeep (names : List Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .lit _ => false
  | .fvar _ ty => occDeep names ty
  | .const n _ => names.contains n
  | .app f a => occDeep names f || occDeep names a
  | .lam ty body _ => occDeep names ty || occDeep names body
  | .forallE ty body _ => occDeep names ty || occDeep names body
  | .letE ty val body => occDeep names ty || occDeep names val || occDeep names body
  | .proj _ _ sub => occDeep names sub

/-! ## Syntactic kit -/

theorem Expr.nestOcc_zero_of_occDeep {names : List Name} :
    ∀ (e : Expr), e.occDeep names = false → e.nestOcc names 0 0 = false := by
  intro e
  induction e with
  | fvar i ty _ => intro _; simp [Expr.nestOcc]
  | app f a ihf iha =>
    intro h; simp only [Expr.occDeep, Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b mm iht ihb =>
    intro h; simp only [Expr.occDeep, Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b mm iht ihb =>
    intro h; simp only [Expr.occDeep, Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.occDeep, Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.occDeep, Expr.nestOcc] at h ⊢; exact ih h
  | const n us => intro h; simpa [Expr.occDeep, Expr.nestOcc] using h
  | _ => intro _; rfl

theorem Expr.occDeep_instantiate1 {names : List Name} {v : Expr}
    (hv : v.occDeep names = false) :
    ∀ (e : Expr) (k : Nat), e.occDeep names = false →
      (e.instantiate1 v k).occDeep names = false := by
  intro e
  induction e with
  | bvar j =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | app f a ihf iha =>
    intro k h; simp only [Expr.occDeep, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b mm iht ihb =>
    intro k h; simp only [Expr.occDeep, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | forallE t b mm iht ihb =>
    intro k h; simp only [Expr.occDeep, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | letE t val b iht ihv ihb =>
    intro k h; simp only [Expr.occDeep, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb _ h.2⟩
  | proj s j e ih => intro k h; simp only [Expr.occDeep, Expr.instantiate1] at h ⊢; exact ih k h
  | _ => intro k h; exact h

theorem Expr.occDeep_abstract1 {names : List Name} (d : Nat) :
    ∀ (e : Expr) (k : Nat), e.occDeep names = false →
      (e.abstract1 d k).occDeep names = false := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro k h
    simp only [Expr.abstract1]
    split
    · rfl
    · exact h
  | app f a ihf iha =>
    intro k h; simp only [Expr.occDeep, Expr.abstract1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b mm iht ihb =>
    intro k h; simp only [Expr.occDeep, Expr.abstract1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | forallE t b mm iht ihb =>
    intro k h; simp only [Expr.occDeep, Expr.abstract1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | letE t val b iht ihv ihb =>
    intro k h; simp only [Expr.occDeep, Expr.abstract1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb _ h.2⟩
  | proj s j e ih => intro k h; simp only [Expr.occDeep, Expr.abstract1] at h ⊢; exact ih k h
  | _ => intro k h; exact h

theorem Expr.occDeep_instantiateLevelParams {names : List Name} (ks : List Name)
    (us : List Level) : ∀ (e : Expr),
      (e.instantiateLevelParams ks us).occDeep names = e.occDeep names := by
  intro e
  induction e with
  | fvar i ty ih => simp only [Expr.instantiateLevelParams, Expr.occDeep, ih]
  | app f a ihf iha => simp only [Expr.instantiateLevelParams, Expr.occDeep, ihf, iha]
  | lam t b mm iht ihb => simp only [Expr.instantiateLevelParams, Expr.occDeep, iht, ihb]
  | forallE t b mm iht ihb => simp only [Expr.instantiateLevelParams, Expr.occDeep, iht, ihb]
  | letE t val b iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, Expr.occDeep, iht, ihv, ihb]
  | proj s j e ih => simp only [Expr.instantiateLevelParams, Expr.occDeep, ih]
  | _ => rfl

theorem Expr.occDeep_mkAppN {names : List Name} :
    ∀ {xs : List Expr} {f : Expr}, f.occDeep names = false →
      (∀ x ∈ xs, x.occDeep names = false) → (Expr.mkAppN f xs).occDeep names = false
  | [], _, hf, _ => hf
  | x :: xs, f, hf, hxs => by
    simp only [Expr.mkAppN]
    refine Expr.occDeep_mkAppN ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [Expr.occDeep, hf, hxs x List.mem_cons_self, Bool.or_self]

theorem Expr.occDeep_getAppArgs {names : List Name} :
    ∀ {e : Expr}, e.occDeep names = false → ∀ x ∈ e.getAppArgs, x.occDeep names = false := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h x hx
    simp only [Expr.occDeep, Bool.or_eq_false_iff] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

theorem Expr.occDeep_getAppFn {names : List Name} :
    ∀ {e : Expr}, e.occDeep names = false → e.getAppFn.occDeep names = false := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.occDeep, Bool.or_eq_false_iff] at h
    exact ihf h.1
  | _ => intro h; exact h

/-- A constant head that occurs in a member-free term is no member. -/
theorem Expr.not_mem_of_getAppFn {names : List Name} {e : Expr} {c : Name} {us : List Level}
    (h : e.occDeep names = false) (hfn : e.getAppFn = .const c us) : c ∉ names := by
  have := Expr.occDeep_getAppFn h
  rw [hfn] at this
  simpa [Expr.occDeep] using this

theorem Expr.occDeep_instSpine {names : List Name} :
    ∀ {args : List Expr} (t : Nat) {e : Expr}, e.occDeep names = false →
      (∀ a ∈ args, a.occDeep names = false) →
      (Expr.instSpine args t e).occDeep names = false
  | [], _, _, he, _ => he
  | a :: _as, t, e, he, hargs =>
    Expr.occDeep_instSpine (t - 1)
      (Expr.occDeep_instantiate1 (hargs a List.mem_cons_self) e t he)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

theorem Expr.occDeep_const {names : List Name} {n : Name} {us : List Level}
    (h : n ∉ names) : (Expr.const n us).occDeep names = false := by
  simpa [Expr.occDeep] using h


/-! ## The environment hypothesis -/

/-- **What reduction and inference can copy out of the environment names
no member of `names`.**  Every clause is about a constant that is NOT a
member (its name occurs in a member-free term, or is a constructor), or
about a name the kernel fabricates:

* the stored type of every non-member constant (inference);
* the value of every non-member definition (δ);
* the rule right-hand sides of every non-member recursor (ι), and its
  η-rescue bits are the store's verdict (`recRuleEtaOf`: the η rescue's
  constructor is the rule's own, a stored constructor);
* the body of every projection-table entry (a `.proj` node's type);
* constructors are no members (the K / `And` rescues and the `Nat`
  literal's constructor form fabricate constructor heads);
* no member is named like a projection function (the structure-η
  rescue fabricates them);
* the literal-support names (`Nat`, `String` and its constructor form's
  constants) are no members when the literal support is on;
* the `Bool` constructors are no members when `Nat.beq`/`Nat.ble` are
  stored (literal acceleration produces them). -/
@[expose] def WhnfNamesFree (env : Env) (names : List Name) : Prop :=
  (∀ n ci, env.find? n = some ci → n ∉ names →
    ci.toConstantVal.type.occDeep names = false) ∧
  (∀ n cv v hint, env.find? n = some (.defnInfo cv v hint) → n ∉ names →
    v.occDeep names = false) ∧
  (∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) → n ∉ names →
    ∀ r ∈ rules, r.rhs.occDeep names = false ∧
      (r.eta = true → recRuleEtaOf env.find? n r.ctor = true)) ∧
  (∀ T i entry, env.findProj? T i = some entry → entry.body.occDeep names = false) ∧
  (∀ c cv nP nF, env.find? c = some (.ctorInfo cv nP nF) → c ∉ names) ∧
  (∀ T j, projFnName T j ∉ names) ∧
  (natLitSupported env = true → natName ∉ names) ∧
  (strLitSupported env = true →
    stringName ∉ names ∧ stringOfListName ∉ names ∧ listNilName ∉ names ∧
      listConsName ∉ names ∧ charName ∉ names ∧ charOfNatName ∉ names) ∧
  (natOpStored env natBeqName = true ∨ natOpStored env natBleName = true →
    boolTrueName ∉ names ∧ boolFalseName ∉ names)

/-! ## Literals -/

theorem strLitList_occDeep {names : List Name} (hc : charName ∉ names)
    (hn : listNilName ∉ names) (hk : listConsName ∉ names) (ho : charOfNatName ∉ names) :
    ∀ cs : List Char, (strLitList cs).occDeep names = false
  | [] => by simp [strLitList, Expr.occDeep, hc, hn]
  | c :: cs => by
    simp [strLitList, Expr.occDeep, hc, hk, ho, strLitList_occDeep hc hn hk ho cs]

theorem strLitToConstructor_occDeep {env : Env} {names : List Name}
    (hN : WhnfNamesFree env names) (hs : strLitSupported env = true) (s : String) :
    (strLitToConstructor s).occDeep names = false := by
  obtain ⟨-, hso, hn, hk, hc, ho⟩ := hN.2.2.2.2.2.2.2.1 hs
  rw [strLitToConstructor_eq]
  simp only [Expr.occDeep, strLitList_occDeep hc hn hk ho, Bool.or_false]
  simpa using hso

theorem litToCtorIfNat_occDeep {env : Env} {names : List Name}
    (hN : WhnfNamesFree env names) {e : Expr} (he : e.occDeep names = false) :
    (litToCtorIfNat env e).occDeep names = false := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · rename_i hs
      obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, -, h0, h1, -⟩ := natLitSupported_inv hs
      have hz := hN.2.2.2.2.1 _ _ _ _ h0
      have hsu := hN.2.2.2.2.1 _ _ _ _ h1
      cases n <;> simp [natLitToConstructor, Expr.occDeep, hz, hsu]
    · exact he
  | .lit (.strVal _) => exact he
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ => exact he

/-- The fast-path reducts: a literal, or a `Bool` constructor from
`Nat.beq`/`Nat.ble`. -/
theorem natOpResult_const {c : Name} {a b : Nat} {bn : Name}
    (h : natOpResult c a b = some (.const bn [])) :
    (c = natBeqName ∨ c = natBleName) ∧ (bn = boolTrueName ∨ bn = boolFalseName) := by
  unfold natOpResult at h
  by_cases h0 : c = natPredName
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  by_cases h1 : c = natAddName
  · rw [ite_eq_left h1] at h; simp at h
  rw [ite_eq_right h1] at h
  by_cases h2 : c = natSubName
  · rw [ite_eq_left h2] at h; simp at h
  rw [ite_eq_right h2] at h
  by_cases h3 : c = natMulName
  · rw [ite_eq_left h3] at h; simp at h
  rw [ite_eq_right h3] at h
  by_cases h4 : c = natPowName
  · rw [ite_eq_left h4] at h; split at h <;> simp at h
  rw [ite_eq_right h4] at h
  by_cases h5 : c = natDivName
  · rw [ite_eq_left h5] at h; simp at h
  rw [ite_eq_right h5] at h
  by_cases h6 : c = natModName
  · rw [ite_eq_left h6] at h; simp at h
  rw [ite_eq_right h6] at h
  by_cases h7 : c = natGcdName
  · rw [ite_eq_left h7] at h; simp at h
  rw [ite_eq_right h7] at h
  by_cases h8 : c = natLandName
  · rw [ite_eq_left h8] at h; simp at h
  rw [ite_eq_right h8] at h
  by_cases h9 : c = natLorName
  · rw [ite_eq_left h9] at h; simp at h
  rw [ite_eq_right h9] at h
  by_cases h10 : c = natXorName
  · rw [ite_eq_left h10] at h; simp at h
  rw [ite_eq_right h10] at h
  by_cases h11 : c = natShiftLeftName
  · rw [ite_eq_left h11] at h; simp at h
  rw [ite_eq_right h11] at h
  by_cases h12 : c = natShiftRightName
  · rw [ite_eq_left h12] at h; simp at h
  rw [ite_eq_right h12] at h
  by_cases hb : c = natBeqName
  · rw [ite_eq_left hb] at h
    simp only [Option.some.injEq, Expr.const.injEq] at h
    refine ⟨Or.inl hb, ?_⟩
    split at h <;> simp_all
  rw [ite_eq_right hb] at h
  by_cases hl : c = natBleName
  · rw [ite_eq_left hl] at h
    simp only [Option.some.injEq, Expr.const.injEq] at h
    refine ⟨Or.inr hl, ?_⟩
    split at h <;> simp_all
  rw [ite_eq_right hl] at h
  exact nomatch h


/-- Literal acceleration's reducts, precisely: a literal, or a `Bool`
constructor produced while `Nat.beq` or `Nat.ble` is stored. -/
theorem reduceNat_inv_bool {env : Env} {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled mode env fuel d e = .ok (some e₂)) :
    (∃ n, e₂ = .lit (.natVal n)) ∨
    (∃ bn, e₂ = .const bn [] ∧ (bn = boolTrueName ∨ bn = boolFalseName) ∧
      (natOpStored env natBeqName = true ∨ natOpStored env natBleName = true)) := by
  dsimp only [reduceNatFueled] at h
  revert h
  match e with
  | .app (.const c []) a => ?_
  | .app (.app (.const c []) a) b => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _ | .app (.fvar _ _) _ | .app (.sort _) _
  | .app (.lam _ _ _) _ | .app (.forallE _ _ _) _
  | .app (.letE _ _ _) _ | .app (.lit _) _ | .app (.proj _ _ _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _ | .app (.app (.fvar _ _) _) _
  | .app (.app (.sort _) _) _ | .app (.app (.app _ _) _) _
  | .app (.app (.lam _ _ _) _) _ | .app (.app (.forallE _ _ _) _) _
  | .app (.app (.letE _ _ _) _) _ | .app (.app (.lit _) _) _
  | .app (.app (.proj _ _ _) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  · intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · intro h
      revert h
      cases hw0 : whnf mode env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a0 =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a0 with
      | some n =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        exact Or.inl ⟨n + 1, h.symm⟩
      | none => intro h; simp [pure, Except.pure] at h
    · intro h; simp [pure, Except.pure] at h
  · intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · rename_i hcond
      intro h
      revert h
      cases hw1 : whnf mode env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a' =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a' with
      | none => intro h; simp [pure, Except.pure] at h
      | some n₁ =>
        intro h
        revert h
        cases hw2 : whnf mode env fuel d b with
        | error err => intro h; exact nomatch h
        | ok b' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? b' with
        | some n₂ =>
          intro h
          dsimp only at h
          cases hres : natOpResult c n₁ n₂ with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            subst h
            rcases natOpResult_shape hres with hl | ⟨bn, rfl⟩
            · exact Or.inl hl
            · obtain ⟨hc, hb⟩ := natOpResult_const hres
              refine Or.inr ⟨bn, rfl, hb, ?_⟩
              rcases hc with rfl | rfl
              · exact Or.inl hcond.2
              · exact Or.inr hcond.2
        | none => intro h; simp [pure, Except.pure] at h
    · split
      · intro h
        revert h
        cases hw1 : whnf mode env fuel d a with
        | error err => intro h; exact nomatch h
        | ok a' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? a' with
        | none => intro h; simp [pure, Except.pure] at h
        | some _ =>
          intro h
          revert h
          cases hw2 : whnf mode env fuel d b with
          | error err => intro h; exact nomatch h
          | ok b' =>
          intro h
          dsimp only at h
          revert h
          match rawNatLit? b' with
          | some _ => intro h; exact nomatch h
          | none => intro h; simp [pure, Except.pure] at h
      · intro h; simp [pure, Except.pure] at h


/-! ## The reduction steps -/

theorem Expr.occDeep_piResult {names : List Name} :
    ∀ {e : Expr}, e.occDeep names = false → e.piResult.occDeep names = false := by
  intro e
  induction e with
  | forallE t b mm _ ihb =>
    intro h
    simp only [Expr.occDeep, Bool.or_eq_false_iff] at h
    exact ihb h.2
  | _ => intro h; exact h

/-- Unfolding a (non-member) definition at the head. -/
theorem unfoldDefinition_occDeep {env : Env} {names : List Name}
    (hN : WhnfNamesFree env names) {e e₂ : Expr} (h : unfoldDefinition env e = some e₂)
    (he : e.occDeep names = false) : e₂.occDeep names = false := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    have hn := Expr.not_mem_of_getAppFn he hfn
    refine Expr.occDeep_mkAppN ?_ (Expr.occDeep_getAppArgs he)
    rw [Expr.occDeep_instantiateLevelParams]
    exact hN.2.1 n cv value hint hf hn
  · intro h; exact nomatch h

/-- The η-rescue's fabricated fields. -/
theorem etaFabArgsE_occDeep {env : Env} {names : List Name} {T : Name} {ust : List Level}
    {targs : List Expr} {major : Expr} {nF : Nat}
    (hpf : ∀ j, projFnName T j ∉ names) (ht : ∀ x ∈ targs, x.occDeep names = false)
    (hm : major.occDeep names = false) :
    ∀ x ∈ etaFabArgsE env T ust targs major nF, x.occDeep names = false := by
  intro x hx
  simp only [etaFabArgsE, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ht x hx
  · unfold etaProjs at hx
    split at hx
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨j, -, rfl⟩ := hx
      simpa [Expr.occDeep] using hm
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨j, -, rfl⟩ := hx
      refine Expr.occDeep_mkAppN (Expr.occDeep_const (hpf j)) ?_
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact ht y hy
      · exact hm

/-- The stuck-major rescue fabricates member-free constructor
applications: the heads are stored constructors or a non-member
structure's η family, the arguments come from the major and its
(member-free) inferred type. -/
theorem majorToCtor_occDeep {env : Env} {names : List Name}
    (hN : WhnfNamesFree env names) {fuel d : Nat}
    (hW : ∀ {e w : Expr}, whnf mode env fuel d e = .ok w →
      e.occDeep names = false → w.occDeep names = false)
    (hI : ∀ {e t : Expr}, inferTypeIO mode env fuel d e = .ok t →
      e.occDeep names = false → t.occDeep names = false)
    {recName : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hrec : env.find? recName = some (.recInfo cv mI rP rules)) (hrn : recName ∉ names)
    {major major' : Expr}
    (h : majorToCtorFueled mode env fuel d recName rules major = .ok major')
    (hm : major.occDeep names = false) : major'.occDeep names = false := by
  rcases majorToCtor_inv h with rfl | ⟨-, -, -, rl, cvj, cnP, cnF, tmaj₀, tmaj, T, us₀, ust,
      cvT, caps, hrules, hfc, hpr, hfT, hinf, hwt, -, hcase⟩
  · exact hm
  have hctor : rl.ctor ∉ names := hN.2.2.2.2.1 _ _ _ _ hfc
  have htmaj : tmaj.occDeep names = false := hW hwt (hI hinf hm)
  have hargs := Expr.occDeep_getAppArgs htmaj
  rcases hcase with ⟨-, -, -, rfl, -⟩ | ⟨heta, -, -, -, rfl, -⟩ | ⟨rfl, -, -, -, rfl, -⟩
  · exact Expr.occDeep_mkAppN (Expr.occDeep_const hctor)
      (fun x hx => hargs x (List.mem_of_mem_take hx))
  · subst hrules
    have hbit := (hN.2.2.1 _ _ _ _ _ hrec hrn rl List.mem_cons_self).2 heta
    obtain ⟨cvj', _, _, T', _, cvT', caps', hfc', hpr', hfT', -, hec, -⟩ :=
      recRuleEtaOf_inv hbit
    rw [hfc] at hfc'
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfc')
    rw [hpr] at hpr'
    obtain ⟨rfl, -⟩ := Expr.const.inj hpr'
    rw [hfT] at hfT'
    obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT')
    refine Expr.occDeep_mkAppN (Expr.occDeep_const (hec ▸ hctor)) ?_
    exact etaFabArgsE_occDeep (hN.2.2.2.2.2.1 T) hargs hm
  · refine Expr.occDeep_mkAppN (Expr.occDeep_const hctor) ?_
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hargs x hx
    · simpa [Expr.occDeep] using hm
    · simpa [Expr.occDeep] using hm


/-- The body of a projection-table entry at member-free arguments. -/
theorem projEntry_typeAt_occDeep {env : Env} {names : List Name}
    (hN : WhnfNamesFree env names) {T : Name} {i : Nat} {entry : ProjEntry}
    (hfp : env.findProj? T i = some entry) (us : List Level) {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr}
    (hargs : ∀ a ∈ targs, a.occDeep names = false) (hpe : pe.occDeep names = false) :
    (entry.typeAt us targs pe).occDeep names = false := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe]
  refine Expr.occDeep_instSpine _ ?_ ?_
  · rw [Expr.occDeep_instantiateLevelParams]
    exact hN.2.2.2.1 T i entry hfp
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hargs a ha
    · rcases List.mem_singleton.mp ha with rfl
      exact hpe

/-- The io slot inherits preservation from whichever lane the mode
selects. -/
theorem inferTypeIO_occDeep_of {env : Env} {names : List Name} {fuel : Nat}
    (hC : ∀ {d : Nat} {e t : Expr}, inferTypeCore mode env fuel d e = .ok t →
      e.occDeep names = false → t.occDeep names = false)
    (hIO : ∀ {d : Nat} {e t : Expr}, inferTypeCoreIO mode env fuel d e = .ok t →
      e.occDeep names = false → t.occDeep names = false)
    {d : Nat} {e t : Expr} (h : inferTypeIO mode env fuel d e = .ok t)
    (he : e.occDeep names = false) : t.occDeep names = false := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg] at h; exact hC h he
  | true => rw [inferTypeIO_on hg] at h; exact hIO h he

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- **Reduction and inference introduce no member constant** (annotations
included): the joint fuel induction over `whnfCore`, `whnf`,
`inferTypeCore` and the io lane `inferTypeCoreIO`. -/
theorem whnfPres_occDeep {env : Env} {names : List Name} (hN : WhnfNamesFree env names) :
    ∀ (fuel : Nat),
      (∀ {c : Bool} {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e c = .ok e' →
        e.occDeep names = false → e'.occDeep names = false) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        e.occDeep names = false → e'.occDeep names = false) ∧
      (∀ {d : Nat} {e t : Expr}, inferTypeCore mode env fuel d e = .ok t →
        e.occDeep names = false → t.occDeep names = false) ∧
      (∀ {d : Nat} {e t : Expr}, inferTypeCoreIO mode env fuel d e = .ok t →
        e.occDeep names = false → t.occDeep names = false)
  | 0 => ⟨(fun {_ _ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h),
      (fun {_ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop, ihInf, ihIO⟩ := whnfPres_occDeep hN fuel
    have ihI : ∀ {d : Nat} {e t : Expr}, inferTypeIO mode env fuel d e = .ok t →
        e.occDeep names = false → t.occDeep names = false :=
      fun h he => inferTypeIO_occDeep_of ihInf ihIO h he
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- whnfCore
      intro c d e e' h he
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | fvar idx ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | forallE ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | lam ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | lit l0 =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE tt vv bb =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | app f a =>
        simp only [Expr.occDeep, Bool.or_eq_false_iff] at he
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hf' := ihCore hwf he.1
        have happ : (Expr.app f' a).occDeep names = false := by
          simp [Expr.occDeep, hf', he.2]
        rcases hcase with ⟨ty, body, mm, rfl, hbeta, -⟩ | ⟨e'', hio, hwe''⟩ | rfl
        · simp only [Expr.occDeep, Bool.or_eq_false_iff] at hf'
          exact ihCore hbeta (Expr.occDeep_instantiate1 he.2 body 0 hf'.2)
        · obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj,
            cvj, cnP, cnF, r, hfn, hfc, hlen, -, hprep,
            hmfn, hfj, hrule, hml, -, hlev, hpeq, hcerts, hmcerts, -, rfl⟩ :=
            iotaRec_inv hio
          have hc : c ∉ names := Expr.not_mem_of_getAppFn happ hfn
          have hmaj : major.occDeep names = false :=
            prepareMajorFueled_ind hprep (fun x => x.occDeep names = false)
              (fun hw' hx => ihLoop hw' hx)
              (fun hl hx => by
                rcases litMajorToCtorFueled_inv hl with rfl | ⟨s, -, hs, hred⟩
                · exact litToCtorIfNat_occDeep hN hx
                · exact ihLoop hred (strLitToConstructor_occDeep hN hs s))
              (fun hs hx => majorToCtor_occDeep hN (fun hw hx' => ihLoop hw hx')
                (fun hi hx' => ihI hi hx') hfc hc hs hx)
              (Expr.occDeep_getAppArgs happ _ (getD_mem (by omega)))
          refine ihCore hwe'' (Expr.occDeep_mkAppN ?_ ?_)
          · rw [Expr.occDeep_instantiateLevelParams]
            exact (hN.2.2.1 _ _ _ _ _ hfc hc r (List.mem_of_find?_eq_some hrule)).1
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact Expr.occDeep_getAppArgs happ _ (List.mem_of_mem_take hx)
            · exact Expr.occDeep_getAppArgs hmaj _ (List.mem_of_mem_drop hx)
        · exact happ
      | proj sn i pe =>
        simp only [Expr.occDeep] at he
        obtain ⟨e₂, hst, hcase⟩ := whnf_proj_inv h
        have h2 : e₂.occDeep names = false := by
          rcases hst with ⟨-, hpe⟩ | ⟨-, hpe⟩
          · exact ihCore hpe he
          · exact ihLoop hpe he
        rcases hcase with rfl | ⟨m, hr, hm⟩
        · simpa [Expr.occDeep] using he
        · exact ihCore hm (reduceProjCore_pres (fun x => x.occDeep names = false)
            Expr.occDeep_getAppArgs ihLoop
            (fun s hs => strLitToConstructor_occDeep hN hs s) hr h2)
    · -- whnf: the loop's own step budget
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          e.occDeep names = false → e'.occDeep names = false := by
        intro n
        induction n with
        | zero => intro _ _ _ h _; exact nomatch h
        | succ n ihN =>
          intro d e e' h he
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have h1 := ihCore hwc he
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
          · refine ihN hcont ?_
            rcases reduceNat_inv_bool hrn with ⟨k, rfl⟩ | ⟨bn, rfl, hbn, hst⟩
            · rfl
            · obtain ⟨ht, hf⟩ := hN.2.2.2.2.2.2.2.2 hst
              rcases hbn with rfl | rfl
              · exact Expr.occDeep_const ht
              · exact Expr.occDeep_const hf
          · exact ihN hcont (unfoldDefinition_occDeep hN hu h1)
          · exact h1
      intro d e e' h he
      exact hloop whnfLoopFuel h he
    · -- inferTypeCore
      intro d e t h he
      cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
    | fvar idx ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        simpa [Expr.occDeep] using he
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          revert h
          split
          · intro h
            simp only [Except.ok.injEq] at h
            subst h
            rw [Expr.occDeep_instantiateLevelParams]
            exact hN.1 n ci hf (by simpa [Expr.occDeep] using he)
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue hs =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h
          exact Expr.occDeep_const (hN.2.2.2.2.2.2.2.1 hs).1
      case natCase =>
        dsimp only [inferBody, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue hs =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h
          exact Expr.occDeep_const (hN.2.2.2.2.2.2.1 hs)
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ := inferTypeCore_forall_inv h
      rfl
    | lam ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, -, rfl⟩ := inferTypeCore_lam_inv h
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at he ⊢
      have hbo := Expr.occDeep_instantiate1 (v := .fvar d ty) (by simpa [Expr.occDeep] using he.1)
        body 0 he.2
      exact ⟨he.1, Expr.occDeep_abstract1 d bt 0 (ihInf hbt hbo)⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ := inferTypeCore_app_inv h
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at he
      have hPi := ihLoop hwh (ihInf htf he.1)
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at hPi
      exact Expr.occDeep_instantiate1 he.2 body' 0 hPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCore_proj_inv h
      simp only [Expr.occDeep] at he
      have hte' := ihLoop hwt (ihInf hte he)
      exact projEntry_typeAt_occDeep hN hfp us hlen (Expr.occDeep_getAppArgs hte') he
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCore_letE_inv h).elim
    · -- inferTypeCoreIO
      intro d e t h he
      cases e with
    | sort u =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
    | fvar idx ty =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        simpa [Expr.occDeep] using he
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCoreIO_succ] at h
      simp only [inferBodyIO, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          revert h
          split
          · intro h
            simp only [Except.ok.injEq] at h
            subst h
            rw [Expr.occDeep_instantiateLevelParams]
            exact hN.1 n ci hf (by simpa [Expr.occDeep] using he)
          · intro h; exact nomatch h
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCoreIO_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBodyIO, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue hs =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h
          exact Expr.occDeep_const (hN.2.2.2.2.2.2.2.1 hs).1
      case natCase =>
        dsimp only [inferBodyIO, Bind.bind, Except.bind, pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue hs =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h
          exact Expr.occDeep_const (hN.2.2.2.2.2.2.1 hs)
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, -, rfl⟩ := inferTypeCoreIO_forall_inv h
      rfl
    | lam ty body m =>
      obtain ⟨bt, hbt, -, -, rfl⟩ := inferTypeCoreIO_lam_inv h
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at he ⊢
      have hbo := Expr.occDeep_instantiate1 (v := .fvar d ty) (by simpa [Expr.occDeep] using he.1)
        body 0 he.2
      exact ⟨he.1, Expr.occDeep_abstract1 d bt 0 (ihIO hbt hbo)⟩
    | app f a =>
      obtain ⟨tf, ty', body', m', htf, hwh, rfl, -⟩ := inferTypeCoreIO_app_inv h
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at he
      have hPi := ihLoop hwh (ihIO htf he.1)
      simp only [Expr.occDeep, Bool.or_eq_false_iff] at hPi
      exact Expr.occDeep_instantiate1 he.2 body' 0 hPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hlen,
        hus, -, rfl, -⟩ := inferTypeCoreIO_proj_inv h
      simp only [Expr.occDeep] at he
      have hte' := ihLoop hwt (ihIO hte he)
      exact projEntry_typeAt_occDeep hN hfp us hlen (Expr.occDeep_getAppArgs hte') he
    | bvar i =>
      rw [inferTypeCoreIO_succ] at h
      simp [inferBodyIO, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE t' v' b' =>
      exact (inferTypeCoreIO_letE_inv h).elim

/-- **Part 1: `whnf` introduces no member constant** (annotations
included). -/
theorem whnf_occDeep {env : Env} {names : List Name} (hN : WhnfNamesFree env names)
    (fuel : Nat) {d : Nat} {e w : Expr} (h : whnf mode env fuel d e = .ok w)
    (he : e.occDeep names = false) : w.occDeep names = false :=
  (whnfPres_occDeep hN fuel).2.1 h he

/-- Part 1 at the walk's occurrence test.  The input premise must see the
annotations (`occDeep`): with `e.nestOcc names 0 0 = false` alone the
claim is FALSE — the structure-η rescue at a projection-FUNCTION
structure (`etaProjs`' non-table branch) copies the parameters of the
stuck major's INFERRED type, i.e. of a free variable's annotation, into
the reduct (`S.proj.j.{us} p⃗ x`), and those parameters need only be
defeq (e.g. proof-irrelevantly) to the member-free ones the recursor
application carries. -/
theorem whnf_nestOcc_zero {env : Env} {names : List Name} (hN : WhnfNamesFree env names)
    (fuel : Nat) {d : Nat} {e w : Expr} (h : whnf mode env fuel d e = .ok w)
    (he : e.occDeep names = false) : w.nestOcc names 0 0 = false :=
  Expr.nestOcc_zero_of_occDeep _ (whnf_occDeep hN fuel h he)


/-! ## Part 2: the walk's normal form -/

/-- What the walk's judgments say about member constants: a field's
normal form, and a telescope's normal-form domains and result, are
member-free when the walked term is (annotations included).  The
frame, constructor-list and seed judgments contribute no output. -/
@[expose] def PosJ.NfFree (names : List Name) : PosJ → Prop
  | .field _ _ _ e _ nf => e.occDeep names = false → nf.occDeep names = false
  | .tele _ _ _ _ cur _ nds res => cur.occDeep names = false →
      (∀ p ∈ nds, p.1.occDeep names = false) ∧ res.occDeep names = false
  | _ => True

/-- **Every judgment of the positivity derivation keeps member constants
out of its normal form.** -/
theorem posD_nfFree {env : Env} {ctx : NestCtx} {F : Nat}
    (hN : WhnfNamesFree env ctx.names) {j : PosJ} {ts : List PosTree}
    (hd : PosD (fueledOps mode F) env ctx j ts) : j.NfFree ctx.names := by
  induction hd with
  | const hw _ =>
    intro he
    split
    · exact whnf_occDeep hN F hw he
    · exact he
  | pi hw _ _ _ ihb =>
    intro he
    have hw' := whnf_occDeep hN F hw he
    simp only [Expr.occDeep, Bool.or_eq_false_iff] at hw' ⊢
    refine ⟨hw'.1, Expr.occDeep_abstract1 _ _ 0 (ihb ?_)⟩
    exact Expr.occDeep_instantiate1 (by simpa [Expr.occDeep] using hw'.1) _ 0 hw'.2
  | hole hw => intro he; exact whnf_occDeep hN F hw he
  | frameHole hw => intro he; exact whnf_occDeep hN F hw he
  | contNew hw => intro he; exact whnf_occDeep hN F hw he
  | contHit hw => intro he; exact whnf_occDeep hN F hw he
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil => intro he; exact ⟨fun p hp => (nomatch hp), he⟩
  | teleCons _ _ iha ihb =>
    intro he
    simp only [Expr.occDeep, Bool.or_eq_false_iff] at he
    obtain ⟨hnds, hres⟩ := ihb (Expr.occDeep_instantiate1
      (by simpa [Expr.occDeep] using he.1) _ 0 he.2)
    refine ⟨?_, hres⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact iha he.1
    · exact hnds p hp
  | seed => trivial

/-- Closing a telescope of member-free domains over a member-free body. -/
theorem closeTelescope_occDeep {names : List Name} :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) {body : Expr},
      (∀ p ∈ nds, p.1.occDeep names = false) → body.occDeep names = false →
      (closeTelescope nds i body).occDeep names = false
  | [], _, _, _, hb => hb
  | (dom, bm) :: bs, i, body, hn, hb => by
    simp only [closeTelescope, Expr.occDeep, Bool.or_eq_false_iff]
    exact ⟨hn _ List.mem_cons_self, Expr.occDeep_abstract1 i _ 0
      (closeTelescope_occDeep bs (i + 1) (fun p hp => hn p (List.mem_cons_of_mem _ hp)) hb)⟩

/-- **Part 2: a member constructor's walked normal form names no member
constant** (annotations included), when its crest names none. -/
theorem memberCtorD_occDeep {env : Env} {ctx : NestCtx} {F nF : Nat} {crest : Expr}
    {ks : List NestFieldKind} {tyN : Expr} {ts : List PosTree}
    (hN : WhnfNamesFree env ctx.names)
    (hd : MemberCtorD (fueledOps mode F) env ctx nF crest ks tyN ts)
    (hcrest : crest.occDeep ctx.names = false) :
    tyN.occDeep ctx.names = false := by
  obtain ⟨nds, cur, ht, rfl, -⟩ := hd
  obtain ⟨hnds, hcur⟩ := posD_nfFree hN ht hcrest
  exact closeTelescope_occDeep nds _ hnds hcur

/-- Part 2, at the positivity walk's own occurrence test. -/
theorem memberCtorD_nestOcc_zero {env : Env} {ctx : NestCtx} {F nF : Nat} {crest : Expr}
    {ks : List NestFieldKind} {tyN : Expr} {ts : List PosTree}
    (hN : WhnfNamesFree env ctx.names)
    (hd : MemberCtorD (fueledOps mode F) env ctx nF crest ks tyN ts)
    (hcrest : crest.occDeep ctx.names = false) :
    tyN.nestOcc ctx.names 0 0 = false :=
  Expr.nestOcc_zero_of_occDeep _ (memberCtorD_occDeep hN hd hcrest)


/-! ### The crest's premise, from the kernel's data

The walk's crest is the stored constructor type (free-variable-free)
canonically abstracted (`nestCanonCrest`: placeholders and holes are
variables annotated `Sort 0`), with the key's parameters and the holes
put in (`nestCrest`).  So the canonical crest's annotations are member-free
by construction, the uniform check's `nestOcc` makes it member-free
outright, and the replacement brings in only the parameters and holes. -/

/-- A member constant inside a free-variable annotation. -/
@[expose] def Expr.annOcc (names : List Name) : Expr → Bool
  | .fvar _ ty => ty.occDeep names
  | .app f a => annOcc names f || annOcc names a
  | .lam ty body _ => annOcc names ty || annOcc names body
  | .forallE ty body _ => annOcc names ty || annOcc names body
  | .letE ty val body => annOcc names ty || annOcc names val || annOcc names body
  | .proj _ _ sub => annOcc names sub
  | _ => false

theorem Expr.occDeep_of_nestOcc_annOcc {names : List Name} :
    ∀ (e : Expr), e.nestOcc names 0 0 = false → e.annOcc names = false →
      e.occDeep names = false := by
  intro e
  induction e with
  | fvar i ty _ => intro _ ha; exact ha
  | const n us => intro h _; simpa [Expr.occDeep, Expr.nestOcc] using h
  | app f a ihf iha =>
    intro h ha
    simp only [Expr.nestOcc, Expr.annOcc, Expr.occDeep, Bool.or_eq_false_iff] at h ha ⊢
    exact ⟨ihf h.1 ha.1, iha h.2 ha.2⟩
  | lam t b mm iht ihb =>
    intro h ha
    simp only [Expr.nestOcc, Expr.annOcc, Expr.occDeep, Bool.or_eq_false_iff] at h ha ⊢
    exact ⟨iht h.1 ha.1, ihb h.2 ha.2⟩
  | forallE t b mm iht ihb =>
    intro h ha
    simp only [Expr.nestOcc, Expr.annOcc, Expr.occDeep, Bool.or_eq_false_iff] at h ha ⊢
    exact ⟨iht h.1 ha.1, ihb h.2 ha.2⟩
  | letE t v b iht ihv ihb =>
    intro h ha
    simp only [Expr.nestOcc, Expr.annOcc, Expr.occDeep, Bool.or_eq_false_iff] at h ha ⊢
    exact ⟨⟨iht h.1.1 ha.1.1, ihv h.1.2 ha.1.2⟩, ihb h.2 ha.2⟩
  | proj s j e ih =>
    intro h ha
    simp only [Expr.nestOcc, Expr.annOcc, Expr.occDeep] at h ha ⊢
    exact ih h ha
  | _ => intro _ _; rfl

theorem Expr.annOcc_of_hasFvar {names : List Name} :
    ∀ (e : Expr), e.hasFvar = false → e.annOcc names = false := by
  intro e
  induction e with
  | fvar i ty _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h; simp only [Expr.hasFvar, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b mm iht ihb =>
    intro h; simp only [Expr.hasFvar, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b mm iht ihb =>
    intro h; simp only [Expr.hasFvar, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.hasFvar, Expr.annOcc] at h ⊢; exact ih h
  | _ => intro _; rfl

theorem Expr.annOcc_instantiate1 {names : List Name} {v : Expr}
    (hv : v.annOcc names = false) :
    ∀ (e : Expr) (k : Nat), e.annOcc names = false →
      (e.instantiate1 v k).annOcc names = false := by
  intro e
  induction e with
  | bvar j =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | app f a ihf iha =>
    intro k h; simp only [Expr.annOcc, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b mm iht ihb =>
    intro k h; simp only [Expr.annOcc, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | forallE t b mm iht ihb =>
    intro k h; simp only [Expr.annOcc, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht k h.1, ihb _ h.2⟩
  | letE t val b iht ihv ihb =>
    intro k h; simp only [Expr.annOcc, Expr.instantiate1, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb _ h.2⟩
  | proj s j e ih => intro k h; simp only [Expr.annOcc, Expr.instantiate1] at h ⊢; exact ih k h
  | _ => intro k h; exact h

theorem annOcc_instPisWith {names : List Name} :
    ∀ (args : List Expr) (e r : Expr), (∀ a ∈ args, a.annOcc names = false) →
      e.annOcc names = false → instPisWith args e = some r → r.annOcc names = false
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h
    exact h ▸ he
  | a :: as, .forallE d b bm, r, ha, he, h => by
    simp only [instPisWith] at h
    simp only [Expr.annOcc, Bool.or_eq_false_iff] at he
    exact annOcc_instPisWith as _ r (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (Expr.annOcc_instantiate1 (ha a List.mem_cons_self) b 0 he.2) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar .., _, _, _, h
  | _ :: _, .sort _, _, _, _, h | _ :: _, .const .., _, _, _, h
  | _ :: _, .app .., _, _, _, h | _ :: _, .lam .., _, _, _, h
  | _ :: _, .letE .., _, _, _, h | _ :: _, .lit _, _, _, _, h
  | _ :: _, .proj .., _, _, _, h => by simp [instPisWith] at h

theorem Expr.annOcc_replaceApps {names : List Name} {f : Name → List Level → Option Expr}
    {b n : Nat} (hf : ∀ c us x, f c us = some x → x.annOcc names = false) :
    ∀ (e : Expr), e.annOcc names = false → (e.replaceApps f b n).annOcc names = false := by
  have himg : ∀ (e x : Expr), e.appHole? f b n = some x → x.annOcc names = false := by
    intro e x h
    simp only [Expr.appHole?, Option.bind_eq_some_iff] at h
    obtain ⟨p, -, hp⟩ := h
    exact hf _ _ _ hp
  intro e
  induction e with
  | app a x iha ihx =>
    intro h
    simp only [Expr.replaceApps]
    cases hh : (Expr.app a x).appHole? f b n with
    | some y => exact himg _ _ hh
    | none =>
      simp only [Option.getD_none, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | const c us =>
    intro _
    simp only [Expr.replaceApps]
    cases hh : (Expr.const c us).appHole? f b n with
    | some y => exact himg _ _ hh
    | none => rfl
  | lam t body mm iht ihb =>
    intro h; simp only [Expr.replaceApps, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t body mm iht ihb =>
    intro h; simp only [Expr.replaceApps, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb =>
    intro h; simp only [Expr.replaceApps, Expr.annOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.replaceApps, Expr.annOcc] at h ⊢; exact ih h
  | bvar _ => intro h; exact h
  | fvar _ _ => intro h; exact h
  | sort _ => intro h; exact h
  | lit _ => intro h; exact h

/-- The canonical crest's annotations are `Sort 0`: member-free. -/
theorem nestCanonCrest_annOcc {names : List Name} {us : List Level} {n : Nat}
    {cty A : Expr} (hcty : cty.hasFvar = false) (h : nestCanonCrest names us n cty = some A) :
    A.annOcc names = false := by
  unfold nestCanonCrest at h
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
  refine Expr.annOcc_replaceApps ?_ B ?_
  · intro c vs x hx
    unfold nestCanonSub at hx
    split at hx
    · obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hx
      rfl
    · exact nomatch hx
  · refine annOcc_instPisWith (nestPhs n) cty B ?_ (Expr.annOcc_of_hasFvar cty hcty) hB
    intro a ha
    simp only [nestPhs, List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    rfl

theorem Expr.occDeep_replaceFVars {names : List Name} {f : Nat → Option Expr}
    (hf : ∀ i x, f i = some x → x.occDeep names = false) :
    ∀ (e : Expr), e.occDeep names = false → (e.replaceFVars f).occDeep names = false := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro h
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | some x => exact hf i x hi
    | none => exact h
  | app a x iha ihx =>
    intro h; simp only [Expr.replaceFVars, Expr.occDeep, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iha h.1, ihx h.2⟩
  | lam t body mm iht ihb =>
    intro h; simp only [Expr.replaceFVars, Expr.occDeep, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t body mm iht ihb =>
    intro h; simp only [Expr.replaceFVars, Expr.occDeep, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb =>
    intro h; simp only [Expr.replaceFVars, Expr.occDeep, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.replaceFVars, Expr.occDeep] at h ⊢; exact ih h
  | _ => intro h; exact h

/-- **The crest premise, from the kernel's data**: a stored (free-variable
free) constructor type whose canonical crest passed the uniform check's
`nestOcc`, put in at member-free parameters and holes, is member-free
(annotations included). -/
theorem nestCrest_occDeep {names : List Name} {us : List Level} {ds holes : List Expr}
    {cty crest A : Expr} (hc : nestCrest names us ds holes cty = some crest)
    (hcty : cty.hasFvar = false) (hA : nestCanonCrest names us ds.length cty = some A)
    (hAocc : A.nestOcc names 0 0 = false)
    (hds : ∀ x ∈ ds, x.occDeep names = false) (hholes : ∀ x ∈ holes, x.occDeep names = false) :
    crest.occDeep names = false := by
  unfold nestCrest at hc
  rw [hA] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  subst hc
  refine Expr.occDeep_replaceFVars ?_ A
    (Expr.occDeep_of_nestOcc_annOcc A hAocc (nestCanonCrest_annOcc hcty hA))
  intro i x hx
  unfold nestKeyMap at hx
  split at hx
  · exact hds x (List.mem_of_getElem? hx)
  · exact hholes x (List.mem_of_getElem? hx)


/-- The crest premise at the ROOT frame: a stored constructor that passed
the uniform check (`nestUniformOk`), at member-free canonical parameters
and holes. -/
theorem rootCrest_occDeep {ctx : NestCtx} {cv : ConstantVal} {holes : List Expr}
    {crest : Expr} (hu : nestUniformOk ctx cv = true) (hcty : cv.type.hasFvar = false)
    (hlen : ctx.params.length = ctx.nP)
    (hc : nestCrest ctx.names (ctx.lps.map .param) ctx.params holes
      (cv.type.instantiateLevelParams cv.levelParams (ctx.lps.map .param)) = some crest)
    (hds : ∀ x ∈ ctx.params, x.occDeep ctx.names = false)
    (hholes : ∀ x ∈ holes, x.occDeep ctx.names = false) :
    crest.occDeep ctx.names = false := by
  obtain ⟨A, hA, hAocc⟩ := nestRootCanon_nestOcc_zero hu
  unfold nestRootCanon at hA
  rw [← hlen] at hA
  exact nestCrest_occDeep hc (by rw [hasFvar_instantiateLevelParams]; exact hcty) hA hAocc
    hds hholes

/-! ## Part 3: the formers' environment -/

theorem piResult_of_stripPis_sort' :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {s : Level},
      e.stripPis n = some (bs, .sort s) → e.piResult = .sort s
  | 0, e, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]; rfl
  | n + 1, e, bs, s, h => by
    match e with
    | .forallE ty b m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', r⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      show b.piResult = _
      exact piResult_of_stripPis_sort' n hr
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [Expr.stripPis])

/-- A term whose constants all resolve before the block names no member. -/
theorem Expr.occDeep_of_constsResolve {env : Env} {names : List Name}
    (hfresh : ∀ n ∈ names, env.find? n = none) :
    ∀ (e : Expr), e.constsResolve env = true → e.occDeep names = false := by
  intro e
  induction e with
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h
    simp only [Expr.occDeep]
    cases hc : names.contains n with
    | false => rfl
    | true =>
      have hm : n ∈ names := by simpa using hc
      rw [hfresh n hm] at h
      exact nomatch h
  | fvar i ty ih => intro h; exact ih h
  | app f a ihf iha =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.occDeep, ihf h.1, iha h.2, Bool.or_self]
  | lam t b mm iht ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.occDeep, iht h.1, ihb h.2, Bool.or_self]
  | forallE t b mm iht ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.occDeep, iht h.1, ihb h.2, Bool.or_self]
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.occDeep, iht h.1.1, ihv h.1.2, ihb h.2, Bool.or_self]
  | proj s j e ih =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact ih h.2
  | _ => intro _; rfl


/-! ### The string-support declarations' result types are no sorts -/

theorem stringOfListTyOk_inv {ci : ConstantInfo} (h : stringOfListTyOk (some ci) = true) :
    ∃ l1 us1 mb, ci.toConstantVal.type =
      .forallE (.app (.const l1 us1) (.const charName [])) (.const stringName []) mb := by
  simp only [stringOfListTyOk, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i l1 us1 c1 c2 mb heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨-, -⟩, rfl⟩, rfl⟩ := h
    exact ⟨l1, us1, mb, heq⟩
  · exact nomatch h

theorem charOfNatTyOk_inv {ci : ConstantInfo} (h : charOfNatTyOk (some ci) = true) :
    ∃ mb, ci.toConstantVal.type = .forallE (.const natName []) (.const charName []) mb := by
  simp only [charOfNatTyOk, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i c1 c2 mb heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨mb, heq⟩
  · exact nomatch h

theorem listNilTyOk_piResult {ci : ConstantInfo} (h : listNilTyOk (some ci) = true) :
    ∀ s, ci.toConstantVal.type.piResult ≠ .sort s := by
  simp only [listNilTyOk] at h
  split at h
  · split at h
    · rename_i heq
      intro s
      rw [heq]
      simp [Expr.piResult]
    · exact nomatch h
  · exact nomatch h

theorem listConsTyOk_piResult {ci : ConstantInfo} (h : listConsTyOk (some ci) = true) :
    ∀ s, ci.toConstantVal.type.piResult ≠ .sort s := by
  simp only [listConsTyOk] at h
  split at h
  · split at h
    · rename_i heq
      intro s
      rw [heq]
      simp [Expr.piResult]
    · exact nomatch h
  · exact nomatch h

/-- **Part 3: `WhnfNamesFree` at the formers' environment.**  `envI` is
the block's formers (members `names`, stored as `indInfo`s whose types
are syntactic telescopes ending in a sort) consed onto a pre-block
`env`: fresh there, and `envI` agrees with `env` off the members.  Three
facts about the pre-block environment are needed beyond `EnvWF`, each
an install-time invariant of the checker's environments:

* `hproj`: no member is named like a projection function
  (`checkConstantVal` rejects `Name.isProjFnShape`);
* `hRecEta`: a set η-rescue bit is the store's verdict (the η part of
  `RecCtorsStored`, `ConLeche/Verify/EnvPreds.lean`);
* `hBool`: `Nat.beq`/`Nat.ble` are stored only with the `Bool`
  constructors (`natOpGuard` at the operation's install). -/
theorem whnfNamesFree_formers {env envI : Env} (hwf : EnvWF env)
    {cvTas : List ConstantVal} {names : List Name}
    (hnames : ∀ n, n ∈ names ↔ ∃ cvTb ∈ cvTas, cvTb.name = n)
    (hfindM : ∀ cvTb ∈ cvTas, (∃ caps, envI.find? cvTb.name = some (.indInfo cvTb caps)) ∧
      ∃ k bs s, cvTb.type.stripPis k = some (bs, .sort s))
    (hfresh : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none)
    (hI : ∀ n, (∀ cvTb ∈ cvTas, cvTb.name ≠ n) → envI.find? n = env.find? n)
    (hproj : ∀ n ∈ names, n.isProjFnShape = false)
    (hRecEta : ∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, r.eta = true → recRuleEtaOf env.find? n r.ctor = true)
    (hBool : natOpStored env natBeqName = true ∨ natOpStored env natBleName = true →
      (env.find? boolTrueName).isSome = true ∧ (env.find? boolFalseName).isSome = true) :
    WhnfNamesFree envI names := by
  -- a member: an `indInfo` of `envI` whose type ends in a sort, fresh in `env`
  have hmem : ∀ n ∈ names, ∃ cvTb caps s, envI.find? n = some (.indInfo cvTb caps) ∧
      cvTb.type.piResult = .sort s ∧ env.find? n = none := by
    intro n hn
    obtain ⟨cvTb, hcv, rfl⟩ := (hnames n).mp hn
    obtain ⟨⟨caps, hf⟩, k, bs, s, hs⟩ := hfindM cvTb hcv
    exact ⟨cvTb, caps, s, hf, piResult_of_stripPis_sort' k hs, hfresh cvTb hcv⟩
  have hmemE : ∀ n ∈ names, env.find? n = none := fun n hn => by
    obtain ⟨-, -, -, -, -, h⟩ := hmem n hn
    exact h
  have hnon : ∀ n, n ∉ names → envI.find? n = env.find? n := fun n hn =>
    hI n (fun cvTb hcv h => hn ((hnames n).mpr ⟨cvTb, hcv, h⟩))
  have hold : ∀ n, (env.find? n).isSome = true → n ∉ names := by
    intro n hs hn
    rw [hmemE n hn] at hs
    exact nomatch hs
  -- a constant of `envI` whose type ends in no sort is no member
  have hnotSort : ∀ n ci, envI.find? n = some ci →
      (∀ s, ci.toConstantVal.type.piResult ≠ .sort s) → n ∉ names := by
    intro n ci hf hs hn
    obtain ⟨cvTb, caps, s, hf', hsort, -⟩ := hmem n hn
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    exact hs s hsort
  -- a constant of `envI` other than an inductive is no member
  have hnotInd : ∀ n ci, envI.find? n = some ci → (∀ cv caps, ci ≠ .indInfo cv caps) →
      n ∉ names := by
    intro n ci hf hs hn
    obtain ⟨cvTb, caps, s, hf', -, -⟩ := hmem n hn
    rw [hf] at hf'
    exact hs _ _ (Option.some.inj hf')
  have hres : ∀ e : Expr, e.constsResolve env = true → e.occDeep names = false :=
    Expr.occDeep_of_constsResolve hmemE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stored types
    intro n ci hf hn
    rw [hnon n hn] at hf
    exact hres _ (hwf ci (find?_mem hf)).2.2.1
  · -- definition values
    intro n cv v hint hf hn
    rw [hnon n hn] at hf
    exact hres _ ((hwf _ (find?_mem hf)).2.2.2.2.1 cv v hint rfl).2.2.1
  · -- recursor rules
    intro n cv mI rP rules hf hn r hr
    rw [hnon n hn] at hf
    refine ⟨hres _ ((hwf _ (find?_mem hf)).2.2.2.2.2.1 cv mI rP rules rfl r hr).2.2.1, ?_⟩
    intro heta
    obtain ⟨cvj, cnP, cnF, T, us, cvT, caps, h1, h2, h3, h4, h5, h6, h7⟩ :=
      recRuleEtaOf_inv (hRecEta n cv mI rP rules hf r hr heta)
    refine recRuleEtaOf_of (f := envI.find?) (cnP := cnP) (cnF := cnF) ?_ h2 ?_ h4 h5 h6 h7
    · rw [hnon _ (hold _ (by rw [h1]; rfl))]; exact h1
    · rw [hnon _ (hold _ (by rw [h3]; rfl))]; exact h3
  · -- projection-table bodies
    intro T i entry hfp
    obtain ⟨tbl, hft, hi, rfl⟩ := Env.findProj?_some hfp
    have hnm : projTableName T ∉ names :=
      hnotInd _ _ hft (fun cv caps h => nomatch h)
    rw [hnon _ hnm] at hft
    obtain ⟨hsz, hb⟩ := (hwf _ (find?_mem hft)).2.2.2.2.2.2.1 tbl rfl
    have hlt : i < tbl.bodies.size := hsz ▸ hi
    have hget : tbl.bodies[i]? = some (tbl.bodies.getD i default) := by
      rw [Array.getElem?_eq_getElem hlt, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hlt]
      rfl
    exact hres _ (hb i _ hget).2.2.1
  · -- constructors
    intro c cv nP nF hf
    exact hnotInd c _ hf (fun cv' caps h => nomatch h)
  · -- projection-function names
    intro T j hn
    have := hproj _ hn
    simp [projFnName, Name.isProjFnShape] at this
  · -- `Nat`
    intro hs
    obtain ⟨-, -, cv0, i0, j0, -, -, -, -, h0, -, -, -, -, -, hty0, -⟩ := natLitSupported_inv hs
    have hz : natZeroName ∉ names := hnotInd _ _ h0 (fun cv caps h => nomatch h)
    rw [hnon _ hz] at h0
    have hr := (hwf _ (find?_mem h0)).2.2.1
    change cv0.type.constsResolve env = true at hr
    rw [hty0] at hr
    exact hold _ (by simpa [Expr.constsResolve] using hr)
  · -- the string-support names
    intro hs
    simp only [strLitSupported, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hO⟩, -⟩, hNil⟩, hCons⟩, -⟩, hCO⟩ := hs
    obtain ⟨ciO, hfO⟩ : ∃ ci, envI.find? stringOfListName = some ci := by
      cases h : envI.find? stringOfListName with
      | none => rw [h] at hO; exact nomatch hO
      | some ci => exact ⟨ci, rfl⟩
    rw [hfO] at hO
    obtain ⟨l1, us1, mb, htyO⟩ := stringOfListTyOk_inv hO
    have hO' : stringOfListName ∉ names :=
      hnotSort _ _ hfO (fun s => by rw [htyO]; simp [Expr.piResult])
    obtain ⟨ciC, hfC⟩ : ∃ ci, envI.find? charOfNatName = some ci := by
      cases h : envI.find? charOfNatName with
      | none => rw [h] at hCO; exact nomatch hCO
      | some ci => exact ⟨ci, rfl⟩
    rw [hfC] at hCO
    obtain ⟨mbC, htyC⟩ := charOfNatTyOk_inv hCO
    have hCO' : charOfNatName ∉ names :=
      hnotSort _ _ hfC (fun s => by rw [htyC]; simp [Expr.piResult])
    have hNil' : listNilName ∉ names := by
      cases h : envI.find? listNilName with
      | none => rw [h] at hNil; exact nomatch hNil
      | some ci => rw [h] at hNil; exact hnotSort _ _ h (listNilTyOk_piResult hNil)
    have hCons' : listConsName ∉ names := by
      cases h : envI.find? listConsName with
      | none => rw [h] at hCons; exact nomatch hCons
      | some ci => rw [h] at hCons; exact hnotSort _ _ h (listConsTyOk_piResult hCons)
    -- `String.ofList : List Char → String` is older than the block, and
    -- so are the `String` and `Char` it mentions
    rw [hnon _ hO'] at hfO
    have hrO := (hwf _ (find?_mem hfO)).2.2.1
    rw [htyO] at hrO
    simp only [Expr.constsResolve, Bool.and_eq_true] at hrO
    exact ⟨hold _ hrO.2, hO', hNil', hCons', hold _ hrO.1.2, hCO'⟩
  · -- the `Bool` constructors
    intro hst
    have hE : natOpStored env natBeqName = true ∨ natOpStored env natBleName = true := by
      have key : ∀ c, natOpStored envI c = true → natOpStored env c = true := by
        intro c hc
        unfold natOpStored at hc ⊢
        cases h : envI.find? c with
        | none => rw [h] at hc; exact nomatch hc
        | some ci =>
          rw [h] at hc
          have hcn : c ∉ names := hnotInd _ _ h (fun cv caps he => by
            subst he; exact nomatch hc)
          rw [← hnon c hcn, h]
          exact hc
      rcases hst with h | h
      · exact Or.inl (key _ h)
      · exact Or.inr (key _ h)
    obtain ⟨ht, hf⟩ := hBool hE
    exact ⟨hold _ ht, hold _ hf⟩

end ConLeche
