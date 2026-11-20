module

public import ConLeche.Model.RuleEqsSound
import ConLeche.Verify.Inductives.IotaRead

public section

/-!
# What the checker's ι reading rule means (task #622)

The checker's rule (`ruleReadsB`, `ConLeche/Kernel/Inductives/IotaRead.lean`) makes a rule's ι
equation read off the recursor's type (`iotaEqOf`, the statement's) the one read through its
constructor (`iotaEqAt`, the proofs'), up to the fields' domains: the stored minor premise's are
the constructor's up to equivalent levels (`Expr.lvlEq`) and up to consumed annotations
(`annEq`).  This module turns that into denotations:

* `Denotes_lvlEq`: terms equal up to equivalent levels denote alike;
* `annEq_mem`: where the annotation's applications apply (`AppsApply`, what the invariant's
  grading gives of a stored type), a member of the consumed domain is a member of the annotated
  one — the annotation is the identity on a type (`annIdent`, its definition's own clause);
* `GradedTele`, `gradedTele_of_wd`: a stored type's domains are graded at every fit of the
  earlier ones (the invariant's `type_wellDenotedTy`);
* `fits_annEq`: a fit of the consumed domains is a fit of the annotated ones.
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule Denotes push)
open ConLeche.Term
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V] {cval : Name → (LevelParam → Nat) → V} {env : Env}
  {φ : LevelParam → Nat}

/-- **Terms equal up to equivalent levels denote alike.** -/
theorem Denotes_lvlEq :
    ∀ (s c : Expr) {ρ : Nat → V} {X : V}, s.lvlEq c = true →
      Denotes cval env φ ρ s X → Denotes cval env φ ρ c X := by
  intro s
  induction s with
  | sort u =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    cases hd
    rw [Level.isEquiv_sound h φ]
    exact .sort
  | const n us =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    obtain ⟨rfl, h⟩ := h
    cases hd with
    | const hf hlen =>
      have he := Level.isEquivList_sound h φ
      rw [funext (Level.substFn_of_evalEqList _ he)]
      exact .const hf ((isEquivList_length h).symm.trans hlen)
  | app f a ihf iha =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    cases hd with
    | app hf ha => exact .app (ihf _ h.1 hf) (iha _ h.2 ha)
  | lam t b iht ihb =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    cases hd with
    | lam hA hF => exact .lam (iht _ h.1 hA) fun x hx => ihb _ h.2 (hF x hx)
  | forallE t b iht ihb =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    cases hd with
    | pi hA hB => exact .pi (iht _ h.1 hA) fun x hx => ihb _ h.2 (hB x hx)
  | letE t v b iht ihv ihb =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    cases hd with
    | letE hv hb => exact .letE (ihv _ h.1.2 hv) (ihb _ h.2 hb)
  | proj T i e ihe =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    cases hd with
    | proj_table ht he => exact .proj_table ht (ihe _ h he)
  | bvar _ | fvar _ _ | lit _ =>
    intro c ρ X h hd
    unfold Expr.lvlEq at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h; · exact hd
    cases c <;> simp at h

/-- **Every application of a term's spine applies** (`AppliesTo`), outside binders. -/
@[expose] def AppsApply (cval : Name → (LevelParam → Nat) → V) (env : Env) (φ : LevelParam → Nat)
    (ρ : Nat → V) : Expr → Prop
  | .app f a => (∀ F A, Denotes cval env φ ρ f F → Denotes cval env φ ρ a A → AppliesTo F A) ∧
      AppsApply cval env φ ρ f ∧ AppsApply cval env φ ρ a
  | _ => True

/-- The truth value `true` is a type of every universe, and it is not the point. -/
theorem truthTrue_mem_univ (k : Nat) : (truthVal True : V) ∈ˢ univ k :=
  mem_univ_of_mem_univZero (truthVal_mem_univZero True)

section Ann

variable (hdef : ∀ n cv v hint, env.find? n = some (.defnInfo cv v hint) →
    ∀ ψ ρ, Denotes cval env ψ ρ v (cval n ψ))
  (hmem : ∀ n ci, env.find? n = some ci → ∀ ψ (ρ : Nat → V), ∃ T,
    Denotes cval env ψ ρ ci.toConstantVal.type T ∧ cval n ψ ∈ˢ T)
include hdef hmem

omit hmem in
/-- **An annotation's value**: the reading of `fun (α : Sort p) … => …` at the levels of its
use. -/
theorem ann_value {n : Name} {a : Nat} (hid : annIdent env.find? n a = true) {l : Level}
    {ρ : Nat → V} {Fn : V} (hF : Denotes cval env φ ρ (.const n [l]) Fn) :
    ∃ cv v hint, env.find? n = some (.defnInfo cv v hint) ∧
      annIdentVal env.find? cv.levelParams a v = true ∧
      Denotes cval env (Level.substFn φ cv.levelParams [l]) ρ v Fn := by
  obtain ⟨cv, v, hint, hn, hv⟩ := annIdent_inv hid
  cases hF with
  | const hf hlen =>
    rw [hn] at hf; cases hf
    exact ⟨cv, v, hint, hn, hv, hdef n cv v hint hn _ ρ⟩

/-- **An annotation of arity two applies as the identity**: where its two applications apply,
its application to a type `A` with a member and anything it applies to is `A`. -/
theorem ann2_app {n : Name} (hid : annIdent env.find? n 2 = true) {l : Level} {ρ : Nat → V}
    {Fn A B : V} (hF : Denotes cval env φ ρ (.const n [l]) Fn) (h1 : AppliesTo Fn A)
    (h2 : AppliesTo (app Fn A) B) {x : V} (hx : x ∈ˢ A) : app (app Fn A) B = A := by
  obtain ⟨cv, v, hint, -, hv, hd⟩ := ann_value hdef hid hF
  obtain ⟨p, D, hlp, rfl, hD⟩ := annIdentVal_two_inv hv
  generalize Level.substFn φ cv.levelParams [l] = ψ at hd
  cases hd with
  | lam hA hB =>
    cases hA
    rename_i F0
    -- the inner abstraction at a type `A₀`: over the reading of `D`, constantly `A₀`
    have hinner : ∀ A₀, A₀ ∈ˢ univ (Level.eval ψ (.param p)) → ∃ S : V,
        ((∃ y, y ∈ˢ A₀) → ∃ y, y ∈ˢ S) ∧ F0 A₀ = lamV S fun _ => A₀ := by
      intro A₀ hA₀
      have hb := hB A₀ hA₀
      generalize hZ : F0 A₀ = Z at hb
      cases hb with
      | lam hS hG =>
        rename_i S G
        refine ⟨S, ?_, lamV_congr fun y hy => ?_⟩
        · rcases hD with rfl | hW
          · cases hS; exact id
          · obtain ⟨m, c, rfl, hc, hct, hcl⟩ := annWitness_inv hW
            obtain ⟨T, hT, hcT⟩ := hmem _ c hc ψ (push A₀ ρ)
            rw [hct] at hT
            rw [ConLeche.Denotes_functional hS hT]
            exact fun _ => ⟨_, hcT⟩
        · have := hG y hy
          generalize G y = Z' at this
          cases this; rfl
    have hne : lamV (univ (Level.eval ψ (.param p))) F0 ≠ (pt : V) := by
      refine lamV_ne_pt_of (truthTrue_mem_univ _) ?_
      obtain ⟨S, hS, he⟩ := hinner _ (truthTrue_mem_univ _)
      obtain ⟨y, hy⟩ := hS ⟨pt, pt_mem_truthVal trivial⟩
      rw [he]
      exact lamV_ne_pt_of hy (ne_pt_of_mem_univ (truthTrue_mem_univ 0))
    rw [lamV_eq_graph hne] at h1 h2 ⊢
    have hA := (appliesTo_graph.mp h1).2
    rw [app_graph hA] at h2 ⊢
    obtain ⟨S, hS, he⟩ := hinner A hA
    rw [he] at h2 ⊢
    obtain ⟨y, hy⟩ := hS ⟨x, hx⟩
    have hne' : lamV S (fun _ => A) ≠ (pt : V) := lamV_ne_pt_of hy (ne_pt_of_mem_univ hA)
    rw [lamV_eq_graph hne'] at h2
    have hB' := (appliesTo_graph.mp h2).2
    exact app_lamV hB'

omit hmem in
/-- **An annotation of arity one applies as the identity.** -/
theorem ann1_app {n : Name} (hid : annIdent env.find? n 1 = true) {l : Level} {ρ : Nat → V}
    {Fn A : V} (hF : Denotes cval env φ ρ (.const n [l]) Fn) (h1 : AppliesTo Fn A) :
    app Fn A = A := by
  obtain ⟨cv, v, hint, -, hv, hd⟩ := ann_value hdef hid hF
  obtain ⟨p, hlp, rfl⟩ := annIdentVal_one_inv hv
  generalize Level.substFn φ cv.levelParams [l] = ψ at hd
  cases hd with
  | lam hA hB =>
    cases hA
    rename_i F0
    have hF0 : ∀ y, y ∈ˢ univ (Level.eval ψ (.param p)) → F0 y = y := fun y hy => by
      have := hB y hy
      generalize F0 y = Z at this
      cases this; rfl
    have hne : lamV (univ (Level.eval ψ (.param p))) F0 ≠ (pt : V) :=
      lamV_ne_pt_of (truthTrue_mem_univ _) (by
        rw [hF0 _ (truthTrue_mem_univ _)]
        exact ne_pt_of_mem_univ (truthTrue_mem_univ 0))
    rw [lamV_eq_graph hne] at h1
    have hA := (appliesTo_graph.mp h1).2
    rw [app_lamV hA, hF0 _ hA]

/-- **A member of a domain with annotations consumed is a member of the annotated domain**,
where the annotations' applications apply. -/
theorem annEq_mem {s c : Expr} (h : annEq env.find? s c = true) {ρ : Nat → V}
    (happ : AppsApply cval env φ ρ c) {S C x : V} (hS : Denotes cval env φ ρ s S)
    (hC : Denotes cval env φ ρ c C) (hx : x ∈ˢ S) : x ∈ˢ C := by
  revert h happ hS hC hx S C x
  fun_induction annEq env.find? s c with
  | case1 n l a b ih =>
    intro h happ S C x hS hC hx
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨-, hi⟩, hr⟩
    · rw [ConLeche.Denotes_functional hC (Denotes_lvlEq _ _ h hS)]; exact hx
    · simp only [AppsApply] at happ
      obtain ⟨hab, ⟨hka, -, happa⟩, -⟩ := happ
      cases hC with
      | app hf hb =>
        cases hf with
        | app hk ha =>
          have hxA := ih hr happa hS ha hx
          rw [ann2_app hdef hmem hi hk (hka _ _ hk ha) (hab _ _ (.app hk ha) hb) hxA]
          exact hxA
  | case2 n l a ih =>
    intro h happ S C x hS hC hx
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨-, hi⟩, hr⟩
    · rw [ConLeche.Denotes_functional hC (Denotes_lvlEq _ _ h hS)]; exact hx
    · simp only [AppsApply] at happ
      obtain ⟨hka, -, happa⟩ := happ
      cases hC with
      | app hk ha =>
        rw [ann1_app hdef hi hk (hka _ _ hk ha)]
        exact ih hr happa hS ha hx
  | case3 c h1 h2 =>
    intro h happ S C x hS hC hx
    rw [ConLeche.Denotes_functional hC (Denotes_lvlEq _ _ h hS)]; exact hx

end Ann

/-! ## Graded telescopes -/

/-- **A telescope's domains are graded** (`AppsApply`) at every fit of the earlier ones, for its
first `n` binders. -/
@[expose] def GradedTele (cval : Name → (LevelParam → Nat) → V) (env : Env)
    (φ : LevelParam → Nat) : (Nat → V) → Nat → Expr → Prop
  | _, 0, _ => True
  | ρ, n + 1, .forallE A B => AppsApply cval env φ ρ A ∧
      ∀ x X, Denotes cval env φ ρ A X → x ∈ˢ X → GradedTele cval env φ (push x ρ) n B
  | _, _ + 1, _ => True

section Wd

variable {acval : Name → (Name → Nat) → Term} (hcl : ∀ n ψ, Term.Closed (acval n ψ))
include hcl

/-- **A graded reading's spine applies**: the invariant's `WellDenoted` of a reading gives
`AppsApply` of the read term. -/
theorem appsApply_of_wd {φ : Name → Nat} :
    ∀ (e : Expr) {d : Nat} {ta : Term} {ρ : Nat → V},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      WellDenoted V ρ ta → AppsApply (cvalOf acval) env φ ρ (closeN d e) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro d ta ρ h hfb hlb hwd
    obtain ⟨tf, tx, hf, hx, rfl⟩ := denote_app_inv h
    have hfb' : Expr.fvarsBelow d f ∧ Expr.fvarsBelow d a := hfb
    have hlb' : (f.looseBVarsBounded 0 && a.looseBVarsBounded 0) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    rw [WellDenoted_app] at hwd
    show AppsApply _ _ _ _ (.app (closeN d f) (closeN d a))
    refine ⟨fun F A hF hA => ?_, ihf hf hfb'.1 hlb'.1 hwd.1, iha hx hfb'.2 hlb'.2 hwd.2.1⟩
    rw [ConLeche.Denotes_functional hF (Denotes_of_denote hcl d f hf hfb'.1 hlb'.1 ρ),
      ConLeche.Denotes_functional hA (Denotes_of_denote hcl d a hx hfb'.2 hlb'.2 ρ)]
    exact hwd.2.2
  | fvar i t => intro d ta ρ _ _ _ _; simp [closeN, AppsApply]
  | _ => intro d ta ρ _ _ _ _; simp [closeN, AppsApply]

/-- **A stored type's domains are graded**: the invariant's `WellDenoted` of its reading gives
`GradedTele` of the read type, at every depth. -/
theorem gradedTele_of_wd {φ : Name → Nat} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ta : Term} {ρ : Nat → V},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      WellDenoted V ρ ta → GradedTele (cvalOf acval) env φ ρ n (closeN d e) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; trivial
  | succ n ih =>
    intro e d ta ρ h hfb hlb hwd
    cases e with
    | forallE ty body =>
      obtain ⟨tA, tB, hta, htb, rfl⟩ := denote_forallE_inv h
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      rw [WellDenoted_pi] at hwd
      show GradedTele _ _ _ _ (n + 1) (.forallE (closeN d ty 0) (closeN d body 1))
      refine ⟨appsApply_of_wd hcl ty hta hfb'.1 hlb'.1 hwd.1, fun x X hX hx => ?_⟩
      rw [ConLeche.Denotes_functional hX (Denotes_of_denote hcl d ty hta hfb'.1 hlb'.1 ρ)] at hx
      rw [← Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, push_eq_cons]
      exact ih _ htb (Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) (hwd.2.2.1 x hx)
    | _ => cases n <;> simp [closeN, GradedTele]

end Wd

/-! ## Fits across the two readings -/

/-- **A fit of domains is a fit of domains equal to them up to equivalent levels.** -/
theorem fits_lvlEq : ∀ (ds' ds : List Expr) (b' b : Expr) {ρ ρ' : Nat → V} {vs : List V},
    listRel Expr.lvlEq ds' ds = true → vs.length = ds'.length →
    Fits cval env φ ρ (ds'.foldr .forallE b') vs ρ' b' →
    Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b
  | [], [], b', b, ρ, ρ', vs, _, hl, h => by
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    obtain ⟨rfl, -⟩ := h.nil_inv
    exact .nil
  | d' :: ds', d :: ds, b', b, ρ, ρ', vs, hr, hl, h => by
    simp only [listRel, Bool.and_eq_true] at hr
    match vs, hl, h with
    | x :: vs, hl, .cons hA hx hrest =>
      exact .cons (Denotes_lvlEq _ _ hr.1 hA) hx
        (fits_lvlEq ds' ds b' b hr.2 (by simpa using hl) hrest)
  | [], _ :: _, _, _, _, _, _, hr, _, _ | _ :: _, [], _, _, _, _, _, hr, _, _ => by
    simp [listRel] at hr

section Ann2

variable (hdef : ∀ n cv v hint, env.find? n = some (.defnInfo cv v hint) →
    ∀ ψ ρ, Denotes cval env ψ ρ v (cval n ψ))
  (hmem : ∀ n ci, env.find? n = some ci → ∀ ψ (ρ : Nat → V), ∃ T,
    Denotes cval env ψ ρ ci.toConstantVal.type T ∧ cval n ψ ∈ˢ T)
include hdef hmem

/-- **A fit of domains with annotations consumed is a fit of the annotated domains**, where these
are graded and denote. -/
theorem fits_annEq : ∀ (ds' ds : List Expr) (b' b : Expr) {ρ ρ' : Nat → V} {vs : List V},
    listRel (annEq env.find?) ds' ds = true → vs.length = ds'.length →
    GradedTele cval env φ ρ ds.length (ds.foldr .forallE b) →
    (∀ d ∈ ds, ∀ σ : Nat → V, ∃ X, Denotes cval env φ σ d X) →
    Fits cval env φ ρ (ds'.foldr .forallE b') vs ρ' b' →
    Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b
  | [], [], b', b, ρ, ρ', vs, _, hl, _, _, h => by
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    obtain ⟨rfl, -⟩ := h.nil_inv
    exact .nil
  | d' :: ds', d :: ds, b', b, ρ, ρ', vs, hr, hl, hg, hden, h => by
    simp only [listRel, Bool.and_eq_true] at hr
    match vs, hl, h with
    | x :: vs, hl, .cons hA hx hrest =>
      obtain ⟨C, hC⟩ := hden d List.mem_cons_self ρ
      obtain ⟨happ, hg'⟩ := hg
      have hxC := annEq_mem hdef hmem hr.1 happ hA hC hx
      exact .cons hC hxC (fits_annEq ds' ds b' b hr.2 (by simpa using hl) (hg' x C hC hxC)
        (fun d hd => hden d (List.mem_cons_of_mem _ hd)) hrest)
  | [], _ :: _, _, _, _, _, _, hr, _, _, _, _ | _ :: _, [], _, _, _, _, _, hr, _, _, _, _ => by
    simp [listRel] at hr

end Ann2

/-- A graded telescope does not read its body. -/
theorem gradedTele_rebody : ∀ (ds : List Expr) {b b' : Expr} {ρ : Nat → V} {n : Nat},
    n ≤ ds.length → GradedTele cval env φ ρ n (ds.foldr .forallE b) →
    GradedTele cval env φ ρ n (ds.foldr .forallE b')
  | _, _, _, _, 0, _, _ => trivial
  | d :: ds, b, b', ρ, n + 1, hn, ⟨h1, h2⟩ =>
    ⟨h1, fun x X hX hx => gradedTele_rebody ds (by simp at hn; omega) (h2 x X hX hx)⟩
  | [], _, _, _, _ + 1, hn, _ => absurd hn (by simp)

/-- **A graded telescope stays graded past a fit of its leading binders.** -/
theorem gradedTele_descend : ∀ (ds : List Expr) {b : Expr} {ρ ρ' : Nat → V} {vs : List V}
    {n : Nat}, vs.length = ds.length →
    GradedTele cval env φ ρ (ds.length + n) (ds.foldr .forallE b) →
    Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b → GradedTele cval env φ ρ' n b
  | [], b, ρ, ρ', vs, n, hl, hg, h => by
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    obtain ⟨rfl, -⟩ := h.nil_inv
    simpa using hg
  | d :: ds, b, ρ, ρ', vs, n, hl, hg, h => by
    match vs, hl, h with
    | x :: vs, hl, .cons hA hx hrest =>
      rw [List.length_cons, show ds.length + 1 + n = (ds.length + n) + 1 by omega] at hg
      exact gradedTele_descend ds (by simpa using hl) (hg.2 x _ hA hx) hrest

/-- **Instantiating variables by variables keeps a spine's applications applying.** -/
theorem appsApply_inst {vs : List Expr} {Ys : List V} {σ : Nat → V}
    (hlen : Ys.length = vs.length)
    (hvs : ∀ j (h : j < vs.length), Denotes cval env φ σ vs[j] (Ys[j]'(hlen ▸ h)))
    (hbv : ∀ v ∈ vs, ∃ k, v = .bvar k) :
    ∀ (e : Expr) {d : Nat} {ρ : Nat → V}, (∀ i, ρ (i + d) = σ i) →
      AppsApply cval env φ (insAt d Ys ρ) e →
      AppsApply cval env φ ρ (e.instantiateLift vs d) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro d ρ hρ h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun F A hF hA => h1 F A (Denotes_instantiateLift_inv hlen hvs f hρ hF)
      (Denotes_instantiateLift_inv hlen hvs a hρ hA), ihf hρ h2, iha hρ h3⟩
  | bvar j =>
    intro d ρ hρ _
    unfold Expr.instantiateLift
    split
    · trivial
    · split
      · rename_i _ hj
        obtain ⟨k, hk⟩ := hbv _ (List.getElem_mem hj)
        rw [hk]
        simp only [Expr.liftLooseBVars]
        split <;> trivial
      · trivial
  | _ => intro d ρ _ _; simp [Expr.instantiateLift, AppsApply]

/-- **Instantiating variables by variables keeps a telescope graded.** -/
theorem gradedTele_inst {vs : List Expr} {Ys : List V} {σ : Nat → V}
    (hlen : Ys.length = vs.length)
    (hvs : ∀ j (h : j < vs.length), Denotes cval env φ σ vs[j] (Ys[j]'(hlen ▸ h)))
    (hbv : ∀ v ∈ vs, ∃ k, v = .bvar k) :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ρ : Nat → V}, (∀ i, ρ (i + d) = σ i) →
      GradedTele cval env φ (insAt d Ys ρ) n e →
      GradedTele cval env φ ρ n (e.instantiateLift vs d) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro e d ρ hρ h
    cases e with
    | forallE A B =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨appsApply_inst hlen hvs hbv A hρ h1, fun x X hX hx => ?_⟩
      have hX' := Denotes_instantiateLift_inv hlen hvs A hρ hX
      have := h2 x X hX' hx
      rw [push_insAt] at this
      exact ih B (fun i => by simpa [ConLeche.push, Nat.add_assoc] using hρ i) this
    | bvar j =>
      unfold Expr.instantiateLift
      split
      · trivial
      · split
        · rename_i _ hj
          obtain ⟨k, hk⟩ := hbv _ (List.getElem_mem hj)
          rw [hk]
          simp only [Expr.liftLooseBVars]
          split <;> trivial
        · trivial
    | _ => cases n <;> simp [Expr.instantiateLift, GradedTele]

/-- **A fit of a telescope closed below `k` transfers to any environment agreeing below `k`.** -/
theorem Fits_shift : ∀ (ds : List Expr) (b : Expr) {ρ ρ' σ : Nat → V} {vs : List V} {k : Nat},
    vs.length = ds.length → (∀ i (h : i < ds.length), ds[i].looseBVarsBounded (k + i) = true) →
    (∀ i, i < k → ρ i = σ i) →
    Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b →
    Fits cval env φ σ (ds.foldr .forallE b) vs (consN vs σ) b
  | [], b, ρ, ρ', σ, vs, k, hl, _, _, h => by
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    exact .nil
  | d :: ds, b, ρ, ρ', σ, vs, k, hl, hb, hag, h => by
    match vs, hl, h with
    | x :: vs, hl, .cons hA hx hrest =>
      have hA' := Denotes_congr_below hA (hb 0 (by simp)) hag
      have := Fits_shift ds b (σ := ConLeche.push x σ) (k := k + 1) (by simpa using hl)
        (fun i hi => by
          have := hb (i + 1) (by simpa using hi)
          rw [List.getElem_cons_succ] at this
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact hag i (by omega)) hrest
      rw [consN_cons, push_eq_cons] at *
      exact .cons hA' hx this

/-- A graded telescope is graded on fewer binders. -/
theorem gradedTele_le : ∀ {m n : Nat} {ρ : Nat → V} {T : Expr}, n ≤ m →
    GradedTele cval env φ ρ m T → GradedTele cval env φ ρ n T
  | _, 0, _, _, _, _ => trivial
  | m + 1, n + 1, ρ, .forallE A B, hn, ⟨h1, h2⟩ =>
    ⟨h1, fun x X hX hx => gradedTele_le (by omega) (h2 x X hX hx)⟩
  | m + 1, n + 1, ρ, .bvar _, _, _ | m + 1, n + 1, ρ, .fvar _ _, _, _
  | m + 1, n + 1, ρ, .sort _, _, _ | m + 1, n + 1, ρ, .const _ _, _, _
  | m + 1, n + 1, ρ, .app _ _, _, _ | m + 1, n + 1, ρ, .lam _ _, _, _
  | m + 1, n + 1, ρ, .letE _ _ _, _, _ | m + 1, n + 1, ρ, .lit _, _, _
  | m + 1, n + 1, ρ, .proj _ _ _, _, _ => trivial
  | 0, _ + 1, _, _, hn, _ => absurd hn (by omega)

/-- The first `k` binders of a telescope are its leading domains. -/
theorem stripPis_take {e : Expr} {k j : Nat} {ds : List Expr} {b : Expr}
    (h : e.stripPis k = some (ds, b)) (hj : j ≤ k) :
    e.stripPis j = some (ds.take j, (ds.drop j).foldr .forallE b) := by
  obtain ⟨rfl, hl⟩ := stripPis_eq_foldr k h
  conv => lhs; rw [← List.take_append_drop j ds, List.foldr_append]
  have := stripPis_foldr (ds.take j) ((ds.drop j).foldr .forallE b)
  rwa [List.length_take, Nat.min_eq_left (by omega)] at this

end ConLeche.Model