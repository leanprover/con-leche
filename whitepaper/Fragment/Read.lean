module

public import Fragment.IndSem
public import Fragment.GenScope
public import Fragment.Sound

@[expose] public section

/-!
# Reading the generated terms

The bridge from the *syntax* the checker stores — the generated types
and rules of `Decl.lean`, read by `interp` in the growing model at a
valuation and a base environment — to the *semantic objects* of
`IndSem.lean`, stated at the block's concrete levels in the closed
environment.  Three kinds of facts:

* **Congruence** (`interp_spec`): an expression of the specification
  reads alike in any model agreeing with the old one on the stored
  constants, at any valuation agreeing on the block's level
  parameters, in any two environments agreeing below its depth — so
  the model, the valuation and the base environment can be changed
  freely under the products and abstractions that read them
  (`piCtx_congr₂`, `lamCtx_congr₂`, `FitsVals_congr₂`).
* **The self-certifying application** (`appList_of_wd`): a
  well-denoted application of a graph tower to arguments is the
  tower's body at the arguments, and the arguments fit the tower's
  context — the graph regime determines its domains, so the type
  former and the constructors, whose sets are graph towers, can be
  applied without any typing information about the arguments beyond
  the invariant.
* **Readings** of the contexts the generators build: the field
  context read at parameter values is `FitsFields` (`fits_fieldCtx`),
  the inductive-hypothesis context is `IhTyped`, a minor premise's
  type gives `MinorOk`, and the recursor's context and the rule's read
  as the recursor's semantic value at their values.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Congruence under the specification's scope -/

/-- Two assignments agreeing on the stored constants. -/
def AgreeOn (env : Env) (M M' : Name → List Nat → V) : Prop :=
  ∀ c, (env.find? c).isSome → ∀ ls, M c ls = M' c ls

/-- **An expression of the specification reads alike** in any model
agreeing on the stored constants, at any valuation agreeing on the
level parameters, in any environments agreeing below its depth. -/
theorem interp_spec {env : Env} {ps : List Name} {k : Nat} {e : Expr}
    (he : Expr.Scoped env ps k e) {M M' : Name → List Nat → V} (hM : AgreeOn env M M')
    {φ φ' : Name → Nat} (hφ : ∀ n ∈ ps, φ n = φ' n) {ρ ρ' : Nat → V}
    (hρ : ∀ i, i < k → ρ i = ρ' i) :
    interp M φ ρ e = interp M' φ' ρ' e := by
  obtain ⟨hc, hcs, hl⟩ := he
  rw [interp_closedAt hc hρ, interp_lparams hl hφ]
  exact interp_consts fun c hcc ls => hM c (hcs c hcc) ls

theorem WellDenoted_spec {env : Env} {ps : List Name} {k : Nat} {e : Expr}
    (he : Expr.Scoped env ps k e) {M M' : Name → List Nat → V} (hM : AgreeOn env M M')
    {φ φ' : Name → Nat} (hφ : ∀ n ∈ ps, φ n = φ' n) {ρ ρ' : Nat → V}
    (hρ : ∀ i, i < k → ρ i = ρ' i) :
    WellDenoted M φ ρ e ↔ WellDenoted M' φ' ρ' e := by
  obtain ⟨hc, hcs, hl⟩ := he
  rw [WellDenoted_closedAt hc hρ, WellDenoted_lparams hl hφ]
  exact WellDenoted_consts fun c hcc ls => hM c (hcs c hcc) ls

omit [IndLib V] in
/-- Environments built by pushing the same values agree below the
pushed values' number. -/
theorem consList_agree_lt {vs : List V} {ρ ρ' : Nat → V} :
    ∀ i, i < vs.length → consList vs ρ i = consList vs ρ' i := by
  intro i hi
  rw [consList_lt hi, consList_lt hi]

/-- Domain-wise agreement of two readings of a context **at fitting
prefixes**: each entry reads alike under values fitting the earlier
entries (in the first reading). -/
def CtxAgree (M M' : Name → List Nat → V) (φ φ' : Name → Nat) (ρ ρ' : Nat → V)
    (Γ : List Expr) : Prop :=
  ∀ i A, Γ[i]? = some A → ∀ vs : List V, FitsVals M φ ρ (Γ.drop (i + 1)) vs →
    interp M φ (consList vs ρ) A = interp M' φ' (consList vs ρ') A

theorem CtxAgree_cons {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V}
    {A : Expr} {Γ : List Expr} (h : CtxAgree M M' φ φ' ρ ρ' (A :: Γ)) :
    CtxAgree M M' φ φ' ρ ρ' Γ ∧
      ∀ vs : List V, FitsVals M φ ρ Γ vs →
        interp M φ (consList vs ρ) A = interp M' φ' (consList vs ρ') A := by
  refine ⟨fun i B hB vs hvs => h (i + 1) B (by simpa using hB) vs (by simpa using hvs), ?_⟩
  intro vs hvs
  exact h 0 A rfl vs (by simpa using hvs)

theorem CtxAgree.of_cons {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V}
    {A : Expr} {Γ : List Expr} (hΓ : CtxAgree M M' φ φ' ρ ρ' Γ)
    (hA : ∀ vs : List V, FitsVals M φ ρ Γ vs →
      interp M φ (consList vs ρ) A = interp M' φ' (consList vs ρ') A) :
    CtxAgree M M' φ φ' ρ ρ' (A :: Γ) := by
  intro i B hB vs hvs
  cases i with
  | zero => simp at hB; subst hB; exact hA vs (by simpa using hvs)
  | succ i => exact hΓ i B (by simpa using hB) vs (by simpa using hvs)

theorem FitsVals_congr₂ {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V} :
    ∀ {Γ : List Expr}, CtxAgree M M' φ φ' ρ ρ' Γ →
      ∀ {vs : List V}, FitsVals M φ ρ Γ vs ↔ FitsVals M' φ' ρ' Γ vs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | A :: Γ, h, v :: vs => by
    obtain ⟨hΓ, hA⟩ := CtxAgree_cons h
    rw [FitsVals_cons, FitsVals_cons]
    constructor
    · rintro ⟨hf, hv⟩
      exact ⟨(FitsVals_congr₂ hΓ).mp hf, by rwa [← hA vs hf]⟩
    · rintro ⟨hf, hv⟩
      have hf' := (FitsVals_congr₂ hΓ).mpr hf
      exact ⟨hf', by rwa [hA vs hf']⟩

theorem piCtx_congr₂ {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V} {p : Bool} :
    ∀ {Γ : List Expr}, CtxAgree M M' φ φ' ρ ρ' Γ →
      ∀ {F G : (Nat → V) → V},
        (∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) = G (consList vs ρ')) →
        piCtx M φ p ρ Γ F = piCtx M' φ' p ρ' Γ G
  | [], _, F, G, h => h [] trivial
  | A :: Γ, hΓ, F, G, h => by
    obtain ⟨hΓ', hA⟩ := CtxAgree_cons hΓ
    simp only [piCtx_cons]
    refine piCtx_congr₂ hΓ' fun vs hvs => ?_
    rw [hA vs hvs]
    refine piR_congr fun x hx => ?_
    rw [← consList_cons, ← consList_cons]
    refine h (x :: vs) ⟨hvs, ?_⟩
    rwa [hA vs hvs]

theorem lamCtx_congr₂ {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V} {p : Bool} :
    ∀ {Γ : List Expr}, CtxAgree M M' φ φ' ρ ρ' Γ →
      ∀ {F G : (Nat → V) → V},
        (∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) = G (consList vs ρ')) →
        lamCtx M φ p ρ Γ F = lamCtx M' φ' p ρ' Γ G
  | [], _, F, G, h => h [] trivial
  | A :: Γ, hΓ, F, G, h => by
    obtain ⟨hΓ', hA⟩ := CtxAgree_cons hΓ
    simp only [lamCtx_cons]
    refine lamCtx_congr₂ hΓ' fun vs hvs => ?_
    rw [hA vs hvs]
    refine lamR_congr fun x hx => ?_
    rw [← consList_cons, ← consList_cons]
    refine h (x :: vs) ⟨hvs, ?_⟩
    rwa [hA vs hvs]

/-- Agreement along an appended context: on the right part, then on
the left part under fitting values of the right. -/
theorem CtxAgree_append {M M' : Name → List Nat → V} {φ φ' : Name → Nat} {ρ ρ' : Nat → V}
    {Δ : List Expr} (hΔ : CtxAgree M M' φ φ' ρ ρ' Δ) :
    ∀ {Γ : List Expr}, (∀ ws, FitsVals M φ ρ Δ ws → CtxAgree M M' φ φ' (consList ws ρ) (consList ws ρ') Γ) →
      CtxAgree M M' φ φ' ρ ρ' (Γ ++ Δ)
  | [], _ => hΔ
  | A :: Γ, h => by
    rw [List.cons_append]
    refine CtxAgree.of_cons (CtxAgree_append hΔ fun ws hws => (CtxAgree_cons (h ws hws)).1) ?_
    intro vs hvs
    obtain ⟨vs₁, ws, rfl, hlen⟩ : ∃ vs₁ ws, vs = vs₁ ++ ws ∧ vs₁.length = Γ.length := by
      have hl := FitsVals_length M φ hvs
      refine ⟨vs.take Γ.length, vs.drop Γ.length, (List.take_append_drop _ _).symm, ?_⟩
      simp at hl; simp [hl]
    obtain ⟨hws, hvs₁⟩ := (FitsVals_append M φ hlen).mp hvs
    rw [consList_append, consList_append]
    exact (CtxAgree_cons (h ws hws)).2 vs₁ hvs₁

/-! ## The self-certifying application -/

theorem lamCtx_append (M : Name → List Nat → V) (φ : Name → Nat) (p : Bool) :
    ∀ (Γ Δ : List Expr) (ρ : Nat → V) (F : (Nat → V) → V),
      lamCtx M φ p ρ (Γ ++ Δ) F = lamCtx M φ p ρ Δ fun ρ' => lamCtx M φ p ρ' Γ F
  | [], _, _, _ => rfl
  | A :: Γ, Δ, ρ, F => by
    simp only [List.cons_append, lamCtx_cons]
    rw [lamCtx_append M φ p Γ Δ ρ]

theorem piCtx_append (M : Name → List Nat → V) (φ : Name → Nat) (p : Bool) :
    ∀ (Γ Δ : List Expr) (ρ : Nat → V) (F : (Nat → V) → V),
      piCtx M φ p ρ (Γ ++ Δ) F = piCtx M φ p ρ Δ fun ρ' => piCtx M φ p ρ' Γ F
  | [], _, _, _ => rfl
  | A :: Γ, Δ, ρ, F => by
    simp only [List.cons_append, piCtx_cons]
    rw [piCtx_append M φ p Γ Δ ρ]

/-- The invariant of a spine gives the invariant of its head and of
every argument (`Sound.lean`'s `WellDenoted_mkAppN`, at any
assignment). -/
theorem WellDenoted_mkAppN' (M : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {f : Expr} {args : List Expr}, WellDenoted M φ ρ (Expr.mkAppN f args) →
      WellDenoted M φ ρ f ∧ ∀ a ∈ args, WellDenoted M φ ρ a
  | _, [], h => ⟨h, by simp⟩
  | f, a :: args, h => by
    rw [Expr.mkAppN_cons] at h
    obtain ⟨h1, h2⟩ := WellDenoted_mkAppN' M φ h
    rw [WellDenoted_app] at h1
    refine ⟨h1.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1.2.1
    · exact h2 b hb

/-- **A well-denoted application of a graph tower** computes the
tower's body at the arguments, and the arguments fit the tower's
context: the graph regime determines its domains, one binder at a
time.  (`hF` bounds the body, which is what makes the tower a member
of a product the domain can be read from.) -/
theorem appList_of_wd (M : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {args : List Expr} {f : Expr} {ρ₀ : Nat → V} {Γ : List Expr} {F G : (Nat → V) → V},
      WellDenoted M φ ρ (Expr.mkAppN f args) →
      interp M φ ρ f = lamCtx M φ false ρ₀ Γ F → args.length = Γ.length →
      (∀ vs, FitsVals M φ ρ₀ Γ vs → F (consList vs ρ₀) ∈ˢ G (consList vs ρ₀)) →
      FitsVals M φ ρ₀ Γ (args.map (interp M φ ρ)).reverse ∧
        interp M φ ρ (Expr.mkAppN f args) = F (consList (args.map (interp M φ ρ)).reverse ρ₀)
  | [], f, ρ₀, Γ, F, G, _, hf, hlen, _ => by
    cases Γ with
    | nil => exact ⟨trivial, hf⟩
    | cons _ _ => simp at hlen
  | a :: args, f, ρ₀, Γ, F, G, hw, hf, hlen, hF => by
    obtain ⟨Γ', A, rfl⟩ : ∃ Γ' A, Γ = Γ' ++ [A] := by
      rcases List.eq_nil_or_concat Γ with h | ⟨Γ', A, h⟩
      · subst h; simp at hlen
      · exact ⟨Γ', A, by simpa [List.concat_eq_append] using h⟩
    have hlen' : args.length = Γ'.length := by simpa using hlen
    rw [Expr.mkAppN_cons] at hw ⊢
    have hwa : WellDenoted M φ ρ (Expr.app f a) := (WellDenoted_mkAppN' M φ hw).1
    rw [WellDenoted_app] at hwa
    obtain ⟨-, -, p, A', B, hslot, hmem, -⟩ := hwa
    rw [hf, lamCtx_append, lamCtx_cons, lamCtx_nil] at hslot
    -- the graph regime, and its domain
    have hp : p = false := by
      cases p
      · rfl
      · exact absurd (eq_pt_of_mem_piR_true hslot) lamR_false_ne_pt
    subst hp
    have hown : lamR false (interp M φ ρ₀ A) (fun x => lamCtx M φ false (cons x ρ₀) Γ' F)
        ∈ˢ piR false (interp M φ ρ₀ A) fun x => piCtx M φ false (cons x ρ₀) Γ' G := by
      refine lamR_mem fun x hx => lamCtx_mem_piCtx M φ fun vs hvs => ?_
      have := hF (vs ++ [x]) ((FitsVals_append M φ (FitsVals_length M φ hvs)).mpr
        ⟨⟨trivial, by simpa using hx⟩, hvs⟩)
      simpa [consList_append] using this
    have hAA := piR_dom_unique hown hslot
    rw [← hAA] at hmem
    -- the step
    have hstep : interp M φ ρ (Expr.app f a) = lamCtx M φ false (cons (interp M φ ρ a) ρ₀) Γ' F := by
      rw [interp_app, hf, lamCtx_append, lamCtx_cons, lamCtx_nil, app_lamR_false hmem]
    obtain ⟨hfit, hval⟩ := appList_of_wd M φ (args := args) (f := Expr.app f a)
      (ρ₀ := cons (interp M φ ρ a) ρ₀) (Γ := Γ') (F := F) (G := G) hw hstep hlen'
      (fun vs hvs => by
        have := hF (vs ++ [interp M φ ρ a]) ((FitsVals_append M φ (FitsVals_length M φ hvs)).mpr
          ⟨⟨trivial, by simpa using hmem⟩, hvs⟩)
        simpa [consList_append] using this)
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.reverse_cons]
      exact (FitsVals_append M φ (by simpa using FitsVals_length M φ hfit)).mpr
        ⟨⟨trivial, by simpa using hmem⟩, by simpa using hfit⟩
    · simp only [List.map_cons, List.reverse_cons, consList_append, consList_cons, consList_nil]
      exact hval

/-- An abstraction over a nonempty context at a proposition is the
point, whatever its body. -/
theorem lamCtx_true_eq_pt (M : Name → List Nat → V) (φ : Name → Nat) :
    ∀ {Γ : List Expr}, Γ ≠ [] → ∀ (ρ : Nat → V) (F : (Nat → V) → V),
      lamCtx M φ true ρ Γ F = pt
  | [], h, _, _ => absurd rfl h
  | [_], _, ρ, F => by simp [lamCtx, lamR_true]
  | _ :: B :: Γ, _, ρ, F => by
    rw [lamCtx_cons]
    exact lamCtx_true_eq_pt M φ (List.cons_ne_nil B Γ) ρ _

/-- Introduction into a product over a nonempty context, with the body
only required inhabited at a proposition (the induction principle's
validity: the motive holds, whatever the recursor's value). -/
theorem lamCtx_mem_piCtx' (M : Name → List Nat → V) (φ : Name → Nat) {p : Bool} {ρ : Nat → V}
    {Γ : List Expr} (hne : Γ ≠ []) {F G : (Nat → V) → V}
    (hF : p = false → ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) ∈ˢ G (consList vs ρ))
    (hG : p = true → ∀ vs, FitsVals M φ ρ Γ vs → ∃ y, y ∈ˢ G (consList vs ρ)) :
    lamCtx M φ p ρ Γ F ∈ˢ piCtx M φ p ρ Γ G := by
  cases p
  · exact lamCtx_mem_piCtx M φ (hF rfl)
  · classical
    let F' : (Nat → V) → V := fun ρ' => if h : ∃ y, y ∈ˢ G ρ' then Classical.choose h else pt
    rw [lamCtx_true_eq_pt M φ hne, ← lamCtx_true_eq_pt M φ hne ρ F']
    refine lamCtx_mem_piCtx M φ fun vs hvs => ?_
    have h := hG rfl vs hvs
    simp only [F', dif_pos h]
    exact Classical.choose_spec h

/-! ## Reading a block -/

namespace IndSpec

variable (S : IndSpec) {env : Env} (M : Name → List Nat → V) (φ : Name → Nat)

/-- The block's valuation at the levels `φ` assigns its parameters
agrees with `φ` on them. -/
theorem ψ_map_agree : ∀ n ∈ S.lparams, φ n = S.ψ (S.lparams.map φ) n := by
  intro n hn
  simp [ψ, valOf_map, hn]

/-- **A reader**: an assignment and a valuation in which the block's
generated syntax may be read — agreeing with the old model on the
stored constants, assigning the type former its set, and agreeing
with `φ` on the block's level parameters. -/
structure Reader (M' : Name → List Nat → V) (φ' : Name → Nat) : Prop where
  /-- Agreement with the old model on the stored constants. -/
  agree : AgreeOn env M M'
  /-- The type former's set. -/
  fam : ∀ ls', M' S.name ls' = S.famSet M ls'
  /-- Agreement with `φ` on the block's level parameters. -/
  val : ∀ n ∈ S.lparams, φ' n = φ n

variable {S M φ}

theorem Reader.val_ψ {env : Env} {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') :
    ∀ n ∈ S.lparams, S.ψ (S.lparams.map φ) n = φ' n :=
  fun n hn => by rw [R.val n hn, ψ_map_agree S φ n hn]

theorem Reader.lvls_map {env : Env} {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') :
    S.lvls.map (Level.eval φ') = S.lparams.map φ := by
  simp only [lvls, List.map_map]
  apply List.map_congr_left
  intro n hn
  simp [R.val n hn]

omit [IndLib V] in
/-- The two environments a specification expression is read under —
values over parameter values over any base — agree below the values. -/
theorem consList₂_agree {vs ps : List V} {ρ ρ' : Nat → V} :
    ∀ i, i < vs.length + ps.length →
      consList vs (consList ps ρ) i = consList vs (consList ps ρ') i := by
  intro i hi
  rw [← consList_append, ← consList_append]
  exact consList_agree_lt i (by simpa using hi)

/-- The parameters a datum mentions, as a membership statement. -/
theorem PropWhen.paramsIn_iff {ps : List Name} :
    ∀ {pw : PropWhen}, pw.paramsIn ps = true ↔ ∀ qs, pw = .whenZero qs → ∀ n ∈ qs, n ∈ ps
  | .never => by simp [PropWhen.paramsIn]
  | .whenZero qs => by
    simp only [PropWhen.paramsIn, List.all_eq_true, PropWhen.whenZero.injEq, forall_eq']
    constructor
    · intro h n hn; simpa using h n hn
    · intro h n hn; simpa using h n hn

theorem Level.zeroness_paramsIn {ps : List Name} :
    ∀ {l : Level}, l.paramsIn ps = true → (Level.zeroness l).paramsIn ps = true
  | .zero, _ => rfl
  | .succ _, _ => rfl
  | .param n, h => by
    rw [PropWhen.paramsIn_iff]
    rintro qs hqs m hm
    simp only [Level.zeroness, PropWhen.whenZero.injEq] at hqs
    subst hqs
    rw [ParamSet.mem_single] at hm
    subst hm
    simpa [Level.paramsIn] using h
  | .max a b, h => by
    simp only [Level.paramsIn, Bool.and_eq_true] at h
    have ha := Level.zeroness_paramsIn (ps := ps) h.1
    have hb := Level.zeroness_paramsIn (ps := ps) h.2
    rw [PropWhen.paramsIn_iff] at ha hb ⊢
    rintro qs hqs n hn
    simp only [Level.zeroness] at hqs
    cases hza : Level.zeroness a with
    | never => rw [hza] at hqs; simp [PropWhen.inter] at hqs
    | whenZero s =>
      cases hzb : Level.zeroness b with
      | never => rw [hza, hzb] at hqs; simp [PropWhen.inter] at hqs
      | whenZero t =>
        rw [hza, hzb] at hqs
        simp only [PropWhen.inter, PropWhen.whenZero.injEq] at hqs
        subst hqs
        rcases ParamSet.mem_union.mp hn with hn | hn
        · exact ha s hza n hn
        · exact hb t hzb n hn
  | .imax _ b, h => by
    simp only [Level.paramsIn, Bool.and_eq_true] at h
    show (Level.zeroness b).paramsIn ps = true
    exact Level.zeroness_paramsIn (ps := ps) h.2

/-- The family's annotation reads as the regime in any reader. -/
theorem Reader.pw_holds {env : Env} {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ')
    (hs : S.sort.paramsIn S.lparams = true) :
    S.pw.holds φ' = S.z (S.lparams.map φ) := by
  unfold z pw
  exact PropWhen.holds_congr (fun n hn => (R.val_ψ n hn).symm)
    (Level.zeroness_paramsIn hs)

/-- The elimination annotation reads as its regime bit. -/
theorem q_holds (φ' : Name → Nat) : S.q.holds φ' = (Level.eval φ' S.ℓ == 0) :=
  Level.holds_zeroness_eq φ' S.ℓ

section Readings

variable {env : Env} {M' : Name → List Nat → V} {φ' : Name → Nat}

/-- A specification expression reads in a reader as it reads in the
old model at the block's valuation, in the closed environment. -/
theorem Reader.read (R : S.Reader (env := env) M φ M' φ') {k : Nat} {e : Expr}
    (he : Expr.Scoped env S.lparams k e)
    {vs ps : List V} {ρ : Nat → V} (hk : k ≤ vs.length + ps.length) :
    interp M' φ' (consList vs (consList ps ρ)) e
      = interp M (S.ψ (S.lparams.map φ)) (consList vs (envP ps)) e :=
  interp_spec he (fun c hc ls => (R.agree c hc ls).symm) (fun n hn => (R.val_ψ n hn).symm)
    fun i hi => consList₂_agree i (by omega)

/-! ### The parameter and index contexts -/

theorem Reader.agree_params (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (ρ : Nat → V) :
    CtxAgree M' M φ' (S.ψ (S.lparams.map φ)) ρ base S.params := by
  intro i A hA vs hvs
  have hl := FitsVals_length M' φ' hvs
  have hi : i < S.params.length := (List.getElem?_eq_some_iff.mp hA).1
  have := R.read (ps := []) (ρ := ρ) (hS.1 i A hA) (vs := vs)
    (by simp only [hl, List.length_drop, List.length_nil, Nat.add_zero, nP]; omega)
  simpa [envP] using this

theorem Reader.fits_params (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {ρ : Nat → V} {ps : List V} :
    FitsVals M' φ' ρ S.params ps ↔ FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps :=
  FitsVals_congr₂ (R.agree_params hS ρ)

theorem Reader.agree_indices (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (ρ : Nat → V) {ps : List V} (hps : ps.length = S.nP) :
    CtxAgree M' M φ' (S.ψ (S.lparams.map φ)) (consList ps ρ) (envP ps) S.indices := by
  intro t T hT vs hvs
  have hl := FitsVals_length M' φ' hvs
  have ht : t < S.indices.length := (List.getElem?_eq_some_iff.mp hT).1
  exact R.read (hS.2.1 t T hT)
    (by simp only [hl, List.length_drop, hps, nI]; omega)

theorem Reader.fits_indices (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {ρ : Nat → V} {ps is : List V} (hps : ps.length = S.nP) :
    FitsVals M' φ' (consList ps ρ) S.indices is ↔
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices is :=
  FitsVals_congr₂ (R.agree_indices hS ρ hps)

/-- The former's set, read in the reader. -/
theorem Reader.famSet_eq (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ') :
    S.famSet M (S.lparams.map φ) = lamCtx M' φ' false base (S.indices ++ S.params) fun ρ' =>
      S.Fam M (S.lparams.map φ) (readEnv S.nP (shiftE S.nI 0 ρ')) (readEnv S.nI ρ') := by
  unfold famSet
  refine (lamCtx_congr₂ ?_ fun _ _ => rfl).symm
  refine CtxAgree_append (R.agree_params hS base) fun ws hws => ?_
  have hws' : ws.length = S.nP := by have := FitsVals_length M' φ' hws; simpa [nP] using this
  have := R.agree_indices hS base hws'
  simpa [envP] using this

/-! ### The family applied -/

/-- **The family applied, by β**: at parameter values fitting the
parameters and index values fitting the indices, the type former's
set applied is the fibre. -/
theorem Reader.famAt_fit (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {o : Nat} {es : List Expr} {ρ'' : Nat → V} {ps isv : List V}
    (hps : readEnv S.nP (shiftE o 0 ρ'') = ps)
    (hes : (es.map (interp M' φ' ρ'')).reverse = isv)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hi : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices isv) :
    interp M' φ' ρ'' (S.famAt o es) = S.Fam M (S.lparams.map φ) ps isv := by
  unfold famAt
  rw [interp_mkAppN_appList, interp_const, R.fam, R.lvls_map, R.famSet_eq hS,
    List.map_append, interp_varsAt, hps]
  have hl₁ : isv.length = S.nI := by have := FitsVals_length M _ hi; simpa [nI] using this
  have hl₂ : ps.length = S.nP := by have := FitsVals_length M _ hp; simpa [nP] using this
  have hfit : FitsVals M' φ' base (S.indices ++ S.params) (isv ++ ps) :=
    (FitsVals_append M' φ' (by simpa [nI] using hl₁)).mpr
      ⟨(R.fits_params hS).mpr hp, (R.fits_indices hS (ρ := base) hl₂).mpr (by simpa [envP] using hi)⟩
  have hrev : ps.reverse ++ es.map (interp M' φ' ρ'') = (isv ++ ps).reverse := by
    rw [List.reverse_append, ← hes, List.reverse_reverse]
  rw [hrev, appList_lamCtx M' φ' hfit (G := fun _ => univ (S.u₀ (S.lparams.map φ)))
    (fun _ _ => S.Fam_mem_univ M _ _ _) (fun h => by simp at h)]
  rw [consList_append,
    show shiftE S.nI 0 (consList isv (consList ps base)) = consList ps base by
      rw [← hl₁]; exact shiftE_consList isv _,
    readEnv_consList hl₂, readEnv_consList hl₁]

/-- **The family applied, from the invariant**: a well-denoted
application of the type former to parameter and index expressions is
the fibre at their values, and the values fit the parameter and index
contexts — no typing of the arguments is consulted. -/
theorem Reader.famAt_wd (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {o : Nat} {es : List Expr} {ρ'' : Nat → V} {ps : List V}
    (hps : readEnv S.nP (shiftE o 0 ρ'') = ps) (hlen : es.length = S.nI)
    (hw : WellDenoted M' φ' ρ'' (S.famAt o es)) :
    FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps ∧
    FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices (es.map (interp M' φ' ρ'')).reverse ∧
    interp M' φ' ρ'' (S.famAt o es)
      = S.Fam M (S.lparams.map φ) ps (es.map (interp M' φ' ρ'')).reverse := by
  have hf : interp M' φ' ρ'' (Expr.const S.name S.lvls)
      = lamCtx M' φ' false base (S.indices ++ S.params) fun ρ' =>
          S.Fam M (S.lparams.map φ) (readEnv S.nP (shiftE S.nI 0 ρ')) (readEnv S.nI ρ') := by
    rw [interp_const, R.fam, R.lvls_map, R.famSet_eq hS]
  obtain ⟨hfit, hval⟩ := appList_of_wd M' φ' (f := Expr.const S.name S.lvls)
    (args := Expr.varsAt o S.nP ++ es) hw hf
    (by simp [Expr.varsAt, hlen, nI, nP]; omega)
    (G := fun _ => univ (S.u₀ (S.lparams.map φ))) (fun _ _ => S.Fam_mem_univ M _ _ _)
  rw [List.map_append, interp_varsAt, hps, List.reverse_append, List.reverse_reverse] at hfit hval
  have hl₁ : (es.map (interp M' φ' ρ'')).reverse.length = S.nI := by simp [hlen]
  obtain ⟨hp, hi⟩ := (FitsVals_append M' φ' (by simpa [nI] using hl₁)).mp hfit
  have hps' : ps.length = S.nP := by have := FitsVals_length M' φ' hp; simpa [nP] using this
  refine ⟨(R.fits_params hS).mp hp, ?_, ?_⟩
  · have := (R.fits_indices hS (ρ := base) hps').mp hi
    simpa [envP] using this
  · unfold famAt
    rw [hval, consList_append,
      show shiftE S.nI 0 (consList (es.map (interp M' φ' ρ'')).reverse (consList ps base))
          = consList ps base by
        rw [← hl₁]; exact shiftE_consList _ _,
      readEnv_consList hps', readEnv_consList hl₁]

/-! ### The field context -/

/-- **A field's index expressions fit** (a recursive field's at the
earlier fields, a reflexive field's at every fitting telescope) — what
the invariant of the constructor's type supplies and the field's
domain is read with. -/
def IdxFitAt (S : IndSpec) (M : Name → List Nat → V) (φ : Name → Nat) (ps vs : List V) :
    Field → Prop
  | .ordinary _ => True
  | .recursive es =>
    FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.idxVals M (S.lparams.map φ) (consList vs (envP ps)) es)
  | .reflexive tele es =>
    ∀ ys, FitsVals M (S.ψ (S.lparams.map φ)) (consList vs (envP ps)) tele ys →
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
        (S.idxVals M (S.lparams.map φ) (consList ys (consList vs (envP ps))) es)

/-- Index expressions of the specification read as index values. -/
theorem Reader.idxVals_eq (R : S.Reader (env := env) M φ M' φ') {k : Nat} {es : List Expr}
    (hes : ∀ e ∈ es, Expr.Scoped env S.lparams k e) {vs ps : List V} {ρ : Nat → V}
    (hk : k ≤ vs.length + ps.length) :
    (es.map (interp M' φ' (consList vs (consList ps ρ)))).reverse
      = S.idxVals M (S.lparams.map φ) (consList vs (envP ps)) es := by
  unfold idxVals
  congr 1
  exact List.map_congr_left fun e he => R.read (hes e he) hk

/-- A reflexive field's telescope agrees between a reader and the
old model. -/
theorem Reader.agree_tele (R : S.Reader (env := env) M φ M' φ') {k : Nat} {tele : List Expr}
    (hsc : ∀ t T, tele[t]? = some T →
      Expr.Scoped env S.lparams (S.nP + k + (tele.length - 1 - t)) T)
    {vs ps : List V} {ρ : Nat → V} (hk : vs.length = k) (hps : ps.length = S.nP) :
    CtxAgree M' M φ' (S.ψ (S.lparams.map φ)) (consList vs (consList ps ρ))
      (consList vs (envP ps)) tele := by
  intro t T hT ys hys
  have hl := FitsVals_length M' φ' hys
  have ht : t < tele.length := (List.getElem?_eq_some_iff.mp hT).1
  rw [← consList_append ys vs (consList ps ρ), ← consList_append ys vs (envP ps)]
  refine R.read (hsc t T hT) ?_
  simp only [List.length_append, hl, List.length_drop, hk, hps]; omega

/-- **A field's domain, read by β** at fitting index expressions: the
field's set. -/
theorem Reader.fieldDom_fit (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {k : Nat} {f : Field} (hsc : S.fieldScoped env k f) {vs ps : List V} {ρ : Nat → V}
    (hk : vs.length = k) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : IdxFitAt S M φ ps vs f) :
    interp M' φ' (consList vs (consList ps ρ)) (S.fieldDom k f)
      = S.fieldSet M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
          (S.Mem M (S.lparams.map φ)) ps vs f := by
  cases f with
  | ordinary A => exact R.read hsc (by omega)
  | recursive es =>
    simp only [fieldDom, fieldSet]
    rw [R.famAt_fit hS (o := k) (ρ'' := consList vs (consList ps ρ)) (ps := ps)
      (isv := S.idxVals M (S.lparams.map φ) (consList vs (envP ps)) es)
      (by rw [← hk, shiftE_consList, readEnv_consList hps])
      (R.idxVals_eq hsc.2 (by omega)) hp hidx]
    rfl
  | reflexive tele es =>
    simp only [fieldDom, fieldSet]
    rw [interp_mkPis, R.pw_holds hS.2.2.1]
    refine piCtx_congr₂ (R.agree_tele hsc.1 hk hps) fun ys hys => ?_
    have hl := FitsVals_length M' φ' hys
    have hys' := (FitsVals_congr₂ (R.agree_tele hsc.1 hk hps)).mp hys
    rw [R.famAt_fit hS (o := k + tele.length) (ρ'' := consList ys (consList vs (consList ps ρ)))
      (ps := ps)
      (isv := S.idxVals M (S.lparams.map φ) (consList ys (consList vs (envP ps))) es)
      (by rw [← consList_append ys vs,
        show k + tele.length = (ys ++ vs).length by simp [hl, hk]; omega,
        shiftE_consList, readEnv_consList hps])
      (by rw [← consList_append ys vs (consList ps ρ),
        R.idxVals_eq hsc.2.2 (by simp [hl, hk, hps]; omega), consList_append])
      hp (hidx ys hys')]
    rfl

/-- **A field's domain, read from the invariant**: the field's set,
and its index expressions fit. -/
theorem Reader.fieldDom_wd (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {k : Nat} {f : Field} (hsc : S.fieldScoped env k f) {vs ps : List V} {ρ : Nat → V}
    (hk : vs.length = k) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hw : WellDenoted M' φ' (consList vs (consList ps ρ)) (S.fieldDom k f)) :
    IdxFitAt S M φ ps vs f ∧
    interp M' φ' (consList vs (consList ps ρ)) (S.fieldDom k f)
      = S.fieldSet M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
          (S.Mem M (S.lparams.map φ)) ps vs f := by
  have hidx : IdxFitAt S M φ ps vs f := by
    cases f with
    | ordinary _ => trivial
    | recursive es =>
      have := (R.famAt_wd hS (o := k) (ρ'' := consList vs (consList ps ρ)) (ps := ps)
        (by rw [← hk, shiftE_consList, readEnv_consList hps]) hsc.1 hw).2.1
      rwa [R.idxVals_eq hsc.2 (by omega)] at this
    | reflexive tele es =>
      intro ys hys
      have hys' := (FitsVals_congr₂ (R.agree_tele (ρ := ρ) hsc.1 hk hps)).mpr hys
      have hl := FitsVals_length M' φ' hys'
      rw [fieldDom, WellDenoted_mkPis] at hw
      have hwb := (hw.2 ys hys').1
      have := (R.famAt_wd hS (o := k + tele.length) (ρ'' := consList ys (consList vs (consList ps ρ)))
        (ps := ps)
        (by rw [← consList_append ys vs,
          show k + tele.length = (ys ++ vs).length by simp [hl, hk]; omega,
          shiftE_consList, readEnv_consList hps])
        hsc.2.1 hwb).2.1
      rwa [← consList_append ys vs (consList ps ρ),
        R.idxVals_eq hsc.2.2 (by simp [hl, hk, hps]; omega), consList_append] at this
  exact ⟨hidx, R.fieldDom_fit hS hsc hk hps hp hidx⟩

/-- The domains of an appended context are well-denoted: the right
part's are, and the left part's under fitting values of the right. -/
theorem CtxWD_append' {ρ : Nat → V} :
    ∀ {Γ Δ : List Expr}, CtxWD M' φ' ρ (Γ ++ Δ) →
      CtxWD M' φ' ρ Δ ∧ ∀ ws, FitsVals M' φ' ρ Δ ws → CtxWD M' φ' (consList ws ρ) Γ
  | [], _, h => ⟨h, fun _ _ => trivial⟩
  | A :: Γ, Δ, h => by
    rw [List.cons_append, CtxWD_cons] at h
    obtain ⟨hΔ, hΓ⟩ := CtxWD_append' h.1
    refine ⟨hΔ, fun ws hws => ?_⟩
    rw [CtxWD_cons]
    refine ⟨hΓ ws hws, fun vs hvs => ?_⟩
    have := h.2 (vs ++ ws) ((FitsVals_append M' φ' (FitsVals_length M' φ' hvs)).mpr ⟨hws, hvs⟩)
    rwa [consList_append] at this

/-- **The field context, read**: at parameter values, values fit the
generated field context exactly when they fit the constructor's
fields semantically — and then every field's index expressions fit. -/
theorem Reader.fits_fieldCtx (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ') :
    ∀ {fields : List Field},
      (∀ i f, fields[i]? = some f → S.fieldScoped env (fields.length - 1 - i) f) →
      ∀ {ps : List V} {ρ : Nat → V}, ps.length = S.nP →
        FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
        CtxWD M' φ' (consList ps ρ) (S.fieldCtx fields) →
        ∀ {vs : List V},
          (FitsVals M' φ' (consList ps ρ) (S.fieldCtx fields) vs ↔
            S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
              (S.Mem M (S.lparams.map φ)) ps fields vs) ∧
          (S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
              (S.Mem M (S.lparams.map φ)) ps fields vs →
            ∀ k f, fields[fields.length - 1 - k]? = some f → k < fields.length →
              IdxFitAt S M φ ps (earlier vs k) f)
  | [], _, ps, ρ, _, _, _, vs => by
    refine ⟨?_, fun _ k _ _ hk => by simp at hk⟩
    cases vs <;> simp [fieldCtx, FitsFields]
  | f :: rest, hsc, ps, ρ, hps, hp, hwd, vs => by
    have hsc' : ∀ i f', rest[i]? = some f' → S.fieldScoped env (rest.length - 1 - i) f' := by
      intro i f' hf'
      have := hsc (i + 1) f' (by simpa using hf')
      simpa [Nat.sub_sub, Nat.add_comm] using this
    simp only [fieldCtx] at hwd
    rw [CtxWD_cons] at hwd
    have ih : ∀ {vs' : List V}, _ := fun {vs'} => R.fits_fieldCtx hS hsc' hps hp hwd.1 (vs := vs')
    have hf : S.fieldScoped env rest.length f := by
      have := hsc 0 f rfl; simpa using this
    cases vs with
    | nil => exact ⟨by simp [fieldCtx, FitsFields], fun h => h.elim⟩
    | cons v vs' =>
      simp only [fieldCtx, FitsVals_cons, FitsFields]
      have key : S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
          (S.Mem M (S.lparams.map φ)) ps rest vs' →
          IdxFitAt S M φ ps vs' f ∧
          interp M' φ' (consList vs' (consList ps ρ)) (S.fieldDom rest.length f)
            = S.fieldSet M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
                (S.Mem M (S.lparams.map φ)) ps vs' f := by
        intro hfit
        have hfit' := (ih (vs' := vs')).1.mpr hfit
        exact R.fieldDom_wd hS hf (by rw [FitsVals_length M' φ' hfit', S.length_fieldCtx]) hps hp
          (hwd.2 vs' hfit')
      refine ⟨?_, ?_⟩
      · rw [(ih (vs' := vs')).1]
        constructor
        · rintro ⟨hfit, hv⟩
          exact ⟨hfit, by rwa [(key hfit).2] at hv⟩
        · rintro ⟨hfit, hv⟩
          exact ⟨hfit, by rwa [(key hfit).2]⟩
      · rintro ⟨hfit, -⟩ k f' hf' hk
        have hl := S.FitsFields_length M _ hfit
        by_cases hkr : k = rest.length
        · subst hkr
          simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getElem?_cons_zero,
            Option.some.injEq] at hf'
          subst hf'
          rw [show earlier (v :: vs') rest.length = vs' by
            simp only [earlier, List.length_cons, hl]
            rw [show rest.length + 1 - rest.length = 1 by omega]; rfl]
          exact (key hfit).1
        · have hk' : k < rest.length := by simp at hk; omega
          have : (f :: rest).length - 1 - k = (rest.length - 1 - k) + 1 := by simp; omega
          rw [this, List.getElem?_cons_succ] at hf'
          rw [earlier_cons (by omega)]
          exact (ih (vs' := vs')).2 hfit k f' hf' hk'

/-- **Fitting the fields semantically gives fitting the generated
context** in any reader, by β, once the index expressions are known to
fit. -/
theorem Reader.fits_fieldCtx_of_idx (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ') :
    ∀ {fields : List Field},
      (∀ i f, fields[i]? = some f → S.fieldScoped env (fields.length - 1 - i) f) →
      ∀ {ps : List V} {ρ : Nat → V}, ps.length = S.nP →
        FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
        ∀ {vs : List V},
          S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
            (S.Mem M (S.lparams.map φ)) ps fields vs →
          (∀ k f, fields[fields.length - 1 - k]? = some f → k < fields.length →
            IdxFitAt S M φ ps (earlier vs k) f) →
          FitsVals M' φ' (consList ps ρ) (S.fieldCtx fields) vs
  | [], _, _, _, _, _, [], _, _ => trivial
  | [], _, _, _, _, _, _ :: _, h, _ => h.elim
  | _ :: _, _, _, _, _, _, [], h, _ => h.elim
  | f :: rest, hsc, ps, ρ, hps, hp, v :: vs', hfit, hidx => by
    have hsc' : ∀ i f', rest[i]? = some f' → S.fieldScoped env (rest.length - 1 - i) f' := by
      intro i f' hf'
      have := hsc (i + 1) f' (by simpa using hf')
      simpa [Nat.sub_sub, Nat.add_comm] using this
    have hl := S.FitsFields_length M _ hfit.1
    have hidx' : ∀ k f', rest[rest.length - 1 - k]? = some f' → k < rest.length →
        IdxFitAt S M φ ps (earlier vs' k) f' := by
      intro k f' hf' hk
      have := hidx k f' (by
        rw [show (f :: rest).length - 1 - k = (rest.length - 1 - k) + 1 by simp; omega]
        simpa using hf') (by simp; omega)
      rwa [earlier_cons (by omega)] at this
    simp only [fieldCtx, FitsVals_cons]
    refine ⟨R.fits_fieldCtx_of_idx hS hsc' hps hp hfit.1 hidx', ?_⟩
    have hk := hidx rest.length f (by simp) (by simp)
    rw [show earlier (v :: vs') rest.length = vs' by
      simp only [earlier, List.length_cons, hl]
      rw [show rest.length + 1 - rest.length = 1 by omega]; rfl] at hk
    rw [R.fieldDom_fit hS (by have := hsc 0 f rfl; simpa using this) hl hps hp hk]
    exact hfit.2

/-! ### The generated contexts, entry by entry -/

/-- The minors' context as a recursion (innermost first): the minors
after `j`, then minor `j` outermost. -/
def minorsFrom (S : IndSpec) : List CtorSpec → Nat → List Expr
  | [], _ => []
  | c :: cs, j => minorsFrom S cs (j + 1) ++ [S.minorTy c j]

theorem minorsFrom_eq : ∀ (cs : List CtorSpec) (j : Nat),
    ((List.range cs.length).map fun i => S.minorTy (cs.getD i ⟨"", [], []⟩) (j + i)).reverse
      = S.minorsFrom cs j
  | [], _ => rfl
  | c :: cs, j => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
    simp only [minorsFrom, List.getD_cons_zero, Nat.add_zero]
    congr 1
    rw [← minorsFrom_eq cs (j + 1)]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

theorem minorsCtx_eq : S.minorsCtx = S.minorsFrom S.ctors 0 := by
  rw [minorsCtx, ← minorsFrom_eq]
  simp [n]

/-- The inductive hypotheses' context as a recursion (innermost
first): the hypotheses of the later recursive fields, then this
field's outermost, with `l` earlier hypotheses. -/
def ihCtxAux (S : IndSpec) (nF o : Nat) : List (Nat × Field) → Nat → List Expr
  | [], _ => []
  | kf :: rest, l => ihCtxAux S nF o rest (l + 1) ++ [S.ihTy nF kf.1 l o kf.2]

theorem ihCtxAux_eq (nF o : Nat) : ∀ (L : List (Nat × Field)) (l : Nat),
    (L.mapIdx fun i kf => S.ihTy nF kf.1 (l + i) o kf.2).reverse = S.ihCtxAux nF o L l
  | [], _ => rfl
  | kf :: rest, l => by
    rw [List.mapIdx_cons, List.reverse_cons]
    simp only [ihCtxAux, Nat.add_zero]
    congr 1
    rw [← ihCtxAux_eq nF o rest (l + 1)]
    congr 1
    refine List.mapIdx_eq_mapIdx_iff.mpr fun i _ => ?_
    simp [Nat.add_assoc, Nat.add_comm 1 i]

theorem ihCtx_eq (c : CtorSpec) (j : Nat) :
    S.ihCtx c j = S.ihCtxAux c.fields.length (j + 1) c.recFields 0 := by
  rw [ihCtx, ← ihCtxAux_eq]
  simp

theorem fieldCtx_getElem? : ∀ (fields : List Field) (i : Nat),
    (S.fieldCtx fields)[i]? = (fields[i]?).map fun f => S.fieldDom (fields.length - 1 - i) f
  | [], _ => rfl
  | f :: fields, 0 => by simp [fieldCtx]
  | f :: fields, i + 1 => by
    have : (f :: fields).length - 1 - (i + 1) = fields.length - 1 - i := by simp; omega
    rw [this]
    simp only [fieldCtx, List.getElem?_cons_succ]
    exact fieldCtx_getElem? fields i

/-- Reading a variable of the context: the value at its position. -/
theorem consList_getD {vs : List V} {ρ : Nat → V} {i : Nat} (h : i < vs.length) :
    consList vs ρ i = vs.getD i pt := by
  rw [consList_lt h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- **A field's lifted domain**, read under the extras: the field's
set. -/
theorem Reader.read_fieldCtxAt (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {c : CtorSpec} (hc : c ∈ S.ctors) {o i : Nat} {A : Expr}
    (hA : (S.fieldCtxAt c o)[i]? = some A) {vs os ps : List V} {ρ : Nat → V}
    (hv : vs.length = c.fields.length - 1 - i) (ho : os.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : ∀ f, c.fields[i]? = some f → IdxFitAt S M φ ps vs f) :
    ∃ f, c.fields[i]? = some f ∧
      interp M' φ' (consList vs (consList os (consList ps ρ))) A
        = S.fieldSet M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
            (S.Mem M (S.lparams.map φ)) ps vs f := by
  unfold fieldCtxAt at hA
  rw [Expr.liftCtx_getElem?, S.fieldCtx_getElem?, S.length_fieldCtx] at hA
  simp only [Option.map_map, Option.map_eq_some_iff, Function.comp] at hA
  obtain ⟨f, hf, rfl⟩ := hA
  refine ⟨f, hf, ?_⟩
  rw [← hv, interp_liftCtx_liftN_entry M' φ' ρ _ ho, hv]
  exact R.fieldDom_fit hS (by
    have := (hS.2.2.2.1 c hc).1 i f hf
    simpa [hv] using this) hv hps hp (hidx f hf)

/-! ### The recursor's contexts -/

/-- β over a context in the graph regime needs no bound on the body. -/
theorem appList_lamCtx_false :
    ∀ {Γ : List Expr} {ρ : Nat → V} {F : (Nat → V) → V} {vs : List V},
      FitsVals M' φ' ρ Γ vs → appList (lamCtx M' φ' false ρ Γ F) vs.reverse = F (consList vs ρ)
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
  | A :: Γ, ρ, F, v :: vs, h => by
    rw [FitsVals_cons] at h
    simp only [lamCtx_cons, List.reverse_cons, appList_append, appList_cons, appList_nil]
    rw [appList_lamCtx_false h.1, app_lamR_false h.2]
    rfl

/-- **A reader of the constructors too**: a reader assigning each
constructor its set. -/
structure Reader₂ (M' : Name → List Nat → V) (φ' : Name → Nat) : Prop where
  /-- The underlying reader. -/
  R : S.Reader (env := env) M φ M' φ'
  /-- The constructors' sets. -/
  ctor : ∀ j c, S.ctors[j]? = some c → ∀ ls', M' c.name ls' = S.ctorSet M ls' j c

/-- The model with the former added is a reader at the block's own
valuation. -/
theorem reader₁ (hfresh : env.find? S.name = none) :
    S.Reader (env := env) M φ (S.M₁ M) (S.ψ (S.lparams.map φ)) where
  agree := fun c hc ls => by
    have hne : c ≠ S.name := fun h => by subst h; simp [hfresh] at hc
    simp [M₁, hne]
  fam := fun ls' => by simp [M₁]
  val := fun n hn => (ψ_map_agree S φ n hn).symm

omit [IndLib V] in
/-- The environment of the recursor's contexts, regrouped. -/
theorem consList_three (a b c : List V) (ρ : Nat → V) :
    consList a (consList b (consList c ρ)) = consList (a ++ b ++ c) ρ := by
  simp [consList_append]

/-- **The major's type, read**: the fibre at the parameters and the
index values. -/
theorem Reader.read_famVars (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {o : Nat} {is os ps : List V} {ρ : Nat → V} (ho : os.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hi : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices is) :
    interp M' φ' (consList is (consList os (consList ps ρ))) (S.famVars o)
      = S.Fam M (S.lparams.map φ) ps is := by
  have hl : is.length = S.nI := by have := FitsVals_length M _ hi; simpa [nI] using this
  unfold famVars
  refine R.famAt_fit hS ?_ ?_ hp hi
  · rw [← consList_append, show o + S.nI = (is ++ os).length by simp [hl, ho]; omega,
      shiftE_consList, readEnv_consList hps]
  · rw [interp_varsAt, shiftE_zero_zero, List.reverse_reverse, readEnv_consList hl]

/-- **The motive's type, read**: the product over the indices and the
fibre into the elimination universe. -/
theorem Reader.read_motiveTy (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {ps : List V} {ρ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps) :
    interp M' φ' (consList ps ρ) S.motiveTy
      = piCtx M (S.ψ (S.lparams.map φ)) false (envP ps) S.indices fun ρ' =>
          piSet (S.Fam M (S.lparams.map φ) ps (readEnv S.nI ρ')) fun _ =>
            univ (Level.eval φ' S.ℓ) := by
  unfold motiveTy
  rw [interp_mkPis, PropWhen.holds_never, piCtx_cons]
  refine piCtx_congr₂ (R.agree_indices hS ρ hps) fun is his => ?_
  have his' := (R.fits_indices hS hps).mp his
  have hl : is.length = S.nI := by have := FitsVals_length M' φ' his; simpa [nI] using this
  have hfv := R.read_famVars hS (o := 0) (os := []) (ρ := ρ) rfl hps hp his'
  simp only [consList_nil] at hfv
  rw [hfv, readEnv_consList hl, piR_false]
  rfl

/-- The set an inductive hypothesis' value must lie in (`IhTyped`,
`IndSem.lean`, as a set). -/
noncomputable def ihSet (S : IndSpec) (M : Name → List Nat → V) (φ : Name → Nat) (q : Bool)
    (ps : List V) (m : V) (fs : List V) : Nat × Field → V
  | (k, .recursive es) =>
    appList m ((S.idxVals M (S.lparams.map φ) (consList (earlier fs k) (envP ps)) es).reverse ++
      [fieldVal fs k])
  | (k, .reflexive tele es) =>
    piCtx M (S.ψ (S.lparams.map φ)) q (consList (earlier fs k) (envP ps)) tele fun ρ' =>
      appList m ((S.idxVals M (S.lparams.map φ) ρ' es).reverse ++
        [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])
  | (_, .ordinary _) => pt

theorem IhTyped_iff {q : Bool} {ps : List V} {m : V} {fs : List V} {kf : Nat × Field}
    (hrec : kf.2.isRec = true) {ih : V} :
    S.IhTyped M (S.lparams.map φ) q ps m fs kf ih ↔ ih ∈ˢ ihSet S M φ q ps m fs kf := by
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | recursive _ => rfl
  | reflexive _ _ => rfl

/-- A product over a telescope lifted into a minor premise or a rule
is the product over the telescope at the field's own frame. -/
theorem Reader.piCtx_liftCtx_atCtx (R : S.Reader (env := env) M φ M' φ')
    {nF k l o : Nat} {ihsE fs os ps : List V} {ρ : Nat → V}
    (hi : ihsE.length = l) (hf : fs.length = nF) (ho : os.length = o) (hk : k ≤ nF)
    (hps : ps.length = S.nP) (p : Bool) :
    ∀ (tele : List Expr),
      (∀ t T, tele[t]? = some T →
        Expr.Scoped env S.lparams (S.nP + k + (tele.length - 1 - t)) T) →
      ∀ (F : (Nat → V) → V),
        piCtx M' φ' p (consList ihsE (consList fs (consList os (consList ps ρ))))
            (Expr.liftCtx (fun t T => Expr.atCtx nF k l o t T) tele) F
          = piCtx M (S.ψ (S.lparams.map φ)) p (consList (fs.drop (nF - k)) (envP ps)) tele
              fun ρ' => F (consList (readEnv tele.length ρ')
                (consList ihsE (consList fs (consList os (consList ps ρ)))))
  | [], _, F => by simp [readEnv]
  | T :: rest, hsc, F => by
    have hsc' : ∀ t T', rest[t]? = some T' →
        Expr.Scoped env S.lparams (S.nP + k + (rest.length - 1 - t)) T' := by
      intro t T' hT'
      have := hsc (t + 1) T' (by simpa using hT')
      simpa [Nat.sub_sub, Nat.add_comm] using this
    simp only [Expr.liftCtx_cons, piCtx_cons]
    rw [R.piCtx_liftCtx_atCtx hi hf ho hk hps p rest hsc']
    refine piCtx_congr M _ fun ys hys => ?_
    have hl := FitsVals_length M _ hys
    have hkd : fs.drop (nF - k) = earlier fs k := by simp [earlier, hf]
    rw [readEnv_consList hl, interp_atCtx M' φ' ρ T hl hi hf ho hk]
    have hT : interp M' φ' (consList ys (consList (fs.drop (nF - k)) (consList ps ρ))) T
        = interp M (S.ψ (S.lparams.map φ)) (consList ys (consList (fs.drop (nF - k)) (envP ps))) T := by
      rw [← consList_append ys (fs.drop (nF - k)) (consList ps ρ),
        ← consList_append ys (fs.drop (nF - k)) (envP ps)]
      refine R.read (hsc 0 T rfl) ?_
      simp only [List.length_append, hl, List.length_drop, hf, hps, List.length_cons,
        Nat.add_sub_cancel]
      omega
    rw [hT]
    refine piR_congr fun x hx => ?_
    rw [show cons x (consList ys (consList (fs.drop (nF - k)) (envP ps)))
        = consList (x :: ys) (consList (fs.drop (nF - k)) (envP ps)) from rfl,
      readEnv_consList (by simp [hl])]
    rfl

/-- **An inductive hypothesis' type, read**: the set its value must
lie in. -/
theorem Reader.read_ihTy (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {c : CtorSpec} (hc : c ∈ S.ctors) {kf : Nat × Field} (hkf : kf ∈ c.recFields)
    {l o : Nat} {ihsE fs os ps : List V} {ρ : Nat → V}
    (hi : ihsE.length = l) (hf : fs.length = c.fields.length) (ho : os.length = o) (hpos : 0 < o)
    (hps : ps.length = S.nP) :
    interp M' φ' (consList ihsE (consList fs (consList os (consList ps ρ))))
        (S.ihTy c.fields.length kf.1 l o kf.2)
      = ihSet S M φ (S.q.holds φ') ps (os.getD (o - 1) pt) fs kf := by
  obtain ⟨hpos', hk, hrec⟩ := mem_recFields hkf
  obtain ⟨k, f⟩ := kf
  have hsc := (hS.2.2.2.1 c hc).1 _ f hpos'
  rw [show c.fields.length - 1 - (c.fields.length - 1 - k) = k by omega] at hsc
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  -- the motive, sitting above the hypotheses, the fields and the extras
  have hhead : consList ihsE (consList fs (consList os (consList ps ρ)))
      (c.fields.length + l + o - 1) = os.getD (o - 1) pt := by
    rw [show c.fields.length + l + o - 1 = ((o - 1) + c.fields.length) + l by omega, ← hi,
      consList_ge, ← hf, consList_ge, consList_getD (by omega)]
  -- the field, sitting above the hypotheses
  have hfv : consList ihsE (consList fs (consList os (consList ps ρ)))
      (c.fields.length - 1 - k + l) = fieldVal fs k := by
    rw [← hi, consList_ge, consList_getD (by omega), fieldVal, hf]
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | recursive es =>
    simp only [ihTy, ihSet]
    rw [interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map, List.map_singleton,
      interp_bvar, hhead, hfv]
    congr 2
    unfold idxVals
    rw [List.reverse_reverse]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    have h1 := interp_atCtx M' φ' ρ e (ys := []) (d := 0) (k := k) (ps := ps) rfl hi hf ho (by omega)
    simp only [consList_nil] at h1
    rw [h1, hkd]
    exact R.read (hsc.2 e he) (by simp [earlier, hf, hps]; omega)
  | reflexive tele es =>
    simp only [ihTy, ihSet]
    rw [interp_mkPis, R.piCtx_liftCtx_atCtx hi hf ho (by omega) hps _ tele hsc.1, hkd]
    refine piCtx_congr M _ fun ys hys => ?_
    have hl := FitsVals_length M _ hys
    rw [readEnv_consList hl, interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map,
      List.map_singleton, interp_mkAppN_appList, interp_bvar, interp_varsAt, shiftE_zero_zero,
      readEnv_consList hl]
    rw [show c.fields.length + l + o - 1 + tele.length = c.fields.length + l + o - 1 + ys.length by
      rw [hl], consList_ge, hhead]
    rw [show c.fields.length - 1 - k + l + tele.length = c.fields.length - 1 - k + l + ys.length by
      rw [hl], consList_ge, hfv]
    congr 2
    unfold idxVals
    rw [List.reverse_reverse]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    rw [interp_atCtx M' φ' ρ e (k := k) hl hi hf ho (by omega), hkd,
      ← consList_append ys (earlier fs k) (consList ps ρ),
      ← consList_append ys (earlier fs k) (envP ps)]
    exact R.read (hsc.2.2 e he) (by simp [earlier, hf, hps, hl]; omega)

end Readings

end IndSpec

end Fragment
