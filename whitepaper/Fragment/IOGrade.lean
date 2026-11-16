module

public import Fragment.Sound

public section

/-!
# The fast-inference grade (task #346)

Lean's kernel infers the type of a term it has already checked with
`infer_only`: an application's type is the head's codomain at the
argument, and the argument's type is never compared with the binder's
domain.  `InferIO` is that grade on the fragment's terms
(`Syntax.lean`).  The question of task #346: what does an
io-inferred type say about the term, in the value-driven model of task
#344, and which consumers can use it?

**The claim** (`IORel`, `inferIO_sound`).  An io-inferred type does
not hold the term: `(fun (h : False) => (h.elim : Nat)) 0` is
well-denoted, denotes the point (an abstraction over an empty domain),
and the point is no member of `Nat`.  The claim "a member unless the
point" fails at λ: `fun (x : Bool) => h x 0` with
`h : (b : Bool) → Bool.rec False Nat b → Nat` is a graph that is the
point at `false` and not in `Bool → Nat`.  What holds is the
**hereditary** claim: the value is the point, or a member of the type,
or — when the type is syntactically a `∀` — a graph over the `∀`'s
domain, not everywhere the point, whose every application satisfies
the claim at the `∀`'s body.  It is keyed on the type's *syntax*: two
`∀`s with equal values need not have equal domains, and a `∀` of sort
`Type` may denote a truth value with a non-point inhabitant
(`IOWitness.lean`, `io_type_value_collision`: `(x : Prop) → E x` with
an empty fibre), so a claim read off the type's value alone can be
carried neither through an application nor to proof irrelevance.  It is proved for every rule of `InferIO`, with no
certificate at any binder: at an application whose head is not the
point the head is a graph, and a graph determines its domain
(`SetLib.graph_dom_unique`), which is therefore the one the application
clause (`AppliesTo`) puts the argument in.

**The consumers.**
* Proof irrelevance (`eq_pt_of_inferIO_prop`, `proofIrrelIO_sound`):
  if the io-inferred type's io-inferred type reduces to `Prop`, the
  term is the point.  The hereditary case needs the *syntactic* sort:
  a `∀` whose sort is `Prop` has a body whose sort is `Prop`, and the
  claim descends.
* η against a term whose head is a variable or a constant
  (`etaIO_sound`): such a term's claim is never the hereditary one
  (`IORel_neutral`), so where it is not the point it is a member, and
  η's proof runs as with the full grade.  The checker's η meets a
  term in weak-head normal form that is not a λ, which has such a
  head.
* The λ/η body-type comparison is NOT a consumer: with io-inferred
  bodies' types it is unsound in the model, whatever the io claim
  (`IOWitness.lean`, `lam_congr_io_unsound`, `eta_body_io_unsound`).
-/

namespace Fragment
open SetLib Expr

universe u

/-- **The fast-inference grade** (Lean's `infer_only`): the rules of
`Infer` without the application's argument check and without the lambda's
domain check.  `∀`-formation still infers the sorts, which its result
needs. -/
inductive InferIO [LevelOracle] (env : Env) : List Expr → Expr → Expr → Prop where
  /-- A bound variable: its context entry. -/
  | bvar {Γ : List Expr} {i : Nat} {A : Expr} :
      Γ[i]? = some A → InferIO env Γ (bvar i) (A.liftN (i + 1))
  /-- `Sort u : Sort (u + 1)`. -/
  | sort {Γ : List Expr} {u : Level} : InferIO env Γ (sort u) (sort (.succ u))
  /-- A stored constant: its declared type. -/
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} :
      env.find? c = some ci → ls.length = ci.lparams.length →
      InferIO env Γ (const c ls) (ci.type.instL ci.lparams ls)
  /-- `∀`-formation: the sorts of the domain and the body. -/
  | pi {Γ : List Expr} {A B s t : Expr} {u v : Level} :
      InferIO env Γ A s → Red env Γ s (sort u) →
      InferIO env (A :: Γ) B t → Red env (A :: Γ) t (sort v) →
      InferIO env Γ (pi A B) (sort (.imax u v))
  /-- Lambda: the `∀` of the body's type; the domain is not checked. -/
  | lam {Γ : List Expr} {A b bt : Expr} :
      InferIO env (A :: Γ) b bt → InferIO env Γ (lam A b) (pi A bt)
  /-- **Application without a certificate**: the head's type reduces
  to a `∀`, and the result is its body at the argument.  The
  argument's type is not inferred. -/
  | app {Γ : List Expr} {f a tf A B : Expr} :
      InferIO env Γ f tf → Red env Γ tf (pi A B) →
      InferIO env Γ (app f a) (B.inst a)
  /-- **`let`, by substitution**:
  as official `infer_only`, the value is not checked
  against the type — the full grade (`Infer.letE`) checks it — and the
  body with the value substituted is inferred at the io grade.  The
  soundness proof needs no check on the value (`InferIO.letE_sound`). -/
  | letE {Γ : List Expr} {T v b B : Expr} :
      InferIO env Γ (b.inst v) B →
      InferIO env Γ (letE T v b) B

/-! ## Reductions of sorts and `∀`s are trivial -/

theorem rigid_app (f a : Expr) :
    ¬ ((∃ A B, app f a = pi A B) ∨ (∃ u, app f a = sort u)) := by
  intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

theorem mkAppN_ne_of {P : Expr → Prop} (hP : ∀ f a, ¬ P (app f a)) :
    ∀ (args : List Expr) (f : Expr), ¬ P f → ¬ P (mkAppN f args)
  | [], _, h => h
  | a :: args, f, _ => mkAppN_ne_of hP args (app f a) (hP f a)

/-- A `∀` or a sort reduces only to itself. -/
theorem Red.eq_of_rigid [LevelOracle] {env : Env} {Γ : List Expr} {e e' : Expr} :
    Red env Γ e e' → ((∃ A B, e = pi A B) ∨ (∃ u, e = sort u)) → e' = e
  | .refl, _ => rfl
  | .trans h₁ h₂, hr => by
    have e₁ := Red.eq_of_rigid h₁ hr
    subst e₁
    exact Red.eq_of_rigid h₂ hr
  | .appFn _, hr => by rcases hr with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  | .beta, hr => by rcases hr with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  | .delta _ _ _, hr => by rcases hr with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  | .iota (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaProp (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaNested (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaSlot (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaNestedSlot (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaStrict (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaNestedStrict (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))
  | .iotaK (args := args) .., hr =>
    absurd hr (mkAppN_ne_of (P := fun e => (∃ A B, e = pi A B) ∨ ∃ u, e = sort u) rigid_app args _ (by
      intro h; rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h))

/-! ## The hereditary claim -/

variable {V : Type u} [SetLib V] (M : Name → List Nat → V) (φ : Name → Nat)

/-- **Membership with the type's invariant.** -/
def IOMem (T : Expr) (ρ : Nat → V) (v : V) : Prop :=
  WellDenoted M φ ρ T ∧ IsTy (interp M φ ρ T) ∧ v ∈ˢ interp M φ ρ T

/-- **The hereditary part**, by recursion on the type's syntax: at a
`∀`, a graph over its domain that is not everywhere the point, whose
applications satisfy the claim at the body.  Nothing at any other
type. -/
def IOHered : Expr → (Nat → V) → V → Prop
  | .pi A B, ρ, v =>
    WellDenoted M φ ρ A ∧ IsTy (interp M φ ρ A) ∧
      (∃ F : V → V, v = graph F (interp M φ ρ A)) ∧
      (∃ x, x ∈ˢ interp M φ ρ A ∧ app v x ≠ pt) ∧
      ∀ x, x ∈ˢ interp M φ ρ A →
        app v x = pt ∨ IOMem M φ B (cons x ρ) (app v x) ∨ IOHered B (cons x ρ) (app v x)
  | .bvar _, _, _ => False
  | .sort _, _, _ => False
  | .const _ _, _, _ => False
  | .app _ _, _, _ => False
  | .lam _ _, _, _ => False
  | .letE _ _ _, _, _ => False

/-- **The io claim**: the point, a member, or hereditarily a member. -/
def IORel (T : Expr) (ρ : Nat → V) (v : V) : Prop :=
  v = pt ∨ IOMem M φ T ρ v ∨ IOHered M φ T ρ v

theorem IOHered_pi {A B : Expr} {ρ : Nat → V} {v : V} :
    IOHered M φ (.pi A B) ρ v ↔
      WellDenoted M φ ρ A ∧ IsTy (interp M φ ρ A) ∧
      (∃ F : V → V, v = graph F (interp M φ ρ A)) ∧
      (∃ x, x ∈ˢ interp M φ ρ A ∧ app v x ≠ pt) ∧
      ∀ x, x ∈ˢ interp M φ ρ A → IORel M φ B (cons x ρ) (app v x) := Iff.rfl

theorem IOHered_not_pi {T : Expr} {ρ : Nat → V} {v : V} (h : IOHered M φ T ρ v) :
    ∃ A B, T = .pi A B := by
  cases T with
  | pi A B => exact ⟨A, B, rfl⟩
  | _ => exact h.elim

/-- **The claim through instantiation** (one direction suffices: a
type that is not a `∀` may become one, and membership is part of the
`∀`'s claim). -/
theorem IORel_inst :
    ∀ (B a : Expr) (k : Nat) (ρ : Nat → V) (v : V),
      WellDenoted M φ (shiftE k 0 ρ) a →
      IORel M φ B (instE k (interp M φ (shiftE k 0 ρ) a) ρ) v →
      IORel M φ (B.inst a k) ρ v := by
  intro B
  induction B with
  | pi C D _ ihD =>
    intro a k ρ v ha h
    rcases h with h | ⟨hw, hT, hm⟩ | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · exact (WellDenoted_inst M φ _ a k ρ ha).mpr hw
      · rw [interp_inst]; exact hT
      · rw [interp_inst]; exact hm
    · rw [IOHered_pi] at h
      obtain ⟨hwC, hTC, hB', hx₀, hall⟩ := h
      refine Or.inr (Or.inr ?_)
      rw [Expr.inst_pi, IOHered_pi, interp_inst]
      refine ⟨(WellDenoted_inst M φ _ a k ρ ha).mpr hwC, hTC, hB', hx₀, fun x hx => ?_⟩
      have ha' : WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
        rwa [shiftE_succ_cons]
      refine ihD a (k + 1) (cons x ρ) _ ha' ?_
      rw [shiftE_succ_cons, ← cons_instE]
      exact hall x hx
  | _ =>
    intro a k ρ v ha h
    rcases h with h | ⟨hw, hT, hm⟩ | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · exact (WellDenoted_inst M φ _ a k ρ ha).mpr hw
      · rw [interp_inst]; exact hT
      · rw [interp_inst]; exact hm
    · exact h.elim

theorem IORel_inst0 {B a : Expr} {ρ : Nat → V} {v : V} (ha : WellDenoted M φ ρ a)
    (h : IORel M φ B (cons (interp M φ ρ a) ρ) v) : IORel M φ (B.inst a) ρ v := by
  refine IORel_inst M φ B a 0 ρ v (by rwa [shiftE_zero_zero]) ?_
  rwa [shiftE_zero_zero, instE_zero]

theorem IOMem_inst0 {B a : Expr} {ρ : Nat → V} {v : V} (ha : WellDenoted M φ ρ a)
    (h : IOMem M φ B (cons (interp M φ ρ a) ρ) v) : IOMem M φ (B.inst a) ρ v := by
  obtain ⟨hw, hT, hm⟩ := h
  refine ⟨(WellDenoted_inst0 M φ ha).mpr hw, ?_, ?_⟩
  · rw [interp_inst0]; exact hT
  · rw [interp_inst0]; exact hm

variable [LevelOracle] {env : Env} {m : EnvModel V env} {φ}

/-- **The claim along a reduction of the type**: a type that is not
the point keeps its value; a `∀` reduces only to itself. -/
theorem IORel_red {Γ : List Expr} {T T' : Expr} {ρ : Nat → V} {v : V}
    (hr : Red env Γ T T') (hs : Sat m.M φ Γ ρ) (h : IORel m.M φ T ρ v) :
    IORel m.M φ T' ρ v := by
  rcases h with h | ⟨hw, hT, hm⟩ | h
  · exact Or.inl h
  · obtain ⟨hw', he⟩ := red_sound (m := m) (φ := φ) hr ρ hs hw hT.ne_pt
    exact Or.inr (Or.inl ⟨hw', he ▸ hT, he ▸ hm⟩)
  · obtain ⟨A, B, rfl⟩ := IOHered_not_pi m.M φ h
    rw [hr.eq_of_rigid (Or.inl ⟨A, B, rfl⟩)]
    exact Or.inr (Or.inr h)

theorem IOMem_red {Γ : List Expr} {T T' : Expr} {ρ : Nat → V} {v : V}
    (hr : Red env Γ T T') (hs : Sat m.M φ Γ ρ) (h : IOMem m.M φ T ρ v) :
    IOMem m.M φ T' ρ v := by
  obtain ⟨hw, hT, hm⟩ := h
  obtain ⟨hw', he⟩ := red_sound (m := m) (φ := φ) hr ρ hs hw hT.ne_pt
  exact ⟨hw', he ▸ hT, he ▸ hm⟩

/-- `InferIO`'s claim: for a well-denoted subject, the hereditary
claim at the inferred type. -/
def InferIOSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (e T : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ e → IORel m.M φ T ρ (interp m.M φ ρ e)

omit [LevelOracle] in
theorem IOMem_of_inferSem {Γ : List Expr} {e T : Expr} (h : InferSem m φ Γ e T) :
    InferIOSem m φ Γ e T :=
  fun ρ hs _ => Or.inr (Or.inl (h ρ hs).2)

/-- **The application, without a certificate.**  Where the head is
not the point it is a graph over a domain holding the argument
(`AppliesTo`); a graph determines its domain, so the argument lies in the
domain of the `∀` the head's type reduces to — in both the member and
the hereditary case. -/
theorem InferIO.app_sound {Γ : List Expr} {f a tf A B : Expr}
    (hf : InferIOSem m φ Γ f tf) (hr : Red env Γ tf (.pi A B)) :
    InferIOSem m φ Γ (.app f a) (B.inst a) := by
  intro ρ hs hw
  rw [WellDenoted_app] at hw
  obtain ⟨hwf, hwa, hap⟩ := hw
  have hrel := IORel_red hr hs (hf ρ hs hwf)
  rw [interp_app]
  by_cases hfp : interp m.M φ ρ f = pt
  · rw [hfp, app_pt]; exact Or.inl rfl
  refine IORel_inst0 m.M φ hwa ?_
  rcases hrel with h | ⟨hwpi, -, hmpi⟩ | h
  · exact absurd h hfp
  · rw [interp_pi] at hmpi
    have hgr := mem_piSet_of_mem_piV hmpi hfp
    have haA : interp m.M φ ρ a ∈ˢ interp m.M φ ρ A := hap.mem hgr
    rw [WellDenoted_pi] at hwpi
    exact Or.inr (Or.inl ⟨hwpi.2.2.1 _ haA, hwpi.2.2.2 _ haA, app_mem_piSet hgr haA⟩)
  · rw [IOHered_pi] at h
    obtain ⟨-, -, ⟨F, hF⟩, -, hall⟩ := h
    rw [hF] at hap
    exact hall _ (appliesTo_graph.mp hap).2

omit [LevelOracle] in
/-- **λ**: where every body value is the point, so is the abstraction;
otherwise it is the graph of its body values, over its own domain. -/
theorem InferIO.lam_sound {Γ : List Expr} {A b bt : Expr}
    (hb : InferIOSem m φ (A :: Γ) b bt) : InferIOSem m φ Γ (.lam A b) (.pi A bt) := by
  intro ρ hs hw
  rw [WellDenoted_lam] at hw
  obtain ⟨hwA, hTA, hwb⟩ := hw
  rw [interp_lam]
  by_cases hall : ∀ x, x ∈ˢ interp m.M φ ρ A → interp m.M φ (cons x ρ) b = pt
  · exact Or.inl (lamV_eq_pt hall)
  have hne : lamV (interp m.M φ ρ A) (fun x => interp m.M φ (cons x ρ) b) ≠ pt := by
    intro h
    exact hall fun x hx => Classical.byContradiction fun hx' => (lamV_ne_pt_of hx hx') h
  rw [lamV_eq_graph hne]
  refine Or.inr (Or.inr ?_)
  rw [IOHered_pi]
  obtain ⟨x₀, hx₀, hx₀'⟩ : ∃ x, x ∈ˢ interp m.M φ ρ A ∧ interp m.M φ (cons x ρ) b ≠ pt :=
    Classical.byContradiction fun hn => hall fun x hx =>
      Classical.byContradiction fun hx' => hn ⟨x, hx, hx'⟩
  refine ⟨hwA, hTA, ⟨_, rfl⟩, ⟨x₀, hx₀, by rw [app_graph hx₀]; exact hx₀'⟩,
    fun x hx => ?_⟩
  rw [app_graph hx]
  exact hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩) (hwb x hx)

/-- **`∀`-formation**: the sorts' claims, at a type that is not the
point, are memberships. -/
theorem InferIO.pi_sound {Γ : List Expr} {A B s t : Expr} {u v : Level}
    (hA : InferIOSem m φ Γ A s) (hu : Red env Γ s (.sort u))
    (hB : InferIOSem m φ (A :: Γ) B t) (hv : Red env (A :: Γ) t (.sort v)) :
    InferIOSem m φ Γ (.pi A B) (.sort (.imax u v)) := by
  have sortMem : ∀ {Δ : List Expr} {X s : Expr} {w : Level} {σ : Nat → V},
      InferIOSem m φ Δ X s → Red env Δ s (.sort w) → Sat m.M φ Δ σ →
      WellDenoted m.M φ σ X → IsTy (interp m.M φ σ X) →
      interp m.M φ σ X ∈ˢ typeU (Level.eval φ w) := by
    intro Δ X s w σ hX hw hs hwX hTX
    rcases IORel_red hw hs (hX σ hs hwX) with h | ⟨-, -, h⟩ | h
    · exact absurd h hTX.ne_pt
    · exact h
    · exact (IOHered_not_pi m.M φ h).elim fun _ ⟨_, h⟩ => by cases h
  intro ρ hs hw
  have hw' := hw
  rw [WellDenoted_pi] at hw'
  obtain ⟨hwA, hTA, hwB, hTB⟩ := hw'
  refine Or.inr (Or.inl ⟨trivial, Or.inr (strict_typeU _), ?_⟩)
  rw [interp_pi, interp_sort, Level.eval_imax]
  exact piV_mem_typeU (sortMem hA hu hs hwA hTA) fun x hx =>
    sortMem hB hv ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩) (hwB x hx) (hTB x hx)

omit [LevelOracle] in
/-- **`let`, by substitution** (task #342, F4): the `let` denotes what
the instantiated body denotes (`interp_zeta`), and is well-denoted
exactly when the body is at the value (`WellDenoted_letE`), so the
body's claim is the `let`'s.  Nothing about the value is needed, so
the rule checks nothing about it. -/
theorem InferIO.letE_sound {Γ : List Expr} {T v b B : Expr}
    (hb : InferIOSem m φ Γ (b.inst v) B) : InferIOSem m φ Γ (.letE T v b) B := by
  intro ρ hs hw
  rw [WellDenoted_letE] at hw
  rw [interp_zeta]
  exact hb ρ hs ((WellDenoted_inst0 m.M φ hw.1).mpr hw.2)

/-- **Soundness of the io grade**: every io-inferred type satisfies
the hereditary claim. -/
theorem inferIO_sound : ∀ {Γ : List Expr} {e T : Expr},
    InferIO env Γ e T → InferIOSem m φ Γ e T
  | _, _, _, .bvar h => IOMem_of_inferSem (Infer.bvar_sound h)
  | _, _, _, .sort => IOMem_of_inferSem Infer.sort_sound
  | _, _, _, .const hfind hls => IOMem_of_inferSem (Infer.const_sound hfind hls)
  | _, _, _, .pi hA hu hB hv =>
    InferIO.pi_sound (inferIO_sound hA) hu (inferIO_sound hB) hv
  | _, _, _, .lam hb => InferIO.lam_sound (inferIO_sound hb)
  | _, _, _, .app hf hr => InferIO.app_sound (inferIO_sound hf) hr
  | _, _, _, .letE hb => InferIO.letE_sound (inferIO_sound hb)

/-! ## Consumer: proof irrelevance -/

/-- **A term whose io-inferred type has io-inferred sort `Prop` is the
point.**  A member of the type: the type is a truth value.  Hereditary:
the type is a `∀` whose sort is `Prop`, so its body's sort is `Prop`
(inversion of `InferIO.pi`; a sort reduces only to itself), and every
application is the point, against the clause's witness. -/
theorem eq_pt_of_IORel_prop :
    ∀ (T : Expr) {Γ : List Expr} {tt : Expr} {u : Level} {ρ : Nat → V} {v : V},
      InferIO env Γ T tt → Red env Γ tt (.sort u) → Level.eval φ u = 0 →
      Sat m.M φ Γ ρ → IORel m.M φ T ρ v → v = pt := by
  intro T
  induction T with
  | pi A B _ ihB =>
    intro Γ tt u ρ v hT hr hu hs h
    rcases h with h | ⟨hw, hTy, hm⟩ | h
    · exact h
    · rcases IORel_red hr hs (inferIO_sound (m := m) (φ := φ) hT ρ hs hw) with h' | ⟨-, -, h'⟩ | h'
      · exact absurd h' hTy.ne_pt
      · rw [show interp m.M φ ρ (Expr.sort u) = typeU 0 by rw [interp_sort, hu]] at h'
        exact eq_pt_of_mem_univ_zero (mem_typeU_zero.mp h') hm
      · exact (IOHered_not_pi m.M φ h').elim fun _ ⟨_, h⟩ => by cases h
    · rw [IOHered_pi] at h
      obtain ⟨hwA, hTA, -, ⟨x₀, hx₀, hne⟩, hall⟩ := h
      cases hT with
      | pi _ _ hB hv =>
        rename_i u₁ v₁ _ _
        have he := hr.eq_of_rigid (Or.inr ⟨_, rfl⟩)
        cases he
        simp only [Level.eval_imax] at hu
        have hv0 := (Level.imaxNat_eq_zero_iff _ _).mp hu
        exact absurd (ihB hB hv hv0 ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx₀⟩)
          (hall x₀ hx₀)) hne
  | _ =>
    intro Γ tt u ρ v hT hr hu hs h
    rcases h with h | ⟨hw, hTy, hm⟩ | h
    · exact h
    · rcases IORel_red hr hs (inferIO_sound (m := m) (φ := φ) hT ρ hs hw) with h' | ⟨-, -, h'⟩ | h'
      · exact absurd h' hTy.ne_pt
      · rw [show interp m.M φ ρ (Expr.sort u) = typeU 0 by rw [interp_sort, hu]] at h'
        exact eq_pt_of_mem_univ_zero (mem_typeU_zero.mp h') hm
      · exact (IOHered_not_pi m.M φ h').elim fun _ ⟨_, h⟩ => by cases h
    · exact h.elim

/-- **Proof irrelevance with io-inferred types and sorts** is sound:
the left side is the point, so the claim is vacuous. -/
theorem proofIrrelIO_sound {Γ : List Expr} {a ta tta b : Expr} {u : Level}
    (hta : InferIO env Γ a ta) (htta : InferIO env Γ ta tta) (hu : Red env Γ tta (.sort u))
    (hu0 : LevelOracle.eq u .zero = true) :
    DefEqSem m φ Γ a b := by
  intro ρ hs hwa _ hna _
  exact absurd (eq_pt_of_IORel_prop ta htta hu
    (by rw [eval_eq_of_oracle hu0, Level.eval_zero]) hs
    (inferIO_sound (m := m) (φ := φ) hta ρ hs hwa)) hna

/-! ## Consumer: η against a variable- or constant-headed term -/

/-- A term whose head (under its applications) is a variable or a
constant. -/
def Expr.atomHead : Expr → Prop
  | .bvar _ => True
  | .const _ _ => True
  | .app f _ => Expr.atomHead f
  | _ => False

/-- **The claim of an atom-headed term is never hereditary**: such a
term is the point or a member of its io-inferred type. -/
theorem IORel_neutral : ∀ {Γ : List Expr} {e T : Expr},
    InferIO env Γ e T → e.atomHead →
    ∀ ρ, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ e →
      interp m.M φ ρ e = pt ∨ IOMem m.M φ T ρ (interp m.M φ ρ e)
  | _, _, _, .bvar h, _ => fun ρ hs _ => Or.inr (Infer.bvar_sound (m := m) h ρ hs).2
  | _, _, _, .const hfind hls, _ => fun ρ hs _ =>
    Or.inr (Infer.const_sound (m := m) hfind hls ρ hs).2
  | _, _, _, .app (f := f) (a := a) (A := A) (B := B) hf hr, hh => by
    intro ρ hs hw
    have hw' := hw
    rw [WellDenoted_app] at hw'
    obtain ⟨hwf, hwa, hap⟩ := hw'
    rw [interp_app]
    rcases IORel_neutral hf hh ρ hs hwf with hfp | hm
    · rw [hfp, app_pt]; exact Or.inl rfl
    by_cases hfp : interp m.M φ ρ f = pt
    · rw [hfp, app_pt]; exact Or.inl rfl
    obtain ⟨hwpi, -, hmpi⟩ := IOMem_red hr hs hm
    rw [interp_pi] at hmpi
    have hgr := mem_piSet_of_mem_piV hmpi hfp
    have haA : interp m.M φ ρ a ∈ˢ interp m.M φ ρ A := hap.mem hgr
    rw [WellDenoted_pi] at hwpi
    exact Or.inr (IOMem_inst0 m.M φ hwa
      ⟨hwpi.2.2.1 _ haA, hwpi.2.2.2 _ haA, app_mem_piSet hgr haA⟩)

/-- **η with the term's type io-inferred**, for a term with a variable
or constant head: sound.  (For a λ it is not, `IOWitness.lean`.) -/
theorem etaIO_sound {Γ : List Expr} {A₁ b₁ b tb A₂ B t₁ : Expr}
    (htb : InferIO env Γ b tb) (hb : b.atomHead) (hr : Red env Γ tb (.pi A₂ B))
    (hA : DefEqSem m φ Γ A₂ A₁)
    (hbody : DefEqSem m φ (A₁ :: Γ) b₁ (.app (b.liftN 1) (.bvar 0)))
    (ht₁ : InferSem m φ (A₁ :: Γ) b₁ t₁) (htB : DefEqSem m φ (A₁ :: Γ) t₁ B) :
    DefEqSem m φ Γ (.lam A₁ b₁) b :=
  DefEq.eta_sound (fun ρ hs hwb hnb =>
      (IORel_neutral htb hb ρ hs hwb).resolve_left hnb)
    (red_sound hr) hA hbody ht₁ htB

end Fragment
