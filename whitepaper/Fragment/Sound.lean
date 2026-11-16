module

public import Fragment.Motive
public import Fragment.Tele
import Fragment.Hygiene

public section

/-!
# Soundness: derivation ⇒ claim

**One mutual structural induction over the three relations**
(`red_sound`/`defeq_sound`/`infer_sound` at the end of this file);
every case is one lemma about one rule, stated over the environment's
laws (`EnvModel`) and the library (`SetLib`), never over an
implementation.  This is the shape of `ConLeche/Model/Rules/Sound.lean`
and its per-rule lemma files, on the fragment.

The case split proof/non-proof is in the proof and only there.  A
reduction claims nothing of a subject that denotes the point; on one
that does not, β is sound at *every* binder: the redex is not the
point, so its λ is not (`app pt _ = pt`), so the λ is a graph
(`SetLib.lamV_eq_graph`), which determines its domain
(`Red.beta_sound`).  A binder carries its domain alone (task #344): the
interpretation reads the regime off the values, and the two rules that
need two terms' proof-ness to agree at every value of a variable —
λ-congruence and η — compare their bodies' types.  Whether a subject denotes the point is
never decided by the checker: the definitional-equality claim is about
two sides that do not, and the typed invariant makes the proof-ness of
the two sides of every sub-comparison agree (an application's graph
head has a type as domain, so its members are all the point or none of it,
`DefEq.app_sound`).  Inferred types are types (`InferSem`), hence never
the point, so the reductions of types that inference runs are sound
outright.

The cases the paper dwells on, each its own lemma:

* `Red.beta_sound` — β at every binder, with no premise;
* `Red.iota_core` and `major_eq` — ι with no condition on how the
  major reduces, even on a recursion over proofs: the major's binder domain is
  a type, so the major and its reduct are both the point or neither is;
* `DefEq.eta_sound` — η, from the library's η law;
* `Red.zeta_sound`, `Infer.letE_sound` — `let` by substitution: ζ is
  an identity at every environment (`interp_zeta`), and the type checks
  on the value are not used (`Infer.letE_sat` is what they give);
* `DefEq.proofIrrel_sound` — proof irrelevance claims nothing: two
  proofs are the point, and the claim is about non-proofs;
* `Infer.app_sound` — the application rule, where no Π-injectivity is
  needed.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## Small facts -/

/-- The oracle's `eq` is `eval`-equality at the valuation. -/
theorem eval_eq_of_oracle [LevelOracle] {u v : Level} (h : LevelOracle.eq u v = true) :
    Level.eval φ u = Level.eval φ v :=
  (LevelOracle.eq_iff u v).mp h φ

/-- A list of length `n + 1` is its first `n` elements and its last. -/
theorem List.take_append_getD {α : Type} (d : α) :
    ∀ (l : List α) (n : Nat), l.length = n + 1 → l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | _ :: l, 0, h => by
    simp at h
    simp [h]
  | a :: l, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [← take_append_getD d l n h]

/-- The head of an application that is not the point is not the point. -/
theorem fn_ne_pt {f a : Expr} {ρ : Nat → V}
    (h : interp m.M φ ρ (.app f a) ≠ pt) : interp m.M φ ρ f ≠ pt := by
  intro hf; apply h; rw [interp_app, hf, app_pt]

/-! ## Reduction -/

namespace Red

theorem refl_sound {Γ : List Expr} {e : Expr} : RedSem m φ Γ e e :=
  fun _ _ h _ => ⟨h, rfl⟩

theorem trans_sound {Γ : List Expr} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ Γ e₁ e₂) (h₂ : RedSem m φ Γ e₂ e₃) : RedSem m φ Γ e₁ e₃ := by
  intro ρ hs hw hn
  obtain ⟨hw₁, he₁⟩ := h₁ ρ hs hw hn
  obtain ⟨hw₂, he₂⟩ := h₂ ρ hs hw₁ (he₁ ▸ hn)
  exact ⟨hw₂, he₁.trans he₂⟩

theorem appFn_sound {Γ : List Expr} {f f' a : Expr} (h : RedSem m φ Γ f f') :
    RedSem m φ Γ (.app f a) (.app f' a) := by
  intro ρ hs hw hn
  rw [WellDenoted_app] at hw
  obtain ⟨hf, ha, hap⟩ := hw
  obtain ⟨hf', he⟩ := h ρ hs hf (fn_ne_pt hn)
  refine ⟨?_, by simp [he]⟩
  rw [WellDenoted_app]
  exact ⟨hf', ha, by rw [← he]; exact hap⟩

/-- **β at every binder, with no premise** — `beta_of_ne_pt`.  The
redex is not the point, so neither is its lambda; a lambda that is not the point
is the graph of its body over its own domain; the application clause (`AppliesTo`)
puts the argument in that domain. -/
theorem beta_sound {Γ : List Expr} {A b a : Expr} :
    RedSem m φ Γ (.app (.lam A b) a) (b.inst a) := by
  intro ρ _ hw hn
  rw [WellDenoted_app] at hw
  obtain ⟨hl, ha, hap⟩ := hw
  rw [WellDenoted_lam] at hl
  obtain ⟨-, -, hbody⟩ := hl
  have hlam := fn_ne_pt hn
  have hval : interp m.M φ ρ (.lam A b) =
      graph (fun x => interp m.M φ (cons x ρ) b) (interp m.M φ ρ A) := by
    rw [interp_lam] at hlam ⊢; exact lamV_eq_graph hlam
  rw [hval] at hap
  have haA : interp m.M φ ρ a ∈ˢ interp m.M φ ρ A := (appliesTo_graph.mp hap).2
  refine ⟨(WellDenoted_inst0 m.M φ ha).mpr (hbody _ haA), ?_⟩
  rw [interp_app, interp_lam, app_lamV haA, interp_inst0]

/-- **ζ, with no certificate**: the `let` and its
reduct denote alike at every environment (`interp_zeta`), so neither
the point hypothesis nor the context is used; the reduct's invariant is
the `let`'s, through the substitution lemma. -/
theorem zeta_sound {Γ : List Expr} {T v b : Expr} :
    RedSem m φ Γ (.letE T v b) (b.inst v) := by
  intro ρ _ hw _
  rw [WellDenoted_letE] at hw
  exact ⟨(WellDenoted_inst0 m.M φ hw.1).mpr hw.2, interp_zeta m.M φ T v b ρ⟩

theorem delta_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr}
    (hfind : env.find? c = some ci) (hv : ci.value? = some v)
    (hls : ls.length = ci.lparams.length) :
    RedSem m φ Γ (.const c ls) (v.instL ci.lparams ls) := by
  intro ρ _ _ _
  obtain ⟨hw, he⟩ := m.unfold c ci v hfind hv φ ρ ls hls
  exact ⟨hw, by rw [interp_const, he]⟩

end Red

/-! ## Definitional equality -/

namespace DefEq

theorem refl_sound {Γ : List Expr} {a : Expr} : DefEqSem m φ Γ a a :=
  fun _ _ _ _ _ _ => rfl

theorem symm_sound {Γ : List Expr} {a b : Expr} (h : DefEqSem m φ Γ a b) :
    DefEqSem m φ Γ b a :=
  fun ρ hs hb ha hnb hna => (h ρ hs ha hb hna hnb).symm

/-- Reduce, then continue — sound with no typing: the side is not the
point, so its reduction is. -/
theorem redL_sound {Γ : List Expr} {a a' b : Expr}
    (hr : RedSem m φ Γ a a') (h : DefEqSem m φ Γ a' b) : DefEqSem m φ Γ a b := by
  intro ρ hs ha hb hna hnb
  obtain ⟨ha', he⟩ := hr ρ hs ha hna
  exact he.trans (h ρ hs ha' hb (he ▸ hna) hnb)

theorem sort_sound [LevelOracle] {Γ : List Expr} {u v : Level} (h : LevelOracle.eq u v = true) :
    DefEqSem m φ Γ (.sort u) (.sort v) :=
  fun _ _ _ _ _ _ => by simp [eval_eq_of_oracle h]

theorem const_sound [LevelOracle] {Γ : List Expr} {c : Name} {ls ls' : List Level}
    (h : Level.eqList ls ls' = true) : DefEqSem m φ Γ (.const c ls) (.const c ls') :=
  fun _ _ _ _ _ _ => by simp [(Level.eqList_iff ls ls').mp h φ]

/-- **`∀`-congruence, with no premise beyond domains and bodies**:
a `∀`'s value is a function of its domain's and fibres' values
(`SetLib.piV_congr`), and both are types, never the point. -/
theorem pi_sound {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr}
    (hA : DefEqSem m φ Γ A₁ A₂) (hB : DefEqSem m φ (A₂ :: Γ) B₁ B₂) :
    DefEqSem m φ Γ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro ρ hs h₁ h₂ _ _
  rw [WellDenoted_pi] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  have hfib : ∀ x, x ∈ˢ interp m.M φ ρ A₂ →
      interp m.M φ (cons x ρ) B₁ = interp m.M φ (cons x ρ) B₂ := by
    intro x hx
    have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
    exact hB (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂.1, h₂.2.1, hx⟩) (h₁.2.2.1 x hx₁)
      (h₂.2.2.1 x hx) (h₁.2.2.2 x hx₁).ne_pt (h₂.2.2.2 x hx).ne_pt
  simp only [interp_pi]
  rw [heA]
  exact piV_congr hfib

/-- **Lambda congruence, typed**: the two bodies lie in one type
at every value of the variable — their inferred types are equal there
— so they are both the point or neither is, and where neither is the
bodies' claim makes them equal.  Neither lambda need be a graph. -/
theorem lam_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ t₁ t₂ : Expr}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂)
    (ht₁ : InferSem m φ (A₂ :: Γ) b₁ t₁) (ht₂ : InferSem m φ (A₂ :: Γ) b₂ t₂)
    (ht : DefEqSem m φ (A₂ :: Γ) t₁ t₂) :
    DefEqSem m φ Γ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hs h₁ h₂ _ _
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_lam]
  rw [heA]
  apply lamV_congr
  intro x hx
  have hs' : Sat m.M φ (A₂ :: Γ) (cons x ρ) := (Sat_cons m.M φ).mpr ⟨hs, h₂.1, h₂.2.1, hx⟩
  obtain ⟨hw₁, hwt₁, hT₁, hm₁⟩ := ht₁ _ hs'
  obtain ⟨hw₂, hwt₂, hT₂, hm₂⟩ := ht₂ _ hs'
  rw [ht _ hs' hwt₁ hwt₂ hT₁.ne_pt hT₂.ne_pt] at hm₁
  exact hT₂.eq_of_ne_pt hm₁ hm₂ (hb _ hs' hw₁ hw₂)

/-- An application that is not the point has a graph as head, whose
domain is a type holding the argument. -/
theorem app_slot {f a : Expr} {ρ : Nat → V} (hw : WellDenoted m.M φ ρ (.app f a))
    (hn : interp m.M φ ρ (.app f a) ≠ pt) :
    ∃ (F : V → V) (A : V), interp m.M φ ρ f = graph F A ∧ IsTy A ∧ interp m.M φ ρ a ∈ˢ A := by
  rw [WellDenoted_app] at hw
  rcases hw.2.2 with h | h
  · exact absurd h (fn_ne_pt hn)
  · exact h

/-- **Application congruence**: the two heads are equal graphs, so the
two arguments lie in one domain, which is a type — both arguments are
the point, or neither is. -/
theorem app_sound {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ Γ f₁ f₂) (ha : DefEqSem m φ Γ a₁ a₂) :
    DefEqSem m φ Γ (.app f₁ a₁) (.app f₂ a₂) := by
  intro ρ hs h₁ h₂ hn₁ hn₂
  obtain ⟨F₁, A₁, he₁, hT₁, hm₁⟩ := app_slot h₁ hn₁
  obtain ⟨F₂, A₂, he₂, -, hm₂⟩ := app_slot h₂ hn₂
  have h₁' := h₁
  have h₂' := h₂
  rw [WellDenoted_app] at h₁' h₂'
  have heF := hf ρ hs h₁'.1 h₂'.1 (fn_ne_pt hn₁) (fn_ne_pt hn₂)
  have hA : A₁ = A₂ := graph_dom_unique (he₁.symm.trans (heF.trans he₂))
  rw [← hA] at hm₂
  have heA : interp m.M φ ρ a₁ = interp m.M φ ρ a₂ := by
    rcases hT₁ with hT | hT
    · rw [eq_pt_of_mem_univ_zero hT hm₁, eq_pt_of_mem_univ_zero hT hm₂]
    · exact ha ρ hs h₁'.2.1 h₂'.2.1 (ne_pt_of_mem_strict hT hm₁) (ne_pt_of_mem_strict hT hm₂)
  simp only [interp_app]
  rw [heF, heA]

end DefEq

/-! ## Inference, and the two rules that use it -/

namespace Infer

theorem bvar_sound {Γ : List Expr} {i : Nat} {A : Expr} (h : Γ[i]? = some A) :
    InferSem m φ Γ (.bvar i) (A.liftN (i + 1)) := by
  intro ρ hs
  obtain ⟨hw, hT, hmem⟩ := Sat_get m.M φ hs h
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [WellDenoted_liftN]; exact hw
  · rw [interp_liftN]; exact hT
  · rw [interp_bvar, interp_liftN]; exact hmem

theorem sort_sound {Γ : List Expr} {u : Level} :
    InferSem m φ Γ (.sort u) (.sort (.succ u)) :=
  fun _ _ => ⟨trivial, trivial, Or.inr (strict_typeU _), by
    simp only [interp_sort, Level.eval_succ]; exact typeU_mem_typeU_succ _⟩

theorem const_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo}
    (hfind : env.find? c = some ci) (hls : ls.length = ci.lparams.length) :
    InferSem m φ Γ (.const c ls) (ci.type.instL ci.lparams ls) := by
  intro ρ _
  obtain ⟨hw, hT, hmem⟩ := m.type_ok c ci hfind φ ρ ls hls
  exact ⟨trivial, hw, hT, hmem⟩

/-- A type whose type reduces to `Sort u` is a member of `typeU u`. -/
theorem mem_typeU_of {Γ : List Expr} {A s : Expr} {u : Level} {ρ : Nat → V}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u)) (hs : Sat m.M φ Γ ρ) :
    WellDenoted m.M φ ρ A ∧ interp m.M φ ρ A ∈ˢ typeU (Level.eval φ u) := by
  obtain ⟨hwA, hws, hTs, hmem⟩ := hA ρ hs
  obtain ⟨-, hes⟩ := hu ρ hs hws hTs.ne_pt
  rw [hes, interp_sort] at hmem
  exact ⟨hwA, hmem⟩

theorem pi_sound {Γ : List Expr} {A B s t : Expr} {u v : Level}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u))
    (hB : InferSem m φ (A :: Γ) B t) (hv : RedSem m φ (A :: Γ) t (.sort v)) :
    InferSem m φ Γ (.pi A B) (.sort (.imax u v)) := by
  intro ρ hs
  obtain ⟨hwA, hmemA⟩ := mem_typeU_of hA hu hs
  have hTA := IsTy_of_mem_typeU hmemA
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) B ∧ interp m.M φ (cons x ρ) B ∈ˢ typeU (Level.eval φ v) :=
    fun x hx => mem_typeU_of hB hv ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩)
  refine ⟨?_, trivial, Or.inr (strict_typeU _), ?_⟩
  · rw [WellDenoted_pi]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).1, fun x hx => IsTy_of_mem_typeU (hbody x hx).2⟩
  · rw [interp_pi, interp_sort, Level.eval_imax]
    exact piV_mem_typeU hmemA fun x hx => (hbody x hx).2

/-- **Lambda**: Lean's rule.  The body's type is a type (`InferSem`), which
is all `lamV_mem` asks of the fibres. -/
theorem lam_sound {Γ : List Expr} {A b s bt : Expr} {u : Level}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u))
    (hb : InferSem m φ (A :: Γ) b bt) :
    InferSem m φ Γ (.lam A b) (.pi A bt) := by
  intro ρ hs
  obtain ⟨hwA, hmemA⟩ := mem_typeU_of hA hu hs
  have hTA := IsTy_of_mem_typeU hmemA
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) b ∧ WellDenoted m.M φ (cons x ρ) bt ∧
      IsTy (interp m.M φ (cons x ρ) bt) ∧
      interp m.M φ (cons x ρ) b ∈ˢ interp m.M φ (cons x ρ) bt :=
    fun x hx => hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩)
  refine ⟨?_, ?_, by rw [interp_pi]; exact IsTy_piV, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).1⟩
  · rw [WellDenoted_pi]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).2.1, fun x hx => (hbody x hx).2.2.1⟩
  · rw [interp_lam, interp_pi]
    exact lamV_mem (fun x hx => (hbody x hx).2.2.2) fun x hx => (hbody x hx).2.2.1

theorem app_sound {Γ : List Expr} {f a tf A B ta : Expr}
    (hf : InferSem m φ Γ f tf) (hr : RedSem m φ Γ tf (.pi A B))
    (ha : InferSem m φ Γ a ta) (hd : DefEqSem m φ Γ ta A) :
    InferSem m φ Γ (.app f a) (B.inst a) := by
  intro ρ hs
  obtain ⟨hwf, hwtf, hTtf, hmemf⟩ := hf ρ hs
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtf hTtf.ne_pt
  rw [hepi, interp_pi] at hmemf
  have hwpi' := hwpi
  rw [WellDenoted_pi] at hwpi'
  obtain ⟨hwA, hTA, hwB, hfib⟩ := hwpi'
  obtain ⟨hwa, hwta, hTta, hmema⟩ := ha ρ hs
  rw [hd ρ hs hwta hwA hTta.ne_pt hTA.ne_pt] at hmema
  refine ⟨?_, (WellDenoted_inst0 m.M φ hwa).mpr (hwB _ hmema), ?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hwf, hwa, appliesTo_of_mem_piR hmemf hTA hmema⟩
  · rw [interp_inst0]; exact hfib _ hmema
  · rw [interp_app, interp_inst0]
    exact app_mem_piV hmemf hmema

/-- **`let`, by substitution**: the body with the value
substituted carries the claim, and the `let` denotes what it denotes
(`interp_zeta`); its invariant is the `let`'s (`WellDenoted_letE`
against `WellDenoted_inst0`).  The type checks on the value (`hT`,
`hu`, `hv`, `hd`) are not used: `interp` reads no type, and the body
is inferred at the value itself, not at a variable of the type. -/
theorem letE_sound {Γ : List Expr} {T v b s tv B : Expr} {u : Level}
    (_hT : InferSem m φ Γ T s) (_hu : RedSem m φ Γ s (.sort u))
    (hv : InferSem m φ Γ v tv) (_hd : DefEqSem m φ Γ tv T)
    (hb : InferSem m φ Γ (b.inst v) B) :
    InferSem m φ Γ (.letE T v b) B := by
  intro ρ hs
  obtain ⟨hwv, -⟩ := hv ρ hs
  obtain ⟨hwb, hwB, hTB, hmem⟩ := hb ρ hs
  refine ⟨?_, hwB, hTB, ?_⟩
  · rw [WellDenoted_letE]; exact ⟨hwv, (WellDenoted_inst0 m.M φ hwv).mp hwb⟩
  · rw [interp_zeta]; exact hmem

/-- **What the value checks give**: the value's value is
a member of the type's, so the value extends a satisfying environment
to one satisfying the context extended by the type.  The substitution
version does not need it (`letE_sound`); a version that opens the body
at a let-variable of type `T` would (the body's claim is then stated at
`T :: Γ`).  The type and the value's inferred type are both types,
never the point, so `DefEq`'s conditional claim applies to them. -/
theorem letE_sat {Γ : List Expr} {T v s tv : Expr} {u : Level}
    (hT : InferSem m φ Γ T s) (hu : RedSem m φ Γ s (.sort u))
    (hv : InferSem m φ Γ v tv) (hd : DefEqSem m φ Γ tv T) {ρ : Nat → V}
    (hs : Sat m.M φ Γ ρ) :
    Sat m.M φ (T :: Γ) (cons (interp m.M φ ρ v) ρ) := by
  obtain ⟨hwT, hmemT⟩ := mem_typeU_of hT hu hs
  have hTT := IsTy_of_mem_typeU hmemT
  obtain ⟨-, hwtv, hTtv, hmem⟩ := hv ρ hs
  rw [hd ρ hs hwtv hwT hTtv.ne_pt hTT.ne_pt] at hmem
  exact (Sat_cons m.M φ).mpr ⟨hs, hwT, hTT, hmem⟩

end Infer

namespace DefEq

/-- **η, typed**: at every value of the variable the lambda's
body and `b` applied lie in one type — the body's inferred type is the
`∀`'s fibre — so they are both the point or neither is, and where
neither is the body's claim makes them equal; a member of a function space is
the abstraction of its applications (`SetLib.lamV_eta`). -/
theorem eta_sound {Γ : List Expr} {A₁ b₁ b tb A₂ B t₁ : Expr}
    (htb : ∀ ρ, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ b → interp m.M φ ρ b ≠ pt →
      WellDenoted m.M φ ρ tb ∧ IsTy (interp m.M φ ρ tb) ∧
        interp m.M φ ρ b ∈ˢ interp m.M φ ρ tb)
    (hr : RedSem m φ Γ tb (.pi A₂ B))
    (hA : DefEqSem m φ Γ A₂ A₁)
    (hbody : DefEqSem m φ (A₁ :: Γ) b₁ (.app (b.liftN 1) (.bvar 0)))
    (ht₁ : InferSem m φ (A₁ :: Γ) b₁ t₁) (htB : DefEqSem m φ (A₁ :: Γ) t₁ B) :
    DefEqSem m φ Γ (.lam A₁ b₁) b := by
  intro ρ hs hlam hwb _ hnb
  obtain ⟨hwtb, hTtb, hmemb⟩ := htb ρ hs hwb hnb
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtb hTtb.ne_pt
  rw [hepi, interp_pi] at hmemb
  rw [WellDenoted_pi] at hwpi
  have hlam' := hlam
  rw [WellDenoted_lam] at hlam'
  have heA := hA ρ hs hwpi.1 hlam'.1 hwpi.2.1.ne_pt hlam'.2.1.ne_pt
  have hsh : ∀ x, shiftE 1 0 (cons x ρ) = ρ := by
    intro x; funext i; simp [shiftE]
  have hlift : ∀ x, interp m.M φ (cons x ρ) (b.liftN 1) = interp m.M φ ρ b := by
    intro x; rw [interp_liftN, hsh]
  have hpt : ∀ x, x ∈ˢ interp m.M φ ρ A₁ →
      interp m.M φ (cons x ρ) b₁ = SetLib.app (interp m.M φ ρ b) x := by
    intro x hx
    have hx₂ : x ∈ˢ interp m.M φ ρ A₂ := by rw [heA]; exact hx
    have hs' : Sat m.M φ (A₁ :: Γ) (cons x ρ) :=
      (Sat_cons m.M φ).mpr ⟨hs, hlam'.1, hlam'.2.1, hx⟩
    have happ : WellDenoted m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) := by
      rw [WellDenoted_app]
      exact ⟨(WellDenoted_liftN m.M φ 1 b 0 (cons x ρ)).mpr (by rw [hsh]; exact hwb), trivial,
        by rw [interp_bvar, cons_zero, hlift]; exact appliesTo_of_mem_piR hmemb hwpi.2.1 hx₂⟩
    obtain ⟨hwb₁, hwt₁, hT₁, hm₁⟩ := ht₁ _ hs'
    rw [htB _ hs' hwt₁ (hwpi.2.2.1 x hx₂) hT₁.ne_pt (hwpi.2.2.2 x hx₂).ne_pt] at hm₁
    have hm₂ : interp m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) ∈ˢ
        interp m.M φ (cons x ρ) B := by
      rw [interp_app, interp_bvar, cons_zero, hlift]; exact app_mem_piV hmemb hx₂
    rw [(hwpi.2.2.2 x hx₂).eq_of_ne_pt hm₁ hm₂ (hbody _ hs' hwb₁ happ), interp_app, interp_bvar,
      cons_zero, hlift]
  rw [interp_lam, lamV_congr hpt, ← heA]
  exact lamV_eta hmemb fun x hx => hwpi.2.2.2 x hx

/-- An abstraction that is not the point has a body value that is not. -/
theorem exists_ne_pt_of_lamV {A : V} {F : V → V} (h : lamV A F ≠ pt) :
    ∃ x, x ∈ˢ A ∧ F x ≠ pt :=
  Classical.byContradiction fun hne => h (lamV_eq_pt fun x hx =>
    Classical.byContradiction fun hx' => hne ⟨x, hx, hx'⟩)

/-- **λ-congruence over a propositional domain, untyped** (task #345):
the domain has at most one member, so a λ that is not the point has
its one body value not the point, on both sides, and there the
bodies' claim applies. -/
theorem lamProp_sound [LevelOracle] {Γ : List Expr} {A₁ b₁ A₂ b₂ s : Expr} {u : Level}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂)
    (hs : InferSem m φ Γ A₂ s) (hu : RedSem m φ Γ s (.sort u))
    (hu0 : LevelOracle.eq u .zero = true) :
    DefEqSem m φ Γ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hsat h₁ h₂ hn₁ hn₂
  obtain ⟨-, hmemT⟩ := Infer.mem_typeU_of hs hu hsat
  rw [eval_eq_of_oracle hu0, Level.eval_zero, mem_typeU_zero] at hmemT
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hsat h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_lam] at hn₁ hn₂ ⊢
  rw [heA] at hn₁ ⊢
  apply lamV_congr
  intro x hx
  have hone : ∀ {F : V → V}, lamV (interp m.M φ ρ A₂) F ≠ pt → F x ≠ pt := by
    intro F hF
    obtain ⟨y, hy, hFy⟩ := exists_ne_pt_of_lamV hF
    obtain rfl : y = x := (eq_pt_of_mem_univ_zero hmemT hy).trans
      (eq_pt_of_mem_univ_zero hmemT hx).symm
    exact hFy
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hsat, h₂.1, h₂.2.1, hx⟩) (h₁.2.2 x hx₁)
    (h₂.2.2 x hx) (hone hn₁) (hone hn₂)

/-- **η over a propositional domain, untyped** (task #345): the λ and
`b` (the abstraction of its applications, `SetLib.lamV_eta`) are not
the point, so their one body value is not, and the body's claim
applies there. -/
theorem etaProp_sound [LevelOracle] {Γ : List Expr} {A₁ b₁ b tb A₂ B s : Expr} {u : Level}
    (htb : InferSem m φ Γ b tb) (hr : RedSem m φ Γ tb (.pi A₂ B))
    (hA : DefEqSem m φ Γ A₂ A₁)
    (hbody : DefEqSem m φ (A₁ :: Γ) b₁ (.app (b.liftN 1) (.bvar 0)))
    (hs : InferSem m φ Γ A₁ s) (hu : RedSem m φ Γ s (.sort u))
    (hu0 : LevelOracle.eq u .zero = true) :
    DefEqSem m φ Γ (.lam A₁ b₁) b := by
  intro ρ hsat hlam hwb hn₁ hn₂
  obtain ⟨-, hmemT⟩ := Infer.mem_typeU_of hs hu hsat
  rw [eval_eq_of_oracle hu0, Level.eval_zero, mem_typeU_zero] at hmemT
  obtain ⟨-, hwtb, hTtb, hmemb⟩ := htb ρ hsat
  obtain ⟨hwpi, hepi⟩ := hr ρ hsat hwtb hTtb.ne_pt
  rw [hepi, interp_pi] at hmemb
  rw [WellDenoted_pi] at hwpi
  have hlam' := hlam
  rw [WellDenoted_lam] at hlam'
  have heA := hA ρ hsat hwpi.1 hlam'.1 hwpi.2.1.ne_pt hlam'.2.1.ne_pt
  have hsh : ∀ x, shiftE 1 0 (cons x ρ) = ρ := by
    intro x; funext i; simp [shiftE]
  have hlift : ∀ x, interp m.M φ (cons x ρ) (b.liftN 1) = interp m.M φ ρ b := by
    intro x; rw [interp_liftN, hsh]
  have hone : ∀ {F : V → V} {x : V}, x ∈ˢ interp m.M φ ρ A₁ →
      lamV (interp m.M φ ρ A₁) F ≠ pt → F x ≠ pt := by
    intro F x hx hF
    obtain ⟨y, hy, hFy⟩ := exists_ne_pt_of_lamV hF
    obtain rfl : y = x := (eq_pt_of_mem_univ_zero hmemT hy).trans
      (eq_pt_of_mem_univ_zero hmemT hx).symm
    exact hFy
  have hbeta := lamV_eta hmemb fun x hx => hwpi.2.2.2 x hx
  rw [heA] at hbeta hmemb
  simp only [interp_lam] at hn₁ ⊢
  rw [← hbeta]
  apply lamV_congr
  intro x hx
  have hx₂ : x ∈ˢ interp m.M φ ρ A₂ := by rw [heA]; exact hx
  have happ : WellDenoted m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) := by
    rw [WellDenoted_app]
    exact ⟨(WellDenoted_liftN m.M φ 1 b 0 (cons x ρ)).mpr (by rw [hsh]; exact hwb), trivial,
      by rw [interp_bvar, cons_zero, hlift]; exact appliesTo_of_mem_piR hmemb (heA ▸ hwpi.2.1) hx⟩
  have hnb : SetLib.app (interp m.M φ ρ b) x ≠ pt :=
    hone (F := fun y => SetLib.app (interp m.M φ ρ b) y) hx (by rw [hbeta]; exact hn₂)
  rw [hbody (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hsat, hlam'.1, hlam'.2.1, hx⟩) (hlam'.2.2 x hx)
    happ (hone hx hn₁) (by rw [interp_app, interp_bvar, cons_zero, hlift]; exact hnb),
    interp_app, interp_bvar, cons_zero, hlift]

/-- **λ-congruence of two constant bodies, untyped** (task #345): each
body's value is the same at every value of the variable; a λ that is
not the point has it not the point. -/
theorem lamConst_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂)
    (hc₁ : b₁.usesVar 0 = false) (hc₂ : b₂.usesVar 0 = false) :
    DefEqSem m φ Γ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hsat h₁ h₂ hn₁ hn₂
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hsat h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_lam] at hn₁ hn₂ ⊢
  rw [heA] at hn₁ ⊢
  have hcst : ∀ {b : Expr}, b.usesVar 0 = false → ∀ x y : V,
      interp m.M φ (cons x ρ) b = interp m.M φ (cons y ρ) b := by
    intro b hc x y
    apply interp_usesVar
    intro i hi
    cases i with
    | zero => rw [hc] at hi; exact absurd hi Bool.false_ne_true
    | succ i => rfl
  obtain ⟨x₁, hx₁, hF₁⟩ := exists_ne_pt_of_lamV hn₁
  obtain ⟨x₂, -, hF₂⟩ := exists_ne_pt_of_lamV hn₂
  apply lamV_congr
  intro x _
  rw [hcst hc₁ x x₁, hcst hc₂ x x₁]
  have hx₁' : x₁ ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx₁
  exact hb (cons x₁ ρ) ((Sat_cons m.M φ).mpr ⟨hsat, h₂.1, h₂.2.1, hx₁⟩) (h₁.2.2 x₁ hx₁')
    (h₂.2.2 x₁ hx₁) hF₁ (by rw [hcst hc₂ x₁ x₂]; exact hF₂)

/-- **Application congruence at the head's type** (task #345): the
heads are equal graphs whose domain is the denotation of `S`, the
domain of the head's type; both arguments lie in it, and the
comparison at `S` makes them equal. -/
theorem appIn_sound {Γ : List Expr} {f₁ a₁ f₂ a₂ tf S B : Expr}
    (hf : DefEqSem m φ Γ f₁ f₂) (hI : InferSem m φ Γ f₁ tf) (hr : RedSem m φ Γ tf (.pi S B))
    (ha : DefEqInSem m φ Γ S a₁ a₂) :
    DefEqSem m φ Γ (.app f₁ a₁) (.app f₂ a₂) := by
  intro ρ hs h₁ h₂ hn₁ hn₂
  obtain ⟨F₁, A₁', he₁, -, hm₁⟩ := app_slot h₁ hn₁
  obtain ⟨F₂, A₂', he₂, -, hm₂⟩ := app_slot h₂ hn₂
  have h₁' := h₁
  have h₂' := h₂
  rw [WellDenoted_app] at h₁' h₂'
  have heF := hf ρ hs h₁'.1 h₂'.1 (fn_ne_pt hn₁) (fn_ne_pt hn₂)
  obtain ⟨-, hwtf, hTtf, hmf⟩ := hI ρ hs
  obtain ⟨hwpi, hetf⟩ := hr ρ hs hwtf hTtf.ne_pt
  rw [hetf, interp_pi] at hmf
  have hfS := mem_piSet_of_mem_piV hmf (fn_ne_pt hn₁)
  have hA₁ : A₁' = interp m.M φ ρ S :=
    graph_dom_unique (he₁.symm.trans (graph_app_eq hfS).symm)
  have hA₂ : A₂' = interp m.M φ ρ S :=
    graph_dom_unique (he₂.symm.trans (heF.symm.trans (graph_app_eq hfS).symm))
  rw [WellDenoted_pi] at hwpi
  have heA := ha ρ hs hwpi.1 hwpi.2.1 h₁'.2.1 h₂'.2.1 (hA₁ ▸ hm₁) (hA₂ ▸ hm₂)
  simp only [interp_app]
  rw [heF, heA]

/-- **Proof irrelevance claims nothing**: a side whose type's sort is
`Prop` is the point, and the claim is about sides that are not. -/
theorem proofIrrel_sound [LevelOracle] {Γ : List Expr} {a ta tta b : Expr} {u : Level}
    (hta : InferSem m φ Γ a ta) (htta : InferSem m φ Γ ta tta)
    (hu : RedSem m φ Γ tta (.sort u)) (hu0 : LevelOracle.eq u .zero = true) :
    DefEqSem m φ Γ a b := by
  intro ρ hs _ _ hna _
  obtain ⟨-, hmemT⟩ := Infer.mem_typeU_of htta hu hs
  obtain ⟨-, -, -, hmem⟩ := hta ρ hs
  rw [eval_eq_of_oracle hu0, Level.eval_zero, mem_typeU_zero] at hmemT
  exact absurd (eq_pt_of_mem_univ_zero hmemT hmem) hna

end DefEq


/-! ## Comparison at a known type (task #345) -/

namespace DefEqIn

theorem of_sound {Γ : List Expr} {T a b : Expr} (h : DefEqSem m φ Γ a b) :
    DefEqInSem m φ Γ T a b :=
  fun ρ hs _ hT ha hb hma hmb => hT.eq_of_ne_pt hma hmb (h ρ hs ha hb)

theorem symm_sound {Γ : List Expr} {T a b : Expr} (h : DefEqInSem m φ Γ T a b) :
    DefEqInSem m φ Γ T b a :=
  fun ρ hs hwT hT hb ha hmb hma => (h ρ hs hwT hT ha hb hma hmb).symm

/-- A λ that is not the point, in a function space, is the graph of its
body over the function space's domain. -/
theorem lam_in_piV {ρ : Nat → V} {A b : Expr} {D : V} {E : V → V}
    (hm : interp m.M φ ρ (.lam A b) ∈ˢ piV D E)
    (hn : interp m.M φ ρ (.lam A b) ≠ pt) :
    interp m.M φ ρ A = D ∧ interp m.M φ ρ (.lam A b) ∈ˢ piSet D E := by
  have hS := mem_piSet_of_mem_piV hm hn
  refine ⟨?_, hS⟩
  rw [interp_lam] at hn hS
  exact graph_dom_unique ((lamV_eq_graph hn).symm.trans (graph_app_eq hS).symm)

/-- **λ-congruence at a `∀`**: no inference, no domain comparison.  Both
λs lie in one type, so both are the point or neither is; two that are
not are graphs over the `∀`'s domain, whose body values lie in its
fibres, where the bodies' claim at the `∀`'s body applies. -/
theorem lam_sound {Γ : List Expr} {T D E A₁ b₁ A₂ b₂ : Expr}
    (hr : RedSem m φ Γ T (.pi D E)) (hb : DefEqInSem m φ (A₂ :: Γ) E b₁ b₂) :
    DefEqInSem m φ Γ T (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hs hwT hT h₁ h₂ hm₁ hm₂
  refine hT.eq_of_ne_pt hm₁ hm₂ fun hn₁ hn₂ => ?_
  obtain ⟨hwpi, heT⟩ := hr ρ hs hwT hT.ne_pt
  rw [heT, interp_pi] at hm₁ hm₂
  rw [WellDenoted_pi] at hwpi
  obtain ⟨hD₁, hS₁⟩ := lam_in_piV hm₁ hn₁
  obtain ⟨hD₂, hS₂⟩ := lam_in_piV hm₂ hn₂
  have h₁' := h₁
  have h₂' := h₂
  rw [WellDenoted_lam] at h₁' h₂'
  have hval : ∀ {A b : Expr}, interp m.M φ ρ (.lam A b) ≠ pt → ∀ x, x ∈ˢ interp m.M φ ρ A →
      interp m.M φ (cons x ρ) b = SetLib.app (interp m.M φ ρ (.lam A b)) x := by
    intro A b hn x hx
    rw [interp_lam] at hn ⊢
    rw [lamV_eq_graph hn, app_graph hx]
  simp only [interp_lam] at hn₁ hn₂ ⊢
  rw [hD₁, hD₂]
  apply lamV_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [hD₁]; exact hx
  have hx₂ : x ∈ˢ interp m.M φ ρ A₂ := by rw [hD₂]; exact hx
  refine hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂'.1, h₂'.2.1, hx₂⟩) (hwpi.2.2.1 x hx)
    (hwpi.2.2.2 x hx) (h₁'.2.2 x hx₁) (h₂'.2.2 x hx₂) ?_ ?_
  · rw [hval (by rw [interp_lam]; exact hn₁) x hx₁]; exact app_mem_piSet hS₁ hx
  · rw [hval (by rw [interp_lam]; exact hn₂) x hx₂]; exact app_mem_piSet hS₂ hx

/-- **η at a `∀`**: no inference of `b`'s type, no domain comparison;
`b` is the abstraction of its applications (`SetLib.lamV_eta`). -/
theorem eta_sound {Γ : List Expr} {T D E A₁ b₁ b : Expr}
    (hr : RedSem m φ Γ T (.pi D E))
    (hb : DefEqInSem m φ (A₁ :: Γ) E b₁ (.app (b.liftN 1) (.bvar 0))) :
    DefEqInSem m φ Γ T (.lam A₁ b₁) b := by
  intro ρ hs hwT hT h₁ hwb hm₁ hmb
  refine hT.eq_of_ne_pt hm₁ hmb fun hn₁ _ => ?_
  obtain ⟨hwpi, heT⟩ := hr ρ hs hwT hT.ne_pt
  rw [heT, interp_pi] at hm₁ hmb
  rw [WellDenoted_pi] at hwpi
  obtain ⟨hD₁, hS₁⟩ := lam_in_piV hm₁ hn₁
  have h₁' := h₁
  rw [WellDenoted_lam] at h₁'
  have hsh : ∀ x, shiftE 1 0 (cons x ρ) = ρ := by
    intro x; funext i; simp [shiftE]
  have hlift : ∀ x, interp m.M φ (cons x ρ) (b.liftN 1) = interp m.M φ ρ b := by
    intro x; rw [interp_liftN, hsh]
  have hn₁' := hn₁
  simp only [interp_lam] at hn₁' ⊢
  rw [hD₁, ← lamV_eta hmb fun x hx => hwpi.2.2.2 x hx]
  apply lamV_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [hD₁]; exact hx
  have happ : WellDenoted m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) := by
    rw [WellDenoted_app]
    exact ⟨(WellDenoted_liftN m.M φ 1 b 0 (cons x ρ)).mpr (by rw [hsh]; exact hwb), trivial,
      by rw [interp_bvar, cons_zero, hlift]; exact appliesTo_of_mem_piR hmb hwpi.2.1 hx⟩
  have h := hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₁'.1, h₁'.2.1, hx₁⟩) (hwpi.2.2.1 x hx)
    (hwpi.2.2.2 x hx) (h₁'.2.2 x hx₁) happ ?_ ?_
  · rw [h, interp_app, interp_bvar, cons_zero, hlift]
  · rw [interp_lam, lamV_eq_graph hn₁', hD₁] at hS₁
    rw [← app_graph (F := fun x => interp m.M φ (cons x ρ) b₁) hx]
    exact app_mem_piSet hS₁ hx
  · rw [interp_app, interp_bvar, cons_zero, hlift]; exact app_mem_piV hmb hx

end DefEqIn

/-! ## λ-telescopes typed at the innermost level (task #349) -/

namespace DefEqLams

/-- Syntactically equal sides denote alike. -/
theorem refl_sound {Γ : List Expr} {a : Expr} : LamsSem m φ Γ a a :=
  fun _ _ _ _ => rfl

/-- **The innermost level**: `DefEq.lam`'s premises give an
unconditional equality.  The bodies lie in one type at every value of
the variable, so they are both the point or neither, and where neither
is the bodies' claim makes them equal; no side need be off the point. -/
theorem inner_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ t₁ t₂ : Expr}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂)
    (ht₁ : InferSem m φ (A₂ :: Γ) b₁ t₁) (ht₂ : InferSem m φ (A₂ :: Γ) b₂ t₂)
    (ht : DefEqSem m φ (A₂ :: Γ) t₁ t₂) :
    LamsSem m φ Γ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hs h₁ h₂
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_lam]
  rw [heA]
  apply lamV_congr
  intro x hx
  have hs' : Sat m.M φ (A₂ :: Γ) (cons x ρ) := (Sat_cons m.M φ).mpr ⟨hs, h₂.1, h₂.2.1, hx⟩
  obtain ⟨hw₁, hwt₁, hT₁, hm₁⟩ := ht₁ _ hs'
  obtain ⟨hw₂, hwt₂, hT₂, hm₂⟩ := ht₂ _ hs'
  rw [ht _ hs' hwt₁ hwt₂ hT₁.ne_pt hT₂.ne_pt] at hm₁
  exact hT₂.eq_of_ne_pt hm₁ hm₂ (hb _ hs' hw₁ hw₂)

/-- **An outer level needs no type**: the bodies are equal
at every value of the variable, unconditionally, so the lambdas are; the
domains are types, never the point, so their conditional claim
applies.  This is why the type comparison is owed only at the
innermost level of a lambda telescope pair. -/
theorem outer_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : LamsSem m φ (A₂ :: Γ) b₁ b₂) :
    LamsSem m φ Γ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hs h₁ h₂
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_lam]
  rw [heA]
  apply lamV_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂.1, h₂.2.1, hx⟩) (h₁.2.2 x hx₁)
    (h₂.2.2 x hx)

end DefEqLams

/-- The telescope relation's unconditional claim gives `DefEq`'s. -/
theorem DefEq.lams_sound {Γ : List Expr} {a b : Expr} (h : LamsSem m φ Γ a b) :
    DefEqSem m φ Γ a b :=
  fun ρ hs ha hb _ _ => h ρ hs ha hb

/-! ## ι -/

/-- **Certificates give fit**: arguments typed against the telescope's
domains fit it.  The inferred types are types, and the domains are
(`WellDenoted` records it), so neither side of a certificate's comparison is
the point and the conditional claim applies. -/
theorem teleFit_of_certs {Γ : List Expr} {ρ : Nat → V} (hs : Sat m.M φ Γ ρ) :
    ∀ {T : Expr} {spine tys doms : List Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ spine, WellDenoted m.M φ ρ a) →
      Expr.piDomains T spine = some doms → tys.length = doms.length →
      (∀ p ∈ spine.zip tys, InferSem m φ Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2) →
      TeleFit m.M φ ρ T spine
  | _, [], _, _, _, _, _, _, _, _ => trivial
  | .pi A B, a :: as, tys, _, hT, hsp, hdoms, hlen, hI, hD => by
    simp only [Expr.piDomains, Option.map_eq_some_iff] at hdoms
    obtain ⟨ds, hds, rfl⟩ := hdoms
    cases tys with
    | nil => simp at hlen
    | cons ta ts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [WellDenoted_pi] at hT
      have hwa := hsp a List.mem_cons_self
      obtain ⟨-, hwta, hTta, hmem⟩ := hI (a, ta) (by simp) ρ hs
      rw [hD (ta, A) (by simp) ρ hs hwta hT.1 hTta.ne_pt hT.2.1.ne_pt] at hmem
      refine ⟨hmem, ?_⟩
      refine teleFit_of_certs hs ((WellDenoted_inst0 m.M φ hwa).mpr (hT.2.2.1 _ hmem))
        (fun b hb => hsp b (List.mem_cons_of_mem a hb)) hds hlen ?_ ?_
      · intro p hp
        exact hI p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
      · intro p hp
        exact hD p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
  | .bvar _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .sort _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .const _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .app _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .lam _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h

/-- The residual of a well-denoted telescope along a fitting spine is
well-denoted. -/
theorem WellDenoted_piResidual {ρ : Nat → V} :
    ∀ {T : Expr} {as : List Expr} {R : Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ as, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ T as → Expr.piResidual T as = some R → WellDenoted m.M φ ρ R
  | T, [], _, hT, _, _, h => by simp at h; subst h; exact hT
  | .pi A B, a :: as, R, hT, has, hfit, h => by
    rw [Expr.piResidual_pi_cons] at h
    obtain ⟨hmem, hfit'⟩ := hfit
    rw [WellDenoted_pi] at hT
    exact WellDenoted_piResidual
      ((WellDenoted_inst0 m.M φ (has a List.mem_cons_self)).mpr (hT.2.2.1 _ hmem))
      (fun b hb => has b (List.mem_cons_of_mem a hb)) hfit' h
  | .bvar _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .sort _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .const _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .app _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .lam _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h

/-- The point applied to any values is the point. -/
theorem appList_pt_sound : ∀ vs : List V, appList (pt : V) vs = pt
  | [] => rfl
  | v :: vs => by rw [appList_cons, app_pt, appList_pt_sound vs]

/-- A telescope of `n + 1` binders has `n`. -/
theorem Expr.hasPis_of_succ : ∀ (e : Expr) (n : Nat), e.hasPis (n + 1) = true → e.hasPis n = true
  | _, 0, _ => by simp
  | .pi _ B, n + 1, h => by simpa using Expr.hasPis_of_succ B n (by simpa using h)
  | .bvar _, _ + 1, h => by simp [Expr.hasPis] at h
  | .sort _, _ + 1, h => by simp [Expr.hasPis] at h
  | .const _ _, _ + 1, h => by simp [Expr.hasPis] at h
  | .app _ _, _ + 1, h => by simp [Expr.hasPis] at h
  | .lam _ _, _ + 1, h => by simp [Expr.hasPis] at h

/-- **A spine that is not the point fits its head's telescope, with no
certificate** (the argument of the paper's ι rule, iterated).  At each step
the application is not the point, so neither is its head
(`app_pt`); the invariant's application clause (`AppliesTo`) then puts
the argument in the domain of the head's graph, and the head's membership
in its type — a function space, not the point — makes that the type's
domain (`AppliesTo.mem`), the binder's.
This is why `Red.iota` carries no certificate on the recursor's
telescope: the reduction claims nothing of a redex that is the point. -/
theorem teleFit_of_ne_pt {ρ : Nat → V} :
    ∀ {xs : List Expr} {f T : Expr},
      WellDenoted m.M φ ρ T → interp m.M φ ρ f ∈ˢ interp m.M φ ρ T →
      T.hasPis xs.length = true →
      WellDenoted m.M φ ρ (Expr.mkAppN f xs) → interp m.M φ ρ (Expr.mkAppN f xs) ≠ pt →
      TeleFit m.M φ ρ T xs
  | [], _, _, _, _, _, _, _ => trivial
  | x :: xs, f, .pi A B, hT, hf, hpis, hw, hn => by
    rw [Expr.mkAppN_cons] at hw hn
    have hw1 := (WellDenoted_mkAppN m.M φ hw).1
    have hn1 : interp m.M φ ρ (.app f x) ≠ pt := by
      intro h; apply hn; rw [interp_mkAppN_appList, h, appList_pt_sound]
    have hw1' := hw1
    rw [WellDenoted_app] at hw1'
    obtain ⟨-, hwx, hap⟩ := hw1'
    have hF := fn_ne_pt hn1
    rw [interp_pi] at hf
    have hxA := hap.mem (mem_piSet_of_mem_piV hf hF)
    rw [WellDenoted_pi] at hT
    refine ⟨hxA, ?_⟩
    refine teleFit_of_ne_pt ((WellDenoted_inst0 m.M φ hwx).mpr (hT.2.2.1 _ hxA)) ?_
      (Expr.hasPis_inst x B 0 _ (by simpa using hpis)) hw hn
    rw [interp_inst0, interp_app]
    exact app_mem_piV hf hxA
  | _ :: _, _, .bvar _, _, _, h, _, _ => by simp [Expr.hasPis] at h
  | _ :: _, _, .sort _, _, _, h, _, _ => by simp [Expr.hasPis] at h
  | _ :: _, _, .const _ _, _, _, h, _, _ => by simp [Expr.hasPis] at h
  | _ :: _, _, .app _ _, _, _, h, _, _ => by simp [Expr.hasPis] at h
  | _ :: _, _, .lam _ _, _, _, h, _, _ => by simp [Expr.hasPis] at h

/-- A fit of a prefix extends by one argument lying in the domain the
prefix leaves. -/
theorem teleFit_snoc {ρ : Nat → V} {y D B : Expr} :
    ∀ {T : Expr} {xs : List Expr}, TeleFit m.M φ ρ T xs →
      Expr.piResidual T xs = some (.pi D B) →
      interp m.M φ ρ y ∈ˢ interp m.M φ ρ D → TeleFit m.M φ ρ T (xs ++ [y])
  | T, [], _, h, hy => by
    simp at h; subst h; exact ⟨hy, trivial⟩
  | .pi A B₀, x :: xs, hfit, h, hy => by
    rw [Expr.piResidual_pi_cons] at h
    exact ⟨hfit.1, teleFit_snoc hfit.2 h hy⟩
  | .bvar _, _ :: _, h, _, _ => h.elim
  | .sort _, _ :: _, h, _, _ => h.elim
  | .const _ _, _ :: _, h, _, _ => h.elim
  | .app _ _, _ :: _, h, _, _ => h.elim
  | .lam _ _, _ :: _, h, _, _ => h.elim

/-- **The major denotes its reduct.**  In an application of
a head `f` of type `T` to a spine `xs` and a major `maj` that is not the
point, with a reduct `maj'` of the major that meets the major's binder:
the two denote alike.  The head applied to `xs` is not the point, so it
is a graph, whose domain is the binder's — a type.  If the major is not
the point, its reduction's claim applies; if it is, the binder's domain
holds the point, so it is a truth value, and the reduct is the point
too.  This is the case of a recursion on proofs (`Acc`-style), where
the major itself may be the point and the reduction's claim says
nothing of it. -/
theorem major_eq {Γ : List Expr} {ρ : Nat → V} {T f maj maj' : Expr} {xs : List Expr}
    (hs : Sat m.M φ Γ ρ) (hT : WellDenoted m.M φ ρ T) (hf : interp m.M φ ρ f ∈ˢ interp m.M φ ρ T)
    (hw : WellDenoted m.M φ ρ (.app (Expr.mkAppN f xs) maj))
    (hn : interp m.M φ ρ (.app (Expr.mkAppN f xs) maj) ≠ pt)
    (hred : RedSem m φ Γ maj maj')
    (hfit : TeleFitV m.M φ ρ T ((xs ++ [maj']).map (interp m.M φ ρ))) :
    interp m.M φ ρ maj = interp m.M φ ρ maj' := by
  rw [List.map_append, List.map_singleton] at hfit
  obtain ⟨A, B, ρ', hb, hfitxs, hv⟩ := teleFitV_snoc m.M φ hfit
  have hmemB := mem_piBodyV m.M φ hf hfitxs hb
  have hwB := WellDenoted_piBodyV m.M φ hT hfitxs hb
  rw [WellDenoted_pi] at hwB
  rw [interp_pi] at hmemB
  rw [WellDenoted_app] at hw
  obtain ⟨-, hwmaj, hap⟩ := hw
  have hF := fn_ne_pt hn
  rw [interp_mkAppN_appList] at hap hF
  have hmaj := hap.mem (mem_piSet_of_mem_piV hmemB hF)
  by_cases hmp : interp m.M φ ρ maj = pt
  · rcases hwB.2.1 with hT0 | hTs
    · rw [hmp, eq_pt_of_mem_univ_zero hT0 hv]
    · exact absurd (hmp ▸ hmaj) hTs.2
  · exact (hred ρ hs hwmaj hmp).2

/-- The conditional comparisons of a spine, on values. -/
theorem cmp_vals {Γ : List Expr} {ρ : Nat → V} (hs : Sat m.M φ Γ ρ) {as bs : List Expr}
    (ha : ∀ a ∈ as, WellDenoted m.M φ ρ a) (hb : ∀ b ∈ bs, WellDenoted m.M φ ρ b)
    (h : ∀ p ∈ as.zip bs, DefEqSem m φ Γ p.1 p.2) :
    ∀ p ∈ (as.map (interp m.M φ ρ)).zip (bs.map (interp m.M φ ρ)),
      p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
  intro p hp h1 h2
  rw [List.zip_map] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
  exact h (a, b) hab ρ hs (ha a (List.of_mem_zip hab).1) (hb b (List.of_mem_zip hab).2) h1 h2

/-! ## A constructor of a family in `Prop` is the point (task #342 F3) -/

/-- Every element of a list zipped with one of the same length has a
partner. -/
theorem List.exists_mem_zip_of_length {α β : Type} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length →
      ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, _, h => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: as, b :: bs, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := exists_mem_zip_of_length (by simpa using h) x hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-- **Walking a type along fitting terms**: the head applied to the
terms lies in the residual (`Expr.piResidual`), and the residual is a
type. -/
theorem mem_piResidual {ρ : Nat → V} :
    ∀ {T : Expr} {as : List Expr} {R : Expr} {f : V},
      WellDenoted m.M φ ρ T → IsTy (interp m.M φ ρ T) → f ∈ˢ interp m.M φ ρ T →
      (∀ a ∈ as, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ T as → Expr.piResidual T as = some R →
      appList f (as.map (interp m.M φ ρ)) ∈ˢ interp m.M φ ρ R ∧ IsTy (interp m.M φ ρ R)
  | T, [], R, f, _, hty, hf, _, _, h => by
    simp at h; subst h; exact ⟨hf, hty⟩
  | .pi A B, a :: as, R, f, hT, _, hf, has, hfit, h => by
    rw [Expr.piResidual_pi_cons] at h
    obtain ⟨hmem, hfit'⟩ := hfit
    rw [WellDenoted_pi] at hT
    have hwa := has a List.mem_cons_self
    rw [interp_pi] at hf
    have hfa := app_mem_piV hf hmem
    have := mem_piResidual ((WellDenoted_inst0 m.M φ hwa).mpr (hT.2.2.1 _ hmem))
      (by rw [interp_inst0]; exact hT.2.2.2 _ hmem)
      (by rw [interp_inst0]; exact hfa)
      (fun b hb => has b (List.mem_cons_of_mem a hb)) hfit' h
    simpa only [List.map_cons, appList_cons] using this
  | .bvar _, _ :: _, _, _, _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .sort _, _ :: _, _, _, _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .const _ _, _ :: _, _, _, _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .app _ _, _ :: _, _, _, _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .lam _ _, _ :: _, _, _, _, _, _, _, _, h => by simp [Expr.piResidual] at h

/-- **A member of a family whose sort evaluates to zero is the point.**
The family `I`'s stored type, walked along the application's
arguments, leaves `Sort u`, and `u` evaluates to `0`.  The application
is a type (`hty`), so not the point; so it fits `I`'s telescope
(`teleFit_of_ne_pt`) and lies in `Sort 0`, the truth values, whose
members are the point.  (A fibre outside the telescope is not reached:
the fit is derived, not assumed.) -/
theorem eq_pt_of_mem_sortZero {ρ : Nat → V} {I : Name} {Ii : ConstInfo} {lsI : List Level}
    {zs : List Expr} {u : Level} {y : V}
    (hI : env.find? I = some Ii) (hlsI : lsI.length = Ii.lparams.length)
    (hpisI : Ii.type.hasPis zs.length = true)
    (hsort : Expr.piResidual (Ii.type.instL Ii.lparams lsI) zs = some (.sort u))
    (hu : Level.eval φ u = 0)
    (hw : WellDenoted m.M φ ρ (Expr.mkAppN (.const I lsI) zs))
    (hty : IsTy (interp m.M φ ρ (Expr.mkAppN (.const I lsI) zs)))
    (hy : y ∈ˢ interp m.M φ ρ (Expr.mkAppN (.const I lsI) zs)) : y = pt := by
  have hT := m.type_ok I Ii hI φ ρ lsI hlsI
  have hfit := teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2)
    (by rw [Expr.hasPis_instL]; exact hpisI) hw hty.ne_pt
  obtain ⟨hmem, -⟩ := mem_piResidual hT.1 hT.2.1 hT.2.2 (WellDenoted_mkAppN m.M φ hw).2 hfit hsort
  rw [interp_sort, hu, mem_typeU_zero] at hmem
  rw [interp_mkAppN_appList, interp_const] at hy
  exact eq_pt_of_mem_univ_zero hmem hy

/-- **A constructor of a family whose sort evaluates to zero denotes the
point**.  The
constructor applied to arguments that fit its stored type, whose
residual is the family `I` at some parameters and indices, at a level
where `I`'s sort evaluates to zero: the application lies in that
residual, a type of `Sort 0`, so it is the point
(`eq_pt_of_mem_sortZero`).  No argument of the application is read
beyond its fit: at such a level the constructor's arguments are not
constrained by its value. -/
theorem ctorApp_eq_pt_of_sortZero {ρ : Nat → V} {cj : Name} {usj : List Level} {cij : ConstInfo}
    {margs : List Expr} {I : Name} {Ii : ConstInfo} {lsI : List Level} {zs : List Expr} {u : Level}
    (hcij : env.find? cj = some cij) (husj : usj.length = cij.lparams.length)
    (hmargs : ∀ a ∈ margs, WellDenoted m.M φ ρ a)
    (hfit : TeleFit m.M φ ρ (cij.type.instL cij.lparams usj) margs)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs =
      some (Expr.mkAppN (.const I lsI) zs))
    (hI : env.find? I = some Ii) (hlsI : lsI.length = Ii.lparams.length)
    (hpisI : Ii.type.hasPis zs.length = true)
    (hsort : Expr.piResidual (Ii.type.instL Ii.lparams lsI) zs = some (.sort u))
    (hu : Level.eval φ u = 0) :
    interp m.M φ ρ (Expr.mkAppN (.const cj usj) margs) = pt := by
  have hT := m.type_ok cj cij hcij φ ρ usj husj
  obtain ⟨hmem, hty⟩ := mem_piResidual hT.1 hT.2.1 hT.2.2 hmargs hfit hres
  have hw := WellDenoted_piResidual hT.1 hmargs hfit hres
  rw [interp_mkAppN_appList, interp_const]
  exact eq_pt_of_mem_sortZero hI hlsI hpisI hsort hu hw hty hmem

/-- Oracle-equal level lists substitute to levels that evaluate alike. -/
theorem Level.eval_lookupLevel_congr (φ : Name → Nat) :
    ∀ (ps : List Name) (ls ls' : List Level), ls.map (Level.eval φ) = ls'.map (Level.eval φ) →
      ∀ n, Level.eval φ (Level.lookupLevel ps ls n) = Level.eval φ (Level.lookupLevel ps ls' n)
  | [], _, _, _, _ => rfl
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, h, _ => by simp at h
  | _ :: _, _ :: _, [], h, _ => by simp at h
  | p :: ps, l :: ls, l' :: ls', h, n => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := Level.eval_lookupLevel_congr φ ps ls ls' h.2 n
    simp only [Level.lookupLevel, List.zip_cons_cons, List.lookup_cons] at ih ⊢
    by_cases hn : n = p
    · subst hn; simpa using h.1
    · have : (n == p) = false := by simpa using hn
      simpa [this] using ih

theorem Level.eval_subst_congr (φ : Name → Nat) {ps : List Name} {ls ls' : List Level}
    (h : ls.map (Level.eval φ) = ls'.map (Level.eval φ)) (l : Level) :
    Level.eval φ (l.subst ps ls) = Level.eval φ (l.subst ps ls') := by
  rw [Level.eval_subst, Level.eval_subst]
  congr 1
  funext n
  exact Level.eval_lookupLevel_congr φ ps ls ls' h n

namespace Red

/-- **ι, the semantic core** of `iota_core` and
`iota_core_strict`, at the constructor's parameter count `nP` and a
right-hand side `rhs`, given the environment's law in the form both ι
laws take once instantiated (`hlaw`), and — at every valuation where
the redex is well-denoted and not the point — the invariant of the
reduced major and the two telescope fits (`hcore`), however obtained:
from certificates (`iota_core`) or from the major's domain being strict
(`iota_core_strict`).  The index comparisons are passed on in their
conditional form; the major's denotation is its reduct's with no β
certificate (`major_eq`). -/
theorem iota_core_sem {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hcore : ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      WellDenoted m.M φ ρ major ∧
      TeleFit m.M φ ρ (ci.type.instL ci.lparams us) (args.take majorIdx ++ [major]) ∧
      TeleFit m.M φ ρ (cij.type.instL cij.lparams usj) margs)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  intro ρ hs hw hn
  subst hmeq
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwxs : ∀ a ∈ args.take majorIdx, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  obtain ⟨hwmajor, hfit, hfit'⟩ := hcore ρ hs hw hn
  have hmargs : ∀ a ∈ margs, WellDenoted m.M φ ρ a := (WellDenoted_mkAppN m.M φ hwmajor).2
  have hsub : Expr.mkAppN (Expr.const c us) args =
      .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx)) (args.getD majorIdx (Expr.bvar 0)) := by
    conv => lhs; rw [hsplit]
    rw [Expr.mkAppN_append]; rfl
  have hmajv : interp m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs)
      = appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ)) := by
    rw [interp_mkAppN_appList, interp_const]
  have hlenmaj : (args.take majorIdx ++ [Expr.mkAppN (Expr.const cj usj) margs]).length
      = majorIdx + 1 := by
    simp only [List.length_append, List.length_take, List.length_singleton, hlen]; omega
  have hfitV₀ := teleFitV_of_teleFit m.M φ ρ
    (by rw [Expr.hasPis_instL, hlenmaj]; exact hpis) hfit
  have hfitV' := teleFitV_of_teleFit m.M φ ρ (by rw [Expr.hasPis_instL]; exact hpis') hfit'
  -- the major denotes its reduct (`major_eq`)
  have hemaj := major_eq (f := Expr.const c us) hs (m.type_ok c ci hfind φ ρ us hus).1
    (by rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2) (hsub ▸ hw) (hsub ▸ hn)
    hmaj hfitV₀
  have hfitV := hfitV₀
  rw [List.map_append, List.map_singleton, hmajv] at hfitV
  -- the index comparisons, in their conditional form
  have hwres : WellDenoted m.M φ ρ residual :=
    WellDenoted_piResidual (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs hfit' hres
  rw [hshape] at hwres
  obtain ⟨-, hwridx⟩ := WellDenoted_mkAppN m.M φ hwres
  have hX' : ∀ (B : Expr) (ρ' : Nat → V) (I' : Name) (lsI' : List Level) (rps' ridx' : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
      B = Expr.mkAppN (.const I' lsI') (rps' ++ ridx') → rps'.length = nP →
      ∀ p ∈ (ridx'.map (interp m.M φ ρ')).zip
        (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    intro B ρ' I' lsI' rps' ridx' hB hBs hrps'
    have hRB := piResidual_of_piBodyV m.M φ ρ hres hB
    rw [hshape, hBs, Expr.instChain_mkAppN, Expr.instChain_const] at hRB
    obtain ⟨-, -, hargs_eq⟩ := Expr.mkAppN_const_inj hRB
    rw [List.map_append] at hargs_eq
    have hridx : ridx = ridx'.map (Expr.instChain · margs) :=
      List.append_inj_right hargs_eq (by simp [hrps, hrps'])
    rw [piBodyV_env hB]
    have hmap : ridx'.map (interp m.M φ (consList (margs.map (interp m.M φ ρ)).reverse ρ))
        = ridx.map (interp m.M φ ρ) := by
      rw [hridx, List.map_map]
      apply List.map_congr_left
      intro r _
      simp [Function.comp, interp_instChain]
    rw [hmap, ← List.map_drop]
    exact cmp_vals hs (fun a ha => hwridx a (List.mem_append_right _ ha))
      (fun a ha => hwxs a (List.mem_of_mem_drop ha)) hX
  -- the environment's ι law
  have hvsub : interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args)
      = appList (m.M c (us.map (Level.eval φ)))
        ((args.take majorIdx).map (interp m.M φ ρ)
          ++ [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) := by
    conv => lhs; rw [hsplit]
    rw [interp_mkAppN_appList, interp_const, List.map_append, List.map_singleton, hemaj, hmajv]
  obtain ⟨heq, hwrhs, hspine⟩ :=
    hlaw ρ hs hargs hmargs hfitV hfitV' hX' (hvsub ▸ hn)
  have hvals : (args.take numBefore ++ margs.drop nP).map (interp m.M φ ρ)
      = ((args.take majorIdx).map (interp m.M φ ρ)).take numBefore
        ++ (margs.map (interp m.M φ ρ)).drop nP := by
    rw [List.map_append, ← List.map_take, ← List.map_drop, List.take_take,
      Nat.min_eq_left hnB]
  refine ⟨?_, ?_⟩
  · apply WellDenoted_mkAppN_of_spineOk m.M φ ρ hwrhs
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hargs a (List.mem_of_mem_take ha)
      · exact hmargs a (List.mem_of_mem_drop ha)
    · rw [hvals]; exact hspine
  · rw [hvsub, interp_mkAppN_appList, hvals]
    exact heq


/-- **ι, the common part** of `iota_sound` and `iotaNested_sound`:
`iota_core_sem` with the certificates of `Red.iota`.  The recursor's
spine up to the major needs none: the redex is not the point, so it
fits the recursor's telescope (`teleFit_of_ne_pt`, task #347).  The
major's own slot certificate gives the reduced major's invariant and
its slot; the constructor's telescope certificate gives the
constructor's fit. -/
theorem iota_core {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {dM bM tM : Expr} {doms' tys' : List Expr} {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hIM : InferSem m φ Γ major tM) (hDM : DefEqSem m φ Γ tM dM)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  refine iota_core_sem hnB hfind hus hlen hpis hmaj hmeq hcij husj hpis' ?_ hres hshape hrps hX hlaw
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwxs : ∀ a ∈ args.take majorIdx, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  -- the major's certificate gives the invariant of the reduced major and of its arguments
  obtain ⟨hwmajor, hwtM, hTtM, hmemM⟩ := hIM ρ hs
  have hmargs : ∀ a ∈ margs, WellDenoted m.M φ ρ a := by
    subst hmeq; exact (WellDenoted_mkAppN m.M φ hwmajor).2
  have hsub : Expr.mkAppN (Expr.const c us) args =
      .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx)) (args.getD majorIdx (Expr.bvar 0)) := by
    conv => lhs; rw [hsplit]
    rw [Expr.mkAppN_append]; rfl
  have hwT := (m.type_ok c ci hfind φ ρ us hus).1
  -- the recursor's fit up to the major, from the redex not being the point (no certificate)
  have hfitxs : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) (args.take majorIdx) := by
    have hw' := hsub ▸ hw
    have hn' := hsub ▸ hn
    rw [WellDenoted_app] at hw'
    refine teleFit_of_ne_pt hwT (by rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2)
      ?_ hw'.1 (fn_ne_pt hn')
    rw [Expr.hasPis_instL]
    exact Expr.hasPis_of_succ _ _ (by
      have : (args.take majorIdx).length = majorIdx := by simp [hlen]
      rw [this]; exact hpis)
  refine ⟨hwmajor, ?_, ?_⟩
  -- the major's slot, from its certificate
  · have hwR := WellDenoted_piResidual hwT hwxs hfitxs hresM
    rw [WellDenoted_pi] at hwR
    refine teleFit_snoc hfitxs hresM ?_
    rw [← hDM ρ hs hwtM hwR.1 hTtM.ne_pt hwR.2.1.ne_pt]
    exact hmemM
  -- the constructor's fit, from its certificate
  · exact teleFit_of_certs hs (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs hdoms' htys' hI' hD'

/-- The domain a fitting spine's last argument meets holds it. -/
theorem teleFit_snoc_mem {ρ : Nat → V} {y D B : Expr} :
    ∀ {T : Expr} {xs : List Expr}, TeleFit m.M φ ρ T (xs ++ [y]) →
      Expr.piResidual T xs = some (.pi D B) → interp m.M φ ρ y ∈ˢ interp m.M φ ρ D
  | T, [], hfit, h => by
    simp at h; subst h; exact hfit.1
  | .pi A B₀, x :: xs, hfit, h => by
    rw [Expr.piResidual_pi_cons] at h
    exact teleFit_snoc_mem hfit.2 h
  | .bvar _, _ :: _, h, _ => h.elim
  | .sort _, _ :: _, h, _ => h.elim
  | .const _ _, _ :: _, h, _ => h.elim
  | .app _ _, _ :: _, h, _ => h.elim
  | .lam _ _, _ :: _, h, _ => h.elim

/-- **ι with no telescope certificate at all, where the major's domain
is strict** (the case of a family that is never a proposition).  If the
domain the major meets holds no point at the valuation — the case of an
inductive family whose sort is never `Prop` at the instance, whose
fibres are sets of tagged tuples — then a redex that is not the point
has a major that is not the point (the major lies in that domain,
`teleFit_of_ne_pt`), so the major's reduction claim applies; the
reduced major, a constructor application that is not the point, fits
the constructor's telescope by the same argument.  No certificate is
needed for the recursor's spine, the major or the constructor's
spine.  The strictness is a semantic hypothesis here (a sort above
`Prop` also holds truth values, so the universe does not give it);
`strict_dom` supplies it from the environment law
`EnvModel.ind_fib` and one level test (`Red.iotaStrict`). -/
theorem iota_core_strict {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {dM bM : Expr} {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hstrict : ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      Strict (interp m.M φ ρ dM))
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  refine iota_core_sem hnB hfind hus hlen hpis hmaj hmeq hcij husj hpis' ?_ hres hshape hrps hX hlaw
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwxs : ∀ a ∈ args.take majorIdx, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  have hwT := (m.type_ok c ci hfind φ ρ us hus).1
  have hcT : interp m.M φ ρ (Expr.const c us) ∈ˢ interp m.M φ ρ (ci.type.instL ci.lparams us) := by
    rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2
  -- the whole unreduced spine fits, the major included
  have hfitAll : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) args :=
    teleFit_of_ne_pt hwT hcT (by rw [Expr.hasPis_instL, hlen]; exact hpis) hw hn
  have hfitAll' := hfitAll
  rw [hsplit] at hfitAll'
  have hmajD := teleFit_snoc_mem hfitAll' hresM
  -- the domain is strict, so the major is not the point and its reduction claim applies
  have hmajne : interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) ≠ pt :=
    ne_pt_of_mem_strict (hstrict ρ hs hw hn) hmajD
  have hwmaj0 : WellDenoted m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) := by
    apply hargs
    have hmem : args.getD majorIdx (Expr.bvar 0) ∈ args.take majorIdx ++ [args.getD majorIdx (Expr.bvar 0)] := by
      simp
    rwa [← hsplit] at hmem
  obtain ⟨hwmajor, hmajeq⟩ := hmaj ρ hs hwmaj0 hmajne
  have hfitxs : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) (args.take majorIdx) := by
    have hsub : Expr.mkAppN (Expr.const c us) args =
        .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx))
          (args.getD majorIdx (Expr.bvar 0)) := by
      conv => lhs; rw [hsplit]
      rw [Expr.mkAppN_append]; rfl
    have hw' := hsub ▸ hw
    have hn' := hsub ▸ hn
    rw [WellDenoted_app] at hw'
    refine teleFit_of_ne_pt hwT hcT ?_ hw'.1 (fn_ne_pt hn')
    rw [Expr.hasPis_instL]
    exact Expr.hasPis_of_succ _ _ (by
      have : (args.take majorIdx).length = majorIdx := by simp [hlen]
      rw [this]; exact hpis)
  refine ⟨hwmajor, teleFit_snoc hfitxs hresM (hmajeq ▸ hmajD), ?_⟩
  -- the reduced major is a constructor application that is not the point
  subst hmeq
  have hcjT := (m.type_ok _ cij hcij φ ρ usj husj)
  exact teleFit_of_ne_pt hcjT.1 (by rw [interp_const]; exact hcjT.2.2)
    (by rw [Expr.hasPis_instL]; exact hpis') hwmajor (hmajeq ▸ hmajne)

/-- **ι with no major-slot certificate, the semantic core** (task #342
F1, generalising F3's `iota_core_prop`).  The constructor's telescope
keeps its certificate; the reduced major's slot needs none, given at
every valuation where the redex is well-denoted and not the point,
the constructor's spine fits and the unreduced major (which lies in
the major's domain `dM`) is the point: then the constructor
application is the point (`hcase`).  Where the unreduced major is not
the point its reduction claim gives the reduct; where it is, the
reduct is the point too.  `iota_core_prop` supplies `hcase` from a sort
that is zero everywhere (F3); `Red.iotaSlot` from the environment's
slot law (`EnvModel.rec_rules_slot`, `slot_of_law`, F2). -/
theorem iota_core_slot {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {dM bM : Expr} {doms' tys' : List Expr} {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hcase : ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ (cij.type.instL cij.lparams usj) margs →
      interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) ∈ˢ interp m.M φ ρ dM →
      interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) = pt →
      interp m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs) = pt)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  refine iota_core_sem hnB hfind hus hlen hpis hmaj hmeq hcij husj hpis' ?_ hres hshape hrps hX hlaw
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwT := (m.type_ok c ci hfind φ ρ us hus).1
  have hcT : interp m.M φ ρ (Expr.const c us) ∈ˢ interp m.M φ ρ (ci.type.instL ci.lparams us) := by
    rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2
  -- the whole unreduced spine fits, the major included: the major lies in `dM`
  have hfitAll : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) args :=
    teleFit_of_ne_pt hwT hcT (by rw [Expr.hasPis_instL, hlen]; exact hpis) hw hn
  have hfitAll' := hfitAll
  rw [hsplit] at hfitAll'
  have hmajD := teleFit_snoc_mem hfitAll' hresM
  have hfitxs : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) (args.take majorIdx) := by
    have hsub : Expr.mkAppN (Expr.const c us) args =
        .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx))
          (args.getD majorIdx (Expr.bvar 0)) := by
      conv => lhs; rw [hsplit]
      rw [Expr.mkAppN_append]; rfl
    have hw' := hsub ▸ hw
    have hn' := hsub ▸ hn
    rw [WellDenoted_app] at hw'
    refine teleFit_of_ne_pt hwT hcT ?_ hw'.1 (fn_ne_pt hn')
    rw [Expr.hasPis_instL]
    exact Expr.hasPis_of_succ _ _ (by
      have : (args.take majorIdx).length = majorIdx := by simp [hlen]
      rw [this]; exact hpis)
  -- the constructor's fit, from its certificate
  have hmargs : ∀ a ∈ margs, WellDenoted m.M φ ρ a := by
    intro a ha
    have hl : margs.length = tys'.length := by rw [htys', Expr.length_of_piDomains hdoms']
    obtain ⟨t, ht⟩ := List.exists_mem_zip_of_length hl a ha
    exact (hI' (a, t) ht ρ hs).1
  have hcjT := m.type_ok _ cij hcij φ ρ usj husj
  have hfit' := teleFit_of_certs hs hcjT.1 hmargs hdoms' htys' hI' hD'
  subst hmeq
  -- the reduced major is well-denoted: its spine fits the constructor's telescope
  have hwmajor : WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs) := by
    have hp : (cij.type.instL cij.lparams usj).hasPis margs.length = true := by
      rw [Expr.hasPis_instL]; exact hpis'
    refine WellDenoted_mkAppN_of_spineOk m.M φ ρ (WellDenoted_const m.M φ ρ _ _) hmargs ?_
    exact spineOk_of_teleFitV m.M φ hcjT.1 (by rw [interp_const]; exact hcjT.2.2)
      (teleFitV_of_teleFit m.M φ ρ hp hfit')
  -- the reduced major's slot, with no certificate
  have hwmaj0 : WellDenoted m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) := by
    apply hargs
    have hmem : args.getD majorIdx (Expr.bvar 0) ∈
        args.take majorIdx ++ [args.getD majorIdx (Expr.bvar 0)] := by simp
    rwa [← hsplit] at hmem
  have hslot : interp m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs) ∈ˢ interp m.M φ ρ dM := by
    by_cases hm0 : interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) = pt
    · rw [hcase ρ hs hw hn hmargs hfit' hmajD hm0, ← hm0]
      exact hmajD
    · rw [← (hmaj ρ hs hwmaj0 hm0).2]; exact hmajD
  exact ⟨hwmajor, teleFit_snoc hfitxs hresM hslot, hfit'⟩

/-- **ι with no major-slot certificate** (task #342 F3; #342 v2 §11.4
case 3: the family may be `Prop`, the motive may not).  The
constructor's telescope keeps its full-grade certificate (every
parameter and field, #349); the reduced major's slot needs none.  The
redex is not the point, so the whole unreduced spine fits the
recursor's telescope (`teleFit_of_ne_pt`) and the unreduced major lies
in its domain `dM`.  If the unreduced major is not the point, its
reduction claim gives the reduct's value.  If it is, then at this
valuation either `dM` is strict — impossible, it holds the point — or
the constructor's family `I` has a sort that evaluates to zero, and then
the reduced constructor application is the point too
(`ctorApp_eq_pt_of_sortZero`), a member of `dM`.

The disjunction `hcase` is the semantic interface: `Red.iotaProp`
supplies its right side at every valuation (the family's sort is `0`
at every valuation, a level test).  It is a corollary of
`iota_core_slot`, whose case split `Red.iotaSlot` supplies from the
environment's fibre law (lane F1: strict where the family's sort is not
zero), the rule for a family that may be `Prop` at some valuations only
(`Quot.{u}`, `PUnit.{u}`).  The index comparisons are passed on in their conditional
form, as in `iota_core`; the slot does not use them. -/
theorem iota_core_prop {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {dM bM : Expr} {doms' tys' : List Expr} {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    {Ii : ConstInfo} {u : Level}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hI : env.find? I = some Ii) (hlsI : lsI.length = Ii.lparams.length)
    (hpisI : Ii.type.hasPis (rps ++ ridx).length = true)
    (hsort : Expr.piResidual (Ii.type.instL Ii.lparams lsI) (rps ++ ridx) = some (.sort u))
    (hcase : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      Strict (interp m.M φ ρ dM) ∨ Level.eval φ u = 0)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  refine iota_core_slot hnB hfind hus hlen hpis hmaj hmeq hcij husj hpis' hresM hdoms' htys' hI' hD'
    hres hshape hrps ?_ hX hlaw
  intro ρ hs hw _ hmargs hfit' hmem h0
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  rcases hcase ρ hs hargs with hstr | hz
  · exact absurd h0 (ne_pt_of_mem_strict hstr hmem)
  · subst hshape
    exact ctorApp_eq_pt_of_sortZero hcij husj hmargs hfit' hres hI hlsI hpisI hsort hz

/-- **A well-denoted family application that is not the point has the
fibre its stored sort says** (task #342 F1): its arguments fit the
former's telescope (`teleFit_of_ne_pt`), so the environment's fibre law
(`EnvModel.ind_fib`) applies. -/
theorem app_fib {ρ : Nat → V} {I : Name} {ls : List Level} {zs : List Expr} {ci : ConstInfo}
    {nP nI : Nat} {cs : List Name} {S : IndSpec}
    (hI : env.find? I = some ci) (hk : ci.kind = .induct nP nI cs S)
    (hls : ls.length = ci.lparams.length) (hz : zs.length = nP + nI)
    (hpisI : ci.type.hasPis (nP + nI) = true)
    (hw : WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const I ls) zs))
    (hne : interp m.M φ ρ (Expr.mkAppN (Expr.const I ls) zs) ≠ pt) :
    Fib (Level.eval φ (S.sort.subst ci.lparams ls) == 0)
      (interp m.M φ ρ (Expr.mkAppN (Expr.const I ls) zs)) := by
  have hT := m.type_ok I ci hI φ ρ ls hls
  have hp : (ci.type.instL ci.lparams ls).hasPis zs.length = true := by
    rw [Expr.hasPis_instL, hz]; exact hpisI
  have hfit := teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2) hp hw hne
  have hfib := m.ind_fib I ci nP nI cs S hI hk φ ρ ls _ hls (by simp [hz])
    (teleFitV_of_teleFit m.M φ ρ hp hfit)
  rw [interp_mkAppN_appList, interp_const]
  exact hfib

/-- **The major's domain has the fibre its family's sort says** (task
#342 F1): where the domain the recursor's telescope leaves for the
major is a stored inductive family at its parameters and indices, at
every valuation where the redex is well-denoted and not the point.  The
redex not being the point puts the spine before the major in the
recursor's telescope (`teleFit_of_ne_pt`), so the domain is well-denoted
and a type, hence not the point (`app_fib`). -/
theorem dom_fib {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {majorIdx : Nat} {dM bM : Expr}
    {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
    {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec}
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdM : dM = Expr.mkAppN (Expr.const I₀ ls₀) dargs)
    (hI₀ : env.find? I₀ = some ci₀) (hk₀ : ci₀.kind = .induct nP₀ nI₀ cs₀ S₀)
    (hls₀ : ls₀.length = ci₀.lparams.length) (hd₀ : dargs.length = nP₀ + nI₀)
    (hpis₀ : ci₀.type.hasPis (nP₀ + nI₀) = true) :
    ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      Fib (Level.eval φ (S₀.sort.subst ci₀.lparams ls₀) == 0) (interp m.M φ ρ dM) := by
  intro ρ _ hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwxs : ∀ a ∈ args.take majorIdx, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  have hwT := (m.type_ok c ci hfind φ ρ us hus).1
  have hcT : interp m.M φ ρ (Expr.const c us) ∈ˢ interp m.M φ ρ (ci.type.instL ci.lparams us) := by
    rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2
  -- the recursor's fit up to the major, from the redex not being the point
  have hfitxs : TeleFit m.M φ ρ (ci.type.instL ci.lparams us) (args.take majorIdx) := by
    have hsub : Expr.mkAppN (Expr.const c us) args =
        .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx))
          (args.getD majorIdx (Expr.bvar 0)) := by
      conv => lhs; rw [hsplit]
      rw [Expr.mkAppN_append]; rfl
    have hw' := hsub ▸ hw
    have hn' := hsub ▸ hn
    rw [WellDenoted_app] at hw'
    refine teleFit_of_ne_pt hwT hcT ?_ hw'.1 (fn_ne_pt hn')
    rw [Expr.hasPis_instL]
    exact Expr.hasPis_of_succ _ _ (by
      have : (args.take majorIdx).length = majorIdx := by simp [hlen]
      rw [this]; exact hpis)
  -- the major's domain is well-denoted and a type
  have hwR := WellDenoted_piResidual hwT hwxs hfitxs hresM
  rw [WellDenoted_pi] at hwR
  obtain ⟨hwD, hTyD, -, -⟩ := hwR
  subst hdM
  exact app_fib hI₀ hk₀ hls₀ hd₀ hpis₀ hwD hTyD.ne_pt

/-- **The major's domain is strict at a never-`Prop` family** (task
#342 F1): `dom_fib` where the family's stored sort is `≥ 1` at every
valuation (one oracle test). -/
theorem strict_dom [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {majorIdx : Nat} {dM bM : Expr}
    {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
    {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec}
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdM : dM = Expr.mkAppN (Expr.const I₀ ls₀) dargs)
    (hI₀ : env.find? I₀ = some ci₀) (hk₀ : ci₀.kind = .induct nP₀ nI₀ cs₀ S₀)
    (hls₀ : ls₀.length = ci₀.lparams.length) (hd₀ : dargs.length = nP₀ + nI₀)
    (hpis₀ : ci₀.type.hasPis (nP₀ + nI₀) = true)
    (hlvl : LevelOracle.le (.succ .zero) (S₀.sort.subst ci₀.lparams ls₀) = true) :
    ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      Strict (interp m.M φ ρ dM) := by
  intro ρ hs hw hn
  have hfib := dom_fib hfind hus hlen hpis hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ ρ hs hw hn
  have hne : Level.eval φ (S₀.sort.subst ci₀.lparams ls₀) ≠ 0 := by
    have := (LevelOracle.le_iff _ _).mp hlvl φ
    simp only [Level.eval_succ, Level.eval_zero] at this
    omega
  rwa [show (Level.eval φ (S₀.sort.subst ci₀.lparams ls₀) == 0) = false by simpa using hne] at hfib

/-- **The slot case of `iota_core_slot`, from the environment's slot
law** (task #342 F2): the redex is not the point, so the whole spine
fits the recursor's telescope (`teleFit_of_ne_pt`); where the major is
the point, `RecRuleSlotLaw` makes the recursor's application — the
redex, which is not the point — or the constructor the point.  No
premise relates the major's domain to the constructor's family: on the
generated recursors that link is the installer's (`IndSpec.rec_rule_slot`,
`rec_rule_slotN`, `rec_rule_slot1N`). -/
theorem slot_of_law {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {majorIdx : Nat} {dM : Expr} {rl : RecRule}
    {usj : List Level} {cij : ConstInfo} {margs : List Expr}
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (husj : usj.length = cij.lparams.length)
    (hlaw : RecRuleSlotLaw m.M c ci majorIdx rl cij)
    (hlv : rl.inst = none →
      usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ)) :
    ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
      WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const c us) args) →
      interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args) ≠ pt →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ (cij.type.instL cij.lparams usj) margs →
      interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) ∈ˢ interp m.M φ ρ dM →
      interp m.M φ ρ (args.getD majorIdx (Expr.bvar 0)) = pt →
      interp m.M φ ρ (Expr.mkAppN (Expr.const rl.ctor usj) margs) = pt := by
  intro ρ _ hw hn _ _ _ h0
  have hT := m.type_ok c ci hfind φ ρ us hus
  have hp : (ci.type.instL ci.lparams us).hasPis args.length = true := by
    rw [Expr.hasPis_instL, hlen]; exact hpis
  have hfitV := teleFitV_of_teleFit m.M φ ρ hp
    (teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2) hp hw hn)
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hvals : args.map (interp m.M φ ρ) = (args.take majorIdx).map (interp m.M φ ρ) ++ [pt] := by
    conv => lhs; rw [hsplit]
    rw [List.map_append, List.map_singleton, h0]
  rw [hvals] at hfitV
  have hv : interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args)
      = appList (m.M c (us.map (Level.eval φ))) ((args.take majorIdx).map (interp m.M φ ρ) ++ [pt]) := by
    rw [interp_mkAppN_appList, interp_const, hvals]
  rcases hlaw φ ρ us usj _ (margs.map (interp m.M φ ρ)) hus husj (by simp [hlen]) hfitV hlv with
    h | h
  · exact absurd (hv.trans h) hn
  · rw [interp_mkAppN_appList, interp_const]; exact h

/-- **ι by K, with no certificate at all** (task #349).  Given the K
law (`RecRuleLawK`), a K redex reduces to the right-hand side applied
to the recursor's parameters, motives and minors, with no major-slot
certificate, no constructor certificate, no parameter or index
comparison, and no reduction of the major: the redex is not the point,
so the whole spine — the major included — fits the recursor's
telescope (`teleFit_of_ne_pt`), which is all the law asks; the reduct
does not mention the major.  The checker's K type check (the
fabricated constructor's type against the major's) decides whether the
step is taken, as in Lean's kernel, and no claim consumes it. -/
theorem iotaK_core_sem {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {rl : RecRule} {numBefore majorIdx : Nat}
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hlaw : RecRuleLawK m.M c ci numBefore majorIdx rl) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore)) := by
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hT := m.type_ok c ci hfind φ ρ us hus
  have hp : (ci.type.instL ci.lparams us).hasPis args.length = true := by
    rw [Expr.hasPis_instL, hlen]; exact hpis
  have hfit := teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2) hp hw hn
  have hfitV := teleFitV_of_teleFit m.M φ ρ hp hfit
  have hv : interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args)
      = appList (m.M c (us.map (Level.eval φ))) (args.map (interp m.M φ ρ)) := by
    rw [interp_mkAppN_appList, interp_const]
  obtain ⟨heq, hwr, hsp⟩ :=
    hlaw φ ρ us (args.map (interp m.M φ ρ)) hus (by simp [hlen]) hfitV (hv ▸ hn)
  have hvals : (args.take numBefore).map (interp m.M φ ρ)
      = (args.map (interp m.M φ ρ)).take numBefore := List.map_take ..
  refine ⟨WellDenoted_mkAppN_of_spineOk m.M φ ρ hwr
    (fun a ha => hargs a (List.mem_of_mem_take ha)) (by rw [hvals]; exact hsp), ?_⟩
  rw [hv, heq, interp_mkAppN_appList, hvals]

/-- **ι**: `iota_core` with the environment's `RecRuleLaw`;
the parameter comparisons are passed on in their conditional form. -/
theorem iota_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {dM bM tM : Expr} {doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = none)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hIM : InferSem m φ Γ major tM) (hDM : DefEqSem m φ Γ tM dM)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  subst hnB hmI hctor
  refine iota_core (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hresM hIM hDM hdoms' htys' hI' hD' hres hshape hrps hX ?_
  intro ρ hs hargs hmargs hfitV hfitV' hX' hn
  have hP' : ∀ p ∈ ((margs.map (interp m.M φ ρ)).take numParams).zip
      (((args.take (numParams + numMotives + numMinors + numIndices)).map
        (interp m.M φ ρ)).take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    exact cmp_vals hs (fun a ha => hmargs a (List.mem_of_mem_take ha))
      (fun a ha => hargs a (List.mem_of_mem_take ha)) hP
  exact m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl hinst cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX' hn

/-- **ι on a family in `Prop`** (`Red.iotaProp`): `iota_core_prop` with
the environment's `RecRuleLaw`; the oracle's `u = 0` is the right side
of its case split at every valuation. -/
theorem iotaProp_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {dM bM : Expr} {doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    {Ii : ConstInfo} {u : Level}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = none)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hI : env.find? I = some Ii) (hlsI : lsI.length = Ii.lparams.length)
    (hpisI : Ii.type.hasPis (rps ++ ridx).length = true)
    (hsort : Expr.piResidual (Ii.type.instL Ii.lparams lsI) (rps ++ ridx) = some (.sort u))
    (hu : LevelOracle.eq u .zero = true) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  subst hnB hmI hctor
  refine iota_core_prop (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hresM hdoms' htys' hI' hD' hres hshape hrps hI hlsI hpisI hsort
    (fun _ _ _ => Or.inr (by rw [eval_eq_of_oracle hu]; rfl)) hX ?_
  intro ρ hs hargs hmargs hfitV hfitV' hX' hn
  have hP' : ∀ p ∈ ((margs.map (interp m.M φ ρ)).take numParams).zip
      (((args.take (numParams + numMotives + numMinors + numIndices)).map
        (interp m.M φ ρ)).take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    exact cmp_vals hs (fun a ha => hmargs a (List.mem_of_mem_take ha))
      (fun a ha => hargs a (List.mem_of_mem_take ha)) hP
  exact m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl hinst cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX' hn

/-- **ι with no major-slot certificate and no level test**
(`Red.iotaSlot`, task #342 F1/F2): `iota_core_slot` with the slot case
from the environment's slot law (`slot_of_law`) and the environment's
`RecRuleLaw`. -/
theorem iotaSlot_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {dM bM : Expr} {doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = none)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  subst hnB hmI
  have hcase := slot_of_law (φ := φ) (Γ := Γ) (args := args) (dM := dM) (margs := margs) hfind hus
    hlen hpis
    husj (m.rec_rules_slot c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl cij
      (hctor ▸ hcij)) (fun _ => (Level.eqList_iff _ _).mp hlv φ)
  subst hctor
  refine iota_core_slot (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hresM hdoms' htys' hI' hD' hres hshape hrps hcase hX ?_
  intro ρ hs hargs hmargs hfitV hfitV' hX' hn
  have hP' : ∀ p ∈ ((margs.map (interp m.M φ ρ)).take numParams).zip
      (((args.take (numParams + numMotives + numMinors + numIndices)).map
        (interp m.M φ ρ)).take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    exact cmp_vals hs (fun a ha => hmargs a (List.mem_of_mem_take ha))
      (fun a ha => hargs a (List.mem_of_mem_take ha)) hP
  exact m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl hinst cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX' hn

/-- **ι, case 2** (task #342 F1): `iota_core_strict` with the
domain's strictness from `strict_dom` and the environment's
`RecRuleLaw`; no certificate. -/
theorem iotaStrict_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {dM bM : Expr} {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
    {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = none)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdM : dM = Expr.mkAppN (Expr.const I₀ ls₀) dargs)
    (hI₀ : env.find? I₀ = some ci₀) (hk₀ : ci₀.kind = .induct nP₀ nI₀ cs₀ S₀)
    (hls₀ : ls₀.length = ci₀.lparams.length) (hd₀ : dargs.length = nP₀ + nI₀)
    (hpis₀ : ci₀.type.hasPis (nP₀ + nI₀) = true)
    (hlvl : LevelOracle.le (.succ .zero) (S₀.sort.subst ci₀.lparams ls₀) = true)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  subst hnB hmI hctor
  refine iota_core_strict (by omega) hfind hus hlen hpis hmaj hmeq hcij husj
    (by rw [hmlen]; exact hpis') hresM
    (strict_dom hfind hus hlen hpis hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl) hres hshape hrps hX ?_
  intro ρ hs hargs hmargs hfitV hfitV' hX' hn
  have hP' : ∀ p ∈ ((margs.map (interp m.M φ ρ)).take numParams).zip
      (((args.take (numParams + numMotives + numMinors + numIndices)).map
        (interp m.M φ ρ)).take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    exact cmp_vals hs (fun a ha => hmargs a (List.mem_of_mem_take ha))
      (fun a ha => hargs a (List.mem_of_mem_take ha)) hP
  exact m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl hinst cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX' hn

/-- **ι by K** (`Red.iotaK`, task #342 F2): `iotaK_core_sem` with the
environment's K law (`EnvModel.rec_rules_k`).  K's type check is not
read. -/
theorem iotaK_sound {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {rl : RecRule}
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = numParams + numMotives + numMinors + numIndices + 1)
    (hpis : ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true)
    (hrl : rl ∈ rules) (hk : rl.k = true) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take (numParams + numMotives + numMinors))) :=
  iotaK_core_sem hfind hus hlen hpis
    (m.rec_rules_k c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl hk)

/-- **ι, nested, case 2** (task #342 F1): `iota_core_strict` at the
constructor's own parameter count, with `RecRuleLawN`. -/
theorem iotaNestedStrict_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level}
    {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
    {lvs : List Level} {pinst : List Expr}
    {dM bM : Expr} {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
    {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = some (lvs, pinst))
    (hcij : env.find? cj = some cij) (hcijk : cij.kind = .ctor I' nPc nfj)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = nPc + rl.nfields)
    (hpis' : cij.type.hasPis (nPc + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdM : dM = Expr.mkAppN (Expr.const I₀ ls₀) dargs)
    (hI₀ : env.find? I₀ = some ci₀) (hk₀ : ci₀.kind = .induct nP₀ nI₀ cs₀ S₀)
    (hls₀ : ls₀.length = ci₀.lparams.length) (hd₀ : dargs.length = nP₀ + nI₀)
    (hpis₀ : ci₀.type.hasPis (nP₀ + nI₀) = true)
    (hlvl : LevelOracle.le (.succ .zero) (S₀.sort.subst ci₀.lparams ls₀) = true)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nPc)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop nPc)) := by
  subst hnB hmI hctor
  refine iota_core_strict (by omega) hfind hus hlen hpis hmaj hmeq hcij husj
    (by rw [hmlen]; exact hpis') hresM
    (strict_dom hfind hus hlen hpis hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl) hres hshape hrps hX ?_
  intro ρ _ _ _ hfitV hfitV' hX' hn
  exact m.rec_rules_nested c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl
    lvs pinst hinst cij I' nPc nfj hcij hcijk φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' hX' hn

/-- **ι, nested**: `iota_core` at the constructor's own
parameter count, with the environment's `RecRuleLawN`. -/
theorem iotaNested_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
    {lvs : List Level} {pinst : List Expr}
    {dM bM tM : Expr} {doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = some (lvs, pinst))
    (hcij : env.find? cj = some cij) (hcijk : cij.kind = .ctor I' nPc nfj)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = nPc + rl.nfields)
    (hpis' : cij.type.hasPis (nPc + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hIM : InferSem m φ Γ major tM) (hDM : DefEqSem m φ Γ tM dM)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nPc)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop nPc)) := by
  subst hnB hmI hctor
  refine iota_core (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hresM hIM hDM hdoms' htys' hI' hD' hres hshape hrps hX ?_
  intro ρ _ _ _ hfitV hfitV' hX' hn
  exact m.rec_rules_nested c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl
    lvs pinst hinst cij I' nPc nfj hcij hcijk φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' hX' hn


/-- **ι, nested, with no major-slot certificate** (`Red.iotaNestedSlot`,
task #342 F1/F2): `iota_core_slot` at the constructor's own parameter
count, with the slot law (`slot_of_law`) and `RecRuleLawN`. -/
theorem iotaNestedSlot_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
    {lvs : List Level} {pinst : List Expr}
    {dM bM : Expr} {doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = some (lvs, pinst))
    (hcij : env.find? cj = some cij) (hcijk : cij.kind = .ctor I' nPc nfj)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = nPc + rl.nfields)
    (hpis' : cij.type.hasPis (nPc + rl.nfields) = true)
    (hresM : Expr.piResidual (ci.type.instL ci.lparams us) (args.take majorIdx) = some (.pi dM bM))
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nPc)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop nPc)) := by
  subst hnB hmI
  have hcase := slot_of_law (φ := φ) (Γ := Γ) (args := args) (dM := dM) (margs := margs) hfind hus
    hlen hpis
    husj (m.rec_rules_slot c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl cij
      (hctor ▸ hcij)) (fun h => by rw [hinst] at h; cases h)
  subst hctor
  refine iota_core_slot (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hresM hdoms' htys' hI' hD' hres hshape hrps hcase hX ?_
  intro ρ _ _ _ hfitV hfitV' hX' hn
  exact m.rec_rules_nested c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl
    lvs pinst hinst cij I' nPc nfj hcij hcijk φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' hX' hn
end Red

/-! ## The master induction -/

mutual

theorem red_sound [LevelOracle] : ∀ {Γ : List Expr} {e e' : Expr},
    Red env Γ e e' → RedSem m φ Γ e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ => Red.trans_sound (red_sound h₁) (red_sound h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound h)
  | _, _, _, .beta => Red.beta_sound
  | _, _, _, .zeta => Red.zeta_sound
  | _, _, _, .delta hfind hv hls => Red.delta_sound hfind hv hls
  | _, _, _, .iota hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis' hresM
      hIM hDM hdoms' htys' hI' hD' hlv hP hres hshape hrps hX =>
    Red.iota_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst hcij husj
      hmlen hpis' hresM (infer_sound hIM) (defeq_sound hDM)
      hdoms' htys' (fun p hp => infer_sound (hI' p hp)) (fun p hp => defeq_sound (hD' p hp))
      hlv (fun p hp => defeq_sound (hP p hp)) hres hshape hrps
      (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaProp hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis' hresM
      hdoms' htys' hI' hD' hlv hP hres hshape hrps hX hI hlsI hpisI hsort hu =>
    Red.iotaProp_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst hcij husj
      hmlen hpis' hresM hdoms' htys' (fun p hp => infer_sound (hI' p hp))
      (fun p hp => defeq_sound (hD' p hp)) hlv (fun p hp => defeq_sound (hP p hp)) hres hshape hrps
      (fun p hp => defeq_sound (hX p hp)) hI hlsI hpisI hsort hu
  | _, _, _, .iotaNested hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj hmlen
      hpis' hresM hIM hDM hdoms' htys' hI' hD' _ _ _ hres hshape hrps hX =>
    Red.iotaNested_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst
      hcij hcijk husj hmlen hpis' hresM (infer_sound hIM)
      (defeq_sound hDM) hdoms' htys' (fun p hp => infer_sound (hI' p hp))
      (fun p hp => defeq_sound (hD' p hp)) hres hshape hrps (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaSlot hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis' hresM
      hdoms' htys' hI' hD' hlv hP hres hshape hrps hX =>
    Red.iotaSlot_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst hcij husj
      hmlen hpis' hresM hdoms' htys' (fun p hp => infer_sound (hI' p hp))
      (fun p hp => defeq_sound (hD' p hp)) hlv (fun p hp => defeq_sound (hP p hp)) hres hshape hrps
      (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaNestedSlot hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj hmlen
      hpis' hresM hdoms' htys' hI' hD' _ _ _ hres hshape hrps hX =>
    Red.iotaNestedSlot_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst
      hcij hcijk husj hmlen hpis' hresM hdoms' htys' (fun p hp => infer_sound (hI' p hp))
      (fun p hp => defeq_sound (hD' p hp)) hres hshape hrps (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaStrict hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis'
      hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl hlv hP hres hshape hrps hX =>
    Red.iotaStrict_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst
      hcij husj hmlen hpis' hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl hlv
      (fun p hp => defeq_sound (hP p hp)) hres hshape hrps (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaNestedStrict hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj
      hmlen hpis' hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl _ _ _ hres hshape hrps hX =>
    Red.iotaNestedStrict_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor
      hinst hcij hcijk husj hmlen hpis' hresM hdM hI₀ hk₀ hls₀ hd₀ hpis₀ hlvl hres hshape hrps
      (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaK hfind hkind hus hlen hpis hrl hk _ _ _ _ =>
    Red.iotaK_sound hfind hkind hus hlen hpis hrl hk
theorem defeq_sound [LevelOracle] : ∀ {Γ : List Expr} {a b : Expr},
    DefEq env Γ a b → DefEqSem m φ Γ a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hr) (defeq_sound h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .pi hA hB => DefEq.pi_sound (defeq_sound hA) (defeq_sound hB)
  | _, _, _, .lam hA hb ht₁ ht₂ ht =>
    DefEq.lam_sound (defeq_sound hA) (defeq_sound hb) (infer_sound ht₁) (infer_sound ht₂)
      (defeq_sound ht)
  | _, _, _, .lamProp hA hb hs hu hu0 =>
    DefEq.lamProp_sound (defeq_sound hA) (defeq_sound hb) (infer_sound hs) (red_sound hu) hu0
  | _, _, _, .etaProp htb hr hA hbody hs hu hu0 =>
    DefEq.etaProp_sound (infer_sound htb) (red_sound hr) (defeq_sound hA) (defeq_sound hbody)
      (infer_sound hs) (red_sound hu) hu0
  | _, _, _, .lamConst hA hb hc₁ hc₂ =>
    DefEq.lamConst_sound (defeq_sound hA) (defeq_sound hb) hc₁ hc₂
  | _, _, _, .appIn hf hI hr ha =>
    DefEq.appIn_sound (defeq_sound hf) (infer_sound hI) (red_sound hr) (defeqIn_sound ha)
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hf) (defeq_sound ha)
  | _, _, _, .eta htb hr hA hbody ht₁ htB =>
    DefEq.eta_sound (fun ρ hs _ _ => (infer_sound htb ρ hs).2) (red_sound hr) (defeq_sound hA)
      (defeq_sound hbody)
      (infer_sound ht₁) (defeq_sound htB)
  | _, _, _, .proofIrrel hta htta hu hu0 _ _ _ _ =>
    DefEq.proofIrrel_sound (infer_sound hta) (infer_sound htta) (red_sound hu) hu0
  | _, _, _, .lams h => DefEq.lams_sound (defeqLams_sound h)

theorem defeqLams_sound [LevelOracle] : ∀ {Γ : List Expr} {a b : Expr},
    DefEqLams env Γ a b → LamsSem m φ Γ a b
  | _, _, _, .refl => DefEqLams.refl_sound
  | _, _, _, .inner hA hb ht₁ ht₂ ht =>
    DefEqLams.inner_sound (defeq_sound hA) (defeq_sound hb) (infer_sound ht₁) (infer_sound ht₂)
      (defeq_sound ht)
  | _, _, _, .outer hA hb => DefEqLams.outer_sound (defeq_sound hA) (defeqLams_sound hb)

theorem defeqIn_sound [LevelOracle] : ∀ {Γ : List Expr} {T a b : Expr},
    DefEqIn env Γ T a b → DefEqInSem m φ Γ T a b
  | _, _, _, _, .of h => DefEqIn.of_sound (defeq_sound h)
  | _, _, _, _, .symm h => DefEqIn.symm_sound (defeqIn_sound h)
  | _, _, _, _, .lam hr hb => DefEqIn.lam_sound (red_sound hr) (defeqIn_sound hb)
  | _, _, _, _, .eta hr hb => DefEqIn.eta_sound (red_sound hr) (defeqIn_sound hb)

theorem infer_sound [LevelOracle] : ∀ {Γ : List Expr} {e T : Expr},
    Infer env Γ e T → InferSem m φ Γ e T
  | _, _, _, .bvar h => Infer.bvar_sound h
  | _, _, _, .sort => Infer.sort_sound
  | _, _, _, .const hfind hls => Infer.const_sound hfind hls
  | _, _, _, .pi hA hu hB hv =>
    Infer.pi_sound (infer_sound hA) (red_sound hu) (infer_sound hB) (red_sound hv)
  | _, _, _, .lam hA hu hb =>
    Infer.lam_sound (infer_sound hA) (red_sound hu) (infer_sound hb)
  | _, _, _, .app hf hr ha hd =>
    Infer.app_sound (infer_sound hf) (red_sound hr) (infer_sound ha) (defeq_sound hd)
  | _, _, _, .letE hT hu hv hd hb =>
    Infer.letE_sound (infer_sound hT) (red_sound hu) (infer_sound hv) (defeq_sound hd)
      (infer_sound hb)

end

/-! ## The theorem -/

/-- **Soundness of the fragment.**  At every model of the environment
and every valuation: a reduction — β included, at every binder, with
no certificate — keeps the invariant and the denotation of a subject
that is not the point; two well-denoted sides that are not the point
and that the checker calls definitionally equal have equal
denotations; an inferred term and its type are well-denoted, the type
is a type, and the term's denotation is a member of the type's. -/
theorem soundness [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) :
    (∀ {Γ : List Expr} {e e' : Expr}, Red env Γ e e' → RedSem m φ Γ e e') ∧
    (∀ {Γ : List Expr} {a b : Expr}, DefEq env Γ a b → DefEqSem m φ Γ a b) ∧
    (∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → InferSem m φ Γ e T) :=
  ⟨red_sound, defeq_sound, infer_sound⟩

/-- **The closed corollary**: a closed term the checker types is a
member of its type, under every model, valuation and environment. -/
theorem closed_infer [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) {e T : Expr}
    (h : Infer env [] e T) (ρ : Nat → V) :
    interp m.M φ ρ e ∈ˢ interp m.M φ ρ T :=
  (infer_sound (m := m) (φ := φ) h ρ (Sat_nil m.M φ ρ)).2.2.2

end Fragment
