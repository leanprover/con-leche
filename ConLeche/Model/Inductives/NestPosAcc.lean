module

public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Semantics.Inductives.HoleAcc
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Denote.Shift
import ConLeche.Model.Inductives.NestPosOut

public section

/-!
# Accessibility in the holes: the vocabulary

The counterpart of `NestPosMono.lean`'s vocabulary for the closure
witness (W): joint accessibility at the instantiation is an install-time
lemma derived from the positivity walk, like monotonicity, proved by
induction on the positivity DERIVATION (`posD_acc`, `PosDerivAcc.lean`),
never on the run; this file holds what that induction states:

* **the relation** (`HoleRelA`) relates COMPARABLE frames: they satisfy
  the context and agree off the hole positions; no growth condition
  (supports carry the elements).  Under a field the relation is
  `underBoth`;
* **a field's conclusion** (`AccConcl`): the type regime, and
  accessibility with a bound reading only the non-hole positions the
  walk's OUTPUT mentions (`InvOn`, `MentNH`) — so a later field's bound
  does not read an earlier recursive, reflexive or nested field (U4 on
  the normal-form telescope), what makes a constructor's bound UNIFORM
  across the tuples of the space; and the output's facts (`OutOk`);
* **a telescope's** (`PiAccThen`, `OutTele`, `TeleSmall`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The positions an output mentions -/

/-- **The non-hole positions an output mentions** at depth `d`: position
`i` is the variable `d - 1 - i`, mentioned by `nf`, and not a hole. -/
@[expose] def MentNH (lo hi d : Nat) (nf : Expr) : Nat → Prop :=
  fun i => i < d ∧ nf.nestOcc [] (d - 1 - i) (d - i) = true ∧ ¬ holeP d lo hi i

omit [SetTheory V] in
theorem noBVar_exists' {α : Type} :
    ∀ {e : AnnotTerm} {P : α → Nat → Prop}, (∀ a, NoBVar (P a) e) →
      NoBVar (fun i => ∃ a, P a i) e := by
  intro e
  induction e with
  | bvar i => intro P h; exact fun ⟨a, ha⟩ => h a ha
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P h; exact ⟨ihf fun a => (h a).1, iha fun a => (h a).2⟩
  | eqE a b iha ihb => intro P h; exact ⟨iha fun a => (h a).1, ihb fun a => (h a).2⟩
  | fst e ihe => intro P h; exact ihe fun a => h a
  | snd e ihe => intro P h; exact ihe fun a => h a
  | lam v A b ihA ihb =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihb (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | pi u v A B ihA ihB =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihB (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi

/-- **A hole-free domain inside the output reads only mentioned non-hole
positions.** -/
theorem noBVar_not_mentNH {lo hi d : Nat} {a nf : Expr} {ta : AnnotTerm}
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hholes : NoBVar (holeP d lo hi) ta)
    (hsub : ∀ s, s < d → nf.nestOcc [] s (s + 1) = false → a.nestOcc [] s (s + 1) = false)
    (hta : denoteMeta m.acval env φ d a = some ta) :
    NoBVar (fun i => ¬ MentNH lo hi d nf i) ta := by
  have hbb := denote_bvarsBelow m.cval_closedL d a hws hb (denoteMeta_erase m.acval_erase d a hta)
  have hbelow : NoBVar (fun i => d ≤ i) ta := NoBVar_of_bvarsBelow hbb fun _ h => h
  have hnone : NoBVar (fun _ => False) ta := NoBVar_of_bvarsBelow hbb fun _ h => h.elim
  have hun : NoBVar (fun i => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i)
      ta := by
    refine noBVar_exists' (P := fun s i => s < d ∧ nf.nestOcc [] s (s + 1) = false ∧
      holeP d s (s + 1) i) fun s => ?_
    by_cases hs : s < d ∧ nf.nestOcc [] s (s + 1) = false
    · exact NoBVar.mono (fun i hn => hn.2.2)
        (denoteMeta_noBVar_of_nestOcc (m := m) (names := []) (lo := s) (hi := s + 1) d a hws
          (by omega) (hsub s hs.1 hs.2) hta)
    · exact NoBVar.mono (fun i hn => absurd ⟨hn.1, hn.2.1⟩ hs) hnone
  have hall := noBVar_exists' (α := Fin 3) (P := fun k i => match k with
    | 0 => d ≤ i
    | 1 => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i
    | 2 => holeP d lo hi i) (e := ta) fun k => by
      match k with
      | 0 => exact hbelow
      | 1 => exact hun
      | 2 => exact hholes
  refine NoBVar.mono (fun i hn => ?_) hall
  by_cases hid : i < d
  · by_cases hh : holeP d lo hi i
    · exact ⟨2, hh⟩
    · refine ⟨1, d - 1 - i, by omega, ?_, ⟨hid, by omega, by omega⟩⟩
      cases hm : nf.nestOcc [] (d - 1 - i) (d - 1 - i + 1)
      · rfl
      · exact absurd ⟨hid, by rw [show d - i = d - 1 - i + 1 by omega]; exact hm, hh⟩ hn
  · exact ⟨0, by omega⟩

/-- The body's output, one binder down, mentions no more than the Π's. -/
theorem mentNH_body {lo hi dep : Nat} {a nb : Expr} {bm : ConLeche.BinderMeta} :
    ∀ i, MentNH lo hi (dep + 1) nb i → liftM (MentNH lo hi dep (.forallE a (nb.abstract1 dep 0) bm)) i
  | 0, _ => trivial
  | i + 1, ⟨hlt, hm, hh⟩ => by
    refine ⟨by omega, ?_, fun h => hh (holeP_succ (i + 1) h)⟩
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true]
    refine Or.inr ?_
    rw [nestOcc_abstract1 (by omega) nb 0]
    rw [show dep + 1 - 1 - (i + 1) = dep - 1 - i by omega,
      show dep + 1 - (i + 1) = dep - i by omega] at hm
    exact hm

/-- No leaf at `q`: no occurrence in `[q, q + 1)`. -/
theorem nestOcc_nil_of_leaves {q : Nat} :
    ∀ (e : Expr), (∀ z ∈ e.fvarLeaves, z.1 ≠ q) → e.nestOcc [] q (q + 1) = false := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl
  | const n _ => intro _; simp [Expr.nestOcc]
  | fvar i ty _ =>
    intro h
    have := h (i, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.nestOcc, decide_eq_false_iff_not]
    omega
  | app f a ihf iha =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨ihf fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      iha fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | lam ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | forallE ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihv fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩,
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | proj _ _ e ihe =>
    intro h
    simp only [Expr.nestOcc]
    exact ihe fun z hz => h z (by simp [Expr.fvarLeaves, hz])

/-- An occurrence in `[q, q + 1)` is a leaf at `q`. -/
theorem leaf_of_nestOcc {q : Nat} {e : Expr} (h : e.nestOcc [] q (q + 1) = true) :
    ∃ l ∈ e.fvarLeaves, l.1 = q := by
  refine Classical.byContradiction fun hn => ?_
  rw [nestOcc_nil_of_leaves e fun z hz hq => hn ⟨z, hz, hq⟩] at h
  exact Bool.false_ne_true h

/-- **The positions a bound may read**: the non-hole positions the output
mentions, or a PARAMETER position (a container's
bound reads the enclosing parameters through its key's parameters, which
may be mentioned only inside an annotation). -/
@[expose] def MentP (lo hi d : Nat) (nf : Expr) : Nat → Prop :=
  fun i => MentNH lo hi d nf i ∨ (i < d ∧ d - 1 - i < lo)

theorem mentP_body {lo hi dep : Nat} {a nb : Expr} {bm : ConLeche.BinderMeta} :
    ∀ i, MentP lo hi (dep + 1) nb i → liftM (MentP lo hi dep (.forallE a (nb.abstract1 dep 0) bm)) i
  | 0, _ => trivial
  | i + 1, Or.inl h => Or.inl (mentNH_body (i + 1) h)
  | i + 1, Or.inr ⟨hlt, hp⟩ => Or.inr ⟨by omega, by omega⟩

/-- **The output mentions only the input's leaves** (below the depth). -/
@[expose] def OutMent (dep : Nat) (e nf : Expr) : Prop :=
  ∀ q, q < dep → nf.nestOcc [] q (q + 1) = true → ∃ l ∈ e.fvarLeaves, l.1 = q

theorem outMent_self (dep : Nat) (e : Expr) : OutMent dep e e :=
  fun _ _ h => leaf_of_nestOcc h

theorem OutMent.trans {dep : Nat} {e w nf : Expr} (h : OutMent dep w nf)
    (hsub : ∀ l ∈ w.fvarLeaves, l ∈ e.fvarLeaves) : OutMent dep e nf := by
  intro q hq ho
  obtain ⟨l, hl, rfl⟩ := h q hq ho
  exact ⟨l, hsub l hl, rfl⟩

omit [SetTheory V] in
theorem InvOn.mono {M M' : Nat → Prop} {A : (Nat → V) → V} (h : InvOn M A) (hM : ∀ i, M i → M' i) :
    InvOn M' A :=
  fun ρ ρ' hag => h ρ ρ' fun i hi => hag i (hM i hi)

/-! ## The admissible items and the relation the run is proved along -/

/-- **The admissible items at depth `d`**: a member hole at its full
arity (its indices — a hole stands for the member's whole application to
the parameters), or a frame's hole at its container member's full arity
past the key's parameters (`nestArity`, the frame-hole check). -/
@[expose] def HoleQ (ctx : NestCtx) (prog : List NestHole) (d : Nat) : Nat → Nat → Prop :=
  fun i n =>
    (∃ t, t < ctx.names.length ∧ ctx.nP + t < d ∧ i = d - 1 - (ctx.nP + t) ∧
      n = ctx.nIdxs.getD t 0) ∨
    (∃ (j : Nat) (hk : NestHole), prog.reverse[j]? = some hk ∧ ctx.hiAt 0 + j < d ∧
      i = d - 1 - (ctx.hiAt 0 + j) ∧ n + hk.key.ds.length = ConLeche.nestArity ctx hk.key.cname)

/-- One binder down, the admissible items are the same holes. -/
theorem shiftQ_holeQ {ctx : NestCtx} {prog : List NestHole} {d : Nat}
    (hd : ctx.hiAt prog.length ≤ d) (i n : Nat) :
    shiftQ (HoleQ ctx prog d) i n ↔ HoleQ ctx prog (d + 1) i n := by
  cases i with
  | zero =>
    simp only [shiftQ, false_iff]
    rintro (⟨t, ht, -, hi, -⟩ | ⟨j, hk, hj, -, hi, -⟩)
    · simp only [NestCtx.hiAt] at hd; omega
    · have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_reverse] at this
      simp only [NestCtx.hiAt] at hd hi ⊢; omega
  | succ i =>
    simp only [shiftQ]
    constructor
    · rintro (⟨t, ht, hlt, hi, hn⟩ | ⟨j, hk, hj, hlt, hi, hn⟩)
      · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
      · exact Or.inr ⟨j, hk, hj, by omega, by omega, hn⟩
    · rintro (⟨t, ht, hlt, hi, hn⟩ | ⟨j, hk, hj, hlt, hi, hn⟩)
      · refine Or.inl ⟨t, ht, ?_, by omega, hn⟩
        simp only [NestCtx.hiAt] at hd; omega
      · have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_reverse] at this
        refine Or.inr ⟨j, hk, hj, ?_, by omega, hn⟩
        simp only [NestCtx.hiAt] at hd hi ⊢; omega

theorem holdsLe_congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n) {ρ ρ' : Nat → V}
    (h : HoldsLe Q ρ ρ') : HoldsLe Q' ρ ρ' :=
  fun o ho => h o ((hQ _ _).mpr ho)

theorem RichOn.congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n) {R : FrameRel V}
    (h : RichOn Q R) : RichOn Q' R := by
  intro ρ ρ₀ hR i vs hq hpt
  obtain ⟨ρ'', hR'', hle, hz⟩ := h ρ ρ₀ hR i vs ((hQ _ _).mpr hq) hpt
  exact ⟨ρ'', hR'', holdsLe_congrQ hQ hle, hz⟩

theorem AccOn.congrQ {w : Nat} {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n)
    {R : FrameRel V} {A : (Nat → V) → V} {a : AnnotTerm} (h : AccOn w Q R A a) :
    AccOn w Q' R A a := by
  intro ρ ρ₀ hR x hxw hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ hR x hxw hx
  exact ⟨B, g, hB, fun b hb => ⟨(hQ _ _).mp (hg b hb).1, (hg b hb).2⟩, hs⟩

/-- **The hole relation for accessibility** at depth `d` under the frames
`prog`: related frames satisfy the context and agree off the hole
positions; the relation is symmetric and its holes are rich (`RichOn`) at
their full arity (a hole stands for a whole application: it takes no
parameters). -/
structure HoleRelA (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x
  symm : R.Symm
  rich : RichOn (HoleQ ctx prog d) R
  /-- left-reflexive: a frame hole's richness
  enlarges the tuple at the SAME enclosing frame -/
  lrefl : ∀ ρ ρ₀, R ρ ρ₀ → R ρ ρ

/-- **Under a binder** whose domain carries its values to every larger
related frame (a hole-free domain, or an earlier field — accessible, its
values small): the relation one level deeper, the bound value in the
domain at both frames. -/
theorem HoleRelA.underBoth {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRelA m φ ctx prog d Δa R) (hd : ctx.hiAt prog.length ≤ d)
    (ta : AnnotTerm)
    (htr : ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe (HoleQ ctx prog d) ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta) :
    HoleRelA m φ ctx prog (d + 1) (ta :: Δa) (R.underBoth ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 hx'⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.underBoth ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  dsScoped := h.dsScoped
  symm := h.symm.underBoth ta
  rich := RichOn.congrQ (shiftQ_holeQ hd) (h.rich.underBoth htr)
  lrefl := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, -⟩
    exact ⟨x, ρ, ρ, rfl, rfl, h.lrefl ρ ρ' hR, hx, hx⟩

/-- A hole-free domain carries its values. -/
theorem transfer_of_constOn {R : FrameRel V} {Q : Nat → Nat → Prop} {ta : AnnotTerm}
    (hA : ConstOn R ta) :
    ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe Q ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta :=
  fun ρ _ ρ'' _ hR'' _ _ hx _ => hA ρ ρ'' hR'' ▸ hx

/-- An accessible domain carries its small values. -/
theorem transfer_of_accOn {w : Nat} {R : FrameRel V} {Q : Nat → Nat → Prop} {ta : AnnotTerm}
    {Af : (Nat → V) → V} (hA : AccOn w Q R Af ta)
    (hsm : ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ (univ w : V)) :
    ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe Q ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta :=
  fun ρ ρ₀ _ hR₀ hR'' hle x hx _ => hA.transfer hR₀ hR'' hle (hsm ρ ρ₀ hR₀ x hx) hx

/-! ## What a field proves -/

/-- **What a field proves of its reading** along an accessibility hole
relation: the type regime, and accessibility with a bound of the level
reading only the non-hole positions the output mentions. -/
@[expose] def AccConcl (w : Nat) (ctx : NestCtx) (prog : List NestHole) (dep : Nat) (e nf : Expr)
    (R : FrameRel V) (ea : AnnotTerm) : Prop :=
  TypeReg R ea ∧ (∃ A, AccOn w (HoleQ ctx prog dep) R A ea ∧ SizeOn w R A ∧
    InvOn (MentP ctx.nP (ctx.hiAt prog.length) dep nf) A) ∧ OutMent dep e nf

/-- **What a field proves of its OUTPUT**:
the output is scoped and bvar-closed, hole-free at an ordinary kind, and
it READS as the input at every satisfying frame — the facts a container
frame needs to run its per-constructor telescope over the walk's normal
form (the input may mention a non-ordinary field or a hole inside a
redex whnf drops, `corner_nestw_u4frame_beta`). -/
@[expose] def OutOk (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (dep : Nat) (Δa : List AnnotTerm) (k : ConLeche.NestFieldKind) (nf : Expr) (ea : AnnotTerm) : Prop :=
  nf.looseBVarsBounded 0 = true ∧ Expr.WScoped dep nf ∧
  (k = .ordinary → nf.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
  ∃ na, denoteMeta m.acval env φ dep nf = some na ∧
    ∀ ρ, Sat V Δa ρ → interp V ρ na = interp V ρ ea

theorem OutOk.congr_read {m : EnvModel V env} {ctx : NestCtx} {prog : List NestHole} {dep : Nat}
    {Δa : List AnnotTerm} {k : ConLeche.NestFieldKind} {nf : Expr} {ea ea' : AnnotTerm}
    (h : OutOk m φ ctx prog dep Δa k nf ea)
    (heq : ∀ ρ, Sat V Δa ρ → interp V ρ ea = interp V ρ ea') :
    OutOk m φ ctx prog dep Δa k nf ea' := by
  obtain ⟨h1, h2, h3, na, hna, hr⟩ := h
  exact ⟨h1, h2, h3, na, hna, fun ρ hρ => (hr ρ hρ).trans (heq ρ hρ)⟩

/-- A Π reads alike when its bodies read alike over its domain. -/
theorem interp_pi_congr_body {u v : Nat} {A B B' : AnnotTerm} {ρ : Nat → V}
    (h : ∀ x, x ∈ˢ interp V ρ A → interp V (cons x ρ) B = interp V (cons x ρ) B') :
    interp V ρ (.pi u v A B) = interp V ρ (.pi u v A B') := by
  rw [interp_pi, interp_pi]
  unfold piR
  split
  · refine truthVal_congr (forall_congr' fun d => imp_congr_right fun hd => ?_)
    show (∃ y, y ∈ˢ interp V (cons d ρ) B) ↔ ∃ y, y ∈ˢ interp V (cons d ρ) B'
    rw [h d hd]
  · exact piSet_congr fun d hd => h d hd

/-! ## A constructor's field telescope -/

/-- **The first `n` Π-domains of a reading accessible**, each under the
earlier ones (`underBoth`), with a bound of the level reading only the
non-hole positions of its walk's output (`nds`, one per field, at their
depths from `d`), and `Q` of the relation and the reading below them. -/
@[expose] def PiAccThen (w : Nat) (ctx : NestCtx) (prog : List NestHole)
    (Q : FrameRel V → AnnotTerm → Prop) :
    Nat → Nat → List Expr → FrameRel V → AnnotTerm → Prop
  | 0, _, _, R, r => Q R r
  | n + 1, d, nd :: nds, R, .pi _ _ A B =>
    (∃ Af, AccOn w (HoleQ ctx prog d) R Af A ∧ SizeOn w R Af ∧
      InvOn (MentP ctx.nP (ctx.hiAt prog.length) d nd) Af) ∧
      PiAccThen w ctx prog Q n (d + 1) nds (R.underBoth A) B
  | _ + 1, _, _, _, _ => False

/-- **The walked fields' outputs, field by field**: each output, at its depth and under the earlier INPUT domains, is
`OutOk` of its field's reading at its kind. -/
@[expose] def OutTele (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (prog : List NestHole) :
    List ConLeche.NestFieldKind → List Expr → Nat → List AnnotTerm → AnnotTerm → Prop
  | [], [], _, _, _ => True
  | k :: ks, nd :: nds, d, Δ, .pi _ _ A B =>
    OutOk m φ ctx prog d Δ k nd A ∧ OutTele m φ ctx prog ks nds (d + 1) (A :: Δ) B
  | _, _, _, _, _ => False

/-- **The first `n` Π-domains' values are small** at every frame of the
relation, each under the earlier ones. -/
@[expose] def TeleSmall (w : Nat) : Nat → FrameRel V → AnnotTerm → Prop
  | 0, _, _ => True
  | n + 1, R, .pi _ _ A B =>
    (∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ A → x ∈ˢ (univ w : V)) ∧
      TeleSmall w n (R.underBoth A) B
  | _ + 1, _, _ => True

theorem PiAccThen.mono {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {Q Q' : FrameRel V → AnnotTerm → Prop}
    (hQ : ∀ R r, Q R r → Q' R r) :
    ∀ (n d : Nat) (nds : List Expr) (R : FrameRel V) (r : AnnotTerm),
      PiAccThen w ctx prog Q n d nds R r → PiAccThen w ctx prog Q' n d nds R r
  | 0, _, _, R, r, h => hQ R r h
  | n + 1, d, _ :: nds, _, .pi _ _ _ B, h => ⟨h.1, PiAccThen.mono hQ n (d + 1) nds _ B h.2⟩
  | _ + 1, _, [], _, _, h => h.elim
  | _ + 1, _, _ :: _, _, .bvar _, h | _ + 1, _, _ :: _, _, .sort _, h
  | _ + 1, _, _ :: _, _, .const _ _, h | _ + 1, _, _ :: _, _, .app _ _, h
  | _ + 1, _, _ :: _, _, .lam _ _ _, h | _ + 1, _, _ :: _, _, .eqE _ _, h
  | _ + 1, _, _ :: _, _, .fst _, h | _ + 1, _, _ :: _, _, .snd _, h
  | _ + 1, _, _ :: _, _, .prf, h => h.elim

end ConLeche.Model
