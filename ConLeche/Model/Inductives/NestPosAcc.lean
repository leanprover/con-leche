module

public import ConLeche.Model.Inductives.HoleAccKit
public import ConLeche.Verify.Inductives.PosDeriv
public import ConLeche.Model.Inductives.ClassAccTele

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
* **a telescope's** (`PiAccThen`, `OutTele`).

The prog-free vocabulary under it (`MentNH`/`MentP`, the `congrQ`
lemmas, `transfer_of_*`, `TeleSmall`) is `HoleAccKit.lean`.
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


/-- An occurrence in `[q, q + 1)` is a leaf at `q`. -/
theorem leaf_of_nestOcc {q : Nat} {e : Expr} (h : e.nestOcc [] q (q + 1) = true) :
    ∃ l ∈ e.fvarLeaves, l.1 = q := by
  refine Classical.byContradiction fun hn => ?_
  rw [nestOcc_nil_of_leaves e fun z hz hq => hn ⟨z, hz, hq⟩] at h
  exact Bool.false_ne_true h

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

/-! ## The admissible items and the relation the run is proved along -/

/-- **The admissible items at depth `d`**: a member hole at its full
arity (the parameters and its indices — `nestPos`'s `holeApp` check), or
a frame's hole at its container member's full arity (`nestArity`, the
frame-hole check). -/
@[expose] def HoleQ (ctx : NestCtx) (prog : List NestHole) (d : Nat) : Nat → Nat → Prop :=
  fun i n =>
    (∃ t, t < ctx.names.length ∧ ctx.nP + t < d ∧ i = d - 1 - (ctx.nP + t) ∧
      n = ctx.nP + ctx.nIdxs.getD t 0) ∨
    (∃ (j : Nat) (hk : NestHole), prog.reverse[j]? = some hk ∧ ctx.hiAt 0 + j < d ∧
      i = d - 1 - (ctx.hiAt 0 + j) ∧ n = ConLeche.nestArity ctx hk.key.cname)

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

/-- **The hole relation for accessibility** at depth `d` under the frames
`prog`: related frames satisfy the context and agree off the hole
positions; every frame's hole is blind in its key's parameters; the
relation is symmetric and its holes are rich (`RichOn`) at their full
arity. -/
structure HoleRelA (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ dsa,
    DenoteMetaSpine m.acval env φ d hk.key.ds dsa → FrameBlind R (d - 1 - (ctx.hiAt 0 + i)) dsa
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x
  symm : R.Symm
  rich : RichOn (HoleQ ctx prog d) R
  /-- left-reflexive: a frame hole's richness
  enlarges the tuple at the SAME enclosing frame -/
  lrefl : ∀ ρ ρ₀, R ρ ρ₀ → R ρ ρ

theorem FrameBlind.underBoth {R : FrameRel V} {h : Nat} {ds : List AnnotTerm}
    (hb : FrameBlind R h ds) (A : AnnotTerm) :
    FrameBlind (R.underBoth A) (h + 1) (ds.map (AnnotTerm.liftN 1 · 0)) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩ is
  have hl : ∀ (σ : Nat → V), (ds.map (AnnotTerm.liftN 1 · 0)).map (interp V (cons x σ))
      = ds.map (interp V σ) := by
    intro σ
    rw [List.map_map]
    refine List.map_congr_left fun a _ => ?_
    show interp V (cons x σ) (a.liftN 1 0) = interp V σ a
    rw [interp_liftN]
    congr 1
  rw [hl, hl]
  exact hb ρ ρ' hR is

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
  frame := by
    intro i key hk dsa' hsp
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < d := by
      simp only [NestCtx.hiAt] at hd ⊢; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped i key hk x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + i) = d - 1 - (ctx.hiAt 0 + i) + 1 by omega]
    exact FrameBlind.underBoth (h.frame i key hk dsa hdsa) ta
  dsScoped := h.dsScoped
  symm := h.symm.underBoth ta
  rich := RichOn.congrQ (shiftQ_holeQ hd) (h.rich.underBoth htr)
  lrefl := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, -⟩
    exact ⟨x, ρ, ρ, rfl, rfl, h.lrefl ρ ρ' hR, hx, hx⟩

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
    (dep : Nat) (Δa : List AnnotTerm) (k : ConLeche.PosKind) (nf : Expr) (ea : AnnotTerm) : Prop :=
  nf.looseBVarsBounded 0 = true ∧ Expr.WScoped dep nf ∧
  (k = .ordinary → nf.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
  ∃ na, denoteMeta m.acval env φ dep nf = some na ∧
    ∀ ρ, Sat V Δa ρ → interp V ρ na = interp V ρ ea

theorem OutOk.congr_read {m : EnvModel V env} {ctx : NestCtx} {prog : List NestHole} {dep : Nat}
    {Δa : List AnnotTerm} {k : ConLeche.PosKind} {nf : Expr} {ea ea' : AnnotTerm}
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
    List ConLeche.PosKind → List Expr → Nat → List AnnotTerm → AnnotTerm → Prop
  | [], [], _, _, _ => True
  | k :: ks, nd :: nds, d, Δ, .pi _ _ A B =>
    OutOk m φ ctx prog d Δ k nd A ∧ OutTele m φ ctx prog ks nds (d + 1) (A :: Δ) B
  | _, _, _, _, _ => False

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
