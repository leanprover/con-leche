module

public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Semantics.Inductives.HoleAcc
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Denote.Shift
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Semantics.Frame
import ConLeche.Verify.InferLemmas

public section

/-!
# `nestPos`'s run ⇒ ACCESSIBLE in the holes (lane ACCMODEL)

The twin of `NestPosMono.lean` for the closure witness (W) (maintainer
ruling "(W) by ACCESSIBILITY", 2026-09-24): joint accessibility at the
instantiation is an install-time lemma derived from the positivity
walk's run, like monotonicity.  The inversion is `nestPos_sem`'s, case
by case, over the reading-level lemmas of
`Semantics/Inductives/HoleAcc.lean`:

* the `whnf` step by `red_sound` (`AccOn.of_eqOn`);
* `const`: the reduct mentions no hole — the empty bound;
* `pi`: a hole-free domain, the body by induction under `underBoth`;
* `holeApp`: a member hole at hole-free arguments — the bound `{pt}`;
* a frame's hole: blind in its key's parameters (`FrameBlind`, a fact of
  the relation, `HoleRelA.frame`) — the bound `{pt}`;
* `contApp`: the premise `ContAcc` (the container case, its own lemma).

**The relation** (`HoleRelA`) relates COMPARABLE frames: they satisfy the
context and agree off the hole positions; no growth condition (supports
carry the elements).  Under a field the relation is `underBoth`.

**The bound's positions.**  Next to accessibility the theorem states
which positions the bound reads (`InvOn`): only the non-hole positions
the walk's OUTPUT mentions (`MentNH`).  A later field's bound then does
not read an earlier recursive, reflexive or nested field (U4 on the
normal-form telescope) — what makes a constructor's bound UNIFORM across
the tuples of the space.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckError CheckM NestCtx NestKey NestHole NestState NestFieldKind
  nestPos nestCont fueledOps)

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

omit [SetTheory V] in
theorem InvOn.mono {M M' : Nat → Prop} {A : (Nat → V) → V} (h : InvOn M A) (hM : ∀ i, M i → M' i) :
    InvOn M' A :=
  fun ρ ρ' hag => h ρ ρ' fun i hi => hag i (hM i hi)

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

/-! ## The theorem -/

/-- **What a run proves of its reading** along an accessibility hole
relation: the type regime, and accessibility with a bound of the level
reading only the non-hole positions the output mentions. -/
@[expose] def AccConcl (w : Nat) (ctx : NestCtx) (prog : List NestHole) (dep : Nat) (nf : Expr)
    (R : FrameRel V) (ea : AnnotTerm) : Prop :=
  TypeReg R ea ∧ ∃ A, AccOn w (HoleQ ctx prog dep) R A ea ∧ SizeOn w R A ∧
    InvOn (MentNH ctx.nP (ctx.hiAt prog.length) dep nf) A

/-- A run of the positivity function (or of its recursive call one fuel
lower) which keeps the state invariant `I`, also when it ends in a
restart request, and whose reading is proved ACCESSIBLE (`AccConcl`)
when it does not. -/
@[expose] def NestPosAcc (m : EnvModel V env) (φ : Name → Nat) (w : Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') → P k →
    ctx.hiAt prog.length ≤ dep → Frame dep e → I st →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      HoleRelA m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none →
        AccConcl w ctx prog dep nf R ea)

/-- **The container case**, as the premise the theorem takes: a
successful `nestCont` at a container reduct whose recursive call is
accessible makes the reduct's reading accessible (`AccConcl`, the output
IS the reduct). -/
@[expose] def ContAcc (m : EnvModel V env) (φ : Name → Nat) (w : Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop) (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (wt : Expr) (n : Name) (us : List Level)
    (st : NestState) (k : NestFieldKind) (st' : NestState),
    wt.getAppFn = .const n us → ctx.names.contains n = false →
    nestCont ctx (fueledOps .verified F) env rec prog kb n us wt.getAppArgs st = .ok (k, st') →
    P k →
    ctx.hiAt prog.length ≤ dep → Frame dep wt → I st →
    ∀ {Δa : List AnnotTerm} {wa : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa wt → denoteMeta m.acval env φ dep wt = some wa → Graded V Δa wa →
      HoleRelA m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none →
        AccConcl w ctx prog dep wt R wa)

/-- **THE THEOREM (non-container cases): a run of `nestPos` is
accessible.**  If the positivity function returns (at the pure verified
instantiation, at any fuel), leaving no restart request pending, then the
reading of its input is in the type regime and accessible along every
accessibility hole relation, with a bound of the level (`w ≠ 0`) reading
only the non-hole positions of the output.  By inversion of the run
(`nestPos_sem`'s): the whnf step by `red_sound`, then `const`, `pi` (by
induction; at a `Prop` codomain the body is truth-valued by the grading,
so hole-free by its type regime), `holeApp` and a frame's hole (both at
their full arity, rich); the container case is the premise `ContAcc`,
given the theorem one fuel lower. -/
theorem nestPos_acc (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat) {w : Nat} (hw : w ≠ 0)
    {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosAcc m φ w ctx P I rec → ContAcc m φ w ctx P I F rec) :
    ∀ fuel, NestPosAcc m φ w ctx P I (nestPos (fueledOps .verified F) env ctx fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro prog dep kb e st k nf st' hrun hP hhi hfr hI Δa ea R hC hea hgr hR
    rw [nestPos] at hrun
    cases hw' : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw'' : (fueledOps .verified F).whnf env dep e = .error err := hw'
      simp [hw'', bind, Except.bind] at hrun
    | ok wt =>
      have hw'' : (fueledOps .verified F).whnf env dep e = .ok wt := hw'
      simp only [hw'', bind, Except.bind] at hrun
      obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
        red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
      have hCw : CtxOkP m φ dep Δa wt := hC.of_subset hsub
      suffices hw2 : I st' ∧ (st'.restart = none → AccConcl w ctx prog dep nf R wa) from
        ⟨hw2.1, fun hc => by
          obtain ⟨hTR, A, hA, hsz, hinv⟩ := hw2.2 hc
          exact ⟨TypeReg.of_eqOn (P := Sat V Δa) hR.dom (fun ρ hρ => heq ρ hρ) hTR,
            A, AccOn.of_eqOn (P := Sat V Δa) hR.dom (fun ρ hρ => heq ρ hρ) hA, hsz, hinv⟩⟩
      have hwempty : (empty : V) ∈ˢ (univ w : V) := empty_mem_univ w
      by_cases hocc : wt.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · have hco : ConstOn R wa := ConstOn.of_noBVar hR.agree
          (denoteMeta_noBVar_of_nestOcc dep wt hfrw.1 hhi hocc hwa)
        refine ⟨?_, fun _ => ⟨hco.typeReg, _, hco.accOn, SizeOn.const hwempty, InvOn.const _ _⟩⟩
        rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        rw [← hrun.2.2]; exact hI
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b mb
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
        obtain ⟨hws, hb, hLb⟩ := hfrw
        simp only [Expr.WScoped] at hws
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hholes : NoBVar (holeP dep ctx.nP (ctx.hiAt prog.length)) ta :=
          denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi (by simpa using ha) hta
        have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree hholes
        obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
        have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        obtain ⟨hI', hB⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv hP (by omega)
          (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hI hCop hba hgB
          (hR.underBoth hhi ta (transfer_of_constOn hA))
        refine ⟨hI', fun hc => ?_⟩
        obtain ⟨hTRb, Ab, hAb, hszb, hinvb⟩ := hB hc
        -- at a `Prop` codomain the body is truth-valued (the grading)
        have hB0 : pwBit φ mb.pw = 0 → ∀ σ σ', R.underBoth ta σ σ' →
            interp V σ ba ∈ˢ (univZero : V) ∧ interp V σ' ba ∈ˢ (univZero : V) := by
          rintro hv0 _ _ ⟨x, ρ, ρ', rfl, rfl, hRr, hx, hx'⟩
          have hval : ∀ σ, Sat V Δa σ → x ∈ˢ interp V σ ta →
              interp V (cons x σ) ba ∈ˢ (univZero : V) := by
            intro σ hσ hxσ
            have := (hgw σ hσ).2
            rw [AnnotValid_pi] at this
            exact this.2.2 hv0 x hxσ
          exact ⟨hval ρ (hR.dom ρ ρ' hRr).1 hx, hval ρ' (hR.dom ρ ρ' hRr).2 hx'⟩
        refine ⟨TypeReg.pi 0 _ hA hTRb hB0, ?_⟩
        by_cases hv0 : pwBit φ mb.pw = 0
        · -- hole-free: the body is
          have hco : ConstOn R (.pi 0 (pwBit φ mb.pw) ta ba) :=
            ConstOn.pi 0 _ hA (hTRb (hB0 hv0))
          exact ⟨_, hco.accOn, SizeOn.const hwempty, InvOn.const _ _⟩
        · refine ⟨_, AccOn.pi hw 0 hv0 hA (AccOn.congrQ (fun i n => (shiftQ_holeQ hhi i n).symm) hAb),
            SizeOn.pi hw hA hszb,
            InvOn.pi ?_ (InvOn.mono hinvb fun i hi => mentNH_body i hi)⟩
          refine noBVar_not_mentNH hws.1 hb.1 hholes (fun s _ hs => ?_) hta
          simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hs
          exact hs.1
      · -- a head applied to arguments
        rename_i hnotpi
        have hspine := Expr.mkAppN_getApp wt
        split at hrun
        · rename_i i ty hfn
          rw [hfn] at hspine
          rw [← hspine] at hwa
          obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
          rw [denoteMeta_fvar] at hfa
          cases hfa
          have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
            have h0 := hfrw.1
            rw [← hspine] at h0
            exact (wScoped_mkAppN _ h0).2
          have hlenv := DenoteMetaSpine.length_eq hsp
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · -- `holeApp`
            rw [if_pos hmem] at hrun
            by_cases hc : (wt.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                List.take ctx.nP wt.getAppArgs == ctx.params &&
                wt.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x)
                = true
            · rw [if_pos hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc hmem
              obtain ⟨⟨hlen, -⟩, hfree⟩ := hc
              simp only [decide_eq_true_eq] at hmem
              have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
              have hQ : HoleQ ctx prog dep (dep - 1 - i) vs.length := by
                refine Or.inl ⟨i - ctx.nP, ?_, ?_, by omega, by rw [← hlenv, hlen]⟩
                · simp only [NestCtx.hiAt] at hmem; omega
                · simp only [NestCtx.hiAt] at hmem hhi; omega
              exact ⟨TypeReg.holeApp hR.rich hR.symm hQ hvs, _, AccOn.holeApp hQ hvs,
                SizeOn.const (unitSet_mem_univ w), InvOn.const _ _⟩
            · rw [if_neg hc] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            by_cases hfr' : (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt prog.length)) = true
            · -- a frame's hole
              rw [if_pos hfr'] at hrun
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr'
              split at hrun
              · simp [throw, throwThe, MonadExceptOf.throw] at hrun
              · rename_i key hk
                by_cases hpar : (decide (key.key.ds.length ≤ wt.getAppArgs.length) &&
                    (List.take key.key.ds.length wt.getAppArgs == key.key.ds)) = true
                · rw [if_pos hpar] at hrun
                  by_cases hidx : ((wt.getAppArgs.drop key.key.ds.length).all fun x =>
                      !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) = true
                  · rw [if_pos hidx] at hrun
                    by_cases har : (wt.getAppArgs.length == ConLeche.nestArity ctx key.key.cname) = true
                    · rw [if_pos har] at hrun
                      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                      refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
                      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpar har
                      simp only [List.all_eq_true, Bool.not_eq_true'] at hidx
                      rw [← List.take_append_drop key.key.ds.length wt.getAppArgs] at hsp
                      obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
                      have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
                        ⟨hwsargs a (List.mem_of_mem_drop ha), by simpa using hidx a ha⟩
                      have hsp₁' : DenoteMetaSpine m.acval env φ dep key.key.ds vs₁ := by
                        rw [← hpar.2]; exact hsp₁
                      have hh := hR.frame (i - ctx.hiAt 0) key hk vs₁ hsp₁'
                      rw [show dep - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = dep - 1 - i by omega] at hh
                      have hQ : HoleQ ctx prog dep (dep - 1 - i) (vs₁.length + vs₂.length) := by
                        refine Or.inr ⟨i - ctx.hiAt 0, key, hk, by omega, by omega, ?_⟩
                        rw [← List.length_append, ← hlenv, har]
                      exact ⟨TypeReg.holeAppArgs hR.rich hR.symm hQ hh hvs₂, _,
                        AccOn.holeAppArgs hQ hh hvs₂, SizeOn.const (unitSet_mem_univ w),
                        InvOn.const _ _⟩
                    · rw [if_neg har] at hrun
                      simp [throw, throwThe, MonadExceptOf.throw] at hrun
                  · rw [if_neg hidx] at hrun
                    simp [throw, throwThe, MonadExceptOf.throw] at hrun
                · rw [if_neg hpar] at hrun
                  simp [throw, throwThe, MonadExceptOf.throw] at hrun
            · rw [if_neg hfr'] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`
          rename_i n us hfn
          by_cases hnm : ctx.names.contains n = true
          · rw [if_pos hnm] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [if_neg hnm] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          exact hcont _ ih prog dep kb wt n us st k₁ _ hfn (by simpa using hnm) hv hP hhi
            hfrw hI hCw hwa hgw hR
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

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
      InvOn (MentNH ctx.nP (ctx.hiAt prog.length) d nd) Af) ∧
      PiAccThen w ctx prog Q n (d + 1) nds (R.underBoth A) B
  | _ + 1, _, _, _, _ => False

/-- **The first `n` Π-domains' values are small** at every frame of the
relation, each under the earlier ones. -/
@[expose] def TeleSmall (w : Nat) : Nat → FrameRel V → AnnotTerm → Prop
  | 0, _, _ => True
  | n + 1, R, .pi _ _ A B =>
    (∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ A → x ∈ˢ (univ w : V)) ∧
      TeleSmall w n (R.underBoth A) B
  | _ + 1, _, _ => True

/-- **The telescope walk is accessible**: a successful `nestFields` whose
recursive call is accessible makes every walked field's reading
accessible under the earlier fields (their values small), with its
bound's positions in its output, and leaves the result reading at the
relation under all of them. -/
theorem nestFields_acc
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {w : Nat} {ctx : NestCtx} {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hrec : NestPosAcc m φ w ctx P I rec)
    {prog : List NestHole} {base : Nat} {err : CheckError} :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × ConLeche.BinderMeta)) (res : Expr) (st' : NestState) (D : Nat),
      ConLeche.nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      (∀ k ∈ ks, P k) → D = base + j + nF →
      ctx.hiAt prog.length ≤ base + j → Frame (base + j) cur → I st →
      ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
        CtxOkP m φ (base + j) Δa cur → denoteMeta m.acval env φ (base + j) cur = some ca →
        Graded V Δa ca → HoleRelA m φ ctx prog (base + j) Δa R → TeleSmall w nF R ca →
        I st' ∧ (st'.restart = none →
          PiAccThen w ctx prog (ResultAt m φ ctx.nP (ctx.hiAt prog.length) D res)
            nF (base + j) (nds.map (·.1)) R ca) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' D h _ hD _ hfr hI Δa ca R _ hca _ hR _
    simp only [ConLeche.nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl, rfl⟩ := h
    subst hD
    exact ⟨hI, fun _ => ⟨hR.agree, hca, hfr.1⟩⟩
  | succ nF ih =>
    intro j cur st ks nds res st' D h hks hD hhi hfr hI Δa ca R hC hca hgr hR hsm
    unfold ConLeche.nestFields at h
    split at h
    · rename_i a b mb
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i r₁ hr₁
        obtain ⟨k₁, nd₁, st₁⟩ := r₁
        simp only at h
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
        obtain ⟨hws, hb, hLb⟩ := hfr
        simp only [Expr.WScoped] at hws
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
        have hk₁ : P k₁ := by
          by_cases hrs : st₁.restart.isSome = true
          · rw [if_pos hrs] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact hks k₁ List.mem_cons_self
          · rw [if_neg hrs] at h
            split at h
            · simp at h
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              exact hks k₁ List.mem_cons_self
        obtain ⟨hI₁, hA⟩ :=
          hrec prog (base + j) 0 a st k₁ nd₁ st₁ hr₁ hk₁ hhi ⟨hws.1, hb.1, hLa⟩ hI
            hC.forallE_ty hta hgA hR
        by_cases hrs : st₁.restart.isSome = true
        · rw [if_pos hrs] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, -, rfl⟩ := h
          refine ⟨hI₁, fun hc => ?_⟩
          rw [hc] at hrs; exact nomatch hrs
        rw [if_neg hrs] at h
        have hc₁ : st₁.restart = none := by simpa using hrs
        obtain ⟨-, Af, hAf, hszf, hinvf⟩ := hA hc₁
        split at h
        · simp at h
        · rename_i r₂ hr₂
          obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
          have hfr' := frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd
          rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
          have hR' := hR.underBoth hhi ta (transfer_of_accOn hAf hsm.1)
          obtain ⟨hI₂, hrest⟩ := ih (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ D hr₂
            (fun k hk => hks k (List.mem_cons_of_mem _ hk)) (by omega) (by omega) hfr' hI₁ hCop
            hba hgB
            (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR') hsm.2
          refine ⟨hI₂, fun hc => ⟨⟨Af, hAf, hszf, hinvf⟩, ?_⟩⟩
          have := hrest hc
          rwa [show base + (j + 1) = base + j + 1 by omega] at this
    · simp at h

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

/-- **A member constructor is accessible, from the run**: a successful
`nestMemberCtor` (every field through `nestPos`, then U4 and the result
indices checked) makes every field's reading accessible under the
earlier fields along the accessibility hole relation (the fields' values
small), each bound a set of the level reading only its field's output's
non-hole positions, and the result's indices hole-free — in the
constructor type's own Π-form; the outputs are the fields of the normal
form `tyN` (`closeTelescope`). -/
theorem nestMemberCtor_acc (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat) {w : Nat}
    (hw : w ≠ 0) {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosAcc m φ w ctx P I rec → ContAcc m φ w ctx P I F rec)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : ConLeche.nestMemberCtor (fueledOps .verified F) env ctx nF crest st = .ok (ks, tyN, st'))
    (hks : ∀ k ∈ ks, P k)
    (hfr : Frame (ctx.hiAt 0) crest) (hI : I st)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP m φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRelA m φ ctx [] (ctx.hiAt 0) Δa R) (hsm : TeleSmall w nF R ca) :
    (∃ (nds : List (Expr × ConLeche.BinderMeta)) (cur : Expr) (err : CheckError),
      ConLeche.nestFields (nestPos (fueledOps .verified F) env ctx (ConLeche.whnfWalkFuel crest))
        [] (ctx.hiAt 0) err nF 0 crest st = .ok (ks, nds, cur, st') ∧ st'.restart = none ∧
      tyN = ConLeche.closeTelescope nds (ctx.hiAt 0) cur ∧
      PiAccThen w ctx [] (ResultIdxConst ctx.nP) nF (ctx.hiAt 0) (nds.map (·.1)) R ca) ∧
    I st' := by
  unfold ConLeche.nestMemberCtor at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i r hr
    obtain ⟨ks₁, nds₁, res, st₁⟩ := r
    simp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hnr
    have hc : st₁.restart = none := by simpa using hnr
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · rename_i hok
      split at h
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      have hks₁ : ∀ k ∈ ks₁, P k := by
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ hks
      obtain ⟨hI₁, hsem⟩ := nestFields_acc
        (nestPos_acc hin ctx F hw hcont (ConLeche.whnfWalkFuel crest))
        nF 0 crest st ks₁ nds₁ res st₁ (ctx.hiAt 0 + nF) hr hks₁ (by omega) (by simp) hfr hI
        hC hca hgr hR hsm
      replace hsem := hsem hc
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hks', htyN', hst'⟩ := h
      subst hks' hst'
      refine ⟨⟨nds₁, res, _, hr, hc, htyN'.symm, ?_⟩, hI₁⟩
      refine PiAccThen.mono (fun R' r hres => ?_) nF _ _ R ca hsem
      obtain ⟨hag, hrd, hws⟩ := hres
      have hspine := Expr.mkAppN_getApp res
      rw [← hspine] at hrd hws
      obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hrd
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hhead, hok⟩ := hok
      have hfa' : ∃ i, fa = .bvar i := by
        unfold ConLeche.nestResHead at hhead
        split at hhead
        · rename_i heq
          rw [heq, denoteMeta] at hfa
          exact ⟨_, (Option.some.inj hfa).symm⟩
        · exact nomatch hhead
      obtain ⟨i, rfl⟩ := hfa'
      rw [← List.take_append_drop ctx.nP res.getAppArgs] at hsp
      obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
      refine ⟨i, vs₁ ++ vs₂, rfl, ?_⟩
      have hl₁ : vs₁.length ≤ ctx.nP := by
        rw [← DenoteMetaSpine.length_eq hsp₁, List.length_take]; omega
      intro v hv
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
      have hdrop : (vs₁ ++ vs₂).drop ctx.nP ⊆ vs₂ := by
        intro x hx
        rw [List.drop_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [List.drop_eq_nil_of_le hl₁] at hx; exact nomatch hx
        · exact List.mem_of_mem_drop hx
      have hwsargs := (wScoped_mkAppN _ hws).2
      refine constOn_spine hag (by simp [NestCtx.hiAt]) hsp₂ (fun a ha => ⟨?_, hok a ha⟩) v
        (hdrop hv)
      exact hwsargs a (List.mem_of_mem_drop ha)
    · simp at h

end ConLeche.Model
