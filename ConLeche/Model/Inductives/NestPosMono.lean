module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Semantics.Inductives.HoleMono
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.CtxOkP
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitShift
import ConLeche.Semantics.Frame
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.InferLemmas
import ConLeche.Model.IndPointKit

public section

/-!
# `nestPos`'s run ⇒ monotone in the holes (lane POSPROOF)

Charter item 3: "the theorem is 'returns true ⇒ the operator is
monotone', proved by inversion of that function's run".  This module
inverts the run of `nestPos` (`Kernel/Inductives/Positivity.lean`) at
the pure instantiation `fueledOps .verified F` and assembles the case
lemmas of `Semantics/Inductives/HoleMono.lean`:

* every step begins with `ops.whnf`: its run is a `Red` derivation
  (`whnf_bridge`) and `red_sound` carries the frame, the context, the
  grading and the reading (`RedSem`) — the reduct reads as the term;
* `const`: the reduct mentions no hole, so its reading mentions no hole
  position (`denoteMeta_noBVar_of_nestOcc`) and is the same at related
  frames;
* `pi`: the domain likewise, the body by induction at the opened
  binder (`CtxOk.openS`, `frame_open2`, `WellDenotedV.hoist_pi`);
* `holeApp`: a member hole applied to hole-free arguments;
* a frame's hole (in progress): parameter-blind, hole-free indices;
* `contApp` (`nestCont`): taken as a premise, `ContSem` — the container
  case is its own lemma (it needs the container's lfp clause in hole
  form, `Model/Annot/BlockLfpMono.lean`).

The holes are the free variables `nP ..< hiAt |prog|`: the members, then
one per frame (`nestPos`'s own layout).  A hole at variable `i` reads,
at depth `d`, as the bound position `d - 1 - i` (`holeP`).
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

/-! ## The hole positions -/

/-- The bound positions, at depth `d`, of the hole variables `lo ..< hi`. -/
@[expose] def holeP (d lo hi : Nat) : Nat → Prop :=
  fun j => j < d ∧ lo ≤ d - 1 - j ∧ d - 1 - j < hi

theorem holeP_succ {d lo hi : Nat} : ∀ i, shiftP (holeP d lo hi) i → holeP (d + 1) lo hi i
  | 0, h => h.elim
  | i + 1, h => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, ?_⟩ <;> omega

/-! ## Occurrences and readings -/

/-- Instantiating a bound variable by a non-hole variable changes no
occurrence. -/
theorem nestOcc_instantiate1_fvar {names : List Name} {lo hi d : Nat}
    (hd : ¬ (lo ≤ d ∧ d < hi)) (ty : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).nestOcc names lo hi = e.nestOcc names lo hi := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1]
    split
    · simp [ConLeche.Expr.nestOcc, hd]
    · split <;> simp [ConLeche.Expr.nestOcc]
  | fvar i t _ => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihv, ihb]
  | proj s i e ih =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, ih]

/-- A reading whose erasure is closed mentions no position at all. -/
theorem noBVar_of_closed {ea : AnnotTerm} (h : Term.bvarsBelow 0 ea.erase) (P : Nat → Prop) :
    NoBVar P ea :=
  NoBVar_of_bvarsBelow h fun _ _ => Nat.zero_le _

theorem noBVar_projAV {P : Nat → Prop} : ∀ (k : Nat) {e : AnnotTerm}, NoBVar P e →
    NoBVar P (projAV k e)
  | 0, _, h => h
  | k + 1, _, h => noBVar_projAV (P := P) k (e := .snd _) h

/-- **A term mentioning no hole reads without the holes' positions.** -/
theorem denoteMeta_noBVar_of_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm}, Expr.WScoped d e → hi ≤ d →
      e.nestOcc names lo hi = false →
      denoteMeta m.acval env φ d e = some ea → NoBVar (holeP d lo hi) ea := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    cases h; trivial
  | case2 d idx ty =>
    intro ea hws _ hocc h
    rw [denoteMeta] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, decide_eq_false_iff_not] at hocc
    show ¬ holeP d lo hi (d - 1 - idx)
    rintro ⟨-, h2, h3⟩
    exact hocc ⟨by omega, by omega⟩
  | case3 d n us ci hf hlen =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    cases h
    exact noBVar_of_closed (m.cval_closedL _ _) _
  | case4 d n us ci hf hlen =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ea hws hd hocc h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    refine ⟨ihty hws.1 hd hocc.1 hta, ?_⟩
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hocc' : (body.instantiate1 (.fvar d ty)).nestOcc names lo hi = false := by
      rw [nestOcc_instantiate1_fvar (by omega) ty body 0]; exact hocc.2
    exact NoBVar.mono holeP_succ (ihbody hws' (by omega) hocc' hba)
  | case7 d ty body mb ihty ihbody =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hta : denoteMeta m.acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta m.acval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    refine ⟨ihty hws.1 hd hocc.1 hta, ?_⟩
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hocc' : (body.instantiate1 (.fvar d ty)).nestOcc names lo hi = false := by
      rw [nestOcc_instantiate1_fvar (by omega) ty body 0]; exact hocc.2
    exact NoBVar.mono holeP_succ (ihbody hws' (by omega) hocc' hba)
  | case8 d fe a ihf iha =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hfa : denoteMeta m.acval env φ d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteMeta m.acval env φ d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    exact ⟨ihf hws.1 hd hocc.1 hfa, iha hws.2 hd hocc.2 haa⟩
  | case9 d ty val body =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hea : denoteMeta m.acval env φ d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc] at hocc
    have hsub := ihe hws hd hocc hea
    replace h : (match env.findProj? sn i with
        | some entry => some (projAV (i + entry.off) ea')
        | none => AnnotTerm.projPair? i ea') = some ea := h
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at h
      cases h
      exact noBVar_projAV _ hsub
    | none =>
      rw [hfp] at h
      rcases i with _ | _ | i
      · cases h; exact hsub
      · cases h; exact hsub
      · exact nomatch h
  | case11 d k hsup =>
    intro ea _ _ _ h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.natVal k)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    exact noBVar_of_closed (denote_bvarsBelow m.cval_closedL 0 _ (by simp [Expr.WScoped]) rfl
      (denoteMeta_erase m.acval_erase 0 _ h0)) _
  | case12 d k hsup =>
    intro ea _ _ _ h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea _ _ _ h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.strVal s)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    exact noBVar_of_closed (denote_bvarsBelow m.cval_closedL 0 _ (by simp [Expr.WScoped]) rfl
      (denoteMeta_erase m.acval_erase 0 _ h0)) _
  | case14 d s hsup =>
    intro ea _ _ _ h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea _ _ _ h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-! ## Spines -/

theorem wScoped_mkAppN {d : Nat} :
    ∀ (as : List Expr) {f : Expr}, Expr.WScoped d (Expr.mkAppN f as) →
      Expr.WScoped d f ∧ ∀ a ∈ as, Expr.WScoped d a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hfa, has⟩ := wScoped_mkAppN as (f := .app f a) h
    simp only [Expr.WScoped] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfa.2
    · exact has x hx

theorem DenoteMetaSpine.length_eq {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [DenoteMetaSpine.length_eq h]

theorem DenoteMetaSpine.split {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ (as : List Expr) {bs : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as ++ bs) vs →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ DenoteMetaSpine acval env φ d as vs₁ ∧
        DenoteMetaSpine acval env φ d bs vs₂
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | a :: as, bs, _, .cons ha h => by
    obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := DenoteMetaSpine.split as h
    exact ⟨_ :: vs₁, vs₂, rfl, .cons ha h₁, h₂⟩

/-- Hole-free arguments read hole-free. -/
theorem constOn_spine {names : List Name} {lo hi d : Nat} {R : FrameRel V}
    (hR : R.AgreesOff (holeP d lo hi)) (hd : hi ≤ d) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine m.acval env φ d as vs →
      (∀ a ∈ as, Expr.WScoped d a ∧ a.nestOcc names lo hi = false) →
      ∀ v ∈ vs, ConstOn R v
  | _, _, .nil, _ => fun _ hv => nomatch hv
  | a :: _, _ :: _, .cons ha h, hall => fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨hw, ho⟩ := hall a (List.mem_cons_self ..)
      exact ConstOn.of_noBVar hR (denoteMeta_noBVar_of_nestOcc d a hw hd ho ha)
    · exact constOn_spine hR hd h (fun b hb => hall b (List.mem_cons_of_mem _ hb)) x hx

/-! ## The relation the run is proved along -/

/-- A spine of `d`-scoped terms read one level deeper is its depth-`d`
reading, lifted. -/
theorem DenoteMetaSpine.weaken_top {d : Nat} :
    ∀ {as : List Expr} {vs' : List AnnotTerm}, (∀ x ∈ as, Expr.WScoped d x) →
      DenoteMetaSpine m.acval env φ (d + 1) as vs' →
      ∃ vs, DenoteMetaSpine m.acval env φ d as vs ∧ vs' = vs.map (AnnotTerm.liftN 1 · 0)
  | _, _, _, .nil => ⟨[], .nil, rfl⟩
  | a :: as, _ :: _, hws, .cons ha h => by
    obtain ⟨vs, hvs, rfl⟩ :=
      DenoteMetaSpine.weaken_top (fun x hx => hws x (List.mem_cons_of_mem _ hx)) h
    rw [denoteMeta_weaken_top m.acval_closed (hws a List.mem_cons_self)] at ha
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨v :: vs, .cons hv hvs, rfl⟩

/-- **The hole relation** at depth `d` under the frames `prog`: related
frames satisfy the context, agree off the hole positions, the member
holes grow (at their full arity), and every frame's hole grows at its
instantiation's own parameters (`HoleOnArgs`: the key's parameter terms,
read at the depth, then any indices). -/
structure HoleRel (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  member : ∀ t, t < ctx.names.length →
    HoleOn R (d - 1 - (ctx.nP + t)) (ctx.nP + ctx.nIdxs.getD t 0)
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ dsa,
    DenoteMetaSpine m.acval env φ d hk.key.ds dsa → ∀ ni,
    HoleOnArgs R (d - 1 - (ctx.hiAt 0 + i)) dsa ni
  /-- the frames' parameter terms are scoped below the frames' holes (the
  kernel checks `fvarB ≤ hiAt` at each frame's entry) -/
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

/-- **Under a positive binder** (a hole-free domain, or an earlier field)
the relation is the same one level deeper. -/
theorem HoleRel.under {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRel m φ ctx prog d Δa R) (hd : ctx.hiAt prog.length ≤ d)
    {ta : AnnotTerm} (hA : MonoOn R ta) :
    HoleRel m φ ctx prog (d + 1) (ta :: Δa) (R.under ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 (hA ρ ρ' hR x hx)⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.under ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  member := by
    intro t ht
    have hlt : ctx.nP + t < d := by
      simp only [NestCtx.hiAt] at hd; omega
    rw [show d + 1 - 1 - (ctx.nP + t) = d - 1 - (ctx.nP + t) + 1 by omega]
    exact (h.member t ht).under ta
  frame := by
    intro i key hk dsa' hsp ni
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < d := by
      simp only [NestCtx.hiAt] at hd ⊢; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped i key hk x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + i) = d - 1 - (ctx.hiAt 0 + i) + 1 by omega]
    exact (h.frame i key hk dsa hdsa ni).under ta
  dsScoped := h.dsScoped

/-! ## The theorem -/

/-- A run of the positivity function (or of its recursive call one fuel
lower) which keeps the state invariant `I` (lane CONTSEM: the cache's —
every cached instantiation the run may hit without walking is positive),
also when it ends in a restart request, and whose reading is proved
positive when it does not. -/
@[expose] def NestPosSem (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') → P k →
    ctx.hiAt prog.length ≤ dep → Frame dep e → I st →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      HoleRel m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none → MonoOn R ea)

/-- **The container case**, as the premise the theorem takes: a
successful `nestCont` at a container reduct whose recursive call is
positive makes the reduct's reading positive. -/
@[expose] def ContSem (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop) (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (w : Expr) (n : Name) (us : List Level)
    (st : NestState) (k : NestFieldKind) (st' : NestState),
    w.getAppFn = .const n us → ctx.names.contains n = false →
    nestCont ctx (fueledOps .verified F) env rec prog kb n us w.getAppArgs st = .ok (k, st') →
    P k →
    ctx.hiAt prog.length ≤ dep → Frame dep w → I st →
    ∀ {Δa : List AnnotTerm} {wa : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa w → denoteMeta m.acval env φ dep w = some wa → Graded V Δa wa →
      HoleRel m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none → MonoOn R wa)

/-- **THE THEOREM (non-container cases): a run of `nestPos` is positive.**
If the positivity function returns (at the pure verified instantiation,
at any fuel), leaving no restart request pending, then
the reading of its input is monotone along every hole relation — at
every valuation of the other variables satisfying the context.  By
inversion of the run: the whnf step by `red_sound`, then `const`,
`pi` (by induction), `holeApp` and a frame's hole; the container case
is the premise `ContSem`, given the theorem one fuel lower. -/
theorem nestPos_sem (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat)
    {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosSem m φ ctx P I rec → ContSem m φ ctx P I F rec) :
    ∀ fuel, NestPosSem m φ ctx P I (nestPos (fueledOps .verified F) env ctx fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro prog dep kb e st k nf st' hrun hP hhi hfr hI Δa ea R hC hea hgr hR
    rw [nestPos] at hrun
    cases hw : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw' : (fueledOps .verified F).whnf env dep e = .error err := hw
      simp [hw', bind, Except.bind] at hrun
    | ok w =>
      have hw' : (fueledOps .verified F).whnf env dep e = .ok w := hw
      simp only [hw', bind, Except.bind] at hrun
      obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
        red_sound hin (ConLeche.Rules.whnf_bridge hw) hfr hC.toCtxOk hea hgr
      have hCw : CtxOkP m φ dep Δa w := hC.of_subset hsub
      suffices hw2 : I st' ∧ (st'.restart = none → MonoOn R wa) from
        ⟨hw2.1, fun hc => MonoOn.of_eqOn (Q := Sat V Δa) hR.dom (fun ρ hρ => heq ρ hρ) (hw2.2 hc)⟩
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · refine ⟨?_, fun _ => (ConstOn.of_noBVar hR.agree
          (denoteMeta_noBVar_of_nestOcc dep w hfrw.1 hhi hocc hwa)).monoOn⟩
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
        have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree
          (denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi (by simpa using ha) hta)
        obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
        have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -, rfl⟩ := hrun
        obtain ⟨hI', hB⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv hP (by omega)
          (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hI hCop hba hgB (hR.under hhi hA.monoOn)
        exact ⟨hI', fun hc => MonoOn.pi 0 _ hA (hB hc)⟩
      · -- a head applied to arguments
        rename_i hnotpi
        have hspine := Expr.mkAppN_getApp w
        split at hrun
        · rename_i i ty hfn
          rw [hfn] at hspine
          rw [← hspine] at hwa
          obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
          rw [denoteMeta_fvar] at hfa
          cases hfa
          have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
            have h0 := hfrw.1
            rw [← hspine] at h0
            exact (wScoped_mkAppN _ h0).2
          have hlenv := DenoteMetaSpine.length_eq hsp
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · -- `holeApp`
            rw [if_pos hmem] at hrun
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
            by_cases hc : (w.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                List.take ctx.nP w.getAppArgs == ctx.params &&
                w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x)
                = true
            · rw [if_pos hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              obtain ⟨⟨hlen, -⟩, hfree⟩ := hc
              have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
              have ht : i - ctx.nP < ctx.names.length := by
                simp only [NestCtx.hiAt] at hmem; omega
              have hh := hR.member (i - ctx.nP) ht
              rw [show dep - 1 - (ctx.nP + (i - ctx.nP)) = dep - 1 - i by omega,
                ← hlen, hlenv] at hh
              exact MonoOn.holeApp hh hvs
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
                by_cases hpar : (decide (key.key.ds.length ≤ w.getAppArgs.length) &&
                    (List.take key.key.ds.length w.getAppArgs == key.key.ds)) = true
                · rw [if_pos hpar] at hrun
                  by_cases hidx : ((w.getAppArgs.drop key.key.ds.length).all fun x =>
                      !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) = true
                  · rw [if_pos hidx] at hrun
                    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                    refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
                    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpar
                    simp only [List.all_eq_true, Bool.not_eq_true'] at hidx
                    rw [← List.take_append_drop key.key.ds.length w.getAppArgs] at hsp
                    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
                    have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
                      ⟨hwsargs a (List.mem_of_mem_drop ha), by simpa using hidx a ha⟩
                    have hsp₁' : DenoteMetaSpine m.acval env φ dep key.key.ds vs₁ := by
                      rw [← hpar.2]; exact hsp₁
                    have hh := hR.frame (i - ctx.hiAt 0) key hk vs₁ hsp₁' vs₂.length
                    rw [show dep - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = dep - 1 - i by omega] at hh
                    exact MonoOn.holeAppArgs hh hvs₂
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
          obtain ⟨rfl, -, rfl⟩ := hrun
          exact hcont _ ih prog dep kb w n us st k₁ _ hfn (by simpa using hnm) hv hP hhi
            hfrw hI hCw hwa hgw hR
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-! ## A constructor's field telescope -/

/-- **The first `n` Π-domains of a reading positive**, each under the
earlier ones, and `P` of the relation and the reading below them. -/
@[expose] def PiPosThen (P : FrameRel V → AnnotTerm → Prop) :
    Nat → FrameRel V → AnnotTerm → Prop
  | 0, R, r => P R r
  | n + 1, R, .pi _ _ A B => MonoOn R A ∧ PiPosThen P n (R.under A) B
  | _ + 1, _, _ => False

/-- What a telescope walk leaves at its result `res`, at depth `D`: the
relation still agrees off the hole positions, and the result reads. -/
@[expose] def ResultAt (m : EnvModel V env) (φ : Name → Nat) (lo hi D : Nat) (res : Expr)
    (R : FrameRel V) (r : AnnotTerm) : Prop :=
  R.AgreesOff (holeP D lo hi) ∧ denoteMeta m.acval env φ D res = some r ∧ Expr.WScoped D res

/-- **The telescope walk is positive**: a successful `nestFields` whose
recursive call is positive makes every walked field's reading positive
under the earlier fields, and leaves the result reading at the relation
under all of them. -/
theorem nestFields_sem
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {ctx : NestCtx} {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hrec : NestPosSem m φ ctx P I rec)
    {prog : List NestHole} {base : Nat} {err : CheckError} :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × ConLeche.BinderMeta)) (res : Expr) (st' : NestState) (D : Nat),
      ConLeche.nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      (∀ k ∈ ks, P k) → D = base + j + nF →
      ctx.hiAt prog.length ≤ base + j → Frame (base + j) cur → I st →
      ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
        CtxOkP m φ (base + j) Δa cur → denoteMeta m.acval env φ (base + j) cur = some ca →
        Graded V Δa ca → HoleRel m φ ctx prog (base + j) Δa R →
        I st' ∧ (st'.restart = none →
          PiPosThen (ResultAt m φ ctx.nP (ctx.hiAt prog.length) D res) nF R ca) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' D h _ hD _ hfr hI Δa ca R _ hca _ hR
    simp only [ConLeche.nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, rfl⟩ := h
    subst hD
    exact ⟨hI, fun _ => ⟨hR.agree, hca, hfr.1⟩⟩
  | succ nF ih =>
    intro j cur st ks nds res st' D h hks hD hhi hfr hI Δa ca R hC hca hgr hR
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
        split at h
        · simp at h
        · rename_i r₂ hr₂
          obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl, rfl⟩ := h
          have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
          have hfr' := frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd
          rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
          obtain ⟨hI₂, hrest⟩ := ih (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ D hr₂
            (fun k hk => hks k (List.mem_cons_of_mem _ hk)) (by omega) (by omega) hfr' hI₁ hCop
            hba hgB
            (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR.under hhi (hA hc₁))
          exact ⟨hI₂, fun hc => ⟨hA hc₁, hrest hc⟩⟩
    · simp at h

theorem PiPosThen.mono {P Q : FrameRel V → AnnotTerm → Prop}
    (hPQ : ∀ R r, P R r → Q R r) :
    ∀ (n : Nat) (R : FrameRel V) (r : AnnotTerm), PiPosThen P n R r → PiPosThen Q n R r
  | 0, R, r, h => hPQ R r h
  | n + 1, R, .pi _ _ A B, h => ⟨h.1, PiPosThen.mono hPQ n (R.under A) B h.2⟩
  | _ + 1, _, .bvar _, h | _ + 1, _, .sort _, h | _ + 1, _, .const _ _, h
  | _ + 1, _, .app _ _, h | _ + 1, _, .lam _ _ _, h | _ + 1, _, .eqE _ _, h
  | _ + 1, _, .fst _, h | _ + 1, _, .snd _, h | _ + 1, _, .prf, h => h.elim

/-- A Π-tower positive along a relation is positive field by field, and
its body satisfies the predicate under the fields. -/
theorem piPosThen_mkPisAV {P : FrameRel V → AnnotTerm → Prop} :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (R : FrameRel V) (b : AnnotTerm),
      PiPosThen P ab.length R (mkPisAV ab b) →
      TeleMonoOn R (ab.map (·.2.2)) ∧ P (R.underTele (ab.map (·.2.2))) b
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: ab, R, b, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ht, hp⟩ := piPosThen_mkPisAV ab _ b h2
    exact ⟨⟨h1, ht⟩, hp⟩

/-- The number of applications on a spine. -/
def spineLenAV : AnnotTerm → Nat
  | .app f _ => spineLenAV f + 1
  | _ => 0

theorem spineLenAV_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    spineLenAV (AnnotTerm.mkAppN f as) = spineLenAV f + as.length
  | [], _ => rfl
  | a :: as, f => by
    rw [ConLeche.Semantics.AnnotTerm.mkAppN_cons, spineLenAV_mkAppN as]
    simp [spineLenAV]; omega

/-- Spines headed by a variable are equal only at equal variables and
arguments. -/
theorem mkAppN_bvar_inj {i j : Nat} {as bs : List AnnotTerm}
    (h : AnnotTerm.mkAppN (.bvar i) as = AnnotTerm.mkAppN (.bvar j) bs) : i = j ∧ as = bs := by
  have hl := congrArg spineLenAV h
  rw [spineLenAV_mkAppN, spineLenAV_mkAppN] at hl
  simp only [spineLenAV, Nat.zero_add] at hl
  obtain ⟨h1, h2⟩ := AnnotTerm.mkAppN_inj h hl
  injection h1 with h1
  exact ⟨h1, h2⟩

/-- **A member constructor's result**: its reading is a spine whose
arguments after the parameters (the result's indices) are hole-free. -/
@[expose] def ResultIdxConst (nP : Nat) (R : FrameRel V) (r : AnnotTerm) : Prop :=
  ∃ i vs, r = AnnotTerm.mkAppN (.bvar i) vs ∧ ∀ v ∈ vs.drop nP, ConstOn R v

/-- **THE CONSUMER'S PREMISE, from the run: a member constructor is
positive.**  A successful `nestMemberCtor` (every field through
`nestPos`, then the result indices checked) makes every
field's reading positive under the earlier fields along the hole
relation, and the result's indices hole-free — the `CtorPos` of
`Model/Annot/BlockLfpMono.lean`, in the constructor type's own Π-form.
The typing premises (`Frame`, `CtxOk`, `Graded` of the member-abstracted
constructor type at the holes' context) are the abstract typing pass's
(E2E-DESIGN's U2). -/
theorem nestMemberCtor_sem (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat)
    {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosSem m φ ctx P I rec → ContSem m φ ctx P I F rec)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : ConLeche.nestMemberCtor (fueledOps .verified F) env ctx nF crest st = .ok (ks, tyN, st'))
    (hks : ∀ k ∈ ks, P k)
    (hfr : Frame (ctx.hiAt 0) crest) (hI : I st)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP m φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel m φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca ∧ I st' := by
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
      have hks₁ : ∀ k ∈ ks₁, P k := by
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ hks
      obtain ⟨hI₁, hsem⟩ := nestFields_sem (nestPos_sem hin ctx F hcont (whnfWalkFuel crest))
        nF 0 crest st ks₁ nds₁ res st₁ (ctx.hiAt 0 + nF) hr hks₁ (by omega) (by simp) hfr hI
        hC hca hgr hR
      replace hsem := hsem hc
      refine ⟨?_, by
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2.2]; exact hI₁⟩
      refine PiPosThen.mono (fun R' r hres => ?_) nF R ca hsem
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

/-! ### Runs without container kinds

A run whose kinds are all `flat` (hole-free, a member, a member under
binders) never took the container case: `nestCont` succeeds only with
`.nested`/`.inProgress`.  So the container premise is vacuous at the
kind predicate `flat`, and the section law holds without `ContSem`. -/

-- the throw-branch closers are tried at every split; each is unused somewhere
set_option linter.unusedSimpArgs false in

theorem nestContNew_not_flat {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {ctx : NestCtx} {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {old : Option Nat} {st : NestState} {k : NestFieldKind}
    {st' : NestState}
    (h : ConLeche.nestContNew ctx ops env' rec prog kb n us ds nPc old st = .ok (k, st')) :
    k.flat = false := by
  unfold ConLeche.nestContNew at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first
    | (split at h)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h;
        rfl)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | (simp at h))

theorem nestContKey_not_flat {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {ctx : NestCtx} {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : ConLeche.nestContKey ctx ops env' rec prog kb n us ds nPc st = .ok (k, st')) :
    k.flat = false := by
  unfold ConLeche.nestContKey at h
  split at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; rfl
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; rfl
      · exact nestContNew_not_flat h
    · exact nestContNew_not_flat h

set_option linter.unusedSimpArgs false in
theorem nestCont_not_flat {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {ctx : NestCtx} {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {args : List Expr} {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : ConLeche.nestCont ctx ops env' rec prog kb n us args st = .ok (k, st')) :
    k.flat = false := by
  unfold ConLeche.nestCont at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first
    | (exact nestContKey_not_flat h)
    | (split at h)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | (simp at h))

/-- The container premise at the kind predicate `flat`: vacuous. -/
theorem contSem_flat {I : NestState → Prop} (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)) :
    ContSem m φ ctx (fun k => k.flat = true) I F rec := by
  intro prog dep kb w n us st k st' _ _ hrun hP
  rw [nestCont_not_flat hrun] at hP
  exact absurd hP Bool.false_ne_true

end ConLeche.Model
