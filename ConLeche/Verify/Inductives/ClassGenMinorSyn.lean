module

public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Verify.Abstract
import ConLeche.Verify.Leaves
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestCallSyn

public section

/-!
# A generated minor premise, as syntax (G1-syn, `hminor`)

Check 6 of the class check generates, per minor slot `s` of class `c`
and constructor `x`, the minor premise's type

    minorTy c x (nP + s) = Π (f⃗ : fields) (ih⃗ : Π a⃗, motive_t e⃗ (f a⃗)), motive_c es (C p⃗ f⃗)

(`ClassGen.minorTy`, `Kernel/Inductives/ClassCheck.lean`) and places it
in the shared prefix at position `nP + s` (`ClassGen.prefixBinders`).
What the model's reading of it (`Model/Inductives/ClassGenMinor.lean`)
needs, as pure syntax:

* **the spelled-out shape** (`ClassGen.minorTy_spec`): a telescope over
  the fields and the `ih`s, closed at `nP + s`, whose conclusion is the
  class's motive variable applied to a nonempty spine, and whose `ih`
  domains are telescopes over the callee's motive variable applied to a
  nonempty spine;
* **the `ih` domains name no `ih` variable** (`fvarsBelow (nP + s + nF)`):
  an `ih`'s own telescope is opened at `nP + s + nF + l` and closed again
  there, so what is left names only the parameters, the motives and the
  fields — the gap `[nP + s + nF, nP + s + nF + l)` is never used
  (`Expr.FvGap`, a shallow "no variable in the gap" predicate that every
  step of the construction keeps);
* **annotation of a telescope over a non-plain body**
  (`annotateCore_closeTelescope_gen`): the annotated telescope is, up to
  erasure, the telescope of the annotated domains over the annotated
  body, each piece the annotation of (an erasure of) the raw one at its
  own depth, and scoped there;
* **annotation of a variable applied to a spine** keeps the variable and
  the spine's length (`annotateCore_mkAppN_fvar`).
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## No variable in a gap -/

/-- Every (shallowly reachable) free variable is below `lo` or at least
`i`: nothing in the gap `[lo, i)`. -/
@[expose] def Expr.FvGap (lo i : Nat) : Expr → Prop
  | .bvar _ | .sort _ | .const .. | .lit _ => True
  | .fvar j _ => j < lo ∨ i ≤ j
  | .app f a => FvGap lo i f ∧ FvGap lo i a
  | .lam ty body _ | .forallE ty body _ => FvGap lo i ty ∧ FvGap lo i body
  | .letE ty val body => FvGap lo i ty ∧ FvGap lo i val ∧ FvGap lo i body
  | .proj _ _ e => FvGap lo i e

theorem Expr.FvGap.of_fvarsBelow {lo i : Nat} :
    ∀ {e : Expr}, Expr.fvarsBelow lo e → Expr.FvGap lo i e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.FvGap]

theorem Expr.FvGap.fvarsBelow {lo i : Nat} :
    ∀ {e : Expr}, Expr.FvGap lo i e → Expr.fvarsBelow i e → Expr.fvarsBelow lo e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.FvGap] <;> omega

theorem Expr.FvGap.instantiate1 {lo i : Nat} {v : Expr} (hv : Expr.FvGap lo i v) :
    ∀ {e : Expr} (k : Nat), Expr.FvGap lo i e → Expr.FvGap lo i (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar j =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | app f a ihf iha =>
    intro k h
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v' b iht ihv ihb =>
    intro k h
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s j e ih =>
    intro k h
    exact ih k h
  | fvar j ty => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h

theorem Expr.FvGap.abstract1 {lo i D : Nat} :
    ∀ {e : Expr} (k : Nat), Expr.FvGap lo i e → Expr.FvGap lo i (e.abstract1 D k) := by
  intro e
  induction e with
  | fvar j ty =>
    intro k h
    simp only [Expr.abstract1]
    split
    · trivial
    · exact h
  | app f a ihf iha =>
    intro k h
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v' b iht ihv ihb =>
    intro k h
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s j e ih =>
    intro k h
    exact ih k h
  | bvar j => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h

theorem Expr.FvGap.mkAppN {lo i : Nat} :
    ∀ {as : List Expr} {f : Expr}, Expr.FvGap lo i f → (∀ a ∈ as, Expr.FvGap lo i a) →
      Expr.FvGap lo i (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha => by
    simp only [Expr.mkAppN]
    exact Expr.FvGap.mkAppN ⟨hf, ha a List.mem_cons_self⟩
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

theorem Expr.FvGap.getAppArgs {lo i : Nat} :
    ∀ {e : Expr}, Expr.FvGap lo i e → ∀ a ∈ e.getAppArgs, Expr.FvGap lo i a
  | .app f a, h, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Expr.FvGap.getAppArgs h.1 x hx
    · exact h.2
  | .bvar _, _, x, hx | .fvar _ _, _, x, hx | .sort _, _, x, hx | .const _ _, _, x, hx
  | .lam _ _ _, _, x, hx | .forallE _ _ _, _, x, hx | .letE _ _ _, _, x, hx
  | .lit _, _, x, hx | .proj _ _ _, _, x, hx => by simp [Expr.getAppArgs] at hx

/-- Opening at or above the gap's top keeps it. -/
theorem Expr.FvGap.openPis {lo i : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars n e d = some (fvs, body) → i ≤ d → Expr.FvGap lo i e →
      Expr.FvGap lo i body ∧ ∀ x ∈ fvs, Expr.FvGap lo i x ∧ Expr.FvGap lo i x.fvarTypeD
  | 0, e, d, fvs, body, h, _, he => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨he, fun x hx => nomatch hx⟩
  | n + 1, e, d, fvs, body, h, hid, he => by
    match e, h with
    | .forallE dom b mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' o' hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hx : Expr.FvGap lo i (.fvar d dom) := Or.inr hid
        obtain ⟨hb, hfv⟩ := Expr.FvGap.openPis n hop (by omega)
          (Expr.FvGap.instantiate1 hx 0 he.2)
        refine ⟨hb, fun x hxm => ?_⟩
        rcases List.mem_cons.mp hxm with rfl | hxm
        · exact ⟨hx, he.1⟩
        · exact hfv x hxm
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

theorem Expr.FvGap.closeTelescope {lo i : Nat} :
    ∀ (nds : List (Expr × BinderMeta)) (j : Nat) {body : Expr},
      (∀ nd ∈ nds, Expr.FvGap lo i nd.1) → Expr.FvGap lo i body →
      Expr.FvGap lo i (ConLeche.closeTelescope nds j body)
  | [], _, _, _, hb => hb
  | (dom, bm) :: nds, j, body, hn, hb => by
    simp only [ConLeche.closeTelescope]
    exact ⟨hn _ List.mem_cons_self, Expr.FvGap.abstract1 0
      (Expr.FvGap.closeTelescope nds (j + 1) (fun nd hnd => hn nd (List.mem_cons_of_mem _ hnd)) hb)⟩

/-! ## Annotating a telescope over a non-plain body -/

/-- **Annotating (an erasure of) a closed telescope**, over ANY body:
the result is, up to erasure, the telescope of the annotated domains
over the annotated body — each annotated piece the annotation of an
erasure of the raw one, at its own depth, and scoped there.
(`annotateCore_closeTelescope` is the plain-body case, where the body is
left alone.) -/
theorem annotateCore_closeTelescope_gen {env : Env} :
    ∀ (nds : List (Expr × BinderMeta)) {F d : Nat} {B E e' : Expr},
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → B.looseBVarsBounded 0 = true →
      Expr.ErasedEq E (closeTelescope nds d B) → WScoped d E →
      annotateCore mode env F d E = .ok e' →
      ∃ (nds' : List (Expr × BinderMeta)) (B' : Expr),
        nds'.length = nds.length ∧ Expr.ErasedEq e' (closeTelescope nds' d B') ∧
        (∃ (B₀ : Expr) (F' : Nat), Expr.ErasedEq B₀ B ∧ WScoped (d + nds.length) B₀ ∧
          annotateCore mode env F' (d + nds.length) B₀ = .ok B') ∧
        ∀ (k : Nat) (nd' : Expr × BinderMeta), nds'[k]? = some nd' →
          ∃ (X : Expr) (F' : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd ∧
            Expr.ErasedEq X nd.1 ∧ WScoped (d + k) X ∧
            annotateCore mode env F' (d + k) X = .ok nd'.1
  | [], F, d, B, E, e', _, _, he, hw, h => by
    simp only [closeTelescope] at he
    exact ⟨[], e', rfl, by simpa [closeTelescope] using Expr.ErasedEq.rfl e',
      ⟨E, F, he, by simpa using hw, by simpa using h⟩, fun k nd' hk => nomatch hk⟩
  | (dom, bm) :: nds, F, d, B, E, e', hcl, hb, he, hw, h => by
    simp only [closeTelescope] at he
    match E, he with
    | .forallE A b m, he =>
      obtain ⟨rfl, hA, hbE⟩ := he
      simp only [WScoped] at hw
      cases F with
      | zero => simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
      | succ F =>
        obtain ⟨A', b', pw, hA', hb', rfl⟩ := annotateCore_forallE_inv h
        have hwA' : WScoped d A' := annotateCore_WScoped F A hA' hw.1
        have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
          fun p hp => hcl p (List.mem_cons_of_mem _ hp)
        have hC := closeTelescope_bounded nds (d + 1) B hcl' hb
        have hE : Expr.ErasedEq (b.instantiate1 (.fvar d A')) (closeTelescope nds (d + 1) B) :=
          Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d A') rfl)
            (Expr.erasedEq_abstract1_instantiate1 _ 0 hC)
        obtain ⟨nds', B', hl, he', ⟨B₀, F₀, hB₀, hwB₀, hannB⟩, hdoms⟩ :=
          annotateCore_closeTelescope_gen nds hcl' hb hE (hwA'.instantiate1 0 hw.2) hb'
        refine ⟨(A', ⟨pw⟩) :: nds', B', by simp [hl], ?_, ⟨B₀, F₀, hB₀, ?_, ?_⟩, ?_⟩
        · simp only [closeTelescope]
          exact ⟨rfl, Expr.ErasedEq.rfl _, Expr.ErasedEq.abstract1 0 he'⟩
        · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
          exact hwB₀
        · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
          exact hannB
        · intro k nd' hk
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            exact ⟨A, F, (dom, m), rfl, hA, by simpa using hw.1, by simpa using hA'⟩
          | succ k =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨X, F', nd, hnd, hX, hwX, hann⟩ := hdoms k nd' hk
            exact ⟨X, F', nd, by simpa using hnd, hX,
              by rw [show d + (k + 1) = d + 1 + k by omega]; exact hwX,
              by rw [show d + (k + 1) = d + 1 + k by omega]; exact hann⟩

/-- **Annotating an application spine** annotates its head (at a smaller
fuel) and keeps the spine's length. -/
theorem annotateCore_mkAppN_inv {env : Env} :
    ∀ (as : List Expr) {F d : Nat} {f r : Expr},
      annotateCore mode env F d (Expr.mkAppN f as) = .ok r →
      ∃ (F' : Nat) (f' : Expr) (as' : List Expr), annotateCore mode env F' d f = .ok f' ∧
        r = Expr.mkAppN f' as' ∧ as'.length = as.length
  | [], F, d, f, r, h => ⟨F, r, [], h, rfl, rfl⟩
  | a :: as, F, d, f, r, h => by
    obtain ⟨F₁, g, as', hg, rfl, hl⟩ := annotateCore_mkAppN_inv as (f := .app f a) h
    cases F₁ with
    | zero => simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at hg
    | succ F₁ =>
      obtain ⟨f', a', hf, -, rfl⟩ := annotateCore_app_inv hg
      exact ⟨F₁, f', a' :: as', hf, rfl, by simp [hl]⟩

/-- **A variable applied to a spine, annotated**: the same variable
applied to a spine of the same length. -/
theorem annotateCore_mkAppN_fvar {env : Env} {F d i : Nat} {T : Expr} {as : List Expr}
    {r : Expr} (h : annotateCore mode env F d (Expr.mkAppN (.fvar i T) as) = .ok r) :
    ∃ as' : List Expr, r = Expr.mkAppN (.fvar i T) as' ∧ as'.length = as.length := by
  obtain ⟨F', f', as', hf, rfl, hl⟩ := annotateCore_mkAppN_inv as h
  obtain rfl := annotateCore_plain F' (e := .fvar i T) trivial hf
  exact ⟨as', rfl, hl⟩

/-! ## A tighter scope survives annotation -/

/-- A term scoped at `d` whose closure leaves all lie below `lo` is
scoped at `lo`. -/
theorem WScoped.of_leaves_below {lo : Nat} :
    ∀ {e : Expr} {d : Nat}, WScoped d e → (∀ l ∈ e.fvarLeaves, l.1 < lo) → WScoped lo e := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨hl (i, ty) (by simp [fvarLeaves]), hw.2⟩
  | app f a ihf iha =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨ihf hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      iha hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | lam ty b m iht ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | forallE ty b m iht ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | letE ty v b iht ihv ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihv hw.2.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | proj s i x ih =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ih hw fun l h => hl l (by simpa [fvarLeaves] using h)
  | _ => intro _ _ _; simp [WScoped]

/-- **Annotation keeps a tighter scope**: annotating at `d` a term scoped
at `lo ≤ d` gives a term scoped at `lo` (annotation only shrinks the
leaf closure). -/
theorem annotateCore_WScoped_below {env : Env} {F d lo : Nat} {e e' : Expr}
    (h : annotateCore mode env F d e = .ok e') (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hlo : WScoped lo e) : WScoped lo e' :=
  WScoped.of_leaves_below (annotateCore_WScoped F e h hw) fun l hl =>
    (WScoped_leaves e hlo l (annotateCore_leaves_sub F e h hw hb l hl)).1

/-! ## The minor premise, spelled out -/

/-- The recursive fields a constructor's minor premise walks: field
index, landing class, telescope length. -/
@[expose] def ClassCtor.recs (x : ClassCtor) : List (Nat × Nat × Nat) :=
  (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none

/-- **The prefix binder at a minor slot** is the minor premise's type of
the slot's constructor. -/
theorem ClassGen.prefixBinders_minor {g : ClassGen} (hg : ClassGenScoped g) {s c : Nat}
    {C : Name} {ihs0 : List (Nat × Nat)} (hs : g.slots[s]? = some (.minor c C ihs0)) :
    ∃ x T, (g.ctors.getD c []).find? (·.cv.name == C) = some x ∧
      g.minorTy c x (g.nP + s) = some T ∧ g.pre[g.nP + s]? = some (T, default) := by
  have hpre := hg.pre
  unfold ClassGen.prefixBinders at hpre
  obtain ⟨slotBs, hsl, hpre⟩ := Option.bind_eq_some_iff.mp hpre
  simp only [Option.pure_def, Option.some.injEq] at hpre
  have hslen : s < g.slots.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hsl s s (List.getElem?_range hslen)
  have hslot : g.slots.getD s default = .minor c C ihs0 := by
    rw [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  simp only at hy
  rw [hslot] at hy
  simp only at hy
  obtain ⟨x, hxf, hy⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨T, hT, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp only [Option.pure_def, Option.some.injEq] at hy
  subst hy
  refine ⟨x, T, hxf, hT, ?_⟩
  rw [← hpre, List.getElem?_append_right (by simp [hg.params_len])]
  simpa [hg.params_len] using hyb

set_option maxHeartbeats 800000 in
/-- **A minor premise's type, spelled out**: the telescope of the fields
and the `ih`s closed at the slot's depth, over the class's motive
variable applied to a nonempty spine; every `ih` domain is a telescope
over its callee's motive variable applied to a nonempty spine, and names
no `ih` variable (its variables lie below `nP + s + nF`). -/
theorem ClassGen.minorTy_spec {g : ClassGen} (hg : ClassGenScoped g) {s c : Nat} {C : Name}
    {ihs0 : List (Nat × Nat)} (hs : g.slots[s]? = some (.minor c C ihs0))
    {x : ClassCtor} (hx : x ∈ g.ctors.getD c []) (hxC : x.cv.name = C) {T : Expr}
    (h : g.minorTy c x (g.nP + s) = some T) :
    ∃ (FB IB : List (Expr × BinderMeta)) (cargs : List Expr) (sc : Nat),
      T = closeTelescope (FB ++ IB) (g.nP + s)
        (Expr.mkAppN (.fvar (g.nP + sc) (.sort .zero)) cargs) ∧
      FB.length = x.nF ∧ IB.length = x.recs.length ∧
      (∀ (k : Nat) (nd : Expr × BinderMeta), (FB ++ IB)[k]? = some nd → ScB (g.nP + s + k) nd.1) ∧
      ClassRead.motiveSlot ⟨g.slots, []⟩ c = some sc ∧ sc < s ∧ cargs ≠ [] ∧
      ScB (g.nP + s + x.nF) (Expr.mkAppN (.fvar (g.nP + sc) (.sort .zero)) cargs) ∧
      ∀ l, l < IB.length → ∃ (i t tele st : Nat) (TB : List (Expr × BinderMeta))
          (bargs : List Expr),
        x.recs.getD l default = (i, t, tele) ∧
        ClassRead.motiveSlot ⟨g.slots, []⟩ t = some st ∧ st < s ∧ bargs ≠ [] ∧
        IB[l]? = some (closeTelescope TB (g.nP + s + x.nF + l)
          (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs), default) ∧
        (∀ (k : Nat) (nd : Expr × BinderMeta), TB[k]? = some nd →
          ScB (g.nP + s + x.nF + l + k) nd.1) ∧
        ScB (g.nP + s + x.nF + l + TB.length)
          (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs) ∧
        Expr.fvarsBelow (g.nP + s + x.nF) (closeTelescope TB (g.nP + s + x.nF + l)
          (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs)) := by
  obtain ⟨⟨sc, hsc, hmc⟩, hmt⟩ := hg.order s c C ihs0 hs
  have htyN : ScB (g.nP + s) x.tyN := (hg.tyN c x hx).mono (by omega)
  unfold ClassGen.minorTy at h
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hfl, hfvs, hres⟩ := ScB.openPis hop htyN
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hihl := option_mapM_length hihs
  simp only [List.length_range] at hihl
  -- the fields
  have hfv : ∀ i, i < x.nF → ∃ ty, fvs.getD i default = .fvar (g.nP + s + i) ty ∧
      ScB (g.nP + s + i) ty := by
    intro i hi
    have hi' : i < fvs.length := by omega
    obtain ⟨ty, hxe, hty⟩ := hfvs i _ (List.getElem?_eq_getElem hi')
    refine ⟨ty, ?_, hty⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hxe
  -- the inductive hypotheses
  have hih : ∀ l, l < ihs.length → ∃ (i t tele st : Nat) (TB : List (Expr × BinderMeta))
      (bargs : List Expr),
      x.recs.getD l default = (i, t, tele) ∧
      ClassRead.motiveSlot ⟨g.slots, []⟩ t = some st ∧ st < s ∧ bargs ≠ [] ∧
      ihs[l]? = some (closeTelescope TB (g.nP + s + x.nF + l)
        (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs), default) ∧
      (∀ (k : Nat) (nd : Expr × BinderMeta), TB[k]? = some nd →
        ScB (g.nP + s + x.nF + l + k) nd.1) ∧
      ScB (g.nP + s + x.nF + l + TB.length)
        (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs) ∧
      Expr.fvarsBelow (g.nP + s + x.nF) (closeTelescope TB (g.nP + s + x.nF + l)
        (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero)) bargs)) := by
    intro l hl
    obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hihs l l (List.getElem?_range (by omega))
    have hlt : l < x.recs.length := lt_of_lt_of_eq hl (hihl.trans rfl)
    generalize hrl : ((List.range x.nF).filterMap fun i =>
        match x.kinds.getD i .ordinary with
        | .recursive t tele => some (i, t, tele)
        | .ordinary => none).getD l default = rl at hy
    obtain ⟨i, t, tele⟩ := rl
    have hmem : (i, t, tele) ∈ x.recs := by
      rw [← hrl]
      exact getD_mem_of_lt hlt _
    obtain ⟨hi, hk⟩ := ClassGen.recs_mem hmem
    obtain ⟨st, hst, hmt'⟩ := hmt x hx hxC t tele (ClassField.mem_of_getD hk)
    obtain ⟨ty, hfe, hty⟩ := hfv i hi
    simp only at hy
    obtain ⟨⟨xs, idx⟩, hparts, hy⟩ := Option.bind_eq_some_iff.mp hy
    simp only [Option.pure_def, Option.some.injEq] at hy
    subst hy
    rw [hfe] at hparts
    obtain ⟨hxl, hxs, hidx⟩ := ClassGen.ihParts_scoped rfl hty (by omega) hparts
    rw [ClassGen.motVar_eq hmt'] at hyb
    have hTB : ∀ (k : Nat) (nd : Expr × BinderMeta), (xs.map classBinder)[k]? = some nd →
        ScB (g.nP + s + x.nF + l + k) nd.1 := by
      intro k nd hk
      rw [List.getElem?_map] at hk
      cases hxk : xs[k]? with
      | none => rw [hxk] at hk; exact nomatch hk
      | some xk =>
        rw [hxk] at hk
        obtain rfl := (Option.some.inj hk).symm
        obtain ⟨ty', hxe, hty'⟩ := hxs k xk hxk
        exact ScB.classBinder hxe hty'
    have hbody : ScB (g.nP + s + x.nF + l + (xs.map classBinder).length)
        (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero))
          (idx ++ [Expr.mkAppN (fvs.getD i default) xs])) := by
      rw [List.length_map, hxl]
      refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact hidx a ha
      · simp only [List.mem_singleton] at ha
        subst ha
        rw [hfe]
        refine ScB.mkAppN (ScB.fvar (by omega) hty) fun b hb => ?_
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]
        exact ScB.fvar (by omega) hty'
    refine ⟨i, t, tele, st, xs.map classBinder, idx ++ [Expr.mkAppN (fvs.getD i default) xs],
      by rw [← hrl]; rfl, hmt', hst, by simp, hyb, hTB, hbody, ?_⟩
    -- the gap: the `ih`'s own variables are closed again
    have hsc : ScB (g.nP + s + x.nF + l) (closeTelescope (xs.map classBinder)
        (g.nP + s + x.nF + l) (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero))
          (idx ++ [Expr.mkAppN (fvs.getD i default) xs]))) :=
      ScB.of_closeTelescope hTB hbody
    refine Expr.FvGap.fvarsBelow (i := g.nP + s + x.nF + l) ?_ hsc.1.fvarsBelow
    -- every piece avoids the gap
    have hfty : Expr.FvGap (g.nP + s + x.nF) (g.nP + s + x.nF + l) ty :=
      Expr.FvGap.of_fvarsBelow (Expr.fvarsBelow_mono (by omega) hty.1.fvarsBelow)
    unfold ClassGen.ihParts at hparts
    obtain ⟨⟨xs', leaf⟩, hop', hparts⟩ := Option.bind_eq_some_iff.mp hparts
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hparts
    obtain ⟨rfl, rfl⟩ := hparts
    obtain ⟨hleaf, hxsG⟩ := Expr.FvGap.openPis _ hop' (Nat.le_refl _) hfty
    refine Expr.FvGap.closeTelescope _ _ (fun nd hnd => ?_) ?_
    · obtain ⟨xk, hxk, rfl⟩ := List.mem_map.mp hnd
      exact (hxsG xk hxk).2
    · refine Expr.FvGap.mkAppN (Or.inl (by omega)) fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact Expr.FvGap.getAppArgs hleaf a (List.mem_of_mem_drop ha)
      · simp only [List.mem_singleton] at ha
        subst ha
        rw [hfe]
        exact Expr.FvGap.mkAppN (Or.inl (by omega)) fun b hb => (hxsG b hb).1
  -- the conclusion
  have hconcl : ScB (g.nP + s + x.nF) (Expr.mkAppN (.fvar (g.nP + sc) (.sort .zero))
      ((res.getAppArgs.drop (g.cls.getD c default).nPc) ++
        [Expr.mkAppN (.const x.cv.name (g.cls.getD c default).key.lvls)
          ((g.cls.getD c default).key.ds ++ fvs)])) := by
    refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact ScB.getAppArgs hres a (List.mem_of_mem_drop ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ScB.mkAppN (ScB.const _ _ _) fun b hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · exact (hg.ds c b hb).mono (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty', hxe, hty'⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]
        exact ScB.fvar (by omega) hty'
  refine ⟨fvs.map classBinder, ihs, _, sc, by rw [ClassGen.motVar_eq hmc], by simp [hfl],
    by rw [hihl]; rfl, ?_, hmc, hsc, by simp, hconcl, hih⟩
  intro k nd hk
  rcases Nat.lt_or_ge k fvs.length with hkl | hkl
  · rw [List.getElem?_append_left (by simpa using hkl)] at hk
    exact ScB.openPis_binders hop htyN k nd hk
  · rw [List.getElem?_append_right (by simpa using hkl)] at hk
    simp only [List.length_map] at hk
    have hkl' : k - fvs.length < ihs.length := (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨i, t, tele, st, TB, bargs, -, -, -, -, hIB, hTB, hbody, -⟩ := hih _ hkl'
    rw [hIB] at hk
    obtain rfl := (Option.some.inj hk).symm
    rw [show g.nP + s + k = g.nP + s + x.nF + (k - fvs.length) by omega]
    exact ScB.of_closeTelescope hTB hbody

end ConLeche
