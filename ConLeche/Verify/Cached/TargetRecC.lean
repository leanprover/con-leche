module

public import ConLeche.Verify.Cached.BlockRunC
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.BlockWF
public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.AgreeFloor
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The cached recursor stage, bridged: the TARGET check

The recursor stage is the classification-free
`targetRecCheck` (`ConLeche/Kernel/Inductives/RecCheck.lean`), written
once over `ShadowOps`: the pure install runs it at `ShadowOps.ofOps`
(`checkBlockRecT`), the cached driver at `shadowOpsC`
(`checkBlockRecS`, `ConLeche/Cached/CheckerC.lean`).  This file proves
the cached run reproduced by the pure fueled one
(`targetRecCheckS_run`), and with it the cached uniform install
(`checkBlockTailS_run`, `checkBlockKS_run`) and the `.indDecl` dispatch
(`checkModeledOrNativeSF_run`).

The layout follows `BlockRunC.lean`'s:

1. the scoping facts every cached operation's simulation needs — the
   target check's terms are opened telescopes, the member-ABSTRACTED
   field types (holes `.fvar (base + t)` past the frame), the fields'
   whnf-telescopes, and the primitive-recursion abstraction's residue,
   whose `ih` variables sit at `base + r` (`targetAbstract_scope`);
2. the operation-free stages, the single-environment stages
   (`targetRecTy`) and the rule stage (`SimG`, two environments) as
   simulations;
3. the assembly, the install and the dispatch.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. Scoping -/

/-- A term scoped past the holes that names none of them is scoped at
the frame. -/
theorem WScoped.below_of_leaves {base k : Nat} :
    ∀ {e : Expr}, WScoped (base + k) e →
      (∀ l ∈ e.fvarLeaves, ¬(base ≤ l.1 ∧ l.1 < base + k)) → WScoped base e := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    have := hl (i, ty) (by simp [fvarLeaves])
    exact ⟨by omega, hw.2⟩
  | app f a ihf iha =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨ihf hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      iha hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | lam ty b m iht ihb =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | forallE ty b m iht ihb =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | letE ty v b iht ihv ihb =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihv hw.2.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | proj s i x ih =>
    intro hw hl
    simp only [WScoped] at hw ⊢
    exact ih hw fun l h => hl l (by simpa [fvarLeaves] using h)
  | _ => intro _ _; simp [WScoped]

/-- **A hole-free term is scoped at the frame** (`targetHoleFree`). -/
theorem WScoped.of_holeFree {base k : Nat} {e : Expr} (hw : WScoped (base + k) e)
    (hf : targetHoleFree base k e = true) : WScoped base e := by
  refine WScoped.below_of_leaves hw fun l hl hb => ?_
  simp only [targetHoleFree, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Expr.mentionsFvar, List.any_eq_false, beq_iff_eq] at hf
  exact hf (l.1 - base) (by omega) l hl (by omega)

theorem piBinders_WScoped {d : Nat} : ∀ {e : Expr}, WScoped d e →
    (∀ b ∈ e.piBinders.1, WScoped d b.1) ∧ WScoped d e.piBinders.2
  | .forallE ty b m, h => by
    simp only [WScoped] at h
    obtain ⟨h1, h2⟩ := piBinders_WScoped h.2
    simp only [Expr.piBinders]
    refine ⟨?_, h2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h1 x hx
  | .bvar _, h | .fvar .., h | .sort _, h | .const .., h | .app .., h | .lam .., h
  | .letE .., h | .lit _, h | .proj .., h => by
    constructor
    · intro b hb; simp [Expr.piBinders] at hb
    · simpa [Expr.piBinders] using h

theorem mkLamsOf_WScoped {d : Nat} :
    ∀ {bs : List (Expr × BinderMeta)} {body : Expr}, (∀ b ∈ bs, WScoped d b.1) →
      WScoped d body → WScoped d (Expr.mkLamsOf bs body)
  | [], _, _, hb => hb
  | (ty, mt) :: bs, body, hbs, hb => by
    simp only [Expr.mkLamsOf, WScoped]
    exact ⟨hbs _ List.mem_cons_self,
      mkLamsOf_WScoped (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb⟩

theorem instPisWith_WScoped {d : Nat} :
    ∀ {as : List Expr} {t r : Expr}, instPisWith as t = some r → WScoped d t →
      (∀ a ∈ as, WScoped d a) → WScoped d r
  | [], t, r, h, ht, _ => by
    simp only [instPisWith, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    cases t with
    | forallE dom body bi =>
      simp only [instPisWith] at h
      simp only [WScoped] at ht
      exact instPisWith_WScoped h (WScoped.instantiate1_gen (ha a List.mem_cons_self) 0 ht.2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ => simp [instPisWith] at h

theorem WScoped.default_expr {d : Nat} : WScoped d (default : Expr) :=
  WScoped.of_not_hasFvar (by rfl)

theorem getD_WScoped {d : Nat} {l : List Expr} (h : ∀ x ∈ l, WScoped d x) (i : Nat) :
    WScoped d (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact WScoped.default_expr
  | some x => exact h x (List.mem_of_getElem? hx)

/-- The frame's holes are scoped past the frame. -/
theorem targetHoles_WScoped {formerTys : List Expr} (hF : ∀ t ∈ formerTys, WScoped 0 t)
    (base : Nat) : ∀ h ∈ targetHoles formerTys base, WScoped (base + formerTys.length) h := by
  intro h hh
  simp only [targetHoles, List.mem_map, List.mem_range] at hh
  obtain ⟨t, ht, rfl⟩ := hh
  simp only [WScoped]
  exact ⟨by omega, ws_of_ws0 (getD_WScoped hF t)⟩

/-- The opened telescope's variables: variable `i` is scoped at `off + i + 1`. -/
theorem openers_WScoped_at {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i + 1) x := by
  intro i x hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e off h i x hx
  have := openers_typeD_WScoped h he i _ hx
  simp only [WScoped]
  exact ⟨by omega, this⟩

/-! ### The primitive-recursion abstraction's residue -/

/-- The first `k` openers are scoped at `k`. -/
theorem openers_take_WScoped {n : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e 0 = some (fvs, body)) (he : WScoped 0 e) (k : Nat) :
    ∀ x ∈ fvs.take k, WScoped k x := by
  intro x hxm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hxm
  have hil : i < k := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this; omega
  rw [List.getElem?_take, if_pos hil] at hi
  exact (openers_WScoped_at h he i x hi).mono (by omega)

/-- The accumulator's entries are the frame's `ih` variables in order. -/
def TargetAccOk (base : Nat) (acc : Array TargetIh) : Prop :=
  ∀ (r : Nat) (h : r < acc.size), acc[r].fv = .fvar (base + r) acc[r].ty

theorem targetCall?_sub {fr : TargetFrame} {d : Nat} {e : Expr} {i c m : Nat}
    {idx : List Expr} (h : targetCall? fr d e = some (i, c, m, idx)) :
    m = (fr.teles.getD i []).length ∧ ∀ x ∈ idx, x ∈ e.getAppArgs := by
  unfold targetCall? at h
  repeat' (first | split at h | (dsimp only at h; split at h))
  all_goals (try contradiction)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, fun x hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)⟩

/-- **The primitive-recursion abstraction, scoped**: the walk only
appends, keeps the entries the frame's variables `base + r`, every new
entry is a recognised call whose `ih` type is `targetIhTy` at the
field's telescope and whose index arguments are sub-terms of the
walked (frame-scoped) term, and the residue is scoped past the entries
once their types are. -/
theorem targetAbstract_scope {fr : TargetFrame} {base : Nat} :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      targetAbstract fr base d e acc = some (e', acc') → WScoped base e →
      TargetAccOk base acc →
      acc.toList <+: acc'.toList ∧ TargetAccOk base acc' ∧
      (∀ ih ∈ acc'.toList, ih ∈ acc.toList ∨
        (targetIhTy fr ih.field ih.callee (fr.teles.getD ih.field []).length ih.idx = some ih.ty
          ∧ ∀ x ∈ ih.idx, WScoped base x)) ∧
      ((∀ ih ∈ acc'.toList, WScoped base ih.ty) → WScoped (base + acc'.size) e')
  | _, .bvar _, acc, _, _, h, _, hok => by
    simp only [targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun _ => by simp [WScoped]⟩
  | _, .sort _, acc, _, _, h, _, hok => by
    simp only [targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun _ => by simp [WScoped]⟩
  | _, .lit _, acc, _, _, h, _, hok => by
    simp only [targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun _ => by simp [WScoped]⟩
  | _, .fvar _ _, acc, _, _, h, hw, hok => by
    simp only [targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun _ => hw.mono (by omega)⟩
  | _, .const n us, acc, _, _, h, _, hok => by
    simp only [targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun _ => by simp [WScoped]⟩
  | d, .lam ty b bi, acc, _, _, h, hw, hok => by
    simp only [targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [WScoped] at hw
    obtain ⟨p1, o1, n1, s1⟩ := targetAbstract_scope d ty acc ty' acc1 h1 hw.1 hok
    obtain ⟨p2, o2, n2, s2⟩ := targetAbstract_scope (d + 1) b acc1 b' acc2 h2 hw.2 o1
    refine ⟨p1.trans p2, o2, fun ih hih => ?_, fun hT => ?_⟩
    · rcases n2 ih hih with h | h
      · exact n1 ih h
      · exact Or.inr h
    · have hsz : acc1.size ≤ acc2.size := by
        have := p2.length_le; simpa using this
      simp only [WScoped]
      exact ⟨(s1 fun ih hih => hT ih (p2.subset hih)).mono (by omega), s2 hT⟩
  | d, .forallE ty b bi, acc, _, _, h, hw, hok => by
    simp only [targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [WScoped] at hw
    obtain ⟨p1, o1, n1, s1⟩ := targetAbstract_scope d ty acc ty' acc1 h1 hw.1 hok
    obtain ⟨p2, o2, n2, s2⟩ := targetAbstract_scope (d + 1) b acc1 b' acc2 h2 hw.2 o1
    refine ⟨p1.trans p2, o2, fun ih hih => ?_, fun hT => ?_⟩
    · rcases n2 ih hih with h | h
      · exact n1 ih h
      · exact Or.inr h
    · have hsz : acc1.size ≤ acc2.size := by
        have := p2.length_le; simpa using this
      simp only [WScoped]
      exact ⟨(s1 fun ih hih => hT ih (p2.subset hih)).mono (by omega), s2 hT⟩
  | d, .letE ty v b, acc, _, _, h, hw, hok => by
    simp only [targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [WScoped] at hw
    obtain ⟨p1, o1, n1, s1⟩ := targetAbstract_scope d ty acc ty' acc1 h1 hw.1 hok
    obtain ⟨p2, o2, n2, s2⟩ := targetAbstract_scope d v acc1 v' acc2 h2 hw.2.1 o1
    obtain ⟨p3, o3, n3, s3⟩ := targetAbstract_scope (d + 1) b acc2 b' acc3 h3 hw.2.2 o2
    refine ⟨(p1.trans p2).trans p3, o3, fun ih hih => ?_, fun hT => ?_⟩
    · rcases n3 ih hih with h | h
      · rcases n2 ih h with h | h
        · exact n1 ih h
        · exact Or.inr h
      · exact Or.inr h
    · have hsz1 : acc1.size ≤ acc3.size := by
        have := (p2.trans p3).length_le; simpa using this
      have hsz2 : acc2.size ≤ acc3.size := by
        have := p3.length_le; simpa using this
      simp only [WScoped]
      exact ⟨(s1 fun ih hih => hT ih ((p2.trans p3).subset hih)).mono (by omega),
        (s2 fun ih hih => hT ih (p3.subset hih)).mono (by omega), s3 hT⟩
  | d, .proj sn i x, acc, _, _, h, hw, hok => by
    simp only [targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [WScoped] at hw
      obtain ⟨p1, o1, n1, s1⟩ := targetAbstract_scope d x acc x' acc1 h1 hw hok
      exact ⟨p1, o1, n1, fun hT => by simp only [WScoped]; exact s1 hT⟩
  | d, .app f a, acc, _, _, h, hw, hok => by
    simp only [targetAbstract] at h
    split at h
    · next i c m idx hc =>
      obtain ⟨hm, hsub⟩ := targetCall?_sub hc
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      split at h
      · next r hr =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨List.prefix_refl _, hok, fun ih h => Or.inl h, fun hT => ?_⟩
        rw [Array.findIdx?_eq_some_iff_getElem] at hr
        obtain ⟨hrl, -, -⟩ := hr
        refine Expr.WScoped.mkAppN ?_ structTeleVars_WScoped
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hrl, Option.getD_some,
          hok r hrl]
        simp only [WScoped]
        exact ⟨by omega, (hT _ (Array.getElem_mem_toList hrl)).mono (by omega)⟩
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, ?_, fun ih hih => ?_, fun hT => ?_⟩
        · intro r hr
          rw [Array.size_push] at hr
          rcases Nat.lt_or_ge r acc.size with hlt | hge
          · rw [Array.getElem_push_lt hlt]; exact hok r hlt
          · obtain rfl : r = acc.size := by omega
            rw [Array.getElem_push_eq]
        · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hih
          rcases hih with hih | rfl
          · exact Or.inl hih
          · refine Or.inr ⟨by rw [← hm]; exact hty, fun x hx => ?_⟩
            exact Expr.WScoped.getAppArgs hw x (hsub x hx)
        · refine Expr.WScoped.mkAppN ?_ structTeleVars_WScoped
          have := hT ⟨i, c, idx, ty, .fvar (base + acc.size) ty⟩ (by rw [Array.toList_push]; simp)
          simp only [WScoped, Array.size_push]
          exact ⟨by omega, this.mono (by omega)⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [WScoped] at hw
      obtain ⟨p1, o1, n1, s1⟩ := targetAbstract_scope d f acc f' acc1 h1 hw.1 hok
      obtain ⟨p2, o2, n2, s2⟩ := targetAbstract_scope d a acc1 a' acc2 h2 hw.2 o1
      refine ⟨p1.trans p2, o2, fun ih hih => ?_, fun hT => ?_⟩
      · rcases n2 ih hih with h | h
        · exact n1 ih h
        · exact Or.inr h
      · have hsz : acc1.size ≤ acc2.size := by
          have := p2.length_le; simpa using this
        simp only [WScoped]
        exact ⟨(s1 fun ih hih => hT ih (p2.subset hih)).mono (by omega), s2 hT⟩

/-- The `ih` type of a recognised call is scoped at the frame, once the
field's telescope is. -/
theorem targetIhTy_WScoped {fr : TargetFrame} {base i c m : Nat} {idx : List Expr} {ty : Expr}
    (h : targetIhTy fr i c m idx = some ty)
    (htele : ∀ b ∈ fr.teles.getD i [], WScoped base b.1)
    (hpref : ∀ x ∈ fr.pref, WScoped base x) (hidx : ∀ x ∈ idx, WScoped base x)
    (hflds : ∀ x ∈ fr.fields, WScoped base x) (hrec : ∀ t ∈ fr.recTys, WScoped 0 t) :
    WScoped base ty := by
  unfold targetIhTy at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  refine mkPisOf_WScoped ?_ ?_
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact htele b' hb'
  · refine instPisAtLift_WScoped hr (ws_of_ws0 ?_) ?_
    · rw [List.getD_eq_getElem?_getD]
      cases hx : fr.recTys[c]? with
      | none => simp [WScoped]
      | some t => exact hrec t (List.mem_of_getElem? hx)
    · intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · exact hpref a ha
      · exact hidx a ha
      · exact Expr.WScoped.mkAppN (getD_WScoped hflds i) structTeleVars_WScoped

/-! ## 2. The stages, simulated -/

/-- A simulation keeps what the cached run is known to yield. -/
theorem SimC.withYields {env : Env} {s₀ : CState} {β α : Type} {P : β → α → Prop}
    {Q : β → Prop} {c : CheckCM β} {p : FueledM α} (h : SimC mode env s₀ P c p)
    (hy : ∀ s a s', c s = .ok (a, s') → Q a) :
    SimC mode env s₀ (fun v w => P v w ∧ Q v) c p := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hF⟩ := h v' s' hr
  exact ⟨hs', v, ⟨hP, hy s₀ v' s' hr⟩, F, hF⟩

section Sims

variable {env : Env}

/-- `targetOutsideInst` is operation-free: at the cached driver it
leaves the state alone and computes the pure value. -/
theorem targetOutsideInst_C {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    (s : CState) :
    targetOutsideInst (m := CheckCM) fe I us ds s =
      (match targetOutsideInst (m := CheckM) fe I us ds with
        | .ok v => .ok (v, s)
        | .error e => .error e) := by
  unfold targetOutsideInst
  cases h1 : fe.find? I with
  | none => rfl
  | some ci =>
    cases ci with
    | indInfo cvI caps =>
      dsimp only
      cases h2 : instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us) with
      | none => rfl
      | some ty =>
        dsimp only
        rcases h3 : ty.piBinders with ⟨ibs, e⟩
        cases e <;> rfl
    | _ => rfl

theorem targetOutsideInstS_sim {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (targetOutsideInst (m := CheckCM) fe I us ds)
      (targetOutsideInst (m := FueledM) fe I us ds) := by
  intro v' s' h
  rw [targetOutsideInst_C] at h
  cases hr : targetOutsideInst (m := CheckM) fe I us ds with
  | error e => rw [hr] at h; exact nomatch h
  | ok v =>
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    exact ⟨hs, v, rfl, 0, by rw [targetOutsideInst_datF]; exact hr⟩

/-- `liftFueled` (the level comparison's fuel) is operation-free. -/
theorem liftFueledS_sim {α : Type} {what : String} {o : Option α} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (liftFueled (m := CheckCM) what o) (liftFueled (m := FueledM) what o) := by
  cases o with
  | none => exact SimC.throw
  | some a => exact SimC.pure hs rfl

/-! ### The class match (`targetClassMatch`) and its three uses -/

theorem targetParamsDefEqS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {absM : Expr → Expr} (habs : ∀ e, WScoped d e → WScoped d (absM e)) {pfvs : List Expr}
    (hp : ∀ x ∈ pfvs, WScoped d x) :
    ∀ (as bs : List Expr) {s₀ : CState}, (∀ a ∈ as, WScoped d a) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (targetParamsDefEq (sharedOpsC mode (mkFEnv env)) env d absM pfvs as bs)
        (targetParamsDefEq (fueledOpsM mode) env d absM pfvs as bs)
  | [], [], _, _, hs => SimC.pure hs rfl
  | [], _ :: _, _, _, hs => SimC.pure hs rfl
  | _ :: _, [], _, _, hs => SimC.pure hs rfl
  | a :: as, b :: bs, _, ha, hs => by
    unfold targetParamsDefEq
    split
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      dsimp only [sharedOpsC]
      have hwa := habs _ (targetCanonParams_WScoped hp a (fvarB_le hg.1.2))
      have hwb := habs _ (targetCanonParams_WScoped hp b (fvarB_le hg.2))
      split
      · exact targetParamsDefEqS_sim hμ henv habs hp as bs
          (fun a' ha' => ha a' (List.mem_cons_of_mem _ ha')) hs
      refine SimC.bind (opE_infer_sim hμ henv hs hwa) (fun s₁ _ _ hs₁ _ => ?_)
      refine SimC.bind (opE_infer_sim hμ henv hs₁ hwb) (fun s₂ _ _ hs₂ _ => ?_)
      refine SimC.bind (opB_sim hμ henv hs₂ hwa hwb) (fun s₃ c c' hs₃ hC => ?_)
      obtain rfl : c = c' := hC
      cases c
      · exact SimC.pure hs₃ rfl
      · exact targetParamsDefEqS_sim hμ henv habs hp as bs
          (fun a' ha' => ha a' (List.mem_cons_of_mem _ ha')) hs₃
    · exact SimC.pure hs rfl

/-- The class match, simulated: the class's openers and parameters
scoped by the block's parameters, the formers closed. -/
theorem targetClassMatchS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds eds : List Expr} {us lvls : List Level}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) (hds : ∀ x ∈ ds, WScoped pfvs.length x)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetClassMatch (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds lvls eds)
      (targetClassMatch (fueledOpsM mode) env p formerTys pfvs us ds lvls eds) := by
  unfold targetClassMatch
  split
  · exact targetParamsDefEqS_sim hμ henv
      (targetAbs_WScoped (targetHoles_WScoped hformer pfvs.length))
      (fun x hx => (hp x hx).mono (by omega)) ds eds (fun x hx => (hds x hx).mono (by omega)) hs
  · exact SimC.pure hs rfl

theorem targetMajorNfsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds : List Expr} {us : List Level} {ctors : List (ConstantVal × Nat)}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) (hds : ∀ x ∈ ds, WScoped pfvs.length x) :
    ∀ (es : List NestCtorNf) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (targetMajorNfs (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds ctors es)
        (targetMajorNfs (fueledOpsM mode) env p formerTys pfvs us ds ctors es)
  | [], _, hs => SimC.pure hs rfl
  | e :: es, _, hs => by
    unfold targetMajorNfs
    refine SimC.bind (targetMajorNfsS_sim hμ henv hformer hp hds es hs)
      (fun s₁ r r' hs₁ hR => ?_)
    obtain rfl : r = r' := hR
    split
    · refine SimC.bind (targetClassMatchS_sim hμ henv hformer hp hds hs₁)
        (fun s₂ c c' hs₂ hC => ?_)
      obtain rfl : c = c' := hC
      cases c <;> exact SimC.pure hs₂ rfl
    · exact SimC.pure hs₁ rfl

theorem targetMajorOfS_sim {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetMajorOf (m := CheckCM) (mkFEnv env) p ctorsAs pfvs fvs mty)
      (targetMajorOf (m := FueledM) (mkFEnv env) p ctorsAs pfvs fvs mty) := by
  unfold targetMajorOf
  dsimp only
  split
  · split
    · refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ ms ms' hs₁ hP => ?_)
      obtain ⟨rfl, -⟩ := hP
      refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ c c' hs₂ hQ => ?_)
      obtain ⟨rfl, -⟩ := hQ
      split
      · exact SimC.pure hs₂ rfl
      · exact SimC.throw_bind
    · repeat' (first
        | exact SimC.throw
        | exact SimC.throw_bind
        | exact SimC.pure hs rfl
        | split)
      all_goals
        refine SimC.bind (targetOutsideInstS_sim hs) (fun s₂ r r' hs₂ hR => ?_)
        cases hR
        refine SimC.bind (liftFueledS_sim hs₂) (fun s₃ q q' hs₃ hQ => ?_)
        cases hQ
        split
        · exact SimC.pure hs₃ rfl
        · exact SimC.throw_bind
  · exact SimC.throw

/-- **What a resolved major is**:
a member, or an outside inductive whose parameters are arguments of the
major's type mentioning only the recursor's parameter binders. -/
private theorem targetMajorOf_shape (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) :
    Yields (targetMajorOf (m := CheckCM) fe p ctorsAs pfvs fvs mty)
      (fun M => M.pfvs = pfvs ∧ ((∃ t, M.member = some t ∧ M.ds = fvs.take p.nP) ∨
        (M.member = none ∧ ∀ x ∈ M.ds, x ∈ mty.getAppArgs ∧ x.fvarB ≤ p.nP))) := by
  unfold targetMajorOf
  dsimp only
  split
  · split
    · refine Yields.bind' Yields.unwrapOr fun ms _ => ?_
      refine Yields.bind' Yields.unwrapOr fun ctorsA _ => ?_
      split
      · exact Yields.pure ⟨rfl, Or.inl ⟨_, rfl, rfl⟩⟩
      · exact Yields.ofThrowBind
    · repeat' (first
        | exact Yields.ofThrow
        | exact Yields.ofThrowBind
        | (refine Yields.bind fun _ => ?_)
        | split)
      all_goals first
        | (refine Yields.pure ⟨rfl, Or.inr ⟨rfl, fun x hx => ⟨List.mem_of_mem_take hx, ?_⟩⟩⟩
           simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at *
           exact ((by assumption : _ ∧ ∀ y ∈ List.take _ mty.getAppArgs,
             y.bvarB = 0 ∧ y.fvarB ≤ p.nP).2 x hx).2)
  · exact Yields.ofThrow

/-- **An outside major's index telescope, simulated**:
the container's former, instantiated at the major's levels and
parameters, opened past the rule prefix. -/
theorem targetIdxDomsS_sim_out (henv : EnvWF env) {p : BlockShape}
    {cvTas : List ConstantVal} {rP : Nat} {M : TargetMajor} (hM : M.member = none)
    (hds : ∀ x ∈ M.ds, WScoped rP x) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ (l : Nat) (x : Expr), v[l]? = some x →
        l < M.nIdx ∧ WScoped (rP + l) x)
      (targetIdxDoms (m := CheckCM) (mkFEnv env) p cvTas rP M)
      (targetIdxDoms (m := FueledM) (mkFEnv env) p cvTas rP M) := by
  unfold targetIdxDoms
  rw [hM]
  dsimp only
  rw [mkFEnv_find?]
  cases h1 : env.find? M.ind with
  | none => exact SimC.throw
  | some ci =>
    cases ci with
    | indInfo cvI caps =>
      dsimp only
      have hwI0 : WScoped rP (cvI.type.instantiateLevelParams cvI.levelParams M.lvls) := by
        refine WScoped.of_not_hasFvar ?_
        rw [Expr.hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem h1)).1
      cases h2 : instPisWith M.ds (cvI.type.instantiateLevelParams cvI.levelParams M.lvls) with
      | none => exact SimC.throw
      | some ty =>
        dsimp only
        have hwI : WScoped rP ty := instPisWith_WScoped h2 hwI0 hds
        refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ y y' hs₁ hY => ?_)
        obtain ⟨rfl, hy⟩ := hY
        obtain ⟨ifs, rest⟩ := y
        refine SimC.pure hs₁ ⟨rfl, fun l x hx => ?_⟩
        rw [List.getElem?_map] at hx
        obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hx
        refine ⟨?_, openers_typeD_WScoped hy hwI l x' hx'⟩
        have := (List.getElem?_eq_some_iff.mp hx').1
        rw [ConLeche.Verify.openPisAtFvars_length _ hy] at this
        exact this
    | _ => exact SimC.throw

/-- The pin typing at the cached driver. -/
theorem targetPinTysS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} :
    ∀ {xs : List Expr}, (∀ x ∈ xs, WScoped d x) → ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun (_ _ : Unit) => True)
        (targetPinTys (sharedOpsC mode (mkFEnv env)) env d xs)
        (targetPinTys (fueledOpsM mode) env d xs)
  | [], _, _, hs => SimC.pure hs trivial
  | x :: xs, hx, _, hs => by
    unfold targetPinTys
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs (hx x List.mem_cons_self))
      (fun s₁ _ _ hs₁ _ => ?_)
    exact targetPinTysS_sim hμ henv (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hs₁

/-- `targetMajorPins` at the cached driver: nothing at a member, the
pins and the instantiation typed at an outside major. -/
theorem targetMajorPinsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {rP : Nat}
    {M : TargetMajor} (hds : M.member = none → ∀ x ∈ M.ds, WScoped rP x) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun (_ _ : Unit) => True)
      (targetMajorPins (sharedOpsC mode (mkFEnv env)) env rP M)
      (targetMajorPins (fueledOpsM mode) env rP M) := by
  unfold targetMajorPins
  cases hM : M.member with
  | some t =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs trivial
  | none =>
    simp only [Option.isNone_none, ↓reduceIte]
    have hw := hds hM
    refine SimC.bind (targetPinTysS_sim hμ henv hw hs) (fun s₁ _ _ hs₁ _ => ?_)
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs₁
      (Expr.WScoped.mkAppN (by simp [WScoped]) hw)) (fun s₂ _ _ hs₂ _ => ?_)
    exact SimC.pure hs₂ trivial

theorem targetIdxDomsS_sim {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal} {rP : Nat}
    {M : TargetMajor} {t : Nat} (hM : M.member = some t) (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hle : p.nP ≤ rP) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ (l : Nat) (x : Expr), v[l]? = some x →
        l < M.nIdx ∧ WScoped (rP + l) x)
      (targetIdxDoms (m := CheckCM) fe p cvTas rP M)
      (targetIdxDoms (m := FueledM) fe p cvTas rP M) := by
  unfold targetIdxDoms
  rw [hM]
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvTa cvTa' hs₁ hP => ?_)
  obtain ⟨rfl, hcvTa⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ y y' hs₂ hQ => ?_)
  obtain ⟨rfl, hy⟩ := hQ
  obtain ⟨tfs, trest⟩ := y
  refine SimC.pure hs₂ ⟨rfl, fun l x hx => ?_⟩
  rw [List.getElem?_map] at hx
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hx
  exact openPisParamsIdx_typeD_WScoped hy (hT cvTa (List.mem_of_getElem? hcvTa)) hle l x' hx'

theorem targetRecTyS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) {rc : RecShape} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 v.1.type)
      (targetRecTy (sharedOpsC mode (mkFEnv env)) (mkFEnv env) p nested cvTas ctorsAs rc)
      (targetRecTy (fueledOpsM mode) (mkFEnv env) p nested cvTas ctorsAs rc) := by
  unfold targetRecTy
  simp only [checkConstantValF_eq, mkFEnv_env]
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ cvRi cvRi' hs₁ hR => ?_)
  obtain ⟨rfl, hwR⟩ := hR
  by_cases h1 : p.nP ≤ rc.rP
  case neg => simp only [h1, if_false]; exact SimC.throw_bind
  simp only [h1, if_true]
  by_cases h2 : rc.rP ≤ rc.mI
  case neg => simp only [h2, if_false]; exact SimC.throw_bind
  simp only [h2, if_true]
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ x x' hs₂ hX => ?_)
  obtain ⟨rfl, hx⟩ := hX
  obtain ⟨fvs, concl⟩ := x
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ maj maj' hs₃ hMj => ?_)
  obtain ⟨rfl, hmaj⟩ := hMj
  have hmajW : WScoped rc.mI maj.fvarTypeD := by
    have := openers_typeD_WScoped hx hwR rc.mI maj hmaj
    rwa [Nat.zero_add] at this
  have hformer : ∀ t ∈ cvTas.map (·.type), WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  have hxl : fvs.length = rc.mI + 1 := ConLeche.Verify.openPisAtFvars_length _ hx
  have hpl : (fvs.take rc.rP).length = rc.rP := by rw [List.length_take]; omega
  have hpf : ∀ x ∈ fvs.take rc.rP, WScoped (fvs.take rc.rP).length x := by
    rw [hpl]; exact openers_take_WScoped hx hwR rc.rP
  have hfvsP : ∀ x ∈ fvs.take p.nP, WScoped (fvs.take rc.rP).length x := by
    rw [hpl]; exact fun x hx' => (openers_take_WScoped hx hwR p.nP x hx').mono h1
  refine SimC.bind ((targetMajorOfS_sim hs₃).withYields
    (targetMajorOf_shape (mkFEnv env) p ctorsAs (fvs.take rc.rP) fvs maj.fvarTypeD))
    (fun s₄ M M' hs₄ hM => ?_)
  obtain ⟨rfl, -, hMsh⟩ := hM
  -- an outside major's parameters, scoped by the recursor's prefix
  have hdsW : M.member = none → ∀ x ∈ M.ds, WScoped rc.rP x := by
    intro hMn x hxd
    rcases hMsh with ⟨t, hmt, -⟩ | ⟨-, hall⟩
    · rw [hMn] at hmt; exact nomatch hmt
    obtain ⟨hxa, hfb⟩ := hall x hxd
    exact (ConLeche.WScoped.of_fvarsBelow (Expr.WScoped.getAppArgs hmajW x hxa)
      (ConLeche.Expr.fvarB_le hfb)).mono (by omega)
  by_cases h3 : Option.all (fun x => x == rc.tgt) M.member = true
  case neg => simp only [h3]; exact SimC.throw_bind
  simp only [h3, if_true]
  -- the pin typing: nothing at a member major, the pins at an outside one
  refine SimC.bind (targetMajorPinsS_sim hμ henv hdsW hs₄) (fun s₄ _ _ hs₄ _ => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₄) (fun s₅ cvTP cvTP' hs₅ hP => ?_)
  obtain ⟨rfl, hcvTP⟩ := hP
  have hwTP : WScoped 0 cvTP.type := by
    cases hMm : M.member with
    | none =>
      rw [hMm] at hcvTP
      exact hT cvTP (List.mem_of_mem_head? hcvTP)
    | some t =>
      rw [hMm] at hcvTP
      exact hT cvTP (List.mem_of_getElem? hcvTP)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ y y' hs₆ hY => ?_)
  obtain ⟨rfl, hy⟩ := hY
  obtain ⟨tfvs, trest⟩ := y
  dsimp only
  have hxl : fvs.length = rc.mI + 1 := ConLeche.Verify.openPisAtFvars_length _ hx
  refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₆) (fun s₇ _ _ hs₇ _ => ?_)
  · intro i a b ha hb
    rw [List.getElem?_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    have hil : i < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hb').1
      simp only [List.length_take] at this; omega
    rw [List.getElem?_take, if_pos hil] at hb'
    exact ⟨(openers_typeD_WScoped hy hwTP i a' ha').mono (by omega),
      (openers_typeD_WScoped hx hwR i b' hb').mono (by omega)⟩
  by_cases h4 : (rc.mI == rc.rP + M.nIdx) = true
  case neg => simp only [h4]; exact SimC.throw_bind
  simp only [h4, if_true]
  split
  case isFalse => exact SimC.throw_bind
  case isTrue h5 =>
  have hmI : rc.mI = rc.rP + M.nIdx := by simpa using h4
  refine SimC.bind (show SimC mode env s₇ (fun v w => v = w ∧ ∀ (l : Nat) (x : Expr),
        v[l]? = some x → l < M.nIdx ∧ WScoped (rc.rP + l) x)
      (targetIdxDoms (m := CheckCM) (mkFEnv env) p cvTas rc.rP M)
      (targetIdxDoms (m := FueledM) (mkFEnv env) p cvTas rc.rP M) from by
    cases hMm : M.member with
    | some t => exact targetIdxDomsS_sim hMm hT (by omega) hs₇
    | none => exact targetIdxDomsS_sim_out henv hMm (hdsW hMm) hs₇)
    (fun s₈ idoms idoms' hs₈ hI => ?_)
  obtain ⟨rfl, hidoms⟩ := hI
  refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₈) (fun s₉ _ _ hs₉ _ => ?_)
  · intro i a b ha hb
    obtain ⟨hil, hwa⟩ := hidoms i a ha
    rw [List.getElem?_map] at hb
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop] at hb'
    refine ⟨hwa.mono (by omega), ?_⟩
    exact (openers_typeD_WScoped hx hwR (rc.rP + i) b' hb').mono (by omega)
  dsimp only [sharedOpsC]
  have hwc : WScoped (rc.mI + 1) concl := by
    have := (openPisAtFvars_WScoped _ _ 0 hx hwR).2
    simpa using this
  refine SimC.bind (opE_infer_sim hμ henv hs₉ hwc) (fun s₁₀ sty sty' hs₁₀ hS => ?_)
  obtain ⟨rfl, hwsty⟩ := hS
  refine SimC.bind (opS_sim hμ henv hs₁₀ hwsty) (fun s₁₁ u u' hs₁₁ hU => ?_)
  obtain rfl : u = u' := hU
  by_cases h6 : blockLargeElimAllowed p nested = true
  · simp only [h6, if_true]
    exact SimC.pure hs₁₁ ⟨rfl, hwR⟩
  · simp only [h6]
    refine SimC.bind (opB_sim hμ henv hs₁₁ hwsty (by simp [WScoped]))
      (fun s₁₂ b b' hs₁₂ hB => ?_)
    obtain rfl : b = b' := hB
    cases b with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimC.throw_bind
    | true => simp only [↓reduceIte]; exact SimC.pure hs₁₂ ⟨rfl, hwR⟩

theorem targetRecTysS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) :
    ∀ {recs : List RecShape} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ q ∈ v, WScoped 0 q.1.type)
        (targetRecTys (sharedOpsC mode (mkFEnv env)) (mkFEnv env) p nested cvTas ctorsAs
          recs)
        (targetRecTys (fueledOpsM mode) (mkFEnv env) p nested cvTas ctorsAs recs)
  | [], s₀, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | rc :: rcs, s₀, hs => by
    unfold targetRecTys
    refine SimC.bind (targetRecTyS_sim hμ henv hT hs) (fun s₁ t t' hs₁ hP => ?_)
    obtain ⟨rfl, hw⟩ := hP
    refine SimC.bind (targetRecTysS_sim hμ henv hT hs₁) (fun s₂ ts ts' hs₂ hQ => ?_)
    obtain ⟨rfl, hws⟩ := hQ
    refine SimC.pure hs₂ ⟨rfl, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hw
    · exact hws q hq

theorem targetRecPinsS_sim {p : BlockShape} {block : List ConstantInfo} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (targetRecPins (m := CheckCM) p block)
      (targetRecPins (m := FueledM) p block) := by
  unfold targetRecPins
  dsimp only
  by_cases h1 : blockRecLpsOk p = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  by_cases h2 : blockRecNamesUnreserved p = true
  case neg => simp only [h2]; exact SimC.throw_bind
  simp only [h2, if_true]
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  split
  · split
    · exact SimC.pure hs rfl
    · exact SimC.throw
  · exact SimC.throw

theorem targetRulePinsAllS_sim {s₀ : CState} (hs : CSOK mode env s₀) :
    ∀ (tys : List (ConstantVal × TargetMajor × Level)) (rss : List (List RecRule)),
      SimC mode env s₀ RelVC (targetRulePinsAll (m := CheckCM) tys rss)
        (targetRulePinsAll (m := FueledM) tys rss)
  | [], _ => SimC.pure hs rfl
  | _ :: _, [] => SimC.pure hs rfl
  | t :: ts, rs :: rss => by
    unfold targetRulePinsAll targetRulePins
    split
    · exact SimC.bind (SimC.pure hs rfl) (fun s₁ _ _ hs₁ _ => targetRulePinsAllS_sim hs₁ ts rss)
    · exact SimC.throw_bind

theorem targetWhnfPisS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ (fuel d : Nat) {e : Expr} {s₀ : CState}, WScoped d e → CSOK mode env s₀ →
      SimC mode env s₀ (RelW d)
        (targetWhnfPis (sharedOpsC mode (mkFEnv env)) env d fuel e)
        (targetWhnfPis (fueledOpsM mode) env d fuel e)
  | 0, _, _, _, _, _ => SimC.throw
  | fuel + 1, d, e, s₀, hw, hs => by
    rw [targetWhnfPis, targetWhnfPis]
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_whnf_sim hμ henv hs hw) (fun s₁ w w' hs₁ hW => ?_)
    obtain ⟨rfl, hww⟩ := hW
    split
    · rename_i dom body bm
      simp only [WScoped] at hww
      refine SimC.bind (targetWhnfPisS_sim hμ henv fuel (d + 1)
        (WScoped.instantiate1 hww.1 0 hww.2) hs₁) (fun s₂ b b' hs₂ hB => ?_)
      obtain ⟨rfl, hwb⟩ := hB
      refine SimC.pure hs₂ ⟨rfl, ?_⟩
      simp only [WScoped]
      exact ⟨hww.1, WScoped.abstract1 0 hwb⟩
    · exact SimC.pure hs₁ ⟨rfl, hw⟩

theorem targetFieldNormsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {depth : Nat} {absM : Expr → Expr} :
    ∀ {fvs : List Expr} {s₀ : CState}, (∀ f ∈ fvs, WScoped depth (absM f.fvarTypeD)) →
      CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ t ∈ v, WScoped depth t)
        (targetFieldNorms (sharedOpsC mode (mkFEnv env)) env depth absM fvs)
        (targetFieldNorms (fueledOpsM mode) env depth absM fvs)
  | [], s₀, _, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | f :: fs, s₀, hf, hs => by
    unfold targetFieldNorms
    refine SimC.bind (targetWhnfPisS_sim hμ henv _ depth (hf f List.mem_cons_self) hs)
      (fun s₁ t t' hs₁ hT => ?_)
    obtain ⟨rfl, hwt⟩ := hT
    refine SimC.bind (targetFieldNormsS_sim hμ henv (fun g hg => hf g (List.mem_cons_of_mem _ hg))
      hs₁) (fun s₂ ts ts' hs₂ hTs => ?_)
    obtain ⟨rfl, hwts⟩ := hTs
    refine SimC.pure hs₂ ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hwt
    · exact hwts x hx

/-- A resolved major's class, scoped by the block's parameters: its
openers and its parameters (what the class match needs). -/
@[expose] def TargetMajScoped (M : TargetMajor) : Prop :=
  (∀ x ∈ M.pfvs, WScoped M.pfvs.length x) ∧ ∀ x ∈ M.ds, WScoped M.pfvs.length x

theorem TargetMajScoped.getD {l : List TargetMajor}
    (h : ∀ M ∈ l, TargetMajScoped M) (i : Nat) : TargetMajScoped (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none =>
    refine ⟨fun x hx' => ?_, fun x hx' => ?_⟩ <;> exact nomatch hx'
  | some M => exact h M (List.mem_of_getElem? hx)

theorem targetK53S_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {Mc : TargetMajor}
    (hMc : TargetMajScoped Mc) {tele : List (Expr × BinderMeta)} {majDom f : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetK53 (sharedOpsC mode (mkFEnv env)) env p formerTys Mc tele majDom f)
      (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f) := by
  unfold targetK53
  repeat' split
  all_goals first
    | exact SimC.pure hs rfl
    | exact targetClassMatchS_sim hμ henv hformer hMc.1 hMc.2 hs

theorem targetK53AllS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {Mc : TargetMajor}
    (hMc : TargetMajScoped Mc) {tele : List (Expr × BinderMeta)} {majDom : Expr} {i : Nat} :
    ∀ (fwss : List (List Expr)) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (targetK53All (sharedOpsC mode (mkFEnv env)) env p formerTys Mc tele majDom i fwss)
        (targetK53All (fueledOpsM mode) env p formerTys Mc tele majDom i fwss)
  | [], _, hs => SimC.pure hs rfl
  | fws :: fwss, _, hs => by
    unfold targetK53All
    split
    · exact SimC.pure hs rfl
    · refine SimC.bind (targetK53S_sim hμ henv hformer hMc hs) (fun s₁ c c' hs₁ hC => ?_)
      obtain rfl : c = c' := hC
      cases c
      · exact SimC.pure hs₁ rfl
      · exact targetK53AllS_sim hμ henv hformer hMc fwss hs₁

/-- **The abstract fields' typing, simulated**: each annotation scoped at
its own position. -/
theorem targetAbsFieldsOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ (d : Nat) (l : List Expr) {s₀ : CState},
      (∀ j x, l[j]? = some x → WScoped (d + j) x.fvarTypeD) → CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w)
        (targetAbsFieldsOk (sharedOpsC mode (mkFEnv env)) env d l)
        (targetAbsFieldsOk (fueledOpsM mode) env d l)
  | _, [], _, _, hs => SimC.pure hs rfl
  | d, f :: fs, _, hl, hs => by
    unfold targetAbsFieldsOk
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs (by simpa using hl 0 f rfl))
      (fun s₁ _ _ hs₁ _ => ?_)
    exact targetAbsFieldsOkS_sim hμ henv (d + 1) fs
      (fun j x hx => by
        have := hl (j + 1) x (by simpa using hx)
        rwa [show d + (j + 1) = d + 1 + j from by omega] at this) hs₁

/-- **One call's typing, simulated**; the call's telescope is hole-free
(the check's first guard). -/
theorem targetCallOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {cn : Name}
    {fam : TargetFamily} (hmajs : ∀ M ∈ fam.majs, TargetMajScoped M)
    {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × BinderMeta))} {absM mvF : Expr → Expr} {base k dA : Nat}
    {pw : PropWhen} {fwss : List (List Expr)} {ih : TargetIh}
    (hpref : ∀ x ∈ fvsPref, WScoped base x) (hflds : ∀ x ∈ fvsF, WScoped base x)
    (htl : ∀ tele ∈ teles, ∀ b ∈ tele, WScoped (base + k) b.1)
    (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (hmvF : ∀ e, WScoped base e → WScoped dA (mvF (absM e)))
    (hmv : ∀ e, WScoped base e → WScoped dA (mvF e))
    (hidx : ∀ x ∈ ih.idx, WScoped base x)
    (hihTy : (∀ b ∈ teles.getD ih.field [], WScoped base b.1) → WScoped base ih.ty)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀
      (fun v w => v = w ∧ (teles.getD ih.field []).all (fun b => targetHoleFree base k b.1))
      (targetCallOk (sharedOpsC mode (mkFEnv env)) env p formerTys cn fam fvsPref fvsF
        teles absM mvF base k dA pw fwss ih)
      (targetCallOk (fueledOpsM mode) env p formerTys cn fam fvsPref fvsF teles absM mvF base
        k dA pw fwss ih) := by
  unfold targetCallOk
  dsimp only
  have htele : ∀ b ∈ teles.getD ih.field [], WScoped (base + k) b.1 := by
    intro b hb
    rw [List.getD_eq_getElem?_getD] at hb
    cases ht : teles[ih.field]? with
    | none => rw [ht] at hb; exact nomatch hb
    | some tele => rw [ht] at hb; exact htl tele (List.mem_of_getElem? ht) b hb
  by_cases h1 : ((teles.getD ih.field []).all fun b => targetHoleFree base k b.1) = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  have htele0 : ∀ b ∈ teles.getD ih.field [], WScoped base b.1 := by
    intro b hb
    exact WScoped.of_holeFree (htele b hb) (List.all_eq_true.mp h1 b hb)
  by_cases h2 : (ih.idx.all fun x => absM x == x) = true
  case neg => simp only [h2]; exact SimC.throw_bind
  simp only [h2, if_true]
  have hrecC : WScoped 0 (fam.recTys.getD ih.callee (.sort .zero)) := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : fam.recTys[ih.callee]? with
    | none => simp [WScoped]
    | some t => exact hrec t (List.mem_of_getElem? hx)
  split
  case h_2 => exact SimC.throw
  rename_i calleeAt hcallee
  split
  case h_2 => exact SimC.throw
  rename_i majDom mb mbm
  have hwC : WScoped base (Expr.forallE majDom mb mbm) :=
    instPisAtLift_WScoped hcallee (ws_of_ws0 hrecC) (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact hpref a ha
      · exact hidx a ha)
  simp only [WScoped] at hwC
  have hfF : WScoped base (fvsF.getD ih.field default) := getD_WScoped hflds _
  dsimp only [sharedOpsC]
  have hfld : WScoped dA (mvF (absM (fvsF.getD ih.field default).fvarTypeD)) :=
    hmvF _ (fvarTypeD_WScoped hfF)
  refine SimC.bind (opE_infer_sim hμ henv hs hfld) (fun s₁ _ _ hs₁ _ => ?_)
  have hwant : WScoped dA (Expr.mkPisOf ((teles.getD ih.field []).map fun b => (mvF b.1, b.2))
      (mvF (absM majDom))) := by
    refine mkPisOf_WScoped (fun b hb => ?_) (hmvF _ hwC.1)
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact hmv _ (htele0 b' hb')
  refine SimC.bind (opE_infer_sim hμ henv hs₁ hwant) (fun s₂ _ _ hs₂ _ => ?_)
  refine SimC.bind (opB_sim hμ henv hs₂ hfld hwant) (fun s₃ b b' hs₃ hB => ?_)
  obtain rfl : b = b' := hB
  cases b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  have hlam : WScoped (base + 1) (Expr.mkLamsOf ((teles.getD ih.field []).map fun b => (b.1, ⟨pw⟩))
      (Expr.mkAppN (.fvar base (fam.recTys.getD ih.callee (.sort .zero)))
        (fvsPref ++ ih.idx ++
          [Expr.mkAppN (fvsF.getD ih.field default)
            (structTeleVars (teles.getD ih.field []).length)]))) := by
    refine mkLamsOf_WScoped ?_ ?_
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      exact (htele0 b' hb').mono (by omega)
    · refine Expr.WScoped.mkAppN ?_ ?_
      · simp only [WScoped]
        exact ⟨by omega, ws_of_ws0 hrecC⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with (ha | ha) | rfl
        · exact (hpref a ha).mono (by omega)
        · exact (hidx a ha).mono (by omega)
        · exact (Expr.WScoped.mkAppN hfF structTeleVars_WScoped).mono (by omega)
  refine SimC.bind (opE_infer_sim hμ henv hs₃ hlam) (fun s₄ cT cT' hs₄ hC => ?_)
  obtain ⟨rfl, hwcT⟩ := hC
  have hwih := hihTy htele0
  refine SimC.bind (opE_infer_sim hμ henv hs₄ hwih) (fun s₅ _ _ hs₅ _ => ?_)
  refine SimC.bind (opB_sim hμ henv hs₅ hwcT (hwih.mono (by omega)))
    (fun s₆ b b' hs₆ hB => ?_)
  obtain rfl : b = b' := hB
  cases b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (targetK53AllS_sim hμ henv hformer (TargetMajScoped.getD hmajs ih.callee) _ hs₆)
    (fun s₇ c c' hs₇ hC => ?_)
  obtain rfl : c = c' := hC
  split
  · exact SimC.pure hs₇ (by simp [h1])
  · exact SimC.throw

theorem targetCallsOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {cn : Name}
    {fam : TargetFamily} (hmajs : ∀ M ∈ fam.majs, TargetMajScoped M)
    {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × BinderMeta))} {absM mvF : Expr → Expr} {base k dA : Nat}
    {pw : PropWhen} {fwss : List (List Expr)}
    (hpref : ∀ x ∈ fvsPref, WScoped base x) (hflds : ∀ x ∈ fvsF, WScoped base x)
    (htl : ∀ tele ∈ teles, ∀ b ∈ tele, WScoped (base + k) b.1)
    (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (hmvF : ∀ e, WScoped base e → WScoped dA (mvF (absM e)))
    (hmv : ∀ e, WScoped base e → WScoped dA (mvF e)) :
    ∀ {ihs : List TargetIh} {s₀ : CState},
      (∀ ih ∈ ihs, (∀ x ∈ ih.idx, WScoped base x) ∧
        ((∀ b ∈ teles.getD ih.field [], WScoped base b.1) → WScoped base ih.ty)) →
      CSOK mode env s₀ →
      SimC mode env s₀
        (fun v w => v = w ∧
          ∀ ih ∈ ihs, (teles.getD ih.field []).all (fun b => targetHoleFree base k b.1) = true)
        (targetCallsOk (sharedOpsC mode (mkFEnv env)) env p formerTys cn fam fvsPref fvsF
          teles absM mvF base k dA pw fwss ihs)
        (targetCallsOk (fueledOpsM mode) env p formerTys cn fam fvsPref fvsF teles absM mvF
          base k dA pw fwss ihs)
  | [], s₀, _, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | ih :: ihs, s₀, hih, hs => by
    unfold targetCallsOk
    obtain ⟨hidx, hty⟩ := hih ih List.mem_cons_self
    refine SimC.bind (targetCallOkS_sim hμ henv hformer hmajs hpref hflds htl hrec hmvF hmv hidx
      hty hs)
      (fun s₁ _ _ hs₁ hP => ?_)
    obtain ⟨-, hh⟩ := hP
    refine SimC.mono ?_ (targetCallsOkS_sim hμ henv hformer hmajs hpref hflds htl hrec hmvF hmv
      (fun x hx => hih x (List.mem_cons_of_mem _ hx)) hs₁)
    rintro v w ⟨rfl, hall⟩
    refine ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh
    · exact hall x hx

end Sims

/-! ### The rule stage: two environments, one state (`SimG`, `BlockRunC.lean`) -/

/-- **One rule, simulated.**  From any residue: the right-hand side
annotated and typed at the rule-less recursors' environment `envR`
(`sharedOpsRuleR`'s flushes on either side), then the domains' defeq,
the fields' whnf-telescopes, the calls' typing, the residue's inference
and the conclusion's defeq at the constructors' `envT`, every input
scoped at the frame it is run at. -/
theorem targetRuleS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr} {M : TargetMajor}
    {c : ConstantVal × Nat} {rhs : Expr}
    (hrecTy : WScoped 0 recTy) (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (hmajs : ∀ M ∈ fam.majs, TargetMajScoped M)
    (hformer : ∀ t ∈ formerTys, WScoped 0 t) (hctor : WScoped 0 (targetCtorAt M c.1))
    (hds : ∀ x ∈ M.ds, WScoped rP x) :
    SimG CSOKF (CSOK mode envT) RelVC
      (targetRule (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envR)
        (sharedOpsC mode (mkFEnv envT)) (mkFEnv envT) p formerTys fam cvR rP recTy M c rhs)
      (targetRule (fueledOpsM mode) .plain (mkFEnv envR) (fueledOpsM mode) (mkFEnv envT) p
        formerTys fam cvR rP recTy M c rhs) := by
  unfold targetRule
  simp only [mkFEnv_env]
  by_cases h1 : looseBVarsBounded 0 rhs = true
  case neg => simp only [h1]; exact SimG.throw_bind
  simp only [h1, if_true]
  by_cases h2 : rhs.hasFvar = true
  case pos => simp only [h2, if_true]; exact SimG.throw_bind
  simp only [h2]
  have hwrhs : WScoped 0 rhs := WScoped.of_not_hasFvar (by simpa using h2)
  refine SimG.bind (ruleR_annotate_simG hμ henvR hwrhs) (fun rhsA rhsA' hA => ?_)
  obtain ⟨rfl, hwA⟩ := hA
  by_cases h3 : allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => simp only [h3]; exact SimG.throw_bind
  simp only [h3, if_true]
  by_cases h4 : StructWalkers.plain.resolve (mkFEnv envR) rhsA = true
  case neg => simp only [h4]; exact SimG.throw_bind
  simp only [h4, if_true]
  refine SimG.bind (ruleR_infer_simG hμ henvR envT hwA) (fun _ _ _ => ?_)
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun x x' hX => ?_)
  obtain ⟨rfl, hx⟩ := hX
  obtain ⟨rbs, body⟩ := x
  dsimp only
  by_cases h5 : (rbs.all fun b => b.2.pw == (structElimLevel p.elim p.large).zeronessOf) = true
  case neg => simp only [h5]; exact SimG.throw_bind
  simp only [h5, if_true]
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun y y' hY => ?_)
  obtain ⟨rfl, hy⟩ := hY
  obtain ⟨fvsPref, oPref⟩ := y
  dsimp only
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun crest crest' hC => ?_)
  obtain ⟨rfl, hcrest⟩ := hC
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun z z' hZ => ?_)
  obtain ⟨rfl, hz⟩ := hZ
  obtain ⟨fvsF, cbody⟩ := z
  dsimp only
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun ld ld' hL => ?_)
  obtain ⟨rfl, hld⟩ := hL
  obtain ⟨ldoms, lrest⟩ := ld
  dsimp only
  -- the frame's scoping
  have hwy : ∀ a ∈ fvsPref, WScoped rP a := by
    have := (openPisAtFvars_WScoped _ _ 0 hy hrecTy).1
    simpa using this
  have hwcrest : WScoped rP crest := instPisWith_WScoped hcrest (ws_of_ws0 hctor) hds
  have hwz := openPisAtFvars_WScoped _ _ _ hz hwcrest
  have hD : ∀ a ∈ fvsPref ++ fvsF, WScoped (rP + c.2) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hwy a ha).mono (by omega)
    · exact hwz.1 a ha
  have hwld := instLamsAt_WScoped (d := rP + c.2) _ _ hld (ws_of_ws0 hwA) hD
  by_cases h6 : (ldoms.all fun t => StructWalkers.plain.resolve (mkFEnv envT) t) = true
  case neg => simp only [h6]; exact SimG.throw_bind
  simp only [h6, if_true]
  refine SimG.bind (SimG.ofC (fun s hs => checkBlockDefEqListS_sim hμ henvT ?_ hs))
    (fun _ _ _ => ?_)
  · intro i a b ha hb
    rw [List.getElem?_map] at ha
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨fvarTypeD_WScoped (hD a' (List.mem_of_getElem? ha')),
      hwld.1 b (List.mem_of_getElem? hb)⟩
  -- the member abstraction and the fields' whnf-telescopes
  have hholes := targetHoles_WScoped hformer (rP + c.2)
  have habs : ∀ e, WScoped (rP + c.2 + formerTys.length) e →
      WScoped (rP + c.2 + formerTys.length)
        (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)) e) :=
    targetAbs_WScoped hholes
  refine SimG.bind (SimG.ofC (fun s hs => targetFieldNormsS_sim hμ henvT
    (fun f hf => habs _ ((fvarTypeD_WScoped (hwz.1 f hf)).mono (by omega))) hs))
    (fun fnorm fnorm' hN => ?_)
  obtain ⟨rfl, hfn⟩ := hN
  by_cases h7 : (fnorm.all fun t => t.allLevelParamsDefined cvR.levelParams) = true
  case neg => simp only [h7]; exact SimG.throw_bind
  simp only [h7, if_true]
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun o o' hO => ?_)
  obtain ⟨rfl, ho⟩ := hO
  obtain ⟨bodyO, ihs⟩ := o
  dsimp only
  -- the residue's scoping
  have hbody : body.hasFvar = false :=
    (stripLams_not_hasFvar _ hx (ws0_hasFvar hwA)).2
  have hbodyF : WScoped (rP + c.2)
      (body.instantiateList (fvsPref ++ fvsF).reverse 0) :=
    instantiateList_WScoped (fun v hv => hD v (List.mem_reverse.mp hv))
      (WScoped.of_not_hasFvar hbody)
  obtain ⟨-, -, hnew, hres⟩ := targetAbstract_scope 0 _ #[] bodyO ihs ho hbodyF
    (fun r h => absurd h (by simp))
  have htl : ∀ tele ∈ fnorm.map (fun t => t.piBinders.1), ∀ b ∈ tele,
      WScoped (rP + c.2 + formerTys.length) b.1 := by
    intro tele ht b hb
    obtain ⟨t, htm, rfl⟩ := List.mem_map.mp ht
    exact (piBinders_WScoped (hfn t htm)).1 b hb
  have hihs : ∀ ih ∈ ihs.toList, (∀ x ∈ ih.idx, WScoped (rP + c.2) x) ∧
      ((∀ b ∈ (fnorm.map fun t => t.piBinders.1).getD ih.field [],
          WScoped (rP + c.2) b.1) → WScoped (rP + c.2) ih.ty) := by
    intro ih hih
    rcases hnew ih hih with h | ⟨hty, hidx⟩
    · exact nomatch h
    · exact ⟨hidx, fun htele => targetIhTy_WScoped hty htele
        (fun a ha => (hwy a ha).mono (by omega)) hidx hwz.1 hrec⟩
  -- the abstract fields, scoped at their positions past the holes
  have hlf : fvsF.length = c.2 := ConLeche.Verify.openPisAtFvars_length _ hz
  have hfvsA : ∀ j x, (if ihs.isEmpty = true then [] else
      targetAbsFields p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)) rP
        (rP + c.2 + formerTys.length) [] fvsF)[j]? = some x →
      j < c.2 ∧ ∃ ty, x = .fvar (rP + c.2 + formerTys.length + j) ty ∧
        WScoped (rP + c.2 + formerTys.length + j) ty := by
    intro j x hx
    split at hx
    · exact nomatch hx
    have hj : j < fvsF.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rwa [(targetAbsFields_nil fvsF).1] at this
    obtain ⟨ty, hty, hw⟩ := targetAbsFields_WScoped (names := p.memberNames)
      (lvls := p.lps.map .param) (rP := rP) hholes
      (fun f hf => (fvarTypeD_WScoped (hwz.1 f hf)).mono (by omega)) j hj
    rw [hty] at hx
    exact ⟨by omega, ty, (Option.some.inj hx).symm, hw⟩
  refine SimG.bind (SimG.ofC (fun s hs => targetAbsFieldsOkS_sim hμ henvT _ _
    (fun j x hx => by
      obtain ⟨-, ty, rfl, hw⟩ := hfvsA j x hx
      exact hw) hs))
    (fun u u' hU => ?_)
  obtain rfl : u = u' := hU
  have hmvF : ∀ e, WScoped (rP + c.2) e →
      WScoped (rP + c.2 + formerTys.length + c.2)
        (targetMoveF rP
          (if ihs.isEmpty = true then [] else
            targetAbsFields p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2))
              rP (rP + c.2 + formerTys.length) [] fvsF)
          (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)) e)) := by
    intro e he
    refine targetMoveF_WScoped (fun x hx => ?_)
      ((targetAbs_WScoped hholes _ (he.mono (by omega))).mono (by omega))
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
    obtain ⟨hjc, ty, rfl, hw⟩ := hfvsA j x (by rw [List.getElem?_eq_getElem hj, hget])
    simp only [WScoped]
    exact ⟨by omega, hw⟩
  have hmv : ∀ e, WScoped (rP + c.2) e →
      WScoped (rP + c.2 + formerTys.length + c.2)
        (targetMoveF rP
          (if ihs.isEmpty = true then [] else
            targetAbsFields p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2))
              rP (rP + c.2 + formerTys.length) [] fvsF) e) := by
    intro e he
    refine targetMoveF_WScoped (fun x hx => ?_) (he.mono (by omega))
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
    obtain ⟨hjc, ty, rfl, hw⟩ := hfvsA j x (by rw [List.getElem?_eq_getElem hj, hget])
    simp only [WScoped]
    exact ⟨by omega, hw⟩
  refine SimG.bind (SimG.ofC (fun s hs => targetCallsOkS_sim (cn := c.1.name) (pw :=
    Level.zeronessOf (structElimLevel p.elim p.large)) hμ henvT hformer hmajs
    (fun a ha => (hwy a ha).mono (by omega)) hwz.1 htl hrec hmvF hmv hihs hs))
    (fun u u' hU => ?_)
  obtain ⟨-, hfree⟩ := hU
  have hwO : WScoped (rP + c.2 + ihs.size) bodyO := by
    refine hres fun ih hih => ?_
    obtain ⟨-, hty⟩ := hihs ih hih
    refine hty fun b hb => ?_
    have hb' := hb
    rw [List.getD_eq_getElem?_getD] at hb'
    cases ht : (fnorm.map fun t => t.piBinders.1)[ih.field]? with
    | none => rw [ht] at hb'; exact nomatch hb'
    | some tele =>
      rw [ht] at hb'
      exact WScoped.of_holeFree (htl tele (List.mem_of_getElem? ht) b hb')
        (List.all_eq_true.mp (hfree ih hih) b hb)
  dsimp only [sharedOpsC]
  refine SimG.bind (SimG.ofC (fun s hs => opE_infer_sim hμ henvT hs hwO))
    (fun tyB tyB' hT => ?_)
  obtain ⟨rfl, hwT⟩ := hT
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun cc cc' hC => ?_)
  obtain ⟨rfl, hcc⟩ := hC
  have hwcc : WScoped (rP + c.2 + ihs.size) cc := by
    refine instPisAtLift_WScoped hcc (ws_of_ws0 hrecTy) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact (hwy a ha).mono (by omega)
    · exact (Expr.WScoped.getAppArgs hwz.2 a (List.mem_of_mem_drop ha)).mono (by omega)
    · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hds x hx).mono (by omega)
      · exact (hwz.1 x hx).mono (by omega)
  refine SimG.bind (SimG.ofC (fun s hs => opB_sim hμ henvT hs hwT hwcc))
    (fun r r' hr => ?_)
  obtain rfl : r = r' := hr
  cases r with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimG.throw_bind
  | true => simp only [↓reduceIte]; exact SimG.pure (fun _ h => h) rfl

theorem targetRulesS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {cvRi : ConstantVal} {rP : Nat} {M : TargetMajor}
    (hrecTy : WScoped 0 cvRi.type) (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (hmajs : ∀ M ∈ fam.majs, TargetMajScoped M)
    (hformer : ∀ t ∈ formerTys, WScoped 0 t) (hds : ∀ x ∈ M.ds, WScoped rP x) :
    ∀ {cs : List (ConstantVal × Nat)} {rhss : List Expr},
      (∀ cA ∈ cs, WScoped 0 (targetCtorAt M cA.1)) →
      SimG CSOKF CSOKF RelVC
        (targetRules (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envR)
          (sharedOpsC mode (mkFEnv envT)) (mkFEnv envT) p formerTys fam cvRi rP M cs rhss)
        (targetRules (fueledOpsM mode) .plain (mkFEnv envR) (fueledOpsM mode) (mkFEnv envT) p
          formerTys fam cvRi rP M cs rhss)
  | [], [], _ => SimG.pure (fun _ h => h) rfl
  | [], _ :: _, _ => SimG.throw
  | _ :: _, [], _ => SimG.throw
  | cA :: cs, rhs :: rhss, hc => by
    unfold targetRules
    refine SimG.bind ((targetRuleS_simG hμ henvR henvT hrecTy hrec hmajs hformer
      (hc cA List.mem_cons_self) hds).mono (fun _ h => h) (fun _ h => h.residue))
      (fun r r' hr => ?_)
    obtain rfl : r = r' := hr
    refine SimG.bind (targetRulesS_simG hμ henvR henvT hrecTy hrec hmajs hformer hds
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))) (fun rest rest' hrest => ?_)
    obtain rfl : rest = rest' := hrest
    exact SimG.pure (fun _ h => h) rfl

/-- What the rule stage needs of each checked recursor: its type
fvar-free, its major's constructors fvar-free at the major's levels,
and the major's parameters scoped by the recursor's prefix. -/
def TargetTyScoped (rc : RecShape) (t : ConstantVal × TargetMajor × Level) : Prop :=
  WScoped 0 t.1.type ∧ (∀ cA ∈ t.2.1.ctors, WScoped 0 (targetCtorAt t.2.1 cA.1)) ∧
    ∀ x ∈ t.2.1.ds, WScoped rc.rP x

theorem targetRecsRulesS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (hmajs : ∀ M ∈ fam.majs, TargetMajScoped M)
    (hformer : ∀ t ∈ formerTys, WScoped 0 t) :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      (∀ (j : Nat) (rc : RecShape) t, recs[j]? = some rc → tys[j]? = some t →
        TargetTyScoped rc t) →
      SimG CSOKF CSOKF RelVC
        (targetRecsRules (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envR)
          (sharedOpsC mode (mkFEnv envT)) (mkFEnv envT) p formerTys fam recs tys)
        (targetRecsRules (fueledOpsM mode) .plain (mkFEnv envR) (fueledOpsM mode)
          (mkFEnv envT) p formerTys fam recs tys)
  | [], _, _ => SimG.pure (fun _ h => h) rfl
  | _ :: _, [], _ => SimG.pure (fun _ h => h) rfl
  | rc :: rcs, (cvRi, M, u) :: ts, hsc => by
    unfold targetRecsRules
    dsimp only
    obtain ⟨hw1, hw2, hw3⟩ := hsc 0 rc _ rfl rfl
    split
    case isFalse => exact SimG.throw_bind
    refine SimG.bind (targetRulesS_simG hμ henvR henvT hw1 hrec hmajs hformer hw3 hw2)
      (fun rh rh' hR => ?_)
    obtain rfl : rh = rh' := hR
    refine SimG.bind (targetRecsRulesS_simG hμ henvR henvT hrec hmajs hformer
      (fun j rc' t hj ht => hsc (j + 1) rc' t (by simpa using hj) (by simpa using ht)))
      (fun rest rest' hrest => ?_)
    obtain rfl : rest = rest' := hrest
    exact SimG.pure (fun _ h => h) rfl

/-! ## 3. The assembly -/

/-- `SimG.bind` that remembers the first component's fueled run. -/
theorem SimG.bindR {A B C : CState → Prop} {β β' α α' : Type} {P : β → α → Prop}
    {Q : β' → α' → Prop} {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α}
    {q : α → FueledM α'} (hx : SimG A B P c p)
    (hf : ∀ b a, P b a → (∃ F, p.val F = .ok a) → SimG B C Q (k b) (q a)) :
    SimG A C Q (c >>= k) (p >>= q) := by
  intro s₀ hs v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx s₀ hs b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf b a hP ⟨F₁, hp₁⟩ s₁ hs₁ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- The stage's closing flush: the pure side's is no operation. -/
theorem flushC_simG : SimG CSOKF CSOKF RelVC flushC (Pure.pure () : FueledM Unit) := by
  intro s₀ hs v' s' hr
  rw [flushC_run] at hr
  injection hr with hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs.flushed, (), rfl, 0, rfl⟩

/-- A flush into any environment's invariant. -/
theorem flushC_simG_to {A : CState → Prop} (hA : ∀ s, A s → CSOKF s) (env' : Env) :
    SimG A (CSOK mode env') RelVC flushC (Pure.pure () : FueledM Unit) := by
  intro s₀ hs v' s' hr
  rw [flushC_run] at hr
  injection hr with hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨flushC_csok (hA s₀ hs), (), rfl, 0, rfl⟩

/-- The shared operations read the index only through `find?`
(`coreKnotI_congr`). -/
theorem sharedOpsC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    sharedOpsC mode fe₁ = sharedOpsC mode fe₂ := by
  unfold sharedOpsC opE opB opS
  simp only [coreKnotI_congr hfe]

/-- Every class's recorded normal forms, at the shared operations. -/
theorem targetMajorsNfsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {tbl : List NestCtorNf} :
    ∀ (tys : List (ConstantVal × TargetMajor × Level)) {s₀ : CState}, CSOK mode env s₀ →
      (∀ t ∈ tys, TargetMajScoped t.2.1) →
      SimC mode env s₀ RelVC
        (targetMajorsNfs (sharedOpsC mode (mkFEnv env)) env p formerTys tbl tys)
        (targetMajorsNfs (fueledOpsM mode) env p formerTys tbl tys)
  | [], _, hs, _ => SimC.pure hs rfl
  | (cv, M, u) :: ts, _, hs, hsc => by
    unfold targetMajorsNfs
    obtain ⟨hp, hds⟩ := hsc _ List.mem_cons_self
    refine SimC.bind (targetMajorNfsS_sim hμ henv hformer hp hds tbl hs)
      (fun s₁ r r' hs₁ hR => ?_)
    obtain rfl : r = r' := hR
    refine SimC.bind (targetMajorsNfsS_sim hμ henv hformer ts hs₁
      (fun t ht => hsc t (List.mem_cons_of_mem _ ht))) (fun s₂ r r' hs₂ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₂ rfl

/-- What the rule stage needs of a checked recursor, off its type run. -/
theorem TargetTyEntry.scoped {F : Nat} {env : Env} (henv : EnvWF env) {p : BlockShape}
    {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F (mkFEnv env) p nested cvTas ctorsAs rc cvRi M u)
    (hw : WScoped 0 cvRi.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) :
    TargetTyScoped rc (cvRi, M, u) := by
  obtain ⟨_, fvs, _, _, _, maj, _, _, _, hroom, hle, hopen, hmaj, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar =>
    refine ⟨hw, fun cA hcA => ?_, ?_⟩
    · simp only [targetCtorAt]
      exact hct _ (List.mem_of_getElem? hctors) cA hcA
    · intro x hx
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have hil : i < p.nP := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp only [List.length_take] at this; omega
      rw [List.getElem?_take, if_pos hil] at hi
      exact (openers_WScoped_at hopen hw i x hi).mono (by omega)
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hinst hsort =>
    refine ⟨hw, fun cA hcA => ?_, ?_⟩
    · simp only [targetCtorAt]
      refine WScoped.of_not_hasFvar ?_
      rw [Expr.hasFvar_instantiateLevelParams]
      have hctx : NestCtxOk ⟨[], [], 0, [], [], .zero, (mkFEnv env).find?,
          (mkFEnv env).env.consts⟩ := by
        rw [mkFEnv_find?_fun, mkFEnv_env]
        exact ⟨fun ci hci => (henv ci hci).1,
          fun n ci hf => (henv ci (List.mem_of_find?_eq_some hf)).1⟩
      exact nestContainer_closed hctx hctors cA hcA
    · intro x hx
      have hmajW : WScoped rc.mI maj.fvarTypeD := by
        have := openers_typeD_WScoped hopen hw rc.mI maj hmaj
        rwa [Nat.zero_add] at this
      obtain ⟨-, hfb⟩ := hdsSc x hx
      exact (ConLeche.WScoped.of_fvarsBelow
        (Expr.WScoped.getAppArgs hmajW x (List.mem_of_mem_take hx))
        (ConLeche.Expr.fvarB_le hfb)).mono (by omega)

/-- A checked recursor's class is scoped by the block's parameters. -/
theorem TargetTyEntry.majScoped {F : Nat} {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F (mkFEnv env) p nested cvTas ctorsAs rc cvRi M u)
    (hw : WScoped 0 cvRi.type) : TargetMajScoped M := by
  obtain ⟨_, fvs, _, _, _, maj, _, _, _, hroom, hle, hopen, hmaj, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  have hxl : fvs.length = rc.mI + 1 := ConLeche.Verify.openPisAtFvars_length _ hopen
  have hpl : (fvs.take rc.rP).length = rc.rP := by rw [List.length_take]; omega
  have hpf : ∀ x ∈ fvs.take rc.rP, WScoped rc.rP x := openers_take_WScoped hopen hw rc.rP
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar =>
    refine ⟨by rw [hpl]; exact hpf, ?_⟩
    rw [hpl]; exact fun x hx' => (openers_take_WScoped hopen hw p.nP x hx').mono hroom
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hinst hsort =>
    refine ⟨by rw [hpl]; exact hpf, fun x hx => ?_⟩
    have hmajW : WScoped rc.mI maj.fvarTypeD := by
      have := openers_typeD_WScoped hopen hw rc.mI maj hmaj
      rwa [Nat.zero_add] at this
    rw [hpl]
    exact (ConLeche.WScoped.of_fvarsBelow
      (Expr.WScoped.getAppArgs hmajW x (List.mem_of_mem_take hx))
      (ConLeche.Expr.fvarB_le (hdsSc x hx).2)).mono hroom

/-- **The target recursor check at the cached driver, simulated**: from
an invariant state of the constructors' environment to a residue.  The
seeds are walked at a view of the index that looks names up as the
formers' environment (`hfe₁`), from a flushed state, the walk's state
`pos` closed (`NestStOk`). -/
theorem targetRecCheckS_simG (hμ : mode.verifiedChecks = true) {env₁ env₂ : Env} {fe₁ : FEnv}
    (henv₁ : EnvWF env₁) (henv₂ : EnvWF env₂) (hfe₁ : fe₁.find? = (mkFEnv env₁).find?)
    {p : BlockShape} {nested : Bool} {pos : NestState}
    (hpos : NestStOk pos) {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) :
    SimG (CSOK mode env₂) CSOKF RelVC
      (targetRecCheck (shadowOpsC mode) fe₁ env₁ (mkFEnv env₂) p nested pos block cvTas
        ctorsAs)
      (targetRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe₁ env₁ (mkFEnv env₂) p nested
        pos block cvTas ctorsAs) := by
  unfold targetRecCheck
  have hso : ∀ fe, (shadowOpsC mode).opsAt fe = sharedOpsC mode fe := fun _ => rfl
  have hsf : (shadowOpsC mode).flush = flushC := rfl
  have hsw : (shadowOpsC mode).walkers = structWalkersC := rfl
  have hsr : ∀ fe, (shadowOpsC mode).opsRuleR fe = sharedOpsRuleR mode fe := fun _ => rfl
  have hpo : ∀ fe, (ShadowOps.ofOps (fueledOpsM mode)).opsAt fe = fueledOpsM mode :=
    fun _ => rfl
  have hpr : ∀ fe, (ShadowOps.ofOps (fueledOpsM mode)).opsRuleR fe = fueledOpsM mode :=
    fun _ => rfl
  have hpw : (ShadowOps.ofOps (fueledOpsM mode)).walkers = .plain := rfl
  have hpf : (ShadowOps.ofOps (fueledOpsM mode)).flush = (Pure.pure () : FueledM Unit) := rfl
  simp only [hso, hsf, hsw, hsr, hpo, hpr, hpw, hpf, structWalkersC_eq_plain, mkFEnv_env,
    consBlockRecsBareF_mkFEnv]
  rw [sharedOpsC_congr hfe₁, hfe₁, mkFEnv_find?_fun]
  refine SimG.bind (SimG.ofC fun s hs => targetRecPinsS_sim hs) fun _ _ _ => ?_
  refine SimG.bindR (SimG.ofC fun s hs => targetRecTysS_sim hμ henv₂ hT hs)
    fun tys₀ tys₀' hP hrun => ?_
  obtain ⟨rfl, hwR₀⟩ := hP
  obtain ⟨F, hF⟩ := hrun
  rw [targetRecTys_datF] at hF
  obtain ⟨hlenT₀, hallT₀⟩ := targetRecTys_run hF
  have hentry₀ : ∀ t ∈ tys₀, ∃ rc, Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas
      ctorsAs rc t.1 t.2.1 t.2.2) := by
    intro t ht
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
    have hjl : j < p.recs.length := by
      rw [← hlenT₀]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨cvRi, M, u, ht', E⟩ := hallT₀ j _ (List.getElem?_eq_getElem hjl)
    rw [hj] at ht'
    obtain rfl := Option.some.inj ht'
    exact ⟨_, E⟩
  have hformer : ∀ t ∈ cvTas.map (·.type), WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  -- the seeds, at the formers' environment
  refine SimG.bind (flushC_simG_to (mode := mode) (fun s h => (h : CSOK mode env₂ s).residue) env₁)
    fun _ _ _ => ?_
  refine SimG.bind (SimG.ofC fun s hs => checkBlockSeedsS_sim hμ henv₁ p cvTas pos
    tys₀ hT (fun t ht hM x hx => by
      obtain ⟨rc, ⟨E⟩⟩ := hentry₀ t ht
      obtain ⟨-, -, -, -, -, -, -, hsc, -⟩ := E.outside_of hM
      exact (hsc x hx).2) hpos hs) fun tbl tbl' hR => ?_
  obtain rfl : tbl = tbl' := hR
  refine SimG.bind (flushC_simG_to (mode := mode) (fun s h => (h : CSOK mode env₁ s).residue) env₂)
    fun _ _ _ => ?_
  -- every class's recorded normal forms
  refine SimG.bindR (SimG.ofC fun s hs => targetMajorsNfsS_sim hμ henv₂ hformer tys₀ hs
    (fun t ht => by
      obtain ⟨rc, ⟨E⟩⟩ := hentry₀ t ht
      exact TargetTyEntry.majScoped E (hwR₀ t ht))) fun tys tys' hP hrun => ?_
  obtain rfl : tys = tys' := hP
  obtain ⟨F', hF'⟩ := hrun
  rw [targetMajorsNfs_datF] at hF'
  obtain ⟨hlenN, hallN⟩ := targetMajorsNfs_run hF'
  have hlenT : tys.length = p.recs.length := by rw [hlenN, hlenT₀]
  have hallT : ∀ (i : Nat) (rc : RecShape), p.recs[i]? = some rc →
      ∃ cvRi M u, tys[i]? = some (cvRi, M, u) ∧
        Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas ctorsAs rc cvRi M u) := by
    intro i rc hi
    obtain ⟨cvRi, M, u, hti, ⟨E⟩⟩ := hallT₀ i rc hi
    obtain ⟨nfs', htn, -⟩ := hallN i _ hti
    exact ⟨cvRi, { M with nfs := nfs' }, u, htn, ⟨E.withNfs nfs'⟩⟩
  have hwR : ∀ q ∈ tys, WScoped 0 q.1.type := by
    intro q hq
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    have hi₀ : i < tys₀.length := by rw [← hlenN]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨nfs', htn, -⟩ := hallN i _ (List.getElem?_eq_getElem hi₀)
    rw [hi] at htn
    obtain rfl := Option.some.inj htn
    exact (hwR₀ _ (List.getElem_mem hi₀) : WScoped 0 tys₀[i].1.type)
  refine SimG.bind (SimG.ofC fun s hs => checkBlockRecSmallElimS_sim hs) fun _ _ _ => ?_
  refine SimG.bind (SimG.ofC fun s hs => checkBlockRecElimPinS_sim hs) fun _ _ _ => ?_
  refine SimG.bind (SimG.ofC fun s hs => checkBlockRecPrefixAgreeS_sim hμ henv₂ ?_ hs)
    fun _ _ _ => ?_
  · intro cv hcv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv
    exact hwR q hq
  refine SimG.bind (SimG.ofC fun s hs => targetRulePinsAllS_sim hs _ _) fun _ _ _ => ?_
  have hentry : ∀ (j : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
      p.recs[j]? = some rc → tys[j]? = some t →
      Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas ctorsAs rc t.1 t.2.1
        t.2.2) := by
    intro j rc t hj ht
    obtain ⟨cvRi, M, u, ht', E⟩ := hallT j rc hj
    rw [ht] at ht'
    obtain rfl := Option.some.inj ht'
    exact E
  have henvR : EnvWF (consBlockRecsBare p 0 (tys.map fun t => (t.1, t.2.1.nIdx)) env₂) := by
    refine envWF_consBlockRecsBare henv₂ fun c hc => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
    have hjl : j < p.recs.length := by
      rw [← hlenT]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨E⟩ := hentry j _ t (List.getElem?_eq_getElem hjl) hj
    have hcv := E.hcv
    rw [checkConstantValF_eq] at hcv
    exact checkConstantVal_typeWF hcv
  have hsc : ∀ (j : Nat) (rc : RecShape) t, p.recs[j]? = some rc → tys[j]? = some t →
      TargetTyScoped rc t := by
    intro j rc t hj ht
    obtain ⟨E⟩ := hentry j rc t hj ht
    exact TargetTyEntry.scoped henv₂ E (hwR t (List.mem_of_getElem? ht)) hct
  have hrec : ∀ t ∈ (targetFamilyOf p tys).recTys, WScoped 0 t := by
    intro t ht
    simp only [targetFamilyOf, List.mem_map] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    exact hwR q hq
  have hmajs : ∀ M ∈ (targetFamilyOf p tys).majs, TargetMajScoped M := by
    intro M hM
    simp only [targetFamilyOf, List.mem_map] at hM
    obtain ⟨t, ht, rfl⟩ := hM
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
    have hjl : j < p.recs.length := by
      rw [← hlenT]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨E⟩ := hentry j _ t (List.getElem?_eq_getElem hjl) hj
    exact TargetTyEntry.majScoped E (hwR t ht)
  refine SimG.bind ((targetRecsRulesS_simG hμ henvR henv₂ hrec hmajs hformer hsc).mono
    (fun _ h => h.residue) (fun _ h => h)) fun out out' hO => ?_
  obtain rfl : out = out' := hO
  exact SimG.bind flushC_simG fun _ _ _ =>
    SimG.pure (fun _ h => h) rfl

/-- **The recursor stage's CHECK at the cached driver** is reproduced
by the pure fueled target check. -/
theorem targetRecCheckS_run (hμ : mode.verifiedChecks = true) {env₁ env₂ : Env} {fe₁ : FEnv}
    (henv₁ : EnvWF env₁) (henv₂ : EnvWF env₂) (hfe₁ : fe₁.find? = (mkFEnv env₁).find?)
    {p : BlockShape} {nested : Bool} {pos : NestState}
    (hpos : NestStOk pos) {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK mode env₂ s₀) {out : List (ConstantVal × TargetMajor × List Expr)}
    {s' : CState}
    (h : targetRecCheck (shadowOpsC mode) fe₁ env₁ (mkFEnv env₂) p nested pos block cvTas
      ctorsAs s₀ = .ok (out, s')) :
    CSOKF s' ∧ ∃ F, targetRecCheck (ShadowOps.fueled mode F) fe₁ env₁ (mkFEnv env₂) p nested
      pos block cvTas ctorsAs = .ok out := by
  obtain ⟨hs', out', rfl, F, hF⟩ :=
    targetRecCheckS_simG hμ henv₁ henv₂ hfe₁ hpos hT hct s₀ hs out s' h
  exact ⟨hs', F, by rw [← targetRecCheck_datF]; exact hF⟩

/-- The check reads its seeds' index only through `find?`. -/
theorem targetRecCheck_fe₁_congr {F : Nat} {fe₁ fe₁' : FEnv} (hfe : fe₁.find? = fe₁'.find?)
    (env₁ : Env) (fe : FEnv) (p : BlockShape) (nested : Bool)
    (pos : NestState) (block : List ConstantInfo)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    targetRecCheck (ShadowOps.fueled mode F) fe₁ env₁ fe p nested pos block cvTas ctorsAs
      = targetRecCheck (ShadowOps.fueled mode F) fe₁' env₁ fe p nested pos block cvTas
        ctorsAs := by
  unfold targetRecCheck
  simp only [ShadowOps.fueled, ShadowOps.ofOps]
  rw [hfe]

/-! ### The cons at the majors

The install conses the checked family with each recursor's rules
at ITS major (`consBlockRecsT`): at an outside major every rule fires
`.nested` as the recursor type's major domain reads (`auxRuleFireR`),
and `EnvWF`'s `.nested` clause is exactly that reading's inversion
(`nestedRuleSyn_inv`). -/

theorem consBlockRecsTF_mkFEnv (find? : Name → Option ConstantInfo) (res : Expr → Bool)
    (p : BlockShape) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      consBlockRecsTF find? res p m out (mkFEnv env) = mkFEnv (consBlockRecsT find? res p m out env)
  | _, [], _ => rfl
  | m, (cv, M, rhss) :: rest, env => by
    simp only [consBlockRecsTF, consBlockRecsT, push_mkFEnv]
    exact consBlockRecsTF_mkFEnv find? res p (m + 1) rest _

theorem find?_consBlockRecsT_le {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((consBlockRecsT find? res q m out env).find? n).isSome = true
  | _, [], _, _, h => h
  | _, _ :: _, env, n, h => by
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_le n ?_
    rw [Env.find?_cons]
    split <;> simp_all

theorem find?_consBlockRecsT_of_bare {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      ∀ n, ((consBlockRecsBare q m (out.map fun t => (t.1, t.2.1.nIdx)) envA).find? n).isSome
          = true →
        ((consBlockRecsT find? res q m out envB).find? n).isSome = true
  | _, [], _, _, hf, n, h => hf n h
  | m, (cv, M, rhss) :: rest, envA, envB, hf, n, h => by
    simp only [List.map_cons, consBlockRecsBare] at h
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_of_bare
      (envA := ⟨.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m) [] :: envA.consts⟩) ?_ n h
    exact find?_cons_mono rfl hf

theorem mem_consBlockRecsT {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env}
      {c : ConstantInfo},
      c ∈ (consBlockRecsT find? res q m out env).consts →
      c ∈ env.consts ∨ ∃ t ∈ out, ∃ j,
        c = .recInfo t.1 (q.majorIdxAt j) (q.rulePrefixAt j)
          (tgtStoredRules find? res t.1 (q.majorIdxAt j) (q.rulePrefixAt j) t.2.1 t.2.2)
  | _, [], _, _, h => Or.inl h
  | m, t0 :: rest, env, c, h => by
    simp only [consBlockRecsT] at h
    rcases mem_consBlockRecsT h with h' | ⟨t, ht, j, hj⟩
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨t0, List.mem_cons_self, m, rfl⟩
      · exact Or.inl h'
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, j, hj⟩

/-- **The family consed at its majors keeps well-formedness**
(`envWF_consBlockRecs` at the majors): the rules' right-hand
sides as there, and an outside major's `.nested` fire off
`nestedRuleSyn_inv`. -/
theorem envWF_consBlockRecsT {find? : Name → Option ConstantInfo} {q : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ t ∈ out, t.1.type.hasFvar = false ∧
      t.1.type.allLevelParamsDefined t.1.levelParams = true ∧
      t.1.type.constsResolve env = true ∧
      t.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ t.2.2, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined t.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare q 0 (out.map fun t => (t.1, t.2.1.nIdx)) env)
          = true ∧
        rhs.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecsT find? (·.constsResolve env) q 0 out env) := by
  have hdomEnv : ∀ n, (env.find? n).isSome = true →
      ((consBlockRecsT find? (·.constsResolve env) q 0 out env).find? n).isSome = true :=
    fun n hn => find?_consBlockRecsT_le n hn
  have hdomBare : ∀ n,
      ((consBlockRecsBare q 0 (out.map fun t => (t.1, t.2.1.nIdx)) env).find? n).isSome
        = true →
      ((consBlockRecsT find? (·.constsResolve env) q 0 out env).find? n).isSome = true :=
    find?_consBlockRecsT_of_bare (fun _ hn => hn)
  intro c hc
  rcases mem_consBlockRecsT hc with hc' | ⟨t, ht, j, rfl⟩
  · exact ConstWF.mono hdomEnv (henv c hc')
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hall t ht
    refine structConstWF h1 h2 (Expr.constsResolve_of_find hdomEnv h3) h4
      (fun _ _ _ heq => nomatch heq) ?_
    intro cvR' mI' rP' rules' heq rl hrl
    injection heq with e1 e2 e3 e4
    subst e1 e2 e3 e4
    unfold tgtStoredRules at hrl
    dsimp only at hrl
    cases hM : t.2.1.member with
    | some _ =>
      rw [hM] at hrl
      obtain ⟨hmem, hfire⟩ := sumRules_mem hrl
      obtain ⟨g1, g2, g3, g4⟩ := h5 rl.rhs hmem
      refine ⟨g1, g2, Expr.constsResolve_of_find hdomBare g3, g4, ?_⟩
      intro lvls pins hf
      exact absurd hf (hfire lvls pins)
    | none =>
      rw [hM] at hrl
      obtain ⟨rl₀, hrl₀, rfl⟩ := List.mem_map.mp hrl
      obtain ⟨hmem, -⟩ := sumRules_mem hrl₀
      obtain ⟨g1, g2, g3, g4⟩ := h5 rl₀.rhs hmem
      refine ⟨g1, g2, Expr.constsResolve_of_find hdomBare g3, g4, ?_⟩
      intro lvls pins hf
      simp only [auxRuleFireR] at hf
      split at hf
      · next lvls' pins' hsyn =>
        obtain ⟨rfl, rfl⟩ : lvls' = lvls ∧ pins' = pins := by
          injection hf with a b; exact ⟨a, b⟩
        obtain ⟨k1, k2, k3, k4⟩ := nestedRuleSyn_inv hsyn
        refine ⟨k1, k2, fun pin hpin => ?_, ?_⟩
        · obtain ⟨p1, p2, p3, p4⟩ := k3 pin hpin
          exact ⟨p1, p2, Expr.constsResolve_of_find hdomEnv p3, p4⟩
        · obtain ⟨pre, dom, body, bm, D, e1, e2, e3, -⟩ := k4
          exact ⟨pre, dom, body, bm, D, e1, e2, e3⟩
      · exact nomatch hf

/-- **The stored family's environment is well-formed**: every stored
recursor type is a checked constant's, every stored rule the annotated
stream right-hand side, resolved at the rule-less recursors' environment
(off the target check's run records). -/
theorem targetRecCheck_recsWF {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape}
    {nested : Bool} {fe₁ : FEnv} {env₁ : Env} {pos : NestState}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe₁ env₁ (mkFEnv env₂) p nested pos block
      cvTas ctorsAs = .ok out) (find? : Name → Option ConstantInfo) :
    EnvWF (consBlockRecsT find? (·.constsResolve env₂) p 0 out env₂) := by
  obtain ⟨R⟩ := targetRecCheck_run h
  obtain ⟨hlenT, hallT⟩ := R.tysRun
  obtain ⟨hlenO, hallO⟩ := targetRecsRules_run R.rules
  have hlenO' : out.length = R.tys.length := by rw [hlenO, hlenT, Nat.min_self]
  -- every stored entry is stage (b)'s recursor and major, with its rules
  have hat : ∀ (i : Nat) (o : ConstantVal × TargetMajor × List Expr), out[i]? = some o →
      ∃ rc t, p.recs[i]? = some rc ∧ R.tys[i]? = some t ∧ o.1 = t.1 ∧ o.2.1 = t.2.1 ∧
        Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas ctorsAs rc t.1 t.2.1
          t.2.2) ∧
        TargetRulesRun mode F (consBlockRecsBareF p 0 (R.tys.map fun t => (t.1, t.2.1.nIdx))
          (mkFEnv env₂)) (mkFEnv env₂) p (cvTas.map (·.type)) (targetFamilyOf p R.tys) t.1
          rc.rP t.2.1 t.2.1.ctors rc.rhss o.2.2 := by
    intro i o ho
    have hil : i < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp ho).1; omega
    obtain ⟨cvRi, M, u, ht, E⟩ := hallT i p.recs[i] (List.getElem?_eq_getElem hil)
    obtain ⟨rh, hoi, -, RR⟩ := hallO i p.recs[i] _ (List.getElem?_eq_getElem hil) ht
    rw [ho] at hoi
    obtain rfl := Option.some.inj hoi
    exact ⟨_, _, List.getElem?_eq_getElem hil, ht, rfl, rfl, E, RR⟩
  have hbare : (tgtRs out).map (fun r => (r.1, r.2.2.1)) = R.tys.map fun t => (t.1, t.2.1.nIdx) := by
    apply List.ext_getElem?
    intro i
    simp only [tgtRs, List.map_map, List.getElem?_map]
    cases ho : out[i]? with
    | none =>
      have : R.tys[i]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; omega
      simp [this]
    | some o =>
      obtain ⟨rc, t, -, ht, h1, h2, -⟩ := hat i o ho
      simp [ht, h1, h2]
  have hbare' : out.map (fun t => (t.1, t.2.1.nIdx)) = R.tys.map fun t => (t.1, t.2.1.nIdx) := by
    simpa [tgtRs, List.map_map, Function.comp_def] using hbare
  refine envWF_consBlockRecsT henv₂ fun o ho => ?_
  obtain ⟨i, hoi⟩ := List.getElem?_of_mem ho
  obtain ⟨rc, t, -, -, h1, h2, ⟨E⟩, RR⟩ := hat i o hoi
  have hcv := E.hcv
  rw [checkConstantValF_eq] at hcv
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hcv
  rw [h1]
  refine ⟨g1, g2, g3, g4, fun rhs hrhs => ?_⟩
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hrhs
  have hjl : j < t.2.1.ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; rw [RR.len] at this; exact this
  have hjr : j < rc.rhss.length := by rw [RR.lenRhs]; exact hjl
  obtain ⟨o', ho', hrun⟩ := RR.rule j _ _ (List.getElem?_eq_getElem hjl)
    (List.getElem?_eq_getElem hjr)
  rw [hj] at ho'
  obtain rfl := Option.some.inj ho'
  obtain ⟨Q⟩ := targetRule_run hrun
  have hws : WScoped 0 rhs :=
    annotateCore_WScoped _ _ Q.hann (WScoped.of_not_hasFvar Q.hfv)
  refine ⟨ws0_hasFvar hws, Q.hlp, ?_, annotateCore_looseBVars _ _ Q.hann Q.hbv⟩
  have hres := Q.hres
  rw [hbare', ← constsResolveF_eq, ← consBlockRecsBareF_mkFEnv]
  exact hres

/-- **The install after the pass, at k members and at the recursor
stage's CHECK, at the cached driver**, is reproduced by the pure fueled
`checkBlockTail`. -/
theorem checkBlockTailS_run (hμ : mode.verifiedChecks = true)
    {env₁ : Env} (henv₁ : EnvWF env₁) {block : List ConstantInfo} {cvTas : List ConstantVal}
    {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    (hfr : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, env₁.find? c.1.name = none)
    (henv₂ : EnvWF (consBlockCtors p.nP ctorsAs env₁)) (hpos : NestStOk pos)
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockTailS mode block ⟨mkFEnv env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
      s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkBlockTail (fueledOpsM mode) block ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
     ).val F = .ok feOut.env := by
  unfold checkBlockTailS at h
  dsimp only at h
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  rw [checkBlockIdxSortsF_eqC] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ p.members.zip cvTas, WScoped 0 x.2.type :=
    fun x hx => hT x.2 (List.of_mem_zip hx).2
  obtain ⟨hsS, isorts', hPs, F₀, hF₀⟩ :=
    checkBlockIdxSortsS_sim hμ henv₁ hzT hs isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  have hview := restrictTo_consBlockCtors_mkFEnv (nP := p.nP) hfr
  rw [consBlockCtorsF_mkFEnv] at h hview
  rw [mkFEnv_env] at h
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  obtain ⟨out, s₃, hrec, h⟩ := bindC_ok h
  unfold checkBlockRecS at hrec
  -- the check, then (where every kind is flat) the reject-only conformance
  -- check
  unfold thenConform at hrec
  obtain ⟨out', s₄, htc, hrec⟩ := bindC_ok hrec
  obtain ⟨hs₄, F₃, hF₃⟩ := targetRecCheckS_run hμ henv₁ henv₂ hview hpos hT hct
    (flushC_csok hsS.residue) htc
  rw [targetRecCheck_fe₁_congr hview] at hF₃
  obtain ⟨u5, s₅, hconf, hrec⟩ := bindC_ok hrec
  obtain ⟨hv, rfl⟩ := pureC_ok hrec
  subst out'
  -- the conformance branch: its run, or nothing
  obtain ⟨hs₅, F₅, hF₅⟩ : CSOKF s₅ ∧ ∃ F₅, (if nestKindsFlat kinds then
      checkBlockRecConform (fueledOps mode F₅) (consBlockCtors p.nP ctorsAs env₁) p cvTas
        ctorsAs nfs else pure ()) = .ok () := by
    cases hk : nestKindsFlat kinds with
    | true =>
      rw [hk] at hconf
      obtain ⟨hs₅, F₅, hF₅⟩ := checkBlockRecConformS_run hμ henv₂ hs₄ hconf
      exact ⟨hs₅, F₅, by simpa using hF₅⟩
    | false =>
      rw [hk] at hconf
      obtain ⟨-, rfl⟩ := pureC_ok hconf
      exact ⟨hs₄, 0, rfl⟩
  have hs₃ := hs₅
  have henv₃ := targetRecCheck_recsWF henv₂ hF₃ (consBlockCtors p.nP ctorsAs env₁).find?
  rw [show FEnv.find? (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
    = (consBlockCtors p.nP ctorsAs env₁).find? from mkFEnv_find?_fun _] at h
  simp only [constsResolveF_eq] at h
  rw [consBlockRecsTF_mkFEnv, structWalkersC_eq_plain] at h
  obtain ⟨hwfO, hfeO, -, hT₆⟩ := checkBlockTablesS_run _ _ _ henv₃ hs₃ h
  obtain ⟨G, hle₀, hle₃, hle₅⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G ∧ F₅ ≤ G :=
    ⟨max F₀ (max F₃ F₅), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₀ : checkBlockIdxSorts (fueledOps mode G) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts := by
    rw [← checkBlockIdxSorts_datF]; exact FueledM.up hle₀ hF₀
  have g₃ : checkBlockRec (fueledOps mode G) env₁ (consBlockCtors p.nP ctorsAs env₁) p
      (blockNestedBit p.toBlockShape kinds) (nestKindsFlat kinds) nfs pos block
      cvTas ctorsAs = .ok out := by
    have gK : targetRecCheck (ShadowOps.fueled mode G) (mkFEnv env₁) env₁
        (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
        p.toBlockShape (blockNestedBit p.toBlockShape kinds) pos block cvTas ctorsAs
        = .ok out := by
      rw [← targetRecCheck_datF]
      exact FueledM.up hle₃ (by rw [targetRecCheck_datF]; exact hF₃)
    have gC : (if nestKindsFlat kinds then
        checkBlockRecConform (fueledOps mode G) (consBlockCtors p.nP ctorsAs env₁) p cvTas
          ctorsAs nfs else pure ()) = .ok () := by
      cases hk : nestKindsFlat kinds with
      | true =>
        rw [hk] at hF₅
        simp only [↓reduceIte] at hF₅ ⊢
        rw [← checkBlockRecConform_datF]
        exact FueledM.up hle₅ (by rw [checkBlockRecConform_datF]; exact hF₅)
      | false => rfl
    unfold checkBlockRec thenConform checkBlockRecT
    simp only [ShadowOps.fueled] at gK ⊢
    simp only [pure, Except.pure] at gC
    simp only [Bind.bind, Except.bind, gK, pure, Except.pure]
    rw [gC]
  rw [checkBlockTail_datF]
  unfold checkBlockTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₀]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  exact hT₆

/-- **The uniform install at k members, at the recursor stage's CHECK,
at the cached driver**, is reproduced by the pure fueled `checkBlock`:
the pass at official's `is_rec` and the install after it. -/
theorem checkBlockKS_run (hμ : mode.verifiedChecks = true)
    {env : Env} (henv : EnvWF env) {block : List ConstantInfo} {p₀ : BlockParts}
    {s₀ : CState} (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockKS mode (mkFEnv env) block p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkBlock (fueledOps mode F) env block p₀ = .ok feOut.env := by
  unfold checkBlockKS at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  obtain ⟨r, s₁, hP, h⟩ := bindC_ok h
  obtain ⟨fe₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hT, hct, hfr, henv₂, hpos, F₁, hF₁⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hT hct hfr henv₂ hpos hF₁
  subst hq₁
  obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkBlockTailS_run hμ henv₁ hT hct hfr henv₂ hpos hs₁ h
  refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
  have g₁ : checkBlockPass (fueledOps mode (max F₁ F₂)) env p₀ (blockRawRec p₀)
      = .ok ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩ := by
    rw [← checkBlockPass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkBlockTail (fueledOps mode (max F₁ F₂)) block
      ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
      = .ok feOut.env := by
    rw [← checkBlockTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  unfold checkBlock
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  exact g₂

variable {pins : List NatOpPinSet}

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkBlockKS`, every other one
declines (`checkShapelessS`), and the pure fueled `checkDecl`
reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match blockParts? nP block with
          | some p => checkBlockKS mode (mkFEnv env) block p
          | none => checkShapelessS mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match basisPinHit block with
      | some kind => checkBasisDecl (m := CheckM) env kind
      | none =>
        if indParamsOk nP block = true then
          (match blockParts? nP block with
            | some p => checkBlock (fueledOps mode F) env block p
            | none => checkShapeless (fueledOps mode F) env block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : blockParts? nP block with
  | some p =>
    rw [hfp] at h
    simp only at h
    -- the block install, at any number of members, nested included
    obtain ⟨hres, hfe, F, hF⟩ := checkBlockKS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    -- the decline never returns an index
    exfalso
    unfold checkShapelessS at h
    obtain ⟨_, _, _, h⟩ := bindC_ok h
    exact nomatch h

end ConLeche.Cached
