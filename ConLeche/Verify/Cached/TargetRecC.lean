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
import ConLeche.Verify.Cached.NestPosC

public section

/-!
# The cached recursor stage, bridged: the TARGET check (lane RECLIB, B1)

The uniform route's recursor stage is the classification-free
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

theorem targetMajorOfS_sim {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (targetMajorOf (m := CheckCM) fe p false ctorsAs fvs mty)
      (targetMajorOf (m := FueledM) fe p false ctorsAs fvs mty) := by
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
    · simp only [Bool.false_eq_true, if_false]
      exact SimC.throw_bind
  · exact SimC.throw

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
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) {rc : RecShape} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 v.1.type)
      (targetRecTy (sharedOpsC mode (mkFEnv env)) (mkFEnv env) p false nested cvTas ctorsAs rc)
      (targetRecTy (fueledOpsM mode) (mkFEnv env) p false nested cvTas ctorsAs rc) := by
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
  obtain ⟨rfl, -⟩ := hMj
  refine SimC.bind ((targetMajorOfS_sim hs₃).withYields
    (targetMajorOf_member (mkFEnv env) p ctorsAs fvs maj.fvarTypeD))
    (fun s₄ M M' hs₄ hM => ?_)
  obtain ⟨rfl, t, hmt, -, -⟩ := hM
  by_cases h3 : Option.all (fun x => x == rc.tgt) M.member = true
  case neg => simp only [h3]; exact SimC.throw_bind
  simp only [h3, if_true]
  refine SimC.bind (SimC.unwrapOr' hs₄) (fun s₅ cvTP cvTP' hs₅ hP => ?_)
  obtain ⟨rfl, hcvTP⟩ := hP
  have hwTP : WScoped 0 cvTP.type := by
    rw [hmt] at hcvTP
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
  refine SimC.bind (targetIdxDomsS_sim hmt hT (by omega) hs₇) (fun s₈ idoms idoms' hs₈ hI => ?_)
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
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) :
    ∀ {recs : List RecShape} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ q ∈ v, WScoped 0 q.1.type)
        (targetRecTys (sharedOpsC mode (mkFEnv env)) (mkFEnv env) p false nested cvTas ctorsAs
          recs)
        (targetRecTys (fueledOpsM mode) (mkFEnv env) p false nested cvTas ctorsAs recs)
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
    refine SimC.bind (targetWhnfPisS_sim hμ henv 1024 depth (hf f List.mem_cons_self) hs)
      (fun s₁ t t' hs₁ hT => ?_)
    obtain ⟨rfl, hwt⟩ := hT
    refine SimC.bind (targetFieldNormsS_sim hμ henv (fun g hg => hf g (List.mem_cons_of_mem _ hg))
      hs₁) (fun s₂ ts ts' hs₂ hTs => ?_)
    obtain ⟨rfl, hwts⟩ := hTs
    refine SimC.pure hs₂ ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hwt
    · exact hwts x hx

/-- **One call's typing, simulated**; the call's telescope is hole-free
(the check's first guard). -/
theorem targetCallOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cn : Name}
    {fam : TargetFamily} {fvsPref fvsF fnorm : List Expr}
    {teles : List (List (Expr × BinderMeta))} {absM : Expr → Expr} {base k : Nat}
    {pw : PropWhen} {ih : TargetIh}
    (hpref : ∀ x ∈ fvsPref, WScoped base x) (hflds : ∀ x ∈ fvsF, WScoped base x)
    (hfn : ∀ t ∈ fnorm, WScoped (base + k) t)
    (htl : ∀ tele ∈ teles, ∀ b ∈ tele, WScoped (base + k) b.1)
    (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (habs : ∀ e, WScoped (base + k) e → WScoped (base + k) (absM e))
    (hidx : ∀ x ∈ ih.idx, WScoped base x)
    (hihTy : (∀ b ∈ teles.getD ih.field [], WScoped base b.1) → WScoped base ih.ty)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀
      (fun v w => v = w ∧ (teles.getD ih.field []).all (fun b => targetHoleFree base k b.1))
      (targetCallOk (sharedOpsC mode (mkFEnv env)) env cn fam fvsPref fvsF fnorm teles absM
        base k pw ih)
      (targetCallOk (fueledOpsM mode) env cn fam fvsPref fvsF fnorm teles absM base k pw ih) := by
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
  have hfld : WScoped (base + k) (absM (fvsF.getD ih.field default).fvarTypeD) :=
    habs _ ((fvarTypeD_WScoped hfF).mono (by omega))
  refine SimC.bind (opE_infer_sim hμ henv hs hfld) (fun s₁ _ _ hs₁ _ => ?_)
  have hwant : WScoped (base + k) (Expr.mkPisOf (teles.getD ih.field []) (absM majDom)) :=
    mkPisOf_WScoped htele (habs _ (hwC.1.mono (by omega)))
  refine SimC.bind (opE_infer_sim hμ henv hs₁ hwant) (fun s₂ _ _ hs₂ _ => ?_)
  refine SimC.bind (opB_sim hμ henv hs₂ (getD_WScoped hfn _) hwant) (fun s₃ b b' hs₃ hB => ?_)
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
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimC.throw
  | true => simp only [↓reduceIte]; exact SimC.pure hs₆ (by simp [h1])

theorem targetCallsOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cn : Name}
    {fam : TargetFamily} {fvsPref fvsF fnorm : List Expr}
    {teles : List (List (Expr × BinderMeta))} {absM : Expr → Expr} {base k : Nat}
    {pw : PropWhen}
    (hpref : ∀ x ∈ fvsPref, WScoped base x) (hflds : ∀ x ∈ fvsF, WScoped base x)
    (hfn : ∀ t ∈ fnorm, WScoped (base + k) t)
    (htl : ∀ tele ∈ teles, ∀ b ∈ tele, WScoped (base + k) b.1)
    (hrec : ∀ t ∈ fam.recTys, WScoped 0 t)
    (habs : ∀ e, WScoped (base + k) e → WScoped (base + k) (absM e)) :
    ∀ {ihs : List TargetIh} {s₀ : CState},
      (∀ ih ∈ ihs, (∀ x ∈ ih.idx, WScoped base x) ∧
        ((∀ b ∈ teles.getD ih.field [], WScoped base b.1) → WScoped base ih.ty)) →
      CSOK mode env s₀ →
      SimC mode env s₀
        (fun v w => v = w ∧
          ∀ ih ∈ ihs, (teles.getD ih.field []).all (fun b => targetHoleFree base k b.1) = true)
        (targetCallsOk (sharedOpsC mode (mkFEnv env)) env cn fam fvsPref fvsF fnorm teles absM
          base k pw ihs)
        (targetCallsOk (fueledOpsM mode) env cn fam fvsPref fvsF fnorm teles absM base k pw ihs)
  | [], s₀, _, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | ih :: ihs, s₀, hih, hs => by
    unfold targetCallsOk
    obtain ⟨hidx, hty⟩ := hih ih List.mem_cons_self
    refine SimC.bind (targetCallOkS_sim hμ henv hpref hflds hfn htl hrec habs hidx hty hs)
      (fun s₁ _ _ hs₁ hP => ?_)
    obtain ⟨-, hh⟩ := hP
    refine SimC.mono ?_ (targetCallsOkS_sim hμ henv hpref hflds hfn htl hrec habs
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
  refine SimG.bind (SimG.ofC (fun s hs => targetCallsOkS_sim (cn := c.1.name) (pw :=
    Level.zeronessOf (structElimLevel p.elim p.large)) hμ henvT
    (fun a ha => (hwy a ha).mono (by omega)) hwz.1 hfn htl hrec habs hihs hs))
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
    refine SimG.bind ((targetRuleS_simG hμ henvR henvT hrecTy hrec hformer
      (hc cA List.mem_cons_self) hds).mono (fun _ h => h) (fun _ h => h.residue))
      (fun r r' hr => ?_)
    obtain rfl : r = r' := hr
    refine SimG.bind (targetRulesS_simG hμ henvR henvT hrecTy hrec hformer hds
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
    refine SimG.bind (targetRulesS_simG hμ henvR henvT hw1 hrec hformer hw3 hw2)
      (fun rh rh' hR => ?_)
    obtain rfl : rh = rh' := hR
    refine SimG.bind (targetRecsRulesS_simG hμ henvR henvT hrec hformer
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

/-- What the rule stage needs of a checked recursor, off its type run. -/
theorem TargetTyEntry.scoped {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) (hw : WScoped 0 cvRi.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) :
    TargetTyScoped rc (cvRi, M, u) := by
  obtain ⟨t, ms, hmt, -, -, -, hctors⟩ := E.member
  refine ⟨hw, fun cA hcA => ?_, ?_⟩
  · simp only [targetCtorAt, hmt]
    exact hct _ (List.mem_of_getElem? hctors) cA hcA
  · obtain ⟨_, fvs, _, _, _, _, _, _, _, hroom, _, hopen, _, major, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _⟩ := E
    cases major with
    | member I t ms ctorsA hfn ht hms hctors hpar =>
      intro x hx
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have hil : i < p.nP := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp only [List.length_take] at this; omega
      rw [List.getElem?_take, if_pos hil] at hi
      exact (openers_WScoped_at hopen hw i x hi).mono (by omega)

/-- **The target recursor check at the cached driver, simulated**: from
an invariant state of the constructors' environment to a residue. -/
theorem targetRecCheckS_simG (hμ : mode.verifiedChecks = true) {env₂ : Env}
    (henv₂ : EnvWF env₂) {p : BlockShape} {nested : Bool} {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) :
    SimG (CSOK mode env₂) CSOKF RelVC
      (targetRecCheck (shadowOpsC mode) (mkFEnv env₂) p false nested block cvTas ctorsAs)
      (targetRecCheck (ShadowOps.ofOps (fueledOpsM mode)) (mkFEnv env₂) p false nested block
        cvTas ctorsAs) := by
  unfold targetRecCheck
  simp only [shadowOpsC, ShadowOps.ofOps, structWalkersC_eq_plain, mkFEnv_env,
    consBlockRecsBareF_mkFEnv]
  refine SimG.bind (SimG.ofC fun s hs => targetRecPinsS_sim hs) fun _ _ _ => ?_
  refine SimG.bindR (SimG.ofC fun s hs => targetRecTysS_sim hμ henv₂ hT hs)
    fun tys tys' hP hrun => ?_
  obtain ⟨rfl, hwR⟩ := hP
  obtain ⟨F, hF⟩ := hrun
  rw [targetRecTys_datF] at hF
  obtain ⟨hlenT, hallT⟩ := targetRecTys_run hF
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
      Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas ctorsAs rc t.1 t.2.1 t.2.2) := by
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
    exact TargetTyEntry.scoped E (hwR t (List.mem_of_getElem? ht)) hct
  have hrec : ∀ t ∈ (targetFamilyOf p tys).recTys, WScoped 0 t := by
    intro t ht
    simp only [targetFamilyOf, List.mem_map] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    exact hwR q hq
  have hformer : ∀ t ∈ cvTas.map (·.type), WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  refine SimG.bind ((targetRecsRulesS_simG hμ henvR henv₂ hrec hformer hsc).mono
    (fun _ h => h.residue) (fun _ h => h)) fun out out' hO => ?_
  obtain rfl : out = out' := hO
  exact SimG.bind flushC_simG fun _ _ _ =>
    SimG.pure (fun _ h => h) rfl

/-- **The recursor stage's CHECK at the cached driver** is reproduced
by the pure fueled target check. -/
theorem targetRecCheckS_run (hμ : mode.verifiedChecks = true) {env₂ : Env}
    (henv₂ : EnvWF env₂) {p : BlockShape} {nested : Bool} {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK mode env₂ s₀) {out : List (ConstantVal × TargetMajor × List Expr)}
    {s' : CState}
    (h : targetRecCheck (shadowOpsC mode) (mkFEnv env₂) p false nested block cvTas ctorsAs s₀
      = .ok (out, s')) :
    CSOKF s' ∧ ∃ F, targetRecCheck (ShadowOps.fueled mode F) (mkFEnv env₂) p false nested
      block cvTas ctorsAs = .ok out := by
  obtain ⟨hs', out', rfl, F, hF⟩ := targetRecCheckS_simG hμ henv₂ hT hct s₀ hs out s' h
  exact ⟨hs', F, by rw [← targetRecCheck_datF]; exact hF⟩

/-- **The stored family's environment is well-formed**: every stored
recursor type is a checked constant's, every stored rule the annotated
stream right-hand side, resolved at the rule-less recursors' environment
(off the target check's run records). -/
theorem targetRecCheck_recsWF {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) (mkFEnv env₂) p false nested block cvTas
      ctorsAs = .ok out) (find? : Name → Option ConstantInfo) (nP : Nat) :
    EnvWF (consBlockRecs find? p nP 0 (tgtRs out) env₂) := by
  obtain ⟨R⟩ := targetRecCheck_run h
  obtain ⟨hlenT, hallT⟩ := targetRecTys_run R.htys
  obtain ⟨hlenO, hallO⟩ := targetRecsRules_run R.rules
  have hlenO' : out.length = R.tys.length := by rw [hlenO, hlenT, Nat.min_self]
  -- every stored entry is stage (b)'s recursor and major, with its rules
  have hat : ∀ (i : Nat) (o : ConstantVal × TargetMajor × List Expr), out[i]? = some o →
      ∃ rc t, p.recs[i]? = some rc ∧ R.tys[i]? = some t ∧ o.1 = t.1 ∧ o.2.1 = t.2.1 ∧
        Nonempty (TargetTyEntry mode F (mkFEnv env₂) p nested cvTas ctorsAs rc t.1 t.2.1 t.2.2) ∧
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
  refine envWF_consBlockRecs henv₂ fun r hr => ?_
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  simp only [tgtRs, List.getElem?_map] at hi
  cases ho : out[i]? with
  | none => rw [ho] at hi; exact nomatch hi
  | some o =>
  rw [ho] at hi
  obtain rfl := Option.some.inj hi
  obtain ⟨rc, t, -, -, h1, h2, ⟨E⟩, RR⟩ := hat i o ho
  have hcv := E.hcv
  rw [checkConstantValF_eq] at hcv
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hcv
  dsimp only
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
  rw [hbare, ← constsResolveF_eq, ← consBlockRecsBareF_mkFEnv]
  exact hres

/-- **The install after the pass, at k members and at the recursor
stage's CHECK, at the cached driver**, is reproduced by the pure fueled
`checkBlockTail`. -/
theorem checkBlockTailS_run (hμ : mode.verifiedChecks = true)
    {env env₁ : Env} (henv₁ : EnvWF env₁) {block : List ConstantInfo} {cvTas : List ConstantVal}
    {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    (henv₂ : EnvWF (consBlockCtors p.nP ctorsAs env₁))
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockTailS mode (mkFEnv env) block ⟨mkFEnv env₁, cvTas, p, ctorsAs, sortsss⟩ s₀
      = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkBlockTail (fueledOpsM mode) env block ⟨env₁, cvTas, p, ctorsAs, sortsss⟩).val F
      = .ok feOut.env := by
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
  rw [structWalkersC_eq_plain, blockFieldsOkF_eqC] at h
  by_cases hk : blockFieldsOk env p.memberNames p.lps p.nP p.nIdxs ctorsAs p.kinds = true
  case neg => rw [if_neg hk] at h; exact absurd h throwC_bind_ok
  rw [if_pos hk] at h
  -- the positivity stage (lane HOLE2)
  obtain ⟨uP, sP, hPos, h⟩ := bindC_ok h
  rw [show FEnv.find? (mkFEnv env₁) = env₁.find? from mkFEnv_find?_fun _] at hPos
  obtain ⟨hsP, uP', hPr, FP, hFP⟩ :=
    checkBlockPositivityS_sim hμ henv₁ p cvTas ctorsAs hT hct hsS uP sP hPos
  rw [consBlockCtorsF_mkFEnv] at h
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sP.flushed = sC := congrArg Prod.snd hfl2
  obtain ⟨rs, s₃, hrec, h⟩ := bindC_ok h
  unfold checkBlockRecS at hrec
  -- the check, then the reject-only conformance check (lane CONF1)
  unfold thenConform at hrec
  obtain ⟨rs', s₄, hrecK, hrec⟩ := bindC_ok hrec
  obtain ⟨out, s₄', htc, hrecK⟩ := bindC_ok hrecK
  obtain ⟨rfl, rfl⟩ := pureC_ok hrecK
  obtain ⟨hs₄, F₃, hF₃⟩ := targetRecCheckS_run hμ henv₂ hT hct (flushC_csok hsP.residue) htc
  obtain ⟨u5, s₅, hconf, hrec⟩ := bindC_ok hrec
  obtain ⟨hs₅, F₅, hF₅⟩ := checkBlockRecConformS_run hμ henv₂ hs₄ hconf
  obtain ⟨hv, rfl⟩ := pureC_ok hrec
  subst rs
  have hs₃ := hs₅
  have henv₃ := targetRecCheck_recsWF henv₂ hF₃ (consBlockCtors p.nP ctorsAs env₁).find? p.nP
  rw [show FEnv.find? (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
    = (consBlockCtors p.nP ctorsAs env₁).find? from mkFEnv_find?_fun _,
    consBlockRecsF_mkFEnv] at h
  obtain ⟨hwfO, hfeO, -, hT₆⟩ := checkBlockTablesS_run _ _ _ henv₃ hs₃ h
  obtain ⟨G, hle₀, hle₃, hle₅, hleP⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G ∧ F₅ ≤ G ∧ FP ≤ G :=
    ⟨max F₀ (max F₃ (max F₅ FP)), by omega, by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₀ : checkBlockIdxSorts (fueledOps mode G) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts := by
    rw [← checkBlockIdxSorts_datF]; exact FueledM.up hle₀ hF₀
  have gP : checkBlockPositivity (fueledOps mode G) env₁ env₁.find? env₁.consts p cvTas ctorsAs
      = .ok () := by
    rw [← checkBlockPositivity_datF]; exact FueledM.up hleP hFP
  have g₃ : checkBlockRec (fueledOps mode G) (consBlockCtors p.nP ctorsAs env₁) p block
      cvTas ctorsAs = .ok (tgtRs out) := by
    have gK : targetRecCheck (ShadowOps.fueled mode G) (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
        p.toBlockShape false false block cvTas ctorsAs = .ok out := by
      rw [← targetRecCheck_datF]
      exact FueledM.up hle₃ (by rw [targetRecCheck_datF]; exact hF₃)
    have gC : checkBlockRecConform (fueledOps mode G) (consBlockCtors p.nP ctorsAs env₁) p cvTas
        ctorsAs = .ok () := by
      rw [← checkBlockRecConform_datF]
      exact FueledM.up hle₅ (by rw [checkBlockRecConform_datF]; exact hF₅)
    unfold checkBlockRec thenConform checkBlockRecT
    simp only [ShadowOps.fueled] at gK
    simp only [Bind.bind, Except.bind, gK, gC, pure, Except.pure]
  rw [checkBlockTail_datF]
  unfold checkBlockTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₀]
  simp only [Except.bind]
  rw [if_pos hk]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [gP]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₃]
  simp only [Except.bind]
  exact hT₆

/-- **The uniform install at k members, at the recursor stage's CHECK,
at the cached driver**, is reproduced by the pure fueled `checkBlock`:
the pass at the syntactic reading, again at the classified verdict
where it overshot, and the install after the settled one. -/
theorem checkBlockKS_run (hμ : mode.verifiedChecks = true)
    {env : Env} (henv : EnvWF env) {block : List ConstantInfo} {p₀ : BlockParts} {s₀ : CState}
    (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
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
  obtain ⟨⟨fe₁, cvTas, p, ctorsAs, sortsss⟩, settled⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hT, hct, henv₂, F₁, hF₁⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hT hct henv₂ hF₁
  subst hq₁
  try simp only at h
  cases settled with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkBlockTailS_run hμ henv₁ hT hct henv₂ hs₁ h
    refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
    have g₁ : checkBlockPass (fueledOps mode (max F₁ F₂)) env p₀ (blockRawRec p₀)
        = .ok (⟨env₁, cvTas, p, ctorsAs, sortsss⟩, true) := by
      rw [← checkBlockPass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : checkBlockTail (fueledOps mode (max F₁ F₂)) env block
        ⟨env₁, cvTas, p, ctorsAs, sortsss⟩
        = .ok feOut.env := by
      rw [← checkBlockTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
    unfold checkBlock
    rw [if_pos hnd]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [g₁]
    simp only [Except.bind, ↓reduceIte]
    exact g₂
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  obtain ⟨r', s₂, hP', h⟩ := bindC_ok h
  obtain ⟨⟨fe₁', cvTas', p', ctorsAs', sortsss'⟩, settled'⟩ := r'
  obtain ⟨env₁', hq₁', hs₁', henv₁', hT', hct', henv₂', F₂, hF₂⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hs₁.residue) hP'
  simp only at hq₁' hs₁' henv₁' hT' hct' henv₂' hF₂
  subst hq₁'
  try simp only at h
  cases settled' with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h throwC_bind_ok
  | true =>
  simp only [↓reduceIte] at h
  obtain ⟨hwfO, hfeO, F₃, hF₃⟩ := checkBlockTailS_run hμ henv₁' hT' hct' henv₂' hs₁' h
  obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
    ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : checkBlockPass (fueledOps mode G) env p₀ (blockRawRec p₀)
      = .ok (⟨env₁, cvTas, p, ctorsAs, sortsss⟩, false) := by
    rw [← checkBlockPass_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkBlockPass (fueledOps mode G) env p₀ (blockIsRec p.kinds)
      = .ok (⟨env₁', cvTas', p', ctorsAs', sortsss'⟩, true) := by
    rw [← checkBlockPass_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkBlockTail (fueledOps mode G) env block ⟨env₁', cvTas', p', ctorsAs', sortsss'⟩
      = .ok feOut.env := by
    rw [← checkBlockTail_datF]; exact FueledM.up hle₃ hF₃
  unfold checkBlock
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind, Bool.false_eq_true, ↓reduceIte]
  rw [g₂]
  simp only [Except.bind, ↓reduceIte]
  exact g₃

variable {pins : List NatOpPinSet}

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkBlockKS`, everything else to `checkIndDeclSF`,
and either way the pure fueled `checkDecl` reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match blockParts? nP block with
          | some p => checkBlockKS mode (mkFEnv env) block p
          | none => checkIndDeclSF mode (mkFEnv env) nP block) s₀ =
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
            | none => checkModeled mode (fueledOps mode F) env nP block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : blockParts? nP block with
  | some p =>
    rw [hfp] at h
    simp only at h
    -- the uniform route, at any number of members
    obtain ⟨hres, hfe, F, hF⟩ := checkBlockKS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩

end ConLeche.Cached
