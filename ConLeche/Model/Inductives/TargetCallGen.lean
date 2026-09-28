module

public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetCallMove
import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Semantics.Kit
import ConLeche.Verify.Leaves
import ConLeche.Verify.BetaGate

public section

/-!
# A target call's target at a valuation of the holes

The target check types a recursive call on the member-ABSTRACTED terms
(`targetCallOk`) at the ABSTRACT frame: the rule's frame, the block's
member holes, then the fields again with their annotations abstracted
(`targetAbsFields`, each typed there: `walkCtx_absFields`).  There the
field's abstract type is defeq to `∀ a⃗, hole x⃗ e⃗` (`hdeq`), both sides
inferred (`hfld`, `hwant`).  `targetCall_gen` reads it at any valuation
`hv` of the holes (at their formers' types) that puts every field in
its abstract type's reading (`hii`): the field lies in the Π's reading
(the defeq equates the two readings); read at the copies' own values the
moved terms are the unmoved ones at the holes' frame (`move_read`,
`move_interp`); the Π's body is the hole applied to the parameters and
the index arguments (the abstraction leaves the index arguments alone),
whose grading makes the arguments fit the hole's type's binder data — a
graph's domain is rigid (`spineFit_of_wellDenoted_mkAppN_pi`).

It is stated at a call's typing run (`TargetCallRun`) and the frame's
walk context, generic in everything the rule data pin;
`TargetCallCore.lean` instantiates it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode TargetIh TargetFamily)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Gen

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

/-- The value of a frame variable, read above extra slots. -/
theorem interp_frame_fvar {D E i : Nat} {L : List V} {ρ : Nat → V} {extra : List V}
    (hL : L.length = D) (hE : extra.length = E) (hi : i < D) :
    interp V (consList extra (consList L ρ)) (.bvar (D + E - 1 - i)) = L.getD i pt := by
  rw [interp_bvar, show D + E - 1 - i = (D - 1 - i) + extra.length from by omega,
    consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hL,
    show D - 1 - (D - 1 - i) = i from by omega]


omit [SetTheory V] in
theorem targetAbs_mkAppN {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (as : List Expr) (f : Expr),
      ConLeche.targetAbs names lvls holes (Expr.mkAppN f as)
        = Expr.mkAppN (ConLeche.targetAbs names lvls holes f)
            (as.map (ConLeche.targetAbs names lvls holes))
  | [], _ => rfl
  | a :: as, f => by
    show ConLeche.targetAbs names lvls holes (Expr.mkAppN (.app f a) as) = _
    rw [targetAbs_mkAppN as (.app f a)]
    rfl

omit [SetTheory V] in
theorem teleDoms_length {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {D : Nat} : ∀ (tys os : List Expr) {ds : List AnnotTerm},
      teleDoms acval env φ D os tys = some ds → ds.length = tys.length
  | [], _, ds, h => by simp [teleDoms] at h; subst h; rfl
  | ty :: tys, os, ds, h => by
    simp only [teleDoms, Option.bind_eq_bind] at h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj h).symm
    simp [teleDoms_length tys _ hr]


/-- Every subject of a read spine reads. -/
theorem spine_reads {d : Nat} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      ∀ e ∈ es, ∃ a, denoteMeta mT.acval envT φ d e = some a
  | _, _, .nil, _, he => nomatch he
  | _, _, .cons (a := a0) ha hr, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, ha⟩
    · exact spine_reads hr e he

/-- A read spine's values, entry by entry. -/
theorem spine_map_getD {d : Nat} {τ : Nat → V} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      vs.map (interp V τ)
        = es.map fun e => interp V τ ((denoteMeta mT.acval envT φ d e).getD default)
  | _, _, .nil => rfl
  | _, _, .cons ha hr => by
    simp only [List.map_cons, ha, Option.getD_some]
    rw [spine_map_getD hr]

/-! ## The call's shape, from the abstraction -/

omit [SetTheory V] in
/-- In a duplicate-free list, an entry is found at its own position. -/
theorem findIdx?_of_nodup {l : List Name} (hnd : l.Nodup) {t : Nat} {a : Name}
    (h : l[t]? = some a) : l.findIdx? (· == a) = some t := by
  obtain ⟨ht, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨ht, by simp [hget], fun j hj => ?_⟩
  have hne : l[j] ≠ l[t] := fun he => by
    have := (List.getElem_inj hnd).mp he
    omega
  simpa [hget] using hne

omit [SetTheory V] in
/-- A recognised call's index arguments number the callee's indices. -/
theorem targetCall?_idxLen {fr : ConLeche.TargetFrame} {d : Nat} {e : Expr} {i c m : Nat}
    {idx : List Expr} (h : ConLeche.targetCall? fr d e = some (i, c, m, idx))
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0) :
    idx.length + fr.rP = fr.mIs.getD c 0 := by
  unfold ConLeche.targetCall? at h
  split at h
  next r us hfn =>
    split at h
    · exact nomatch h
    next c0 hc0 =>
      split at h
      · exact nomatch h
      next hus =>
      split at h
      · exact nomatch h
      next hrp =>
      dsimp only at h
      split at h
      · exact nomatch h
      next hlen =>
      split at h
      · exact nomatch h
      next hpref =>
      split at h
      · exact nomatch h
      next maj hmaj =>
      split at h
      · exact nomatch h
      next i0 hi0 =>
      split at h
      · exact nomatch h
      next hmd =>
      split at h
      · exact nomatch h
      next hargs =>
      split at h
      · exact nomatch h
      next hidx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, h2, -, h4⟩ := h
      subst h2; subst h4
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hrp hlen
      have := hle c0
      rw [hrp] at this
      simp only [List.length_take, List.length_drop, hlen]
      omega
  · exact nomatch h

omit [SetTheory V] in
/-- **Every `ih` entry the abstraction allocates is a recognised call's**:
its index arguments number the callee's indices and are bounded by the
field's telescope. -/
theorem targetAbstract_callShape {fr : ConLeche.TargetFrame} {B : Nat}
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0) :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      ∀ ih ∈ acc'.toList, ih ∈ acc.toList ∨
        (ih.idx.length + fr.rP = fr.mIs.getD ih.callee 0 ∧ fr.rPs.getD ih.callee 0 = fr.rP ∧
          ∀ x ∈ ih.idx, x.looseBVarsBounded (fr.teles.getD ih.field []).length = true)
  | _, .bvar _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .sort _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .lit _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .fvar _ _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .const n us, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | d, .lam ty b bi, acc, _, _, h | d, .forallE ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases targetAbstract_callShape hle (d + 1) b acc1 b' acc2 h2 ih hih with hA | hA
    · exact targetAbstract_callShape hle d ty acc ty' acc1 h1 ih hA
    · exact Or.inr hA
  | d, .letE ty v b, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases targetAbstract_callShape hle (d + 1) b acc2 b' acc3 h3 ih hih with hA | hA
    · rcases targetAbstract_callShape hle d v acc1 v' acc2 h2 ih hA with hB | hB
      · exact targetAbstract_callShape hle d ty acc ty' acc1 h1 ih hB
      · exact Or.inr hB
    · exact Or.inr hA
  | d, .proj sn i x, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact targetAbstract_callShape hle d x acc x' acc1 h1
  | d, .app f a, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro ih hih
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hih
        rcases hih with hih | rfl
        · exact Or.inl hih
        · obtain ⟨rn, -, -, hrp, hm, -, -, hidx⟩ := targetCall?_inv hc hle
          refine Or.inr ⟨targetCall?_idxLen hc hle, hrp, fun x hx => ?_⟩
          have := (hidx x hx).1
          rwa [hm] at this
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro ih hih
      rcases targetAbstract_callShape hle d a acc1 a' acc2 h2 ih hih with hA | hA
      · exact targetAbstract_callShape hle d f acc f' acc1 h1 ih hA
      · exact Or.inr hA


/-- **The abstract fields extend the holes' context** (the call frame's
slots past the holes, `targetAbsFields`): each copy's annotation was
inferred at its own position (`targetAbsFieldsOk`), draws its leaves
from the frame, the holes and the copies before it, and holds its
field's value (`hmem`). -/
theorem walkCtx_absFields
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F rP nF B : Nat} {names : List Name} {lvls : List Level} {holes : List Expr}
    {fvsF fvsA L0 : List Expr}
    (hA : fvsA = ConLeche.targetAbsFields names lvls holes rP B [] fvsF)
    (hfA : ConLeche.targetAbsFieldsOk (ConLeche.fueledOps .verified F) envT B fvsA = .ok ())
    (hlf : fvsF.length = nF)
    (hL0 : FvarList B L0) {σH : Nat → V} {Δ0 : List AnnotTerm}
    (hW0 : WalkCtx V mT φ B σH Δ0 L0)
    -- the fields' member-abstracted types draw their leaves from the frame
    (habsL : ∀ j, j < nF → ∀ l ∈ (ConLeche.targetAbs names lvls holes
      (fvsF.getD j default).fvarTypeD).fvarLeaves, Expr.fvar l.1 l.2 ∈ L0)
    (hFW : ∀ f ∈ fvsF, Expr.WScoped B f.fvarTypeD) (hholes : ∀ h ∈ holes, Expr.WScoped B h)
    {fs : List V} (hfsl : fs.length = nF)
    (hmem : ∀ j, j < nF → ∀ tb : AnnotTerm,
      denoteMeta mT.acval envT φ (B + j) (fvsA.getD j default).fvarTypeD = some tb →
      fs.getD j pt ∈ˢ interp V (consList (fs.take j) σH) tb) :
    FvarList (B + nF) (fvsA.reverse ++ L0) ∧
      ∃ ΔA, WalkCtx V mT φ (B + nF) (consList fs σH) ΔA (fvsA.reverse ++ L0) := by
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  obtain ⟨hlenA, hget⟩ := ConLeche.targetAbsFields_nil (names := names) (lvls := lvls)
    (holes := holes) (rP := rP) (D := B) fvsF
  rw [← hA] at hlenA hget
  have hWSA := ConLeche.targetAbsFields_WScoped (names := names) (lvls := lvls) (rP := rP) (D := B)
    hholes hFW
  rw [← hA] at hWSA
  have hrun := ConLeche.targetAbsFieldsOk_run hfA
  suffices key : ∀ n, n ≤ nF → FvarList (B + n) ((fvsA.take n).reverse ++ L0) ∧
      ∃ Δn, WalkCtx V mT φ (B + n) (consList (fs.take n) σH) Δn ((fvsA.take n).reverse ++ L0) by
    have h := key nF (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h
  intro n
  induction n with
  | zero => intro _; simpa using ⟨hL0, Δ0, hW0⟩
  | succ n ih =>
    intro hn
    obtain ⟨hFL, Δn, hWn⟩ := ih (by omega)
    have hn' : n < fvsF.length := by omega
    have hx := hget n hn'
    generalize hE : ConLeche.targetMoveF rP (fvsA.take n)
      (ConLeche.targetAbs names lvls holes (fvsF.getD n default).fvarTypeD) = E at hx
    obtain ⟨ty, hty, hwty'⟩ := hWSA n hn'
    have hwty : Expr.WScoped (B + n) E := by
      have h1 : Expr.fvar (B + n) ty = Expr.fvar (B + n) E := Option.some.inj (hty.symm.trans hx)
      injection h1 with _ h2
      exact h2 ▸ hwty'
    -- the copy's leaves: the frame's, the holes', the copies' before it
    have hcll : ∀ l ∈ E.fvarLeaves, Expr.fvar l.1 l.2 ∈ (fvsA.take n).reverse ++ L0 := by
      intro l hl
      rw [← hE] at hl
      rcases ConLeche.targetMoveF_fvarLeaves _ l hl with h | ⟨r, hr, h⟩
      · exact List.mem_append_right _ (habsL n (by omega) l h)
      · have hr' : r ∈ (fvsA.take n).reverse ++ L0 :=
          List.mem_append_left _ (List.mem_reverse.mpr hr)
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
        simp only [List.length_take] at hj
        obtain ⟨tyj, htyj, -⟩ := hWSA j (by omega)
        have hrj : (fvsA.take n)[j] = .fvar (B + j) tyj := by
          rw [List.getElem_take]; exact (List.getElem?_eq_some_iff.mp htyj).2
        rw [hrj] at h hr'
        simp only [Expr.fvarLeaves, List.mem_cons] at h
        rcases h with rfl | h
        · exact hr'
        · exact hWn.2.2.2.2.2.2 _ hr' l h
    -- its typing run
    obtain ⟨t, ht⟩ := hrun n _ hx
    simp only [Expr.fvarTypeD] at ht
    have hInf := Rules.inferTypeCore_bridge ht
    have hlbb := ConLeche.infer_full_bvarClosed hInf
    have hcb : ConstsBound envT E := infer_constsBound_of_full hInf rfl (fun l hl => by
      have := hWn.2.2.2.2.2.1 _ (hcll l hl)
      simpa [ConstsBound] using this)
    obtain ⟨tb, htb⟩ := acceptedReads_of mT φ ht (wscoped_of_leaves_mem hFL _ hcll) hlbb
      (fun l hl => hWn.2.2.2.2.1 _ (hcll l hl))
    have hmemn := hmem n (by omega) tb (by
      rw [List.getD_eq_getElem?_getD, hx, Option.getD_some]; exact htb)
    have h := WalkCtx.consOpenL hacl1 hin hFL hWn hcll hlbb hcb htb ⟨t, hInf⟩ hmemn
    have hLn : (fvsA.take (n + 1)).reverse ++ L0
        = Expr.fvar (B + n) E :: ((fvsA.take n).reverse ++ L0) := by
      rw [List.take_add_one, hx, Option.toList_some, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.cons_append]
    have hfs : fs.take (n + 1) = fs.take n ++ [fs.getD n pt] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show n < fs.length by omega)]
      rfl
    rw [hLn, hfs, consList_append, show B + (n + 1) = B + n + 1 from by omega]
    exact ⟨hFL.cons E hwty, _, h⟩

set_option maxHeartbeats 8000000 in
/-- **A call's target at a valuation of the holes, as a MEMBERSHIP**
(`targetCall_gen`'s steps (1)–(9), with no reading of the callee's major
domain): at every spine `bs` of the field's telescope,
the applied field lies in the reading of the call's member-abstracted
major domain, opened at the telescope's canonical openers, and that
reading is graded there.  The typing ran at the ABSTRACT frame (the
holes, then the fields' copies, `targetAbsFields`); read at the copies'
own values it is the member-abstracted reading at the holes' frame
(`move_read`, `move_interp`). -/
theorem targetCall_genW (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F rP nF : Nat} {fam : TargetFamily} {fvsPref fvsF fvsA : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {names : List Name} {lvls : List Level}
    {formerTys : List Expr} {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF teles
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF)))
      (ConLeche.targetMoveF rP fvsA) (rP + nF) formerTys.length
      (rP + nF + formerTys.length + nF) pw ih)
    (hA : fvsA = ConLeche.targetAbsFields names lvls (ConLeche.targetHoles formerTys (rP + nF)) rP
      (rP + nF + formerTys.length) [] fvsF)
    (hfA : ConLeche.targetAbsFieldsOk (ConLeche.fueledOps μ F) envT (rP + nF + formerTys.length)
      fvsA = .ok ())
    -- the frame
    (hlf : fvsF.length = nF)
    (hL : FvarList (rP + nF) (fvsPref ++ fvsF).reverse)
    {ρ : Nat → V} {xs fs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF)
    {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ (rP + nF) (consList (xs ++ fs) ρ) Δ (fvsPref ++ fvsF).reverse)
    (hfi : ih.field < nF)
    -- the telescope's and the index arguments' leaves
    (htL : ∀ b ∈ teles.getD ih.field [], ∀ l ∈ b.1.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    (hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    -- the holes
    {hv : List V} (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    -- every field in its member-abstracted type's reading
    (hii : ∀ j, j < nF → ∀ Aty : AnnotTerm,
      denoteMeta mT.acval envT φ (rP + nF + formerTys.length)
        (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))
          (fvsF.getD j default).fvarTypeD) = some Aty →
      fs.getD j pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty)
    (hRf : (fam.recTys.getD ih.callee (.sort .zero)).hasFvar = false)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mT.acval envT φ (rP + nF) [] ((teles.getD ih.field []).map (·.1))).getD []) bs) :
    ∃ (os' : List Expr) (Xr : AnnotTerm),
      LocList (rP + nF + formerTys.length) (teles.getD ih.field []).length os' ∧
      denoteMeta mT.acval envT φ (rP + nF + formerTys.length + (teles.getD ih.field []).length)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))
          C.majDom).instantiateList os' 0) = some Xr ∧
      bs.length = (teles.getD ih.field []).length ∧
      WellDenoted V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr ∧
      bs.foldl SetTheory.app (fs.getD ih.field pt)
        ∈ˢ interp V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  -- names
  generalize hD : rP + nF = D at *
  generalize hk : formerTys.length = k at *
  generalize hm : (teles.getD ih.field []).length = m at *
  have hlenS : (xs ++ fs).length = D := by rw [List.length_append, hxl, hfl]; omega
  -- (1) the holes' readings, and the context past them
  let Ts : List AnnotTerm := (List.range k).map fun t =>
    (denoteMeta mT.acval envT φ 0 (formerTys.getD t default)).getD default
  have hTsLen : Ts.length = k := by simp [Ts]
  have hTsGet : ∀ t, t < k → ∃ T, Ts.getD t default = T ∧
      denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
      Term.bvarsBelow 0 T.erase ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
      ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T := by
    intro t ht
    obtain ⟨hf, hb, -, T, hT, hG, hvT⟩ := hformer t (by omega)
    refine ⟨T, ?_, hT, bvarsBelow_of_reading (m := mT) (Expr.WScoped.of_not_hasFvar hf) hb hT,
      hG, hvT⟩
    have hT' := hT
    rw [List.getD_eq_getElem?_getD] at hT'
    simp [Ts, List.getD_eq_getElem?_getD, List.getElem?_range ht, hT']
  have hL0 : FvarList (D + k)
      ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    have h := fvarList_ihs hL formerTys (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      have := (hformer i (by omega)).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
      exact Expr.WScoped.of_not_hasFvar this)
    rw [hk] at h
    exact h
  have hW0 : WalkCtx V mT φ (D + k) (consList hv (consList (xs ++ fs) ρ))
      ((ihDomsLifted Ts).reverse ++ Δ)
      ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    have h := walkCtx_ihs hacl hL hW formerTys Ts hv (by rw [hTsLen, hk]) (by rw [hvl, hTsLen])
      (fun t ht => by
        rw [hTsLen] at ht
        obtain ⟨T, hTe, hT, hcl, hG, hvT⟩ := hTsGet t ht
        obtain ⟨hf, hb, hcb, -⟩ := hformer t (by omega)
        have hnl : ∀ l ∈ (formerTys.getD t default).fvarLeaves,
            Expr.fvar l.1 l.2 ∈ (fvsPref ++ fvsF).reverse := by
          intro l hl
          rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf] at hl
          exact nomatch hl
        refine ⟨hnl, hb, hcb, ?_, fun σ _ => by rw [hTe]; exact hG σ, ?_⟩
        · rw [hTe]
          exact denoteMeta_depth_of_closed hacl1 hf (fun j => liftN_eq_self_of_closed hcl j 1) hT D
        · rw [hTe]
          exact hvT _)
    rw [hTsLen] at h
    exact h
  -- the frame's and the holes' leaves
  have hframeL : ∀ x ∈ fvsPref ++ fvsF, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF :=
    frame_leaves_mem (Lf := fvsPref ++ fvsF) hL (fun x hx l hl =>
      List.mem_reverse.mp (hW.2.2.2.2.2.2 x (List.mem_reverse.mpr hx) l hl))
  have hinL0 : ∀ y ∈ fvsPref ++ fvsF,
      y ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse :=
    fun y hy => List.mem_append_right _ (List.mem_reverse.mpr hy)
  have habsL : ∀ e : Expr, (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) →
      ∀ l ∈ (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) e).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse := by
    intro e he l hl
    rcases ConLeche.targetAbs_fvarLeaves e l hl with h1 | ⟨h, hh, h1⟩
    · exact hinL0 _ (he l h1)
    · have hh' := hh
      simp only [ConLeche.targetHoles, List.mem_map, List.mem_range] at hh'
      obtain ⟨t', ht', rfl⟩ := hh'
      have hcl := (hformer t' (by omega)).1
      simp only [Expr.fvarLeaves, List.mem_cons,
        ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl, List.not_mem_nil, or_false] at h1
      subst h1
      exact List.mem_append_left _ (List.mem_reverse.mpr hh)
  -- the fields' types: framed, scoped
  have hfmemJ : ∀ j, j < nF → fvsF.getD j default ∈ fvsPref ++ fvsF := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_append_right _ (List.getElem_mem _)
  have hfmemF : ∀ j, j < nF → fvsF.getD j default ∈ fvsF := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hftyLJ : ∀ j, j < nF → ∀ l ∈ (fvsF.getD j default).fvarTypeD.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := fun j hj l hl =>
    List.mem_reverse.mp (hW.2.2.2.2.2.2 _ (List.mem_reverse.mpr (hfmemJ j hj)) l hl)
  have hholesWS : ∀ h ∈ ConLeche.targetHoles formerTys D, Expr.WScoped (D + k) h :=
    fun h hh => hL0.2.2 h (List.mem_append_left _ (List.mem_reverse.mpr hh))
  have hFW : ∀ f ∈ fvsF, Expr.WScoped (D + k) f.fvarTypeD := fun f hf =>
    (ConLeche.fvarTypeD_WScoped (hL.2.2 f (List.mem_reverse.mpr (List.mem_append_right _ hf)))).mono
      (by omega)
  -- the abstract fields
  obtain ⟨hlenA, hgetA⟩ := ConLeche.targetAbsFields_nil (names := names) (lvls := lvls)
    (holes := ConLeche.targetHoles formerTys D) (rP := rP) (D := D + k) fvsF
  rw [← hA] at hlenA hgetA
  have hlenA' : fvsA.length = nF := by rw [hlenA, hlf]
  have hAfv : ∀ j, j < nF → ∃ ty, fvsA[j]? = some (.fvar (D + k + j) ty) :=
    fun j hj => ⟨_, hgetA j (by omega)⟩
  have hAfvT : ∀ n, n ≤ nF → ∀ j, j < n → ∃ ty, (fvsA.take n)[j]? = some (.fvar (D + k + j) ty) :=
    fun n hn j hj => by
      obtain ⟨ty, hty⟩ := hAfv j (by omega)
      exact ⟨ty, by rw [List.getElem?_take_of_lt hj, hty]⟩
  have hxl' : xs.length = rP := hxl
  have hBk : rP + nF + k = D + k := by omega
  -- a field's member-abstracted type, moved to the copies before `n`, reads as unmoved
  have hmoveMem : ∀ j, j < nF → ∀ n, n ≤ nF → ∀ tb : AnnotTerm,
      denoteMeta mT.acval envT φ (D + k + n)
        (ConLeche.targetMoveF rP (fvsA.take n)
          (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)
            (fvsF.getD j default).fvarTypeD)) = some tb →
      fs.getD j pt ∈ˢ interp V (consList (fs.take n) (consList hv (consList (xs ++ fs) ρ))) tb := by
    intro j hj n hn tb htb
    have hX : Expr.fvarsBelow (D + k) (ConLeche.targetAbs names lvls
        (ConLeche.targetHoles formerTys D) (fvsF.getD j default).fvarTypeD) :=
      Expr.WScoped.fvarsBelow (ConLeche.targetAbs_WScoped hholesWS _ (hFW _ (hfmemF j hj)))
    have hr := move_read (φ := φ) mT (rP := rP) (B := D + k) (L := fvsA.take n) (n := n)
      (by rw [List.length_take]; omega) (hAfvT n hn) hX (LocList.nil _) (LocList.nil _)
    simp only [Expr.instantiateList_nil, Nat.add_zero] at hr
    rw [htb] at hr
    cases hR : denoteMeta mT.acval envT φ (D + k) (ConLeche.targetAbs names lvls
        (ConLeche.targetHoles formerTys D) (fvsF.getD j default).fvarTypeD) with
    | none => rw [hR] at hr; exact nomatch hr
    | some R =>
      rw [hR, Option.map_some] at hr
      obtain rfl := Option.some.inj hr
      have hi := (move_interp (ρ := ρ) hxl' hfl hvl hn hBk R []).1
      simp only [consList_nil, List.length_nil] at hi
      rw [hi]
      exact hii j hj R hR
  -- (2) the context past the holes: the fields' copies
  obtain ⟨hLA, ΔA, hWA⟩ := walkCtx_absFields hacl hin (nF := nF) hA hfA hlf hL0 hW0
    (fun j hj l hl => habsL _ (hftyLJ j hj) l hl) hFW hholesWS hfl
    (fun j hj tb htb => by
      rw [List.getD_eq_getElem?_getD, hgetA j (by omega), Option.getD_some] at htb
      exact hmoveMem j hj j (by omega) tb htb)
  have hWSA := hWA.2.2.2.2.1
  -- a moved term's leaves are the copies' or the holes' frame's
  have hmvL : ∀ e : Expr,
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈
        (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) →
      ∀ l ∈ (ConLeche.targetMoveF rP fvsA e).fvarLeaves, Expr.fvar l.1 l.2 ∈
        fvsA.reverse ++
          ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    intro e he l hl
    rcases ConLeche.targetMoveF_fvarLeaves e l hl with h | ⟨r, hr, h⟩
    · exact List.mem_append_right _ (he l h)
    · have hr' := List.mem_append_left
        ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse)
        (List.mem_reverse.mpr hr)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨tyj, htyj⟩ := hAfv j (by omega)
      have hrj : fvsA[j] = .fvar (D + k + j) tyj := (List.getElem?_eq_some_iff.mp htyj).2
      rw [hrj] at h hr'
      simp only [Expr.fvarLeaves, List.mem_cons] at h
      rcases h with rfl | h
      · exact hr'
      · exact hWA.2.2.2.2.2.2 _ hr' l h
  -- (3) the field's abstract type: framed, read, graded
  have hAL := hmvL _ (habsL _ (hftyLJ ih.field hfi))
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hfld)
  obtain ⟨Aty, hAty⟩ := acceptedReads_of mT φ C.hfld (wscoped_of_leaves_mem hLA _ hAL) hAb
    (fun l hl => hWSA _ (hAL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hLA hWA hAL hAb hAty
    ⟨_, Rules.inferTypeCore_bridge C.hfld⟩
  -- (4) the major type: framed, read, graded
  have hmajL : ∀ l ∈ C.majDom.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
    intro l hl
    have hl' : l ∈ C.calleeAt.fvarLeaves := by
      rw [C.hmajDom]; simp [Expr.fvarLeaves, hl]
    rcases ConLeche.instPisAtLift_fvarLeaves _ _ C.hcallee l hl' with h1 | ⟨x, hx, h1⟩
    · rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf] at h1; exact nomatch h1
    · rcases List.mem_append.mp hx with hx | hx
      · exact hframeL x (List.mem_append_left _ hx) l h1
      · exact hidxL x hx l h1
  have hWL : ∀ l ∈ (Expr.mkPisOf ((teles.getD ih.field []).map fun b =>
        (ConLeche.targetMoveF rP fvsA b.1, b.2))
      (ConLeche.targetMoveF rP fvsA
        (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) C.majDom))).fvarLeaves,
      Expr.fvar l.1 l.2 ∈
        fvsA.reverse ++
          ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    intro l hl
    rcases ConLeche.mkPisOf_fvarLeaves _ _ l hl with ⟨b, hb, h1⟩ | h1
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      exact hmvL _ (fun l' hl' => hinL0 _ (htL b' hb' l' hl')) l h1
    · exact hmvL _ (habsL _ hmajL) l h1
  have hWb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hwant)
  obtain ⟨WA, hWA'⟩ := acceptedReads_of mT φ C.hwant (wscoped_of_leaves_mem hLA _ hWL) hWb
    (fun l hl => hWSA _ (hWL l hl))
  obtain ⟨hFrW, hCW, hGW⟩ := WalkCtx.subjOkL hacl1 hin hLA hWA hWL hWb hWA'
    ⟨_, Rules.inferTypeCore_bridge C.hwant⟩
  -- (5) the call's typing: the two readings are one
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge C.hdeq) hFrA hFrW hCA hCW hAty hWA'
    hGA hGW _ hWA.2.1
  -- (6) the field lies in the major type's reading
  have hfW : fs.getD ih.field pt
      ∈ˢ interp V (consList fs (consList hv (consList (xs ++ fs) ρ))) WA := by
    rw [← heq]
    have := hmoveMem ih.field hfi nF (Nat.le_refl _) Aty
      (by rw [List.take_of_length_le (by omega)]; exact hAty)
    rwa [List.take_of_length_le (by omega)] at this
  -- (7) the major type's reading: a Π-tower over the moved telescope
  have hWA2 : denoteMeta mT.acval envT φ (D + k + nF + 0)
      ((Expr.mkPisOf ((teles.getD ih.field []).map fun b =>
        (ConLeche.targetMoveF rP fvsA b.1, b.2))
      (ConLeche.targetMoveF rP fvsA
        (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)
          C.majDom))).instantiateList [] 0) = some WA := by
    rw [ConLeche.Expr.instantiateList_nil]; exact hWA'
  obtain ⟨ds', Xr', osA, rfl, hdoms', -, hosA, hXr'⟩ :=
    denoteMeta_mkPisOf (acval := mT.acval) (env := envT) (φ := φ) (D := D + k + nF) _ _ 0 []
      _ (LocList.nil _) hWA2
  simp only [List.length_map] at hosA hXr'
  rw [Nat.zero_add, hm] at hosA hXr'
  -- (8) the telescope's spine fits the major type's binders
  have htleL : ∀ t ∈ (teles.getD ih.field []).map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < D := by
    intro t ht l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (htL b hb l hl)) l hl
  have hdeep := teleDoms_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D _ 0 [] []
    htleL (LocList.nil D) (LocList.nil (D + k))
  have htWS : ∀ tW ∈ (teles.getD ih.field []).map (·.1), Expr.WScoped (D + k) tW := by
    intro tW ht
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact wscoped_of_leaves_mem hL0 _ (fun l hl => hinL0 _ (htL b hb l hl))
  have hsub := teleDoms_substFvars mT (φ := φ) (b := D + k) (B := D + k + nF)
    (s := moveS rP nF (D + k)) (moveS_ok (rP := rP) (n := nF) (B := D + k))
    (((teles.getD ih.field []).map fun b => (ConLeche.targetMoveF rP fvsA b.1, b.2)).map (·.1))
    ((teles.getD ih.field []).map (·.1)) 0 [] [] (LocList.nil _) (LocList.nil _) (by simp)
    (fun l tR tW hR hW' => by
      simp only [List.map_map, List.getElem?_map] at hR hW'
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hR
      rw [hb, Option.map_some, Option.some.injEq] at hW'
      subst hW'
      exact targetMoveF_erasedEq hlenA' hAfv _
        (Expr.WScoped.fvarsBelow (htWS _ (List.mem_map_of_mem (List.mem_of_getElem? hb)))))
    (fun tW ht => Expr.WScoped.fvarsBelow (htWS tW ht))
  rw [hdoms'] at hsub
  obtain ⟨dsB, hdsB, hdsEq⟩ : ∃ dsB, teleDoms mT.acval envT φ (D + k) []
      ((teles.getD ih.field []).map (·.1)) = some dsB ∧
      ds'.map (·.2.2) = substAt (moveTau rP nF (D + k)) 0 dsB := by
    cases h : teleDoms mT.acval envT φ (D + k) [] ((teles.getD ih.field []).map (·.1)) with
    | none => rw [h] at hsub; exact nomatch hsub
    | some dsB => rw [h, Option.map_some] at hsub; exact ⟨dsB, rfl, Option.some.inj hsub⟩
  obtain ⟨ts, hts, hlift⟩ : ∃ ts, teleDoms mT.acval envT φ D [] ((teles.getD ih.field []).map (·.1))
      = some ts ∧ dsB = liftAt k 0 ts := by
    cases hts : teleDoms mT.acval envT φ D [] ((teles.getD ih.field []).map (·.1)) with
    | none => rw [hts, hdsB] at hdeep; exact nomatch hdeep
    | some ts => rw [hts, hdsB] at hdeep; exact ⟨ts, rfl, Option.some.inj hdeep⟩
  rw [hts, Option.getD_some] at hbs
  have hbsH : SpineFit (consList hv (consList (xs ++ fs) ρ)) dsB bs := by
    rw [hlift, spineFit_liftAt, ← hvl, shiftE_consList]; exact hbs
  have hfsT : fs.take nF = fs := List.take_of_length_le (by omega)
  have hbsA : SpineFit (consList fs (consList hv (consList (xs ++ fs) ρ)))
      (ds'.map (·.2.2)) bs := by
    have hE := substE_moveTau (ρ := ρ) hxl' hfl hvl (Nat.le_refl _) hBk
    rw [hfsT] at hE
    rw [hdsEq, spineFit_substAt, hE]
    exact hbsH
  have hbl : bs.length = m := by
    rw [hbs.length_eq, teleDoms_length _ _ hts, List.length_map, hm]
  -- (9) the applied field lies in the Π's body, which is graded there
  have hGWσ := hGW _ hWA.2.1
  have hfoldA : bs.foldl SetTheory.app (fs.getD ih.field pt)
      ∈ˢ interp V (consList bs (consList fs (consList hv (consList (xs ++ fs) ρ)))) Xr' :=
    foldl_app_mem_mkPisAV hGWσ.2 hbsA hfW
  have hwdA : WellDenoted V (consList bs (consList fs (consList hv (consList (xs ++ fs) ρ)))) Xr' :=
    (WellDenoted_mkPisAV_inv hGWσ.1).2 bs hbsA
  -- (10) back to the holes' frame: the body unmoved
  have hmajWS : Expr.WScoped (D + k)
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) C.majDom) :=
    ConLeche.targetAbs_WScoped hholesWS _
      (wscoped_of_leaves_mem hL0 _ (fun l hl => hinL0 _ (hmajL l hl)))
  have hr := move_read (φ := φ) mT (rP := rP) (B := D + k) (L := fvsA) (n := nF) hlenA' hAfv
    (Expr.WScoped.fvarsBelow hmajWS) (locOpen_locList (D + k) m) hosA
  rw [hXr'] at hr
  cases hX : denoteMeta mT.acval envT φ (D + k + m)
      ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) C.majDom).instantiateList
        (locOpen (D + k) m) 0) with
  | none => rw [hX] at hr; exact nomatch hr
  | some Xr =>
    rw [hX, Option.map_some] at hr
    obtain rfl := Option.some.inj hr
    have hi := move_interp (ρ := ρ) hxl' hfl hvl (Nat.le_refl _) hBk Xr bs
    rw [hfsT, hbl] at hi
    exact ⟨locOpen (D + k) m, Xr, locOpen_locList (D + k) m, hX, hbl, hi.2.mp hwdA,
      hi.1 ▸ hfoldA⟩


set_option maxHeartbeats 8000000 in
/-- **A call's target at a valuation of the holes, from its typing run.**
At the frame `D = rP + nF` (prefix and fields, `hW`) extended by the
member holes at values `hv` of their formers' types, with every field in
its member-abstracted type's reading (`hii`) and the call's major domain
the callee's member `I` (hole `t`) at the prefix's parameters and the
index arguments (`hmaj`): at every spine `bs` of the field's telescope
the parameters and the index readings fit the hole's type's binder
data, and the applied field lies in the hole applied to them. -/
theorem targetCall_gen (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F rP nF : Nat} {fam : TargetFamily} {fvsPref fvsF fvsA : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {names : List Name} {lvls : List Level}
    {formerTys : List Expr} {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF teles
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF)))
      (ConLeche.targetMoveF rP fvsA) (rP + nF) formerTys.length
      (rP + nF + formerTys.length + nF) pw ih)
    (hA : fvsA = ConLeche.targetAbsFields names lvls (ConLeche.targetHoles formerTys (rP + nF)) rP
      (rP + nF + formerTys.length) [] fvsF)
    (hfA : ConLeche.targetAbsFieldsOk (ConLeche.fueledOps μ F) envT (rP + nF + formerTys.length)
      fvsA = .ok ())
    -- the frame
    (hlp : fvsPref.length = rP) (hlf : fvsF.length = nF)
    (hL : FvarList (rP + nF) (fvsPref ++ fvsF).reverse)
    {ρ : Nat → V} {xs fs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF)
    {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ (rP + nF) (consList (xs ++ fs) ρ) Δ (fvsPref ++ fvsF).reverse)
    (hfi : ih.field < nF)
    -- the telescope's and the index arguments' leaves
    (htL : ∀ b ∈ teles.getD ih.field [], ∀ l ∈ b.1.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    (hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    -- the holes
    {hv : List V} (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    (hii : ∀ j, j < nF → ∀ Aty : AnnotTerm,
      denoteMeta mT.acval envT φ (rP + nF + formerTys.length)
        (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))
          (fvsF.getD j default).fvarTypeD) = some Aty →
      fs.getD j pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty)
    -- the call's major domain: the callee's member at the parameters and the indices
    {I : Name} {t nP : Nat} (hnP : nP ≤ rP)
    (hRf : (fam.recTys.getD ih.callee (.sort .zero)).hasFvar = false)
    (hmaj : ∀ os : List Expr, LocList (rP + nF + formerTys.length) (teles.getD ih.field []).length os →
      C.majDom.instantiateList os 0 = Expr.mkAppN (.const I lvls)
        ((fvsPref.take nP).map (·.instantiateList os 0) ++ ih.idx.map (·.instantiateList os 0)))
    (hI : names.findIdx? (· == I) = some t) (ht : t < formerTys.length)
    {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm}
    (hTt : denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some (mkPisAV pds R))
    (hpdsNZ : ∀ d ∈ pds, d.2.1 ≠ 0) (hpdsLen : pds.length = nP + ih.idx.length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mT.acval envT φ (rP + nF) [] ((teles.getD ih.field []).map (·.1))).getD []) bs) :
    SpineFit ρ (pds.map (·.2.2))
      (xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          (x.instantiateList (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD
          default))) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          ((Expr.mkAppN (fvsF.getD ih.field default)
            (ConLeche.structTeleVars (teles.getD ih.field []).length)).instantiateList
            (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD default)
      ∈ˢ (xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          (x.instantiateList (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD
          default))).foldl SetTheory.app (hv.getD t pt) := by
  obtain ⟨os', Xr, hos', hXr, hbl, hwdX, hfold⟩ := targetCall_genW hμ hacl hin C hA hfA hlf hL
    hxl hfl hW hfi htL hidxL hvl hformer hii hRf bs hbs
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  -- names
  generalize hD : rP + nF = D at *
  generalize hk : formerTys.length = k at *
  generalize hm : (teles.getD ih.field []).length = m at *
  have hlenS : (xs ++ fs).length = D := by rw [List.length_append, hxl, hfl]; omega
  have hframeL : ∀ x ∈ fvsPref ++ fvsF, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF :=
    frame_leaves_mem (Lf := fvsPref ++ fvsF) hL (fun x hx l hl =>
      List.mem_reverse.mp (hW.2.2.2.2.2.2 x (List.mem_reverse.mpr hx) l hl))
  -- (10) the body's syntax: the hole applied to the parameters and the indices
  have hfvPref : ∀ i, i < rP → ∃ ty, (fvsPref ++ fvsF)[i]? = some (Expr.fvar i ty) := by
    intro i hi
    have hlt : i < (fvsPref ++ fvsF).length := by
      simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hL.reverse_idx i _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    exact ⟨ty, by rw [List.getElem?_eq_getElem hlt, hty]⟩
  have hprefAbs : (fvsPref.take nP).map (ConLeche.targetAbs names lvls
      (ConLeche.targetHoles formerTys D)) = fvsPref.take nP := by
    refine (List.map_congr_left (g := id) fun x hx => ?_).trans (List.map_id _)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (List.mem_of_mem_take hx)
    obtain ⟨ty, hty⟩ := hfvPref i (by omega)
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hget] at hty
    obtain rfl := Option.some.inj hty
    rfl
  have hholeT : ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) (.const I lvls)
      = Expr.fvar (D + t) (formerTys.getD t default) := by
    simp only [ConLeche.targetAbs, beq_self_eq_true, if_true, hI]
    rw [List.getD_eq_getElem?_getD, ConLeche.targetHoles, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  have hprefInst : (fvsPref.take nP).map (·.instantiateList os' 0) = fvsPref.take nP := by
    refine (List.map_congr_left (g := id) fun x hx => ?_).trans (List.map_id _)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (List.mem_of_mem_take hx)
    obtain ⟨ty, hty⟩ := hfvPref i (by omega)
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hget] at hty
    obtain rfl := Option.some.inj hty
    simp [Expr.instantiateList]
  have hholesF : ∀ h ∈ ConLeche.targetHoles formerTys D, ∃ i ty, h = Expr.fvar i ty := by
    intro h hh
    simp only [ConLeche.targetHoles, List.mem_map] at hh
    obtain ⟨t', -, rfl⟩ := hh
    exact ⟨_, _, rfl⟩
  have hosF : ∀ o ∈ os', ∃ i ty, o = Expr.fvar i ty := by
    intro o ho
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem ho
    obtain ⟨ty, hty⟩ := hos'.2 j (by rw [← hos'.1]; exact hj)
    rw [List.getElem?_eq_getElem hj, hget] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  have hAbsMaj : (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)
      C.majDom).instantiateList os' 0
      = Expr.mkAppN (Expr.fvar (D + t) (formerTys.getD t default))
          (fvsPref.take nP ++ ih.idx.map (·.instantiateList os' 0)) := by
    rw [← targetAbs_instantiateList hholesF hosF, hmaj os' hos', targetAbs_mkAppN, hholeT,
      List.map_append, hprefInst, hprefAbs, List.map_map]
    congr 2
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp]
    rw [targetAbs_instantiateList hholesF hosF, C.hidxAbs x hx]
  rw [hAbsMaj] at hXr
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hXr
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  -- (11) the head's value: the hole's
  have hhead : interp V (consList bs (consList hv (consList (xs ++ fs) ρ)))
      (AnnotTerm.bvar (D + k + m - 1 - (D + t))) = hv.getD t pt := by
    rw [interp_bvar, show D + k + m - 1 - (D + t) = (k - 1 - t) + bs.length from by omega,
      consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hvl,
      show k - 1 - (k - 1 - t) = t from by omega]
  -- (12) the spine fits the hole's type's binder data
  obtain ⟨-, -, -, T, hT, -, hvT⟩ := hformer t ht
  obtain rfl : T = mkPisAV pds R := Option.some.inj (hT.symm.trans hTt)
  have hvsLen : vs.length = pds.length := by
    rw [← hvs.length, hpdsLen, List.length_append, List.length_take, hlp, List.length_map]; omega
  have hsp := spineFit_of_wellDenoted_mkAppN_pi (σ := ρ) hpdsNZ hwdX (by rw [hhead]; exact hvT ρ)
    hvsLen
  -- (13) the spine's values: the parameters and the index readings
  have hτ : consList bs (consList hv (consList (xs ++ fs) ρ)) = consList (hv ++ bs) (consList (xs ++ fs) ρ) :=
    (consList_append hv bs _).symm
  have hvals : vs.map (interp V (consList bs (consList hv (consList (xs ++ fs) ρ))))
      = xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0)).getD
            default)) := by
    rw [spine_map_getD hvs, List.map_append]
    congr 1
    · apply List.ext_getElem (by simp [hlp, hxl])
      intro i h1 h2
      simp only [List.length_map, List.length_take] at h1
      have hi : i < rP := by omega
      obtain ⟨ty, hty⟩ := hfvPref i hi
      rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)] at hty
      simp only [List.getElem_map, List.getElem_take]
      rw [Option.some.inj hty, denoteMeta_fvar, Option.getD_some, hτ,
        show D + k + m - 1 - i = D + (hv ++ bs).length - 1 - i from by
          rw [List.length_append, hvl, hbl]; omega,
        interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some]
    · rw [List.map_map]
      refine List.map_congr_left fun x hx => ?_
      have hxL : ∀ l ∈ x.fvarLeaves, l.1 < D :=
        leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (hidxL x hx l hl))
      have hd := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D x m
        (locOpen D m) os' hxL (locOpen_locList D m) hos'
      obtain ⟨A1, hA1⟩ := spine_reads hvs _ (List.mem_append_right _ (List.mem_map_of_mem hx))
      rw [hA1] at hd
      cases hA0 : denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0) with
      | none => rw [hA0] at hd; exact nomatch hd
      | some A0 =>
        rw [hA0, Option.map_some] at hd
        simp only [Function.comp, hA1, Option.getD_some]
        rw [Option.some.inj hd, interp_liftN, shiftE_consList_ih hbl hvl]
  -- (14) the applied field's value
  have hfvF : ∃ ty, fvsF.getD ih.field default = Expr.fvar (rP + ih.field) ty := by
    have hlt : rP + ih.field < (fvsPref ++ fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hL.reverse_idx (rP + ih.field) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem_append_right (by omega)] at hty
    simpa [hlp] using hty
  obtain ⟨fty0, hfty0⟩ := hfvF
  have hfap : interp V (consList bs (consList (xs ++ fs) ρ))
      ((denoteMeta mT.acval envT φ (D + m)
        ((Expr.mkAppN (fvsF.getD ih.field default) (ConLeche.structTeleVars m)).instantiateList
          (locOpen D m) 0)).getD default)
      = bs.foldl SetTheory.app (fs.getD ih.field pt) := by
    rw [instantiateList_mkAppN, hfty0]
    simp only [Expr.instantiateList]
    rw [denoteMeta_mkAppN (denoteMetaSpine_teleVars (acval := mT.acval) (env := envT) (φ := φ)
      (locOpen_locList D m) (Nat.le_refl m)) (denoteMeta_fvar _ _ _ _), Option.getD_some,
      interp_mkAppN_foldl, map_teleVarsAV_interp' hbl,
      show D + m - 1 - (rP + ih.field) = D + bs.length - 1 - (rP + ih.field) from by rw [hbl],
      interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_⟩
  · rw [← hvals]; exact hsp
  · rw [hfap, ← hvals, ← hhead, ← interp_mkAppN_foldl]
    exact hfold

end Gen

end ConLeche.Model
