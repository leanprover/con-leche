module

public import ConLeche.Model.Inductives.TargetCallTie
public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Verify.InstList
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Shift
import ConLeche.Verify.SubstFvars
import ConLeche.Semantics.SubstAV
import ConLeche.Semantics.Inductives.HoleApp
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.SumKit
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.PosFieldLeaf
import ConLeche.Model.Inductives.TargetCallRead
public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Verify.Inductives.PosNodes

public section

/-!
# A call, walked

K.53′ ties a call's callee major, under the call's telescope, to the
walk's normal form of the called field (`callTie`).  At a node's
constructor read at an admissible frame (the walk valuation `σW`, which
agrees off the holes with the rule's valuation seen through the walk's
substitution), this is the call's semantics on the WALK's side
(`callWalkSyn`, `callWalkSem`): the call's telescope fits there exactly when the walk's
field telescope does, so the call target — the field applied along the
telescope — lies in the walk's leaf read at `σW`; the leaf is a member
hole, a frame hole or a container instance whose head is the callee's
major's (a leaf naming no member and no hole contradicts K.53′ with
official's `is_nested`: the callee's major names a member); and the
call's index readings are the leaf's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole BinderMeta nestHoleConst extendF CheckM
  PosD PosKind PosTree nestArity nestContainer closeTelescope targetPiDomsWith)

universe w

/-! ## Syntactic kit -/

theorem substFvars_mkAppN {b D : Nat} {s : Nat → Expr} :
    ∀ (as : List Expr) (f : Expr),
      Expr.substFvars b D s (Expr.mkAppN f as)
        = Expr.mkAppN (Expr.substFvars b D s f) (as.map (Expr.substFvars b D s))
  | [], _ => rfl
  | a :: as, f => by
    show Expr.substFvars b D s (Expr.mkAppN (.app f a) as) = _
    rw [substFvars_mkAppN as (.app f a)]
    rfl

theorem fvarsBelow_of_erasedEq {d : Nat} :
    ∀ {a b : Expr}, Expr.ErasedEq a b → Expr.fvarsBelow d b → Expr.fvarsBelow d a := by
  intro a
  induction a with
  | bvar i => intro b _ _; simp [Expr.fvarsBelow]
  | fvar i ty _ =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    subst h
    simpa [Expr.fvarsBelow] using hb
  | sort u => intro b _ _; simp [Expr.fvarsBelow]
  | const n us => intro b _ _; simp [Expr.fvarsBelow]
  | lit l => intro b _ _; simp [Expr.fvarsBelow]
  | app f x ihf ihx =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at hb ⊢
    exact ⟨ihf h.1 hb.1, ihx h.2 hb.2⟩
  | lam t bd m iht ihb =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at hb ⊢
    exact ⟨iht h.2.1 hb.1, ihb h.2.2 hb.2⟩
  | forallE t bd m iht ihb =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at hb ⊢
    exact ⟨iht h.2.1 hb.1, ihb h.2.2 hb.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at hb ⊢
    exact ⟨iht h.1 hb.1, ihv h.2.1 hb.2.1, ihb h.2.2 hb.2.2⟩
  | proj s i e ih =>
    intro b h hb
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at hb ⊢
    exact ih h.2.2 hb

/-- **A read-back mentions no member constant** when the term mentions no
member and no hole and the read-back maps every variable outside the
hole range to a term mentioning no member constant. -/
theorem nestOcc_replaceFVars_zero {names : List Name} {lo hi : Nat} {f : Nat → Option Expr}
    (hf : ∀ v y, f v = some y → (lo ≤ v ∧ v < hi) ∨ y.nestOcc names 0 0 = false) :
    ∀ (e : Expr), e.nestOcc names lo hi = false → (e.replaceFVars f).nestOcc names 0 0 = false := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro h
    simp only [Expr.nestOcc, decide_eq_false_iff_not] at h
    simp only [Expr.replaceFVars]
    cases hfi : f i with
    | none => simp [Expr.nestOcc]
    | some y =>
      rcases hf i y hfi with h' | h'
      · exact absurd h' h
      · simpa using h'
  | sort u => intro _; rfl
  | const n us => intro h; simpa [Expr.replaceFVars, Expr.nestOcc] using h
  | lit l => intro _; rfl
  | app a b iha ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceFVars, Expr.nestOcc, iha h.1, ihb h.2, Bool.or_false]
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceFVars, Expr.nestOcc, iht h.1, ihb h.2, Bool.or_false]
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceFVars, Expr.nestOcc, iht h.1, ihb h.2, Bool.or_false]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceFVars, Expr.nestOcc, iht h.1.1, ihv h.1.2, ihb h.2, Bool.or_false]
  | proj s i e ih =>
    intro h
    simp only [Expr.nestOcc] at h
    simp only [Expr.replaceFVars, Expr.nestOcc, ih h]

theorem nestOcc_mkPisOf {names : List Name} {lo hi : Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (X : Expr),
      (Expr.mkPisOf tele X).nestOcc names lo hi
        = (tele.any (fun p => p.1.nestOcc names lo hi) || X.nestOcc names lo hi)
  | [], X => by simp [Expr.mkPisOf]
  | (t, bm) :: r, X => by
    simp only [Expr.mkPisOf, Expr.nestOcc, nestOcc_mkPisOf r X, List.any_cons, Bool.or_assoc]

theorem nestOcc_mkAppN {names : List Name} {lo hi : Nat} :
    ∀ (as : List Expr) (f : Expr),
      (Expr.mkAppN f as).nestOcc names lo hi = (f.nestOcc names lo hi || as.any (·.nestOcc names lo hi))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).nestOcc names lo hi = _
    rw [nestOcc_mkAppN as (.app f a)]
    simp [Expr.nestOcc, Bool.or_assoc]

/-- A spine headed by a variable or a constant is no `∀`. -/
theorem notPi_mkAppN {f : Expr} (hf : NotPi f) : ∀ (as : List Expr), NotPi (Expr.mkAppN f as)
  | [] => hf
  | a :: as => notPi_mkAppN (f := .app f a) (fun _ _ _ h => nomatch h) as

/-- A term whose opening is no `∀` is no `∀`. -/
theorem notPi_of_instantiateList {os : List Expr} {k : Nat} {e : Expr}
    (h : NotPi (e.instantiateList os k)) : NotPi e := by
  intro a b bm he
  subst he
  exact h (a.instantiateList os k) (b.instantiateList os (k + 1)) bm
    (by simp [Expr.instantiateList])

/-- A fvar list's members are variables. -/
theorem fvars_of_locList {rP : Nat} {fvsF : List Expr}
    (h : ∀ l, l < fvsF.length → ∃ ty, fvsF[l]? = some (.fvar (rP + l) ty)) :
    ∀ x ∈ fvsF, ∃ j ty, x = .fvar j ty := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hty⟩ := h l hl
  rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hty
  exact ⟨_, _, hty⟩

theorem fvarsBelow_mkPisOf {d : Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (X : Expr), Expr.fvarsBelow d (Expr.mkPisOf tele X) →
      (∀ p ∈ tele, Expr.fvarsBelow d p.1) ∧ Expr.fvarsBelow d X
  | [], X, h => ⟨fun _ hp => (nomatch hp), h⟩
  | (t, bm) :: r, X, h => by
    simp only [Expr.mkPisOf, Expr.fvarsBelow] at h
    obtain ⟨h1, h2⟩ := fvarsBelow_mkPisOf r X h.2
    refine ⟨fun p hp => ?_, h2⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact h1 p hp

theorem getAppFn_ne_app : ∀ (e f a : Expr), e.getAppFn ≠ .app f a
  | .app g b, f, a => by simpa [Expr.getAppFn] using getAppFn_ne_app g f a
  | .bvar _, _, _ | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lam _ _ _, _, _
  | .forallE _ _ _, _, _ | .letE _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by
    simp [Expr.getAppFn]

theorem getApp_of_not_app {e : Expr} (h : ∀ f a, e ≠ .app f a) :
    e.getAppFn = e ∧ e.getAppArgs = [] := by
  cases e with
  | app f a => exact absurd rfl (h f a)
  | _ => exact ⟨rfl, rfl⟩

theorem substFvars_not_app {b D : Nat} {s : Nat → Expr} (hs : ∀ v, v < b → ∀ f a, s v ≠ .app f a)
    {e : Expr} (he : ∀ f a, e ≠ .app f a) : ∀ f a, Expr.substFvars b D s e ≠ .app f a := by
  intro f a h
  cases e with
  | app g c => exact he g c rfl
  | fvar v ty =>
    by_cases hv : v < b
    · rw [Expr.substFvars_fvar_lt hv] at h; exact hs v hv f a h
    · rw [Expr.substFvars_fvar_ge (by omega)] at h; exact nomatch h
  | _ => simp [Expr.substFvars] at h

theorem fvarsBelow_mkAppN_args {d : Nat} :
    ∀ (as : List Expr) {f : Expr}, Expr.fvarsBelow d (Expr.mkAppN f as) → ∀ a ∈ as, Expr.fvarsBelow d a
  | [], _, _, a, ha => nomatch ha
  | x :: as, f, h, a, ha => by
    have h' : Expr.fvarsBelow d (Expr.mkAppN (.app f x) as) := h
    rcases List.mem_cons.mp ha with rfl | ha
    · have := fvarsBelow_mkAppN_head as h'
      simp only [Expr.fvarsBelow] at this
      exact this.2
    · exact fvarsBelow_mkAppN_args as h' a ha
where
  fvarsBelow_mkAppN_head : ∀ (as : List Expr) {f : Expr}, Expr.fvarsBelow d (Expr.mkAppN f as) →
      Expr.fvarsBelow d f
    | [], _, h => h
    | y :: as, f, h => by
      have := fvarsBelow_mkAppN_head as (f := .app f y) h
      simp only [Expr.fvarsBelow] at this
      exact this.1

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 16000000 in
/-- **A call, walked — the syntax** (see the module docstring): K.53′ at
the walk's normal form of the called field makes the call's telescope the
walk's field telescope substituted, the callee's major (opened at the
telescope's variables) the walk's leaf substituted, and the leaf a member
hole, a frame hole or a container instance with the callee major's head. -/
theorem callWalkSyn {ops : ConLeche.CheckerOps CheckM} {envW : Env}
    (hwb : ∀ d e w, ops.whnf envW d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true)
    {ctx : NestCtx} {prog : List NestHole}
    {nds : List (Expr × BinderMeta)} {cur : Expr}
    (hndC : ∀ (l : Nat) (p : Expr × BinderMeta), nds[l]? = some p →
      p.1.looseBVarsBounded 0 = true ∧ Expr.WScoped (ctx.hiAt prog.length + l) p.1)
    (hcurC : cur.looseBVarsBounded 0 = true)
    {rP : Nat} {fvsF : List Expr}
    (hfvF : ∀ l, l < fvsF.length → ∃ ty, fvsF[l]? = some (.fvar (rP + l) ty))
    (hlenF : fvsF.length = nds.length)
    {i : Nat} (hi : i < nds.length) {nd : Expr} (hnd : nds[i]?.map (·.1) = some nd)
    {e : Expr} {k : PosKind} {tsi : List PosTree}
    (hfd : PosD ops envW ctx (.field prog (ctx.hiAt prog.length + i) 0 e k nd) tsi)
    (he : e.looseBVarsBounded 0 = true)
    {tele : List (Expr × BinderMeta)} {majDom : Expr}
    (hK : ((targetPiDomsWith fvsF ((closeTelescope nds (ctx.hiAt prog.length) cur).replaceFVars
        (nestHoleConst ctx prog))).getD [])[i]?.map Expr.eraseFVarTys
      = some (Expr.mkPisOf tele majDom).eraseFVarTys)
    {I : Name} {us : List Level} {P idxR : List Expr}
    (hmajO : majDom.instantiateList (locOpen (rP + fvsF.length) tele.length) 0
      = Expr.mkAppN (.const I us) (P ++ idxR))
    (hment : (Expr.mkAppN (.const I us) P).nestOcc ctx.names 0 0 = true) :
    ∃ (teleW : List (Expr × BinderMeta)) (leafC w : Expr),
      nd = Expr.mkPisOf teleW leafC ∧ tele.length = teleW.length ∧
      (∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → teleW[l]? = some p' →
        p.2 = p'.2 ∧ Expr.ErasedEq p.1 (Expr.substFvars (ctx.hiAt prog.length + i)
          (rP + fvsF.length) (callSubst ctx prog fvsF) p'.1)) ∧
      (∀ p ∈ teleW, p.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false ∧
        Expr.fvarsBelow (ctx.hiAt prog.length + i) p.1) ∧
      (∀ os, LocList (ctx.hiAt prog.length + i) teleW.length os →
        Expr.ErasedEq (leafC.instantiateList os 0) w) ∧
      Expr.fvarsBelow (ctx.hiAt prog.length + i + teleW.length) w ∧
      w.getAppArgs.length = P.length + idxR.length ∧
      (∀ (q : Nat) (xM xW : Expr), (P ++ idxR)[q]? = some xM → w.getAppArgs[q]? = some xW →
        Expr.ErasedEq xM (Expr.substFvars (ctx.hiAt prog.length + i) (rP + fvsF.length)
          (callSubst ctx prog fvsF) xW)) ∧
      ( (∃ t ty, t < ctx.names.length ∧ w.getAppFn = .fvar (ctx.nP + t) ty ∧
          I = ctx.names.getD t .anonymous ∧ us = ctx.lps.map .param ∧
          w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD t 0 ∧
          w.getAppArgs.take ctx.nP = ctx.params ∧
          (∀ y ∈ w.getAppArgs, y.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)) ∨
        (∃ v ty h, ctx.hiAt 0 ≤ v ∧ v < ctx.hiAt prog.length ∧ w.getAppFn = .fvar v ty ∧
          prog.reverse[v - ctx.hiAt 0]? = some h ∧ I = h.key.cname ∧ us = h.key.lvls ∧
          h.key.ds.length ≤ w.getAppArgs.length ∧
          w.getAppArgs.take h.key.ds.length = h.key.ds ∧
          (∀ y ∈ w.getAppArgs.drop h.key.ds.length,
            y.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
          w.getAppArgs.length = nestArity ctx h.key.cname) ∨
        (∃ u nPc L, u ∈ tsi ∧ u.occ = prog ∧ w.getAppFn = .const I us ∧
          nestContainer ctx I = some (nPc, L) ∧ nPc ≤ w.getAppArgs.length ∧
          u.key = ⟨I, us, w.getAppArgs.take nPc⟩ ∧
          (∀ y ∈ w.getAppArgs.drop nPc,
            y.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)) ) := by
  generalize hB : rP + fvsF.length = B at *
  have hsb : ∀ v, v < ctx.hiAt prog.length + i →
      (callSubst ctx prog fvsF v).looseBVarsBounded 0 = true := by
    intro v hv
    unfold callSubst
    split
    · rfl
    · split
      · rename_i h1 h2
        obtain ⟨n, us', hc⟩ := nestHoleConst_hole (prog := prog) (by omega) h2
        rw [hc]; rfl
      · rename_i h2
        have hl : v - ctx.hiAt prog.length < fvsF.length := by omega
        rw [List.getElem?_eq_getElem hl, Option.getD_some]
        obtain ⟨ty, hty⟩ := hfvF _ hl
        rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hty
        rw [hty]; rfl
  have hfvs := fvars_of_locList hfvF
  have hiF : i ≤ fvsF.length := by omega
  -- the called field's normal form
  obtain ⟨p, hp, hpnd⟩ : ∃ p, nds[i]? = some p ∧ p.1 = nd := by
    cases h : nds[i]? with
    | none => rw [h] at hnd; exact nomatch hnd
    | some p => rw [h] at hnd; exact ⟨p, rfl, Option.some.inj hnd⟩
  obtain ⟨hndB, hndW⟩ := hndC i p hp
  rw [hpnd] at hndB hndW
  have hndF : nd.fvarsBelow (ctx.hiAt prog.length + i) := hndW.fvarsBelow
  -- K.53′: the recorded field IS the callee's major type under the telescope
  have hKE : Expr.ErasedEq
      (nd.replaceFVars (extendF (nestHoleConst ctx prog) (ctx.hiAt prog.length) (fvsF.take i)))
      (Expr.mkPisOf tele majDom) := by
    cases hdoms : targetPiDomsWith fvsF ((closeTelescope nds (ctx.hiAt prog.length) cur).replaceFVars
        (nestHoleConst ctx prog)) with
    | none => rw [hdoms] at hK; simp at hK
    | some doms =>
      rw [hdoms, Option.getD_some] at hK
      cases hd0 : doms[i]? with
      | none => rw [hd0] at hK; exact nomatch hK
      | some d0 =>
        rw [hd0, Option.map_some, Option.some.injEq] at hK
        obtain ⟨p', hp', hd0E⟩ := targetPiDomsWith_close nds (ctx.hiAt prog.length) cur
          (nestHoleConst ctx prog) fvsF doms (fun v hv => nestHoleConst_ge hv)
          (fun v y hy => by
            unfold nestHoleConst at hy
            split at hy
            · cases hy; rfl
            · split at hy
              · obtain ⟨h', -, rfl⟩ := Option.map_eq_some_iff.mp hy; rfl
              · exact nomatch hy)
          (fun y hy => by obtain ⟨j, ty, rfl⟩ := hfvs y hy; rfl)
          (fun q hq => by
            obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hq
            exact (hndC l _ (List.getElem?_eq_getElem hl)).1)
          hcurC (by omega) hdoms i d0 hd0
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        rw [hd0E, hpnd] at hK
        exact Expr.eraseFVarTys_eq_iff.mp hK
  -- the walk's leaf
  obtain ⟨-, teleW, leafC, w, hshape, hteleH, hopen, hleaf⟩ :=
    posD_field_leaf hwb hfd (by omega) he
  obtain ⟨hteleF, hleafF⟩ := fvarsBelow_mkPisOf teleW leafC (hshape ▸ hndF)
  have hosW := locOpen_locList (ctx.hiAt prog.length + i) teleW.length
  have hwE := hopen _ hosW
  have hwF : Expr.fvarsBelow (ctx.hiAt prog.length + i + teleW.length) w :=
    fvarsBelow_of_erasedEq hwE.symm (fvarsBelow_instantiateList _ (by simpa using hosW.fvarsBelow)
      leafC 0 (Expr.fvarsBelow_mono (Nat.le_add_right _ _) hleafF))
  -- the callee's major names a member
  have hmajM : majDom.nestOcc ctx.names 0 0 = true := by
    rw [← nestOcc_instantiateList_locList (Nat.zero_le _) tele.length _ (locOpen_locList B _) majDom 0,
      hmajO]
    rw [nestOcc_mkAppN] at hment ⊢
    rw [List.any_append]
    simp only [Bool.or_eq_true] at hment ⊢
    rcases hment with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  -- the common part: the telescope, the major's head and arguments
  have common : NotPi w →
      tele.length = teleW.length ∧
      (∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → teleW[l]? = some p' →
        p.2 = p'.2 ∧ Expr.ErasedEq p.1 (Expr.substFvars (ctx.hiAt prog.length + i) B
          (callSubst ctx prog fvsF) p'.1)) ∧
      Expr.ErasedEq (.const I us)
        (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) w.getAppFn) ∧
      w.getAppArgs.length = P.length + idxR.length ∧
      (∀ (q : Nat) (xM xW : Expr), (P ++ idxR)[q]? = some xM → w.getAppArgs[q]? = some xW →
        Expr.ErasedEq xM
          (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) xW)) := by
    intro hwNP
    have hleafNP : NotPi leafC := notPi_of_instantiateList (ErasedEq.notPi hwE hwNP)
    have hmajNP : NotPi majDom := notPi_of_instantiateList (os := locOpen B tele.length) (k := 0)
      (by rw [hmajO]; exact notPi_mkAppN (fun _ _ _ h => Expr.noConfusion h) _)
    obtain ⟨htl, htel, hmajE⟩ := callTie (B := B) hfvs hiF hndF hKE hshape hmajNP hleafNP
    have hosRn : LocList B teleW.length (locOpen B teleW.length) := locOpen_locList _ _
    have hM : Expr.ErasedEq (majDom.instantiateList (locOpen B teleW.length) 0)
        (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) w) :=
      (erasedEq_instantiateList _ 0 hmajE).trans
        ((Expr.substFvars_instantiateList hsb teleW.length _ _ hosW.1 hosRn.1
          (fun j hj => by
            obtain ⟨ty, h1⟩ := hosW.2 j hj
            obtain ⟨ty', h2⟩ := hosRn.2 j hj
            exact ⟨ty, ty', h1, h2⟩) leafC 0).trans
          (Expr.ErasedEq.substFvars hwE))
    rw [← htl, hmajO, ← Expr.mkAppN_getApp w, substFvars_mkAppN] at hM
    have hsNA : ∀ v, v < ctx.hiAt prog.length + i → ∀ f' a',
        callSubst ctx prog fvsF v ≠ .app f' a' := by
      intro v hv f' a' h
      unfold callSubst at h
      split at h
      · exact nomatch h
      · split at h
        · rename_i h1 h2
          obtain ⟨n, us', hc⟩ := nestHoleConst_hole (prog := prog) (by omega) h2
          rw [hc] at h; exact nomatch h
        · rename_i h2
          have hl : v - ctx.hiAt prog.length < fvsF.length := by omega
          rw [List.getElem?_eq_getElem hl, Option.getD_some] at h
          obtain ⟨j, ty, hj⟩ := hfvs _ (List.getElem_mem hl)
          rw [hj] at h; exact nomatch h
    have hSna := substFvars_not_app (D := B) hsNA (e := w.getAppFn)
      (fun f' a' => getAppFn_ne_app w f' a')
    obtain ⟨hSfn, hSargs⟩ := getApp_of_not_app hSna
    obtain ⟨hG1, hG2, hG3⟩ := erasedEq_getApp _ _ hM
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN, hSfn] at hG1
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN, hSargs] at hG2 hG3
    simp only [Expr.getAppArgs, List.nil_append, List.length_map,
      List.length_append] at hG2 hG3
    refine ⟨htl, htel, hG1, by simpa using hG2.symm, fun q xM xW hxM hxW => ?_⟩
    exact hG3 q xM _ hxM (by rw [List.getElem?_map, hxW]; rfl)
  rcases hleaf with hH | hFr | hCn | hK0
  rotate_left 3
  -- the leaf is no hole-free term: K.53′ against the callee's major naming a member
  · exfalso
    have hlC : leafC.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
      rw [← nestOcc_instantiateList_locList (Nat.le_add_right _ i) teleW.length _ hosW leafC 0,
        erasedEq_nestOcc _ _ hwE]
      exact hK0
    have hndO : nd.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
      rw [hshape, nestOcc_mkPisOf, hlC, Bool.or_false, List.any_eq_false]
      intro q hq; simp [hteleH q hq]
    have hrb := nestOcc_replaceFVars_zero (f := extendF (nestHoleConst ctx prog)
      (ctx.hiAt prog.length) (fvsF.take i)) (fun v y hy => by
        unfold extendF at hy
        split at hy
        · right
          obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem (List.mem_of_getElem? hy)
          obtain ⟨j, ty, hj⟩ := hfvs _ (List.mem_of_mem_take (List.getElem_mem hl))
          rw [hj]; simp [Expr.nestOcc]
        · left
          unfold nestHoleConst at hy
          split at hy
          · rename_i h1; simp only [ConLeche.NestCtx.hiAt] at h1 ⊢; omega
          · split at hy
            · rename_i h1 h2; simp only [ConLeche.NestCtx.hiAt] at h1 h2 ⊢; omega
            · exact nomatch hy) nd hndO
    rw [erasedEq_nestOcc _ _ hKE, nestOcc_mkPisOf, hmajM, Bool.or_true] at hrb
    exact Bool.noConfusion hrb
  -- a member hole
  · obtain ⟨v, ty, hfn, hlo, hhi0, hlenA, hpar, hfree⟩ := hH
    have hwNP : NotPi w := by
      rw [← Expr.mkAppN_getApp w, hfn]; exact notPi_mkAppN (fun _ _ _ h => Expr.noConfusion h) _
    obtain ⟨htl, htel, hG1, hlen, hargs⟩ := common hwNP
    have hvb : v < ctx.hiAt prog.length + i := by
      have : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp [ConLeche.NestCtx.hiAt]
      omega
    rw [hfn, Expr.substFvars_fvar_lt hvb] at hG1
    unfold callSubst at hG1
    rw [if_neg (by omega), if_pos (by simp [ConLeche.NestCtx.hiAt] at hhi0 ⊢; omega)] at hG1
    unfold nestHoleConst at hG1
    rw [if_pos ⟨hlo, hhi0⟩, Option.getD_some] at hG1
    obtain ⟨rfl, rfl⟩ := hG1
    exact ⟨teleW, leafC, w, hshape, htl, htel, fun q hq => ⟨hteleH q hq, hteleF q hq⟩, hopen, hwF,
      hlen, hargs, Or.inl ⟨v - ctx.nP, ty, by simp only [ConLeche.NestCtx.hiAt] at hhi0; omega,
        by rw [hfn]; congr 1; omega, rfl, rfl, by rw [hlenA], hpar, hfree⟩⟩
  -- a frame hole
  · obtain ⟨v, ty, h, hfn, hlo, hhi', hk, hle, hpar, hfree, har⟩ := hFr
    have hwNP : NotPi w := by
      rw [← Expr.mkAppN_getApp w, hfn]; exact notPi_mkAppN (fun _ _ _ h => Expr.noConfusion h) _
    obtain ⟨htl, htel, hG1, hlen, hargs⟩ := common hwNP
    have hvb : v < ctx.hiAt prog.length + i := by omega
    rw [hfn, Expr.substFvars_fvar_lt hvb] at hG1
    unfold callSubst at hG1
    rw [if_neg (by simp [ConLeche.NestCtx.hiAt] at hlo ⊢; omega), if_pos hhi'] at hG1
    unfold nestHoleConst at hG1
    rw [if_neg (by simp [ConLeche.NestCtx.hiAt] at hlo ⊢; omega), if_pos ⟨hlo, hhi'⟩, hk,
      Option.map_some, Option.getD_some] at hG1
    obtain ⟨rfl, rfl⟩ := hG1
    exact ⟨teleW, leafC, w, hshape, htl, htel, fun q hq => ⟨hteleH q hq, hteleF q hq⟩, hopen, hwF,
      hlen, hargs, Or.inr (Or.inl ⟨v, ty, h, hlo, hhi', hfn, hk, rfl, rfl, hle, hpar, hfree, har⟩)⟩
  -- a container instance
  · obtain ⟨n, us', nPc, L, u, hfn, hnm, hq, hle, hidxF, hds, hu, hocc, hkey⟩ := hCn
    have hwNP : NotPi w := by
      rw [← Expr.mkAppN_getApp w, hfn]; exact notPi_mkAppN (fun _ _ _ h => Expr.noConfusion h) _
    obtain ⟨htl, htel, hG1, hlen, hargs⟩ := common hwNP
    rw [hfn] at hG1
    simp only [Expr.substFvars, Expr.ErasedEq] at hG1
    obtain ⟨rfl, rfl⟩ := hG1
    exact ⟨teleW, leafC, w, hshape, htl, htel, fun q hq => ⟨hteleH q hq, hteleF q hq⟩, hopen, hwF,
      hlen, hargs, Or.inr (Or.inr ⟨u, nPc, L, hu, hocc, hfn, hq, hle, hkey, hidxF⟩)⟩

set_option maxHeartbeats 16000000 in
/-- **A call, walked — the semantics**: at the walk valuation `σW` of the
called field (agreeing off the holes with the rule's valuation seen
through the walk's substitution), the call's telescope fits exactly when
the walk's does, the field applied along it lies in the walk's leaf, and
the call's index readings are the leaf's (at hole-free arguments). -/
theorem callWalkSem {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    {ctx : NestCtx} {prog : List NestHole} {i rP : Nat} {fvsF : List Expr}
    {teleW tele : List (Expr × BinderMeta)} {leafC w : Expr}
    (htl : tele.length = teleW.length)
    (htel : ∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → teleW[l]? = some p' →
      p.2 = p'.2 ∧ Expr.ErasedEq p.1 (Expr.substFvars (ctx.hiAt prog.length + i)
        (rP + fvsF.length) (callSubst ctx prog fvsF) p'.1))
    (hteleHF : ∀ p ∈ teleW, p.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false ∧
      Expr.fvarsBelow (ctx.hiAt prog.length + i) p.1)
    (hopen : ∀ os, LocList (ctx.hiAt prog.length + i) teleW.length os →
      Expr.ErasedEq (leafC.instantiateList os 0) w)
    (hwF : Expr.fvarsBelow (ctx.hiAt prog.length + i + teleW.length) w)
    {P idxR : List Expr}
    (hargs : ∀ (q : Nat) (xM xW : Expr), (P ++ idxR)[q]? = some xM → w.getAppArgs[q]? = some xW →
      Expr.ErasedEq xM (Expr.substFvars (ctx.hiAt prog.length + i) (rP + fvsF.length)
        (callSubst ctx prog fvsF) xW))
    {x : Nat → AnnotTerm}
    (hs : ∀ v, v < ctx.hiAt prog.length + i →
      Expr.WScoped (rP + fvsF.length) (callSubst ctx prog fvsF v) ∧
      (callSubst ctx prog fvsF v).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env ψ (rP + fvsF.length) (callSubst ctx prog fvsF v) = some (x v))
    {nda : AnnotTerm}
    (hnda : denoteMeta m.acval env ψ (ctx.hiAt prog.length + i) (Expr.mkPisOf teleW leafC)
      = some nda)
    {σR σW : Nat → V} {f : V} (hf : f ∈ˢ interp V σW nda) (hval : AnnotValid V σW nda)
    (hag : AgreeOff (holeP (ctx.hiAt prog.length + i) ctx.nP (ctx.hiAt prog.length))
      (substE V (substTau (ctx.hiAt prog.length + i) (rP + fvsF.length) x) 0 σR) σW)
    {bs : List V}
    (hbs : SpineFit σR ((teleDoms m.acval env ψ (rP + fvsF.length) [] (tele.map (·.1))).getD [])
      bs) :
    bs.length = tele.length ∧
    ∃ (ha : AnnotTerm) (argsA : List AnnotTerm),
      denoteMeta m.acval env ψ (ctx.hiAt prog.length + i + bs.length) w.getAppFn = some ha ∧
      DenoteMetaSpine m.acval env ψ (ctx.hiAt prog.length + i + bs.length) w.getAppArgs argsA ∧
      bs.foldl app f ∈ˢ (argsA.map (interp V (consList bs σW))).foldl app
        (interp V (consList bs σW) ha) ∧
      (∀ (l : Nat) (xR xW : Expr) (xa : AnnotTerm), idxR[l]? = some xR →
        w.getAppArgs[P.length + l]? = some xW → argsA[P.length + l]? = some xa →
        xW.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false →
        interp V (consList bs σR) ((denoteMeta m.acval env ψ (rP + fvsF.length + bs.length)
            xR).getD default)
          = interp V (consList bs σW) xa) := by
  generalize hB : rP + fvsF.length = B at *
  -- the walk's reading of the field
  obtain ⟨dsW, Xr, os', hndaE, hdomsW, hbitsW, hos', hXr⟩ :=
    denoteMeta_mkPisOf (acval := m.acval) (env := env) (φ := ψ)
      (D := ctx.hiAt prog.length + i) teleW leafC 0 [] nda (LocList.nil _)
      (by rw [Expr.instantiateList_nil, Nat.add_zero]; exact hnda)
  subst hndaE
  rw [Nat.zero_add] at hos' hXr
  have hlD : dsW.length = teleW.length := by
    have := congrArg List.length hbitsW; simpa using this
  have hwX : denoteMeta m.acval env ψ (ctx.hiAt prog.length + i + teleW.length) w = some Xr := by
    rw [← denoteMeta_erasedEq (hopen os' hos')]; exact hXr
  -- the rule's telescope is the walk's, substituted
  have hT := teleDoms_substFvars m (φ := ψ) (x := x) hs (tele.map (·.1)) (teleW.map (·.1)) 0 [] []
    (LocList.nil _) (LocList.nil _) (by simp [htl])
    (fun l tR tW h1 h2 => by
      obtain ⟨p1, hp1, rfl⟩ : ∃ p1, tele[l]? = some p1 ∧ p1.1 = tR := by
        rw [List.getElem?_map] at h1
        cases hq : tele[l]? with
        | none => rw [hq] at h1; exact nomatch h1
        | some q => rw [hq] at h1; exact ⟨q, rfl, Option.some.inj h1⟩
      obtain ⟨p2, hp2, rfl⟩ : ∃ p2, teleW[l]? = some p2 ∧ p2.1 = tW := by
        rw [List.getElem?_map] at h2
        cases hq : teleW[l]? with
        | none => rw [hq] at h2; exact nomatch h2
        | some q => rw [hq] at h2; exact ⟨q, rfl, Option.some.inj h2⟩
      exact (htel l p1 p2 hp1 hp2).2)
    (fun tW htW => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp htW
      exact (hteleHF q hq).2)
  rw [hdomsW, Option.map_some] at hT
  rw [hT, Option.getD_some, spineFit_substAt] at hbs
  have hbsW : SpineFit σW (dsW.map (·.2.2)) bs :=
    (spineFit_teleDoms_holeFree (m := m) (φ := ψ) (Nat.le_add_right _ i) (teleW.map (·.1)) 0 []
      (dsW.map (·.2.2)) (LocList.nil _) hdomsW
      (fun t ht => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
        exact hteleHF q hq)
      (by simpa using hag) bs).mp hbs
  have hbl : bs.length = teleW.length := by
    rw [hbsW.length_eq, List.length_map, hlD]
  refine ⟨by rw [hbl, htl], ?_⟩
  -- the value: the field applied along the telescope lands in the leaf
  have hmem := foldl_app_mem_mkPisAV hval hbsW hf
  rw [← hbl, ← Expr.mkAppN_getApp w] at hwX
  obtain ⟨ha, argsA, hha, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwX
  rw [interp_mkAppN_foldl] at hmem
  have hwF' : Expr.fvarsBelow (ctx.hiAt prog.length + i + bs.length)
      (Expr.mkAppN w.getAppFn w.getAppArgs) := by
    rw [Expr.mkAppN_getApp, hbl]; exact hwF
  have hargsF := fvarsBelow_mkAppN_args _ hwF'
  refine ⟨ha, argsA, hha, hsp, hmem, fun l xR xW xa hxR hxW hxa hfree => ?_⟩
  have hE := hargs (P.length + l) xR xW
    (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hxR]) hxW
  obtain ⟨xa', hxa', hread⟩ := denoteMetaSpine_getElem?' hsp _ _ hxW
  rw [hxa] at hxa'
  obtain rfl := Option.some.inj hxa'
  have hxWF := hargsF xW (List.mem_of_getElem? hxW)
  have hRd : denoteMeta m.acval env ψ (B + bs.length) xR
      = some (AnnotTerm.substAV (substTau (ctx.hiAt prog.length + i) B x) xa bs.length) := by
    rw [denoteMeta_erasedEq hE, denoteMeta_substFvars m hs xW bs.length hxWF, hread]
    rfl
  rw [hRd, Option.getD_some, interp_substAV, show bs.length = bs.length + 0 from rfl,
    substE_consList]
  exact interp_holeFree hxWF (by omega) hfree hread (agreeOff_holeP_consList bs hag)

end ConLeche.Model
