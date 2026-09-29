module

public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase

public section

/-!
# Completeness of the positivity walk against a derivation (half (B))

`PosD` (`Verify/Inductives/PosDeriv.lean`) is what a SUCCESSFUL run implies
(`nestPos_deriv`).
The converse — "a `PosD` derivation exists ⇒ `nestPos` succeeds (given
enough fuel)" — is FALSE for `PosD` as it stands, for two reasons, each a
place where `PosD` forgets something the run checks:

1. **Freshness.**  The run rejects an instantiation met as a CONSTANT while
   it is in progress (`nestContKey`: in the
   run's `active` list — the frames being walked, including those walked
   at the empty stack).  `PosD.contNew` has no such premise.
2. **The walk stack.**  The run walks an instantiation whose parameters
   lie below every frame hole at the EMPTY stack (`nestWalkStack`);
   `PosD.contNew` may derive its frame under the occurrence's stack.

`PosDR` is `PosD` with exactly these two facts added: its judgments
carry the in-progress list `act` (the run's `active`), and the container
rule (`cont`, subsuming `contNew`/`contHit`) walks its frame at
`nestWalkStack` and requires the key fresh.  Every judgment carries a
FUEL index: the run's fuel is spent one unit per `Π` body and per
container descent.  (The seeds, `nestSeeds`, are the install stage's,
not the walk's.)

* `posDR_run` (**(B)**): a `PosDR` derivation at fuel index `n` ⇒ the run at
  any fuel `≥ n` succeeds with the derivation's kinds and normal forms
  (for every state whose `active` is `act` and whose container cache is
  the environment's; a member hole read as the root frame's entry,
  `NestRootOk`); `nestRoot_complete`/`nestedBlockPositivity_complete`: the
  root frame's run (the members' constructor lists derived at the root
  key), the fuel side condition being `n ≤ nestRootFuel`.
* `posDR_posD`: `PosDR` refines `PosD` (the erasure: forget `act` and the
  fuel).
-/

namespace ConLeche

open Expr

/-- The keys of a frame's group at its instantiation (`nestContNew`'s
`active` entries). -/
@[expose] def grpKeys (us : List Level) (ds : List Expr) (grp : List (Name × Expr)) : List NestKey :=
  grp.map fun p => ⟨p.1, us, ds⟩

/-- The run-complete judgments: `PosJ` with the in-progress list `act`. -/
inductive PosJR where
  | field (act : List NestKey) (prog : List NestHole) (dep kb : Nat) (e : Expr) (k : NestFieldKind)
      (nf : Expr)
  | tele (act : List NestKey) (prog : List NestHole) (base nF j : Nat) (cur : Expr)
      (ks : List NestFieldKind) (nds : List (Expr × BinderMeta)) (res : Expr)
  | ctors (act : List NestKey) (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
      (sub : Name → List Level → Option Expr) (cs : List (ConstantVal × Nat))
  | frame (act : List NestKey) (prog : List NestHole) (us : List Level) (ds : List Expr)
      (grp : List (Name × Expr))

/-- **The run-complete positivity derivation** (see the module doc), at a
fuel index. -/
inductive PosDR (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : Nat → PosJR → Prop where
  | const {n : Nat} {act : List NestKey} {prog : List NestHole} {dep kb : Nat} {e w : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) :
      PosDR ops env ctx (n + 1)
        (.field act prog dep kb e .ordinary
          (if e.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) then w else e))
  | pi {n m : Nat} {act : List NestKey} {prog : List NestHole} {dep kb : Nat} {e a b : Expr}
      {bm : BinderMeta} {k : NestFieldKind} {nb : Expr}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hocc : (Expr.forallE a b bm).nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hm : m < n)
      (hb : PosDR ops env ctx m
        (.field act prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) k nb)) :
      PosDR ops env ctx n (.field act prog dep kb e k (.forallE a (nb.abstract1 dep) bm))
  | hole {n : Nat} {act : List NestKey} {prog : List NestHole} {dep kb : Nat} {e w : Expr} {i : Nat}
      {ty : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.nP ≤ i) (hhi : i < ctx.hiAt 0)
      (hlen : w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0)
      (hpar : w.getAppArgs.take ctx.nP = ctx.params)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) :
      PosDR ops env ctx (n + 1)
        (.field act prog dep kb e
          (if kb = 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP)) w)
  | frameHole {n : Nat} {act : List NestKey} {prog : List NestHole} {dep kb : Nat} {e w : Expr}
      {i : Nat} {ty : Expr} {h : NestHole}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 ≤ i) (hhi : i < ctx.hiAt prog.length)
      (hk : prog.reverse[i - ctx.hiAt 0]? = some h)
      (hle : h.key.ds.length ≤ w.getAppArgs.length)
      (hpar : w.getAppArgs.take h.key.ds.length = h.key.ds)
      (hfree : ∀ x ∈ w.getAppArgs.drop h.key.ds.length,
        x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (har : w.getAppArgs.length = nestArity ctx h.key.cname) :
      PosDR ops env ctx (n + 1) (.field act prog dep kb e .inProgress w)
  /-- a container at a concrete instantiation: FRESH (in no frame of `prog`,
  not in progress), its frame derived at the run's walk stack -/
  | cont {n m : Nat} {act : List NestKey} {prog : List NestHole} {dep kb : Nat} {e w : Expr}
      {c : Name} {us : List Level} {L : List (ConstantVal × Nat)} {nPc nI : Nat} {cty : Expr}
      {grp : List (Name × Expr)}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .const c us) (hnm : ctx.names.contains c = false)
      (hC : nestContainer ctx c = some (nPc, L)) (hlen : w.getAppArgs.length = nPc + nI)
      (hquot : c ≠ quotName)
      (hidx : ∀ x ∈ w.getAppArgs.drop nPc,
        x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hds : ∀ x ∈ w.getAppArgs.take nPc,
        x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
      (hdsw : ∀ x ∈ w.getAppArgs.take nPc, Expr.WScoped (ctx.hiAt prog.length) x)
      (hdsA : ∀ x ∈ w.getAppArgs.take nPc, x.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true)
      (hsc : ProgScoped ctx prog)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨c, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hact : ⟨c, us, w.getAppArgs.take nPc⟩ ∉ act)
      (hhead : (grp.headD default).1 = c)
      (hm : m < n)
      (hfr : PosDR ops env ctx m
        (.frame act (nestWalkStack ctx prog (w.getAppArgs.take nPc)) us (w.getAppArgs.take nPc)
          grp)) :
      PosDR ops env ctx n (.field act prog dep kb e (.nested (kb != 0)) w)
  /-- a container frame: the container's whole recorded block, its
  constructors walked with the group in progress; the instantiation
  itself typed at the frame's depth (K.52, as `PosD.frame`) -/
  | frame {n m : Nat} {act : List NestKey} {prog : List NestHole} {us : List Level}
      {ds : List Expr} {grp : List (Name × Expr)} {ctors : List (ConstantVal × Nat)}
      (hne : grp ≠ [])
      (hhd : ctx.names.contains (grp.headD default).1 = false ∧ (grp.headD default).1 ≠ quotName)
      (hhdC : ∃ L, nestContainer ctx (grp.headD default).1 = some (ds.length, L))
      (hnd : (grp.map (·.1)).Nodup)
      (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨p.1, us, ds⟩ = .ok (nI, p.2))
      (hblk : ∀ p ∈ grp.tail, (nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
      (hgrp : grp.map (·.1) = (grp.headD default).1 :: nestFrameMates ctx (grp.headD default).1)
      (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
      (hkty : ∃ ty, ops.inferType env (ctx.hiAt prog.length)
        (Expr.mkAppN (.const (grp.headD default).1 us) ds) = .ok ty)
      (hm : m ≤ n)
      (hwalk : PosDR ops env ctx m
        (.ctors (grpKeys us ds grp ++ act)
          ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
          (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp)
          ctors)) :
      PosDR ops env ctx n (.frame act prog us ds grp)
  | ctorsNil {n : Nat} {act : List NestKey} {prog : List NestHole} {hi : Nat} {us : List Level}
      {ds : List Expr} {sub : Name → List Level → Option Expr} :
      PosDR ops env ctx n (.ctors act prog hi us ds sub [])
  | ctorsCons {n m₁ m₂ : Nat} {act : List NestKey} {prog : List NestHole} {hi : Nat}
      {us : List Level} {ds : List Expr} {sub : Name → List Level → Option Expr} {cv : ConstantVal}
      {nF : Nat} {cs : List (ConstantVal × Nat)} {crest ty : Expr} {sv : Level}
      {ks : List NestFieldKind} {nds : List (Expr × BinderMeta)} {cur : Expr}
      (hnd : Name.nodup cv.levelParams = true)
      (hcrest : instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts sub)
        = some crest)
      (hty : ops.inferType env hi crest = .ok ty) (hsort : ops.ensureSort env hi ty = .ok sv)
      (hm₁ : m₁ ≤ n)
      (htele : PosDR ops env ctx m₁ (.tele act prog hi nF 0 crest ks nds cur))
      (hu4 : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) = false)
      (hres : nestResHead cur = true)
      (hidx : (cur.getAppArgs.drop ds.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) = true)
      (hm₂ : m₂ ≤ n)
      (hrest : PosDR ops env ctx m₂ (.ctors act prog hi us ds sub cs)) :
      PosDR ops env ctx n (.ctors act prog hi us ds sub ((cv, nF) :: cs))
  | teleNil {n : Nat} {act : List NestKey} {prog : List NestHole} {base j : Nat} {cur : Expr} :
      PosDR ops env ctx n (.tele act prog base 0 j cur [] [] cur)
  /-- one field: its walk, then the rest -/
  | teleCons {n m₁ m₃ : Nat} {act : List NestKey} {prog : List NestHole} {base nF j : Nat}
      {a b : Expr} {bm : BinderMeta} {k : NestFieldKind} {nd : Expr} {ks : List NestFieldKind}
      {nds : List (Expr × BinderMeta)} {res : Expr}
      (hm₁ : m₁ ≤ n)
      (ha : PosDR ops env ctx m₁ (.field act prog (base + j) 0 a k nd))
      (hm₃ : m₃ ≤ n)
      (hb : PosDR ops env ctx m₃
        (.tele act prog base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res)) :
      PosDR ops env ctx n
        (.tele act prog base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)

/-! ## Fuel monotonicity (one step: every premise is at a bounded index) -/

theorem PosDR.mono {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {n n' : Nat} {J : PosJR}
    (h : PosDR ops env ctx n J) (hle : n ≤ n') : PosDR ops env ctx n' J := by
  cases h with
  | const hw hocc =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .const hw hocc
  | pi hw hocc ha hm hb => exact .pi hw hocc ha (by omega) hb
  | hole hw hocc hfn hlo hhi hlen hpar hfree =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .hole hw hocc hfn hlo hhi hlen hpar hfree
  | frameHole hw hocc hfn hlo hhi hk hle' hpar hfree har =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .frameHole hw hocc hfn hlo hhi hk hle' hpar hfree har
  | cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hdsA hsc hnI hact hhead hm hfr =>
    exact .cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hdsA hsc hnI hact hhead (by omega) hfr
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hm hwalk =>
    exact .frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty (by omega) hwalk
  | ctorsNil => exact .ctorsNil
  | ctorsCons hnd hcrest hty hsort hm₁ htele hu4 hres hidx hm₂ hrest =>
    exact .ctorsCons hnd hcrest hty hsort (by omega) htele hu4 hres hidx (by omega) hrest
  | teleNil => exact .teleNil
  | teleCons hm₁ ha hm₃ hb => exact .teleCons (by omega) ha (by omega) hb

/-! ## (B): the derivation's run -/

/-- **The run's state, as the derivation sees it**: its in-progress list
is `act`. -/
@[expose] def RInv (_ctx : NestCtx) (st : NestState) (act : List NestKey) : Prop :=
  st.active = act

section Helpers

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

theorem nestGrowGroup_ok {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (ext grp : List (Name × Expr)),
      (∀ p ∈ ext, ∃ nI, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2)) →
      nestGrowGroup (m := CheckM) ctx hi us ds (ext.map (·.1)) grp = .ok (grp ++ ext)
  | [], grp, _ => by simp [nestGrowGroup, pure, Except.pure]
  | p :: ext, grp, h => by
    obtain ⟨nI, hp⟩ := h p List.mem_cons_self
    simp only [List.map_cons, nestGrowGroup, bind, Except.bind, hp]
    rw [nestGrowGroup_ok ext _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp

theorem nestGroupCtors_ok {nPc : Nat} :
    ∀ (cs : List Name) (ctors : List (ConstantVal × Nat)),
      groupCtors ctx nPc cs = some ctors →
      nestGroupCtors (m := CheckM) ctx nPc cs = .ok ctors
  | [], ctors, h => by
    simp only [groupCtors, Option.some.injEq] at h
    subst h
    rfl
  | c :: cs, ctors, h => by
    simp only [groupCtors] at h
    split at h
    · rename_i nP' L hq
      split at h
      · rename_i hok
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have h₁ := nestGroupCtors_ok cs rest hr
        simp only [nestGroupCtors, bind, Except.bind, hq, unwrapOr, pure, Except.pure]
        rw [if_pos (by simpa using hok)]
        simp only [h₁]
      · exact nomatch h
    · exact nomatch h

/-- What a frame's run needs of its walk: its run from any state whose
in-progress list holds the group. -/
@[expose] def FrameRun (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (act : List NestKey) (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  ∀ st, RInv ctx st (grpKeys us ds grp ++ act) →
    ∃ st', nestFrame ctx ops env rec prog (ctx.hiAt prog.length) us ds ds.length grp st
      = .ok st' ∧ RInv ctx st' (grpKeys us ds grp ++ act)

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

/-- **A new (or re-walked) instantiation runs**: given its frame's facts and
its frame's run at the walk stack. -/
theorem nestContNew_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {cty : Expr} {st : NestState} {act : List NestKey}
    {grp : List (Name × Expr)}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hne : grp ≠ []) (hhead : grp.headD default = (c, cty))
    (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hgrp : grp.map (·.1) = c :: nestFrameMates ctx c)
    (hfr : FrameRun ops env ctx rec act (nestWalkStack ctx prog ds) us ds grp) :
    ∃ k st', nestContNew ctx ops env rec prog kb c us ds nPc cty st = .ok (k, st') ∧
      k = .nested (kb != 0) ∧ RInv ctx st' act := by
  subst hnPc
  obtain ⟨⟨c', cty'⟩, rest, rfl⟩ : ∃ p rest, grp = p :: rest := by
    cases grp with
    | nil => exact absurd rfl hne
    | cons p rest => exact ⟨p, rest, rfl⟩
  simp only [List.headD_cons, Prod.mk.injEq] at hhead
  obtain ⟨h1, h2⟩ := hhead
  subst h1
  subst cty'
  have hmap : rest.map (·.1) = nestFrameMates ctx c' := by
    simpa using hgrp
  have hgrow := nestGrowGroup_ok (ctx := ctx) (hi := ctx.hiAt (nestWalkStack ctx prog ds).length)
    (us := us) (ds := ds) rest [(c', cty)] (fun p hp => hinst p (List.mem_cons_of_mem _ hp))
  rw [hmap] at hgrow
  obtain ⟨st₁, hf₁, -⟩ := hfr { st with active := grpKeys us ds ((c', cty) :: rest) ++ st.active }
    (by show _ ++ st.active = _; rw [hI])
  simp only [nestContNew, bind, Except.bind, hgrow, List.singleton_append]
  have hf₁' : nestFrame ctx ops env rec (nestWalkStack ctx prog ds)
      (ctx.hiAt (nestWalkStack ctx prog ds).length) us ds ds.length ((c', cty) :: rest)
      { st with active := (List.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey))
        ((c', cty) :: rest) ++ st.active) } = .ok st₁ := hf₁
  rw [hf₁']
  exact ⟨_, _, rfl, rfl, hI⟩

/-- The preconditions of a frame walk at the walk stack (the frame rule's
facts the run's `nestContNew` reads, and the frame's run). -/
@[expose] def NewOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (act : List NestKey) (prog : List NestHole) (c : Name) (us : List Level) (ds : List Expr) :
    Prop :=
  ∃ grp : List (Name × Expr), grp ≠ [] ∧ (grp.headD default).1 = c ∧
    (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2)) ∧
    grp.map (·.1) = c :: nestFrameMates ctx c ∧
    FrameRun ops env ctx rec act (nestWalkStack ctx prog ds) us ds grp

theorem nestContNew_ok' {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc nI : Nat} {cty : Expr} {st : NestState} {act : List NestKey}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨c, us, ds⟩ = .ok (nI, cty))
    (hnew : NewOk ops env ctx rec act prog c us ds) :
    ∃ k st', nestContNew ctx ops env rec prog kb c us ds nPc cty st = .ok (k, st') ∧
      k = .nested (kb != 0) ∧ RInv ctx st' act := by
  obtain ⟨grp, hne, hhead, hinst, hgrp, hfr⟩ := hnew
  -- the head's hole type is the occurrence's (`nestInstType` at the walk's
  -- smaller hole range computes the same)
  have hmono := nestInstType_mono_hi (show ctx.hiAt (nestWalkStack ctx prog ds).length ≤
    ctx.hiAt prog.length by unfold nestWalkStack; split <;> simp [NestCtx.hiAt]) hnI
  have hhd : grp.headD default = (c, cty) := by
    cases grp with
    | nil => exact absurd rfl hne
    | cons p rest =>
      obtain ⟨nI', h'⟩ := hinst p List.mem_cons_self
      simp only [List.headD_cons] at hhead ⊢
      rw [hhead, hmono] at h'
      obtain ⟨-, h2⟩ : nI = nI' ∧ cty = p.2 := by simpa using h'
      rw [h2, ← hhead]
  exact nestContNew_ok hI hnPc hne hhd hinst hgrp hfr

/-- **A fresh instantiation met runs.** -/
theorem nestContKey_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc nI : Nat} {cty : Expr} {st : NestState} {act : List NestKey}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨c, us, ds⟩ = .ok (nI, cty))
    (hact : (⟨c, us, ds⟩ : NestKey) ∉ act)
    (hnew : NewOk ops env ctx rec act prog c us ds) :
    ∃ k st', nestContKey ctx ops env rec prog kb c us ds nPc cty st = .ok (k, st') ∧
      k = .nested (kb != 0) ∧ RInv ctx st' act := by
  unfold nestContKey
  have hactc : st.active.contains ⟨c, us, ds⟩ = false := by
    rw [show st.active = act from hI]; simpa using hact
  rw [if_neg (by rw [hactc]; simp)]
  split
  · exact ⟨_, _, rfl, rfl, hI⟩
  · exact nestContNew_ok' hI hnPc hnI hnew

/-- **The container case runs.** -/
theorem nestCont_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {args : List Expr} {st : NestState} {act : List NestKey} {L : List (ConstantVal × Nat)}
    {nPc nI : Nat} {cty : Expr}
    (hI : RInv ctx st act) (hC : nestContainer ctx c = some (nPc, L))
    (hlen : args.length = nPc + nI) (hquot : c ≠ quotName)
    (hidx : ∀ x ∈ args.drop nPc, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
    (hds : ∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hdsA : ∀ x ∈ args.take nPc, x.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true)
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨c, us, args.take nPc⟩
      = .ok (nI, cty))
    (hact : (⟨c, us, args.take nPc⟩ : NestKey) ∉ act)
    (hnew : NewOk ops env ctx rec act prog c us (args.take nPc)) :
    ∃ k st', nestCont ctx ops env rec prog kb c us args st = .ok (k, st') ∧
      k = .nested (kb != 0) ∧ RInv ctx st' act := by
  unfold nestCont
  simp only [bind, Except.bind, hC, unwrapOr, pure, Except.pure]
  rw [if_neg (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_false,
      not_or, not_exists, not_and, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨by omega, fun x hx => by simpa using hidx x hx⟩)]
  rw [if_neg (by simpa using hquot)]
  rw [if_pos (by
    rw [List.all_eq_true]
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hds x hx)]
  rw [if_pos (List.all_eq_true.mpr hdsA)]
  simp only [hnI]
  rw [if_pos (by simp [hlen])]
  exact nestContKey_ok hI (by simp; omega) hnI hact hnew

/-- **The claim of (B) at a judgment**: the corresponding run, at every
fuel at least the index, from every state the judgment's in-progress list
describes, succeeds with the judgment's outputs. -/
@[expose] def RunOK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (n : Nat) : PosJR → Prop
  | .field act prog dep kb e k nf => ∀ fuel, n ≤ fuel → ∀ st, RInv ctx st act →
      ∃ k' st', nestPos ops env ctx fuel prog dep kb e st = .ok (k', nf, st') ∧ k' = k ∧
        RInv ctx st' act
  | .tele act prog base nF j cur ks nds res => ∀ fuel, n ≤ fuel → ∀ st, RInv ctx st act →
      ∃ ks' st', (∀ err, nestFields (nestPos ops env ctx fuel) prog base
          err nF j cur st = .ok (ks', nds, res, st')) ∧ ks' = ks ∧ RInv ctx st' act
  | .ctors act prog hi us ds sub cs => ∀ fuelOf : Expr → Nat,
      (∀ x ∈ cs, ∀ crest, instPisWith ds
        ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub) = some crest →
        n ≤ fuelOf crest) → ∀ st, RInv ctx st act →
      ∃ os st', nestCtors ctx ops env (fun crest => nestPos ops env ctx (fuelOf crest)) prog hi us
          ds ds.length sub cs st = .ok (os, st') ∧ RInv ctx st' act ∧
        ∀ (j : Nat) (cA : ConstantVal × Nat) (o : List NestFieldKind × Expr), cs[j]? = some cA →
          os[j]? = some o → ∃ crest m nds cur,
            instPisWith ds ((cA.1.type.instantiateLevelParams cA.1.levelParams us).replaceConsts
              sub) = some crest ∧
            PosDR ops env ctx m (.tele act prog hi cA.2 0 crest o.1 nds cur) ∧
            o.2 = closeTelescope nds hi cur
  | .frame act prog us ds grp => ∀ fuel, n ≤ fuel →
      FrameRun ops env ctx (nestPos ops env ctx fuel) act prog us ds grp

/-- The frame rule's facts the run reads before walking. -/
theorem PosDR.frame_inv {n : Nat} {act : List NestKey} {prog : List NestHole} {us : List Level}
    {ds : List Expr} {grp : List (Name × Expr)}
    (h : PosDR ops env ctx n (.frame act prog us ds grp)) :
    grp ≠ [] ∧ (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨p.1, us, ds⟩ = .ok (nI, p.2)) ∧
      grp.map (·.1) = (grp.headD default).1 :: nestFrameMates ctx (grp.headD default).1 := by
  cases h with
  | frame hne _ _ _ hinst _ hgrp _ _ _ _ => exact ⟨hne, hinst, hgrp⟩

theorem newOk_of {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
      {n : Nat} {act : List NestKey} {prog : List NestHole} {c : Name} {us : List Level}
    {ds : List Expr} {grp : List (Name × Expr)}
    (h : PosDR ops env ctx n (.frame act (nestWalkStack ctx prog ds) us ds grp))
    (hhead : (grp.headD default).1 = c)
    (hrun : FrameRun ops env ctx rec act (nestWalkStack ctx prog ds) us ds grp) :
    NewOk ops env ctx rec act prog c us ds := by
  obtain ⟨hne, hinst, hgrp⟩ := h.frame_inv
  rw [hhead] at hgrp
  exact ⟨grp, hne, hhead, hinst, hgrp, hrun⟩

/-- **(B), THE COMPLETENESS OF THE WALK AGAINST ITS DERIVATION.**  A
`PosDR` derivation at fuel index `n` makes the corresponding run succeed at
every fuel `≥ n`, with the derivation's kinds and normal forms. -/
theorem posDR_run (hroot : NestRootOk ctx) {n : Nat} {J : PosJR} (h : PosDR ops env ctx n J) :
    RunOK ops env ctx n J := by
  induction h with
  | const hw hocc =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨.ordinary, st, ?_, rfl, hI⟩
    rw [nestPos]
    simp only [hw, bind, Except.bind]
    rw [if_pos (by simpa using hocc)]
    rfl
  | pi hw hocc ha hm hb ih =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨k', st', hr, hk, hI'⟩ := ih f (by omega) st hI
    refine ⟨k', st', ?_, hk, hI'⟩
    rw [nestPos]
    simp only [hw, bind, Except.bind]
    rw [if_neg (by simpa using hocc)]
    simp only [ha, Bool.false_eq_true, if_false, hr]
    rfl
  | @hole n act prog dep kb e w i ty hw hocc hfn hlo hhi hlen hpar hfree =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP), st, ?_, ?_, hI⟩
    · obtain ⟨hPl, -, hAr⟩ := hroot
      have ht : i - ctx.nP < ctx.names.length := by simp only [NestCtx.hiAt] at hhi; omega
      rw [nestPos]
      simp only [hw, bind, Except.bind]
      rw [if_neg (by simpa using hocc)]
      simp only [hfn]
      split
      · simp [Expr.getAppFn] at hfn
      · rename_i hfn'
        simp only [nestHoleAt_of_root prog hlo hhi]
        have hc : (decide (ctx.params.length ≤ w.getAppArgs.length) &&
            (w.getAppArgs.take ctx.params.length == ctx.params) &&
            ((w.getAppArgs.drop ctx.params.length).all fun x =>
              !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) &&
            (w.getAppArgs.length == nestArity ctx (ctx.names.getD (i - ctx.nP) .anonymous)))
            = true := by
          rw [hPl, hAr _ ht]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true]
          exact ⟨⟨⟨by omega, hpar⟩, fun x hx => hfree x (List.mem_of_mem_drop hx)⟩, hlen⟩
        rw [if_pos hc, if_pos hhi]
        rfl
    · by_cases hkb : kb = 0 <;> simp [hkb]
  | @frameHole n act prog dep kb e w i ty h hw hocc hfn hlo hhi hk hle hpar hfree har =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨.inProgress, st, ?_, rfl, hI⟩
    rw [nestPos]
    simp only [hw, bind, Except.bind]
    rw [if_neg (by simpa using hocc)]
    simp only [hfn]
    split
    · simp [Expr.getAppFn] at hfn
    · rename_i hfn'
      simp only [nestHoleAt_of_frame hlo hk]
      have hc : (decide (h.key.ds.length ≤ w.getAppArgs.length) &&
          (w.getAppArgs.take h.key.ds.length == h.key.ds) &&
          ((w.getAppArgs.drop h.key.ds.length).all fun x =>
            !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) &&
          (w.getAppArgs.length == nestArity ctx h.key.cname)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true]
        exact ⟨⟨⟨hle, hpar⟩, hfree⟩, har⟩
      rw [if_pos hc, if_neg (by omega)]
      rfl
  | @cont n m act prog dep kb e w c us L nPc nI cty grp hw hocc hfn hnm hC hlen hquot hidx hds
      hdsw hdsA hsc hnI hact hhead hm hfr ih =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨k', st', hr, hk, hI'⟩ := nestCont_ok (rec := nestPos ops env ctx f) (kb := kb) (us := us) hI hC hlen hquot
      hidx hds hdsA hnI hact
      (newOk_of hfr hhead (ih f (by omega)))
    refine ⟨k', st', ?_, hk, hI'⟩
    rw [nestPos]
    simp only [hw, bind, Except.bind]
    rw [if_neg (by simpa using hocc)]
    simp only [hfn]
    rw [if_neg (by simpa using hnm)]
    rw [hr]
    split
    · simp [Expr.getAppFn] at hfn
    · rfl
  | @frame n m act prog us ds grp ctors hne hhd hhdC hnd hinst hblk hgrp hctors hkty hm hwalk ih =>
    intro fuel hf st hI
    have h₁ := nestGroupCtors_ok (ctx := ctx) (nPc := ds.length) _ ctors hctors
    obtain ⟨os, st', h', hI', -⟩ := ih (fun _ => fuel) (fun _ _ _ _ => by omega) st hI
    replace h' := And.intro h' True.intro
    obtain ⟨ty, hty⟩ := hkty
    refine ⟨st', ?_, hI'⟩
    simp only [nestFrame, bind, Except.bind, h₁, hty]
    rw [grpNews_mapIdx]
    split
    · rename_i heq; exact absurd (heq.symm.trans h'.1) (by simp)
    · rename_i v heq
      have := heq.symm.trans h'.1
      simp only [Except.ok.injEq] at this
      subst this
      rfl
  | ctorsNil =>
    intro fuelOf _ st hI
    exact ⟨[], st, rfl, hI, fun _ _ _ hj => by simp at hj⟩
  | @ctorsCons n m₁ m₂ act prog hi us ds sub cv nF cs crest ty sv ks nds cur hnd hcrest hty hsort
      hm₁ htele hu4 hres hidx hm₂ hrest iht ihr =>
    intro fuelOf hf st hI
    simp only [nestCtors, bind, Except.bind]
    rw [if_pos hnd]
    simp only [hcrest, unwrapOr, pure, Except.pure, hty, hsort]
    obtain ⟨ks', st₁, h₁, hks, hI₁⟩ :=
      iht (fuelOf crest) (by have := hf _ List.mem_cons_self crest hcrest; omega) st hI
    simp only [h₁]
    subst hks
    rw [if_neg (by
      rw [hu4]; simp)]
    rw [if_pos (by simp [hres, hidx])]
    obtain ⟨os, st', h₂, hI', hos⟩ := ihr fuelOf
      (fun x hx c' hc' => by have := hf x (List.mem_cons_of_mem _ hx) c' hc'; omega)
      { st₁ with ctorNfs := st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) } hI₁
    simp only [h₂]
    refine ⟨_, st', rfl, hI', fun j cA o hj ho => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj ho
      subst hj ho
      exact ⟨crest, m₁, nds, cur, hcrest, htele, rfl⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ho
      exact hos j cA o hj ho
  | teleNil =>
    intro fuel _ st hI
    exact ⟨[], st, fun _ => rfl, rfl, hI⟩
  | @teleCons n m₁ m₃ act prog base nF j a b bm k nd ks nds res hm₁ ha hm₃ hb iha ihb =>
    intro fuel hf st hI
    obtain ⟨k₁, st₁, h₁, hk₁, hI₁⟩ := iha fuel (by omega) st hI
    obtain ⟨ks₂, st₃, h₃, hks₂, hI₃⟩ := ihb fuel (by omega) st₁ hI₁
    refine ⟨k₁ :: ks₂, st₃, fun err => ?_, by simp [hk₁, hks₂], hI₃⟩
    simp only [nestFields, bind, Except.bind, h₁]
    simp only [h₃]
    rfl

/-- **(B) at the root frame**: every member's constructor list derived
run-completely at the root key (from the empty in-progress list) within
the fuel makes the root frame's walk succeed, every constructor's output
a derived telescope's. -/
theorem nestRoot_complete (hroot : NestRootOk ctx) {holes : List Expr} :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState), RInv ctx st [] →
      (∀ cs ∈ css, ∃ n, (∀ x ∈ cs, ∀ crest, instPisWith ctx.params
          ((x.1.type.instantiateLevelParams x.1.levelParams (ctx.lps.map .param)).replaceConsts
            (nestRootSub ctx holes)) = some crest → n ≤ whnfWalkFuel crest) ∧
        PosDR ops env ctx n (.ctors [] [] (ctx.hiAt 0)
        (ctx.lps.map .param) ctx.params (nestRootSub ctx holes) cs)) →
      ∃ outs st', nestRoot ops env ctx holes css st = .ok (outs, st') ∧ RInv ctx st' [] ∧
        ∀ (c : Nat) (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)),
          css[c]? = some cs → outs[c]? = some os →
          ∀ (j : Nat) (cA : ConstantVal × Nat) (o : List NestFieldKind × Expr),
            cs[j]? = some cA → os[j]? = some o → ∃ crest m nds cur,
              instPisWith ctx.params ((cA.1.type.instantiateLevelParams cA.1.levelParams
                (ctx.lps.map .param)).replaceConsts (nestRootSub ctx holes)) = some crest ∧
              PosDR ops env ctx m (.tele [] [] (ctx.hiAt 0) cA.2 0 crest o.1 nds cur) ∧
              o.2 = closeTelescope nds (ctx.hiAt 0) cur
  | [], st, hI, _ => ⟨[], st, rfl, hI, fun _ _ _ hc => by simp at hc⟩
  | cs :: css, st, hI, hall => by
    obtain ⟨n, hn, hd⟩ := hall cs List.mem_cons_self
    obtain ⟨os, st₁, h₁, hI₁, hos⟩ := posDR_run hroot hd whnfWalkFuel hn st hI
    obtain ⟨outs, st', h₂, hI', houts⟩ := nestRoot_complete hroot css st₁ hI₁
      (fun cs' hcs' => hall cs' (List.mem_cons_of_mem _ hcs'))
    refine ⟨os :: outs, st', ?_, hI', fun c cs' os' hc ho => ?_⟩
    · rw [hroot.1] at h₁
      simp only [nestRoot, bind, Except.bind, h₁, h₂, pure, Except.pure]
    · cases c with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc ho
        subst hc ho
        exact hos
      | succ c =>
        simp only [List.getElem?_cons_succ] at hc ho
        exact houts c cs' os' hc ho

/-- **(B), THE COMPLETENESS THEOREM OF THE NESTED POSITIVITY CHECK**:
official's uniform-occurrence check passing at every constructor, and
every member's constructor list derived (run-complete, at the root key)
within the root's fuel, make `nestedBlockPositivity` succeed. -/
theorem nestedBlockPositivity_complete (hroot : NestRootOk ctx) {holes : List Expr}
    (hh : nestHoles ctx = some holes) {ctorss : List (List (ConstantVal × Nat))}
    (hunif : ∀ cs ∈ ctorss, ∀ cA ∈ cs, nestUniformOk ctx holes cA.1.type = true)
    (hall : ∀ cs ∈ ctorss, ∃ n, (∀ x ∈ cs, ∀ crest, instPisWith ctx.params
        ((x.1.type.instantiateLevelParams x.1.levelParams (ctx.lps.map .param)).replaceConsts
          (nestRootSub ctx holes)) = some crest → n ≤ whnfWalkFuel crest) ∧
      PosDR ops env ctx n (.ctors [] []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params (nestRootSub ctx holes) cs)) :
    ∃ r, nestedBlockPositivity ops env ctx ctorss = .ok r := by
  obtain ⟨outs, st', h, -, -⟩ :=
    nestRoot_complete hroot ctorss {} rfl hall
  have hU : nestUniform (m := CheckM) ctx holes ctorss = .ok () := by
    unfold nestUniform
    rw [(List.findSome?_eq_none_iff).mpr fun cs hcs =>
      List.find?_eq_none.mpr fun cA hcA => by simp [hunif cs hcs cA hcA]]
    rfl
  simp only [nestedBlockPositivity, bind, Except.bind, hh, unwrapOr, pure, Except.pure, hU, h]
  exact ⟨_, rfl⟩

/-! ## `PosDR` refines `PosD` -/

/-- A run-complete judgment's `PosD` judgment. -/
@[expose] def PosJR.erase : PosJR → PosJ
  | .field _ prog dep kb e k nf => .field prog dep kb e k nf
  | .tele _ prog base nF j cur ks nds res => .tele prog base nF j cur ks nds res
  | .ctors _ prog hi us ds sub cs => .ctors prog hi us ds sub cs
  | .frame _ prog us ds grp => .frame prog us ds grp

/-- The frame of a walked instantiation, as `PosD` states it: at the
occurrence's stack with the container's former, or — below every frame
hole — at the empty stack. -/
theorem walkStack_split {prog : List NestHole} {c : Name} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} {ts : List PosTree} {n : Nat} {act : List NestKey}
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x)
    (hhead : (grp.headD default).1 = c)
    (hdr : PosDR ops env ctx n (.frame act (nestWalkStack ctx prog ds) us ds grp))
    (hd : PosD ops env ctx (.frame (nestWalkStack ctx prog ds) us ds grp) ts) :
    (nestWalkStack ctx prog ds = prog ∧ ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨c, us, ds⟩ = .ok (nI, (grp.headD default).2) ∧
        grp.head? = some (c, (grp.headD default).2) ∧ PosD ops env ctx (.frame prog us ds grp) ts) ∨
    (nestWalkStack ctx prog ds = [] ∧ (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧
      (∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x) ∧ c ∈ grp.map (·.1) ∧
      PosD ops env ctx (.frame [] us ds grp) ts) := by
  obtain ⟨hne, hinst, -⟩ := hdr.frame_inv
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, grp = p :: rest := by
    cases grp with
    | nil => exact absurd rfl hne
    | cons p rest => exact ⟨p, rest, rfl⟩
  simp only [List.headD_cons] at hhead ⊢
  subst hhead
  unfold nestWalkStack at hinst hd hdr ⊢
  split
  · rename_i hfree
    have hfree' : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0 := by simpa using hfree
    rw [if_pos hfree] at hd
    refine Or.inr ⟨rfl, hfree', fun x hx => WScoped.of_fvarsBelow (hdsw x hx)
      (Expr.fvarB_le (hfree' x hx)), List.mem_cons_self, hd⟩
  · rename_i hfree
    rw [if_neg hfree] at hinst hd
    obtain ⟨nI, h⟩ := hinst p List.mem_cons_self
    exact Or.inl ⟨rfl, nI, h, rfl, hd⟩

/-- **`PosDR` refines `PosD`**: every run-complete derivation erases to a
`PosD` derivation of the same judgment (the in-progress list, the fuel and
the skipped keys forgotten). -/
theorem posDR_posD {n : Nat} {J : PosJR} (h : PosDR ops env ctx n J) :
    ∃ ts, PosD ops env ctx J.erase ts := by
  induction h with
  | const hw hocc => exact ⟨[], .const hw hocc⟩
  | pi hw hocc ha _ _ ih =>
    obtain ⟨ts, h⟩ := ih
    exact ⟨ts, .pi hw hocc ha h⟩
  | hole hw hocc hfn hlo hhi hlen hpar hfree =>
    exact ⟨[], .hole hw hocc hfn hlo hhi hlen hpar hfree⟩
  | frameHole hw hocc hfn hlo hhi hk hle hpar hfree har =>
    exact ⟨[], .frameHole hw hocc hfn hlo hhi hk hle hpar hfree har⟩
  | cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hdsA hsc hnI hact hhead hm hfr ih =>
    obtain ⟨ts, hd⟩ := ih
    rcases walkStack_split hdsw hhead hfr hd with ⟨-, nI', hnI', hhd, hd'⟩ |
      ⟨-, hfree, hdsw', hmem, hd'⟩
    · have heq := hnI'.symm.trans hnI
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      rw [heq.2] at hhd
      exact ⟨_, .contNew hw hocc hfn hnm hC hlen hquot hidx hds hdsw hdsA hnI hhd hsc hd'⟩
    · exact ⟨_, .contHit hw hocc hfn hnm hC hlen hquot hidx
        (fun x hx => ⟨(hds x hx).1, hfree x hx⟩) hdsw' hdsA hnI hmem hd'⟩
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty _ _ ih =>
    obtain ⟨ts, hd⟩ := ih
    exact ⟨ts, .frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hd⟩
  | ctorsNil => exact ⟨[], .ctorsNil⟩
  | ctorsCons hnd hcrest hty hsort _ _ hu4 hres hidx _ _ iht ihr =>
    obtain ⟨ts, ht⟩ := iht
    obtain ⟨ts', hr⟩ := ihr
    exact ⟨ts ++ ts', .ctorsCons hnd hcrest hty hsort ht hu4 hres hidx hr⟩
  | teleNil => exact ⟨[], .teleNil⟩
  | teleCons _ _ _ _ iha ihb =>
    obtain ⟨ts, ha⟩ := iha
    obtain ⟨ts', hb⟩ := ihb
    exact ⟨ts ++ ts', .teleCons ha hb⟩

end Helpers

end ConLeche
