module

public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase

public section

/-!
# Completeness of the positivity walk against a derivation (lane COMPLETE-2, half (B))

`PosD` (`PosDeriv.lean`) is what a SUCCESSFUL run implies (`nestPos_deriv`).
The converse — "a `PosD` derivation exists ⇒ `nestPos` succeeds (given
enough fuel)" — is FALSE for `PosD` as it stands, for three reasons, each a
place where `PosD` forgets something the run checks:

1. **The syntactic pass is unkeyed.**  `PosD`'s `teleCons` carries a
   `.syn prog` derivation that is not tied to the field: `synNil` derives
   it for every field.  The run scans the field's domain (`nestSynOccs`)
   and walks — or rejects — every occurrence it finds (e.g. a whnf-erased
   `K (N T)` with `N` negative, or a whnf-erased occurrence whose
   parameters mention a field variable: "cannot contain local variables").
2. **Freshness.**  The run rejects an instantiation met as a CONSTANT while
   it is in progress (`nestContKey`: in the frame stack `prog`, or in the
   run's `active` list — the frames being walked, including those walked
   at the empty stack).  `PosD.contNew` has no such premise.
3. **The walk stack.**  The run walks an instantiation whose parameters
   lie below every frame hole at the EMPTY stack (`nestWalkStack`);
   `PosD.contNew` may derive its frame under the occurrence's stack.

`PosDR` is `PosD` with exactly these three facts added: its judgments
carry the in-progress list `act` (the run's `active`), the container rule
(`cont`, subsuming `contNew`/`contHit`) walks its frame at
`nestWalkStack` and requires the key fresh, and the syntactic pass is the
judgment `synKeys act prog keys` over the keys the run's scan returns
(`teleCons` instantiates it at `nestSynOccs` of the field).  Every judgment
carries a FUEL index: the run's fuel is spent one unit per `Π` body, per
container descent and per syntactic pass.

* `posDR_run` (**(B)**): a `PosDR` derivation at fuel index `n` ⇒ the run at
  any fuel `≥ n` succeeds with the derivation's kinds and normal forms
  (for every state whose `active` is `act` and whose container cache is
  the environment's); `memberCtorDR_run`/`nestedBlockPositivity_complete`: the
  member constructors' runs, the fuel side condition being `n ≤
  whnfWalkFuel crest`.
* `posDR_posD`: `PosDR` refines `PosD` (the erasure: forget `act`, the
  fuel, and the scanned keys that are skipped).
-/

namespace ConLeche

open Expr

/-- The keys of a frame's group at its instantiation (`nestContNew`'s
`active` entries). -/
@[expose] def grpKeys (us : List Level) (ds : List Expr) (grp : List (Name × Expr)) : List NestKey :=
  grp.map fun p => ⟨p.1, us, ds⟩

/-- The run-complete judgments: `PosJ` with the in-progress list `act`,
and the syntactic pass keyed by the scanned keys. -/
inductive PosJR where
  | field (act : List NestKey) (prog : List NestHole) (dep kb : Nat) (e : Expr) (k : PosKind)
      (nf : Expr)
  | tele (act : List NestKey) (prog : List NestHole) (base nF j : Nat) (cur : Expr)
      (ks : List PosKind) (nds : List (Expr × BinderMeta)) (res : Expr)
  | ctors (act : List NestKey) (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
      (sub : Name → List Level → Option Expr) (cs : List (ConstantVal × Nat))
  | frame (act : List NestKey) (prog : List NestHole) (us : List Level) (ds : List Expr)
      (grp : List (Name × Expr))
  | synKeys (act : List NestKey) (prog : List NestHole) (e : Expr) (keys : List NestKey)

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
      {bm : BinderMeta} {k : PosKind} {nb : Expr}
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
      (hsc : ProgScoped ctx prog)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨c, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hfresh : ∀ h ∈ prog, h.key ≠ ⟨c, us, w.getAppArgs.take nPc⟩)
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
      {ks : List PosKind} {nds : List (Expr × BinderMeta)} {cur : Expr}
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
  /-- one field: its post-whnf walk, then its SYNTACTIC pass over exactly
  the keys the run's scan returns, then the rest -/
  | teleCons {n m₁ m₂ m₃ : Nat} {act : List NestKey} {prog : List NestHole} {base nF j : Nat}
      {a b : Expr} {bm : BinderMeta} {k : PosKind} {nd : Expr} {ks : List PosKind}
      {nds : List (Expr × BinderMeta)} {res : Expr}
      (hm₁ : m₁ ≤ n)
      (ha : PosDR ops env ctx m₁ (.field act prog (base + j) 0 a k nd))
      (hm₂ : m₂ < n)
      (hs : PosDR ops env ctx m₂
        (.synKeys act prog a (nestSynOccs ctx (ctx.hiAt prog.length) a)))
      (hm₃ : m₃ ≤ n)
      (hb : PosDR ops env ctx m₃
        (.tele act prog base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res)) :
      PosDR ops env ctx n
        (.tele act prog base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)
  | synNil {n : Nat} {act : List NestKey} {prog : List NestHole} {e : Expr} :
      PosDR ops env ctx n (.synKeys act prog e [])
  /-- a scanned key in progress (in a frame of `prog`, or in `act`): the
  run skips it -/
  | synSkip {n m : Nat} {act : List NestKey} {prog : List NestHole} {e : Expr} {key : NestKey}
      {keys : List NestKey}
      (hds : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
      (hin : (∃ h ∈ prog, h.key = key) ∨ key ∈ act)
      (hm : m ≤ n)
      (hrest : PosDR ops env ctx m (.synKeys act prog e keys)) :
      PosDR ops env ctx n (.synKeys act prog e (key :: keys))
  /-- a scanned key walked: its frame at the run's walk stack; its SOURCE
  (`SynSrc`, as `PosD.synNew`/`synHit`) is a raw subterm of the scanned
  field `e` (`nestSynOccs_src` supplies it for every scanned key) -/
  | synWalk {n m₁ m₂ : Nat} {act : List NestKey} {prog : List NestHole} {e : Expr}
      {key : NestKey} {keys : List NestKey} {L : List (ConstantVal × Nat)}
      {grp : List (Name × Expr)}
      (hsrc : SynSrc ctx (ctx.hiAt prog.length) e key)
      (hds : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
      (hdsw : ∀ x ∈ key.ds, Expr.WScoped (ctx.hiAt prog.length) x)
      (hsc : ProgScoped ctx prog)
      (hnm : ctx.names.contains key.cname = false) (hquot : key.cname ≠ quotName)
      (hC : nestContainer ctx key.cname = some (key.ds.length, L))
      (hhead : (grp.headD default).1 = key.cname)
      (hm₁ : m₁ ≤ n)
      (hfr : PosDR ops env ctx m₁
        (.frame act (nestWalkStack ctx prog key.ds) key.lvls key.ds grp))
      (hm₂ : m₂ ≤ n)
      (hrest : PosDR ops env ctx m₂ (.synKeys act prog e keys)) :
      PosDR ops env ctx n (.synKeys act prog e (key :: keys))

/-- **A member constructor, run-completely derived** (`MemberCtorD` with
`PosDR` at fuel index `n`, no frame in progress). -/
@[expose] def MemberCtorDR (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (n nF : Nat)
    (crest : Expr) (ks : List PosKind) (tyN : Expr) : Prop :=
  ∃ nds cur, PosDR ops env ctx n (.tele [] [] (ctx.hiAt 0) nF 0 crest ks nds cur) ∧
    tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
    ((List.range nF).any fun i =>
      (ks.getD i .ordinary).guarded && structUsedLater tyN 0 i) = false ∧
    nestResHead cur = true ∧
    (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true ∧
    tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true

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
  | cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hsc hnI hfresh hact hhead hm hfr =>
    exact .cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hsc hnI hfresh hact hhead (by omega) hfr
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hm hwalk =>
    exact .frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty (by omega) hwalk
  | ctorsNil => exact .ctorsNil
  | ctorsCons hnd hcrest hty hsort hm₁ htele hu4 hres hidx hm₂ hrest =>
    exact .ctorsCons hnd hcrest hty hsort (by omega) htele hu4 hres hidx (by omega) hrest
  | teleNil => exact .teleNil
  | teleCons hm₁ ha hm₂ hs hm₃ hb => exact .teleCons (by omega) ha (by omega) hs (by omega) hb
  | synNil => exact .synNil
  | synSkip hds hin hm hrest => exact .synSkip hds hin (by omega) hrest
  | synWalk hsrc hds hdsw hsc hnm hquot hC hhead hm₁ hfr hm₂ hrest =>
    exact .synWalk hsrc hds hdsw hsc hnm hquot hC hhead (by omega) hfr (by omega) hrest

/-! ## (B): the derivation's run -/

/-- **The run's state, as the derivation sees it**: its in-progress list
is `act`, and its container lookups are the environment's. -/
@[expose] def RInv (ctx : NestCtx) (st : NestState) (act : List NestKey) : Prop :=
  st.active = act ∧ ∀ c r, st.ctorsOf.lookup c = some r → r = nestContainer ctx c

theorem RInv.lookup {ctx : NestCtx} {st : NestState} {act : List NestKey} (h : RInv ctx st act)
    (c : Name) : (nestContainerC ctx st c).1 = nestContainer ctx c := by
  unfold nestContainerC
  split
  · rename_i r hr; exact h.2 c r hr
  · rfl

theorem RInv.insert {ctx : NestCtx} {st : NestState} {act : List NestKey} (h : RInv ctx st act)
    (c : Name) : RInv ctx (nestContainerC ctx st c).2 act := by
  unfold nestContainerC
  split
  · exact h
  · refine ⟨h.1, fun c' r hl => ?_⟩
    simp only [List.lookup] at hl
    split at hl
    · rename_i heq
      simp only [Option.some.injEq] at hl
      rw [← hl]
      congr 1
      exact (beq_iff_eq.mp heq).symm
    · exact h.2 c' r hl

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

theorem nestAcceptGroup_ok {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st : NestState),
      (∀ p ∈ grp, ∃ nI ty, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, ty)) →
      ∃ st', nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' ∧
        st'.active = st.active ∧ st'.ctorsOf = st.ctorsOf
  | [], st, _ => ⟨st, rfl, rfl, rfl⟩
  | (c, ty) :: rest, st, h => by
    simp only [nestAcceptGroup, bind, Except.bind]
    split
    · obtain ⟨nI, ty', hp⟩ := h (c, ty) List.mem_cons_self
      rw [hp]
      exact nestAcceptGroup_ok rest _ (fun p hp => h p (List.mem_cons_of_mem _ hp))
    · exact nestAcceptGroup_ok rest st (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem nestGroupCtors_ok {nPc : Nat} {act : List NestKey} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)),
      groupCtors ctx nPc cs = some ctors → RInv ctx st act →
      ∃ st', nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') ∧ RInv ctx st' act
  | [], st, ctors, h, hI => by
    simp only [groupCtors, Option.some.injEq] at h
    subst h
    exact ⟨st, rfl, hI⟩
  | c :: cs, st, ctors, h, hI => by
    simp only [groupCtors] at h
    split at h
    · rename_i nP' L hq
      split at h
      · rename_i hok
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨st₁, h₁, hI₁⟩ := nestGroupCtors_ok cs _ rest hr (hI.insert c)
        refine ⟨st₁, ?_, hI₁⟩
        simp only [nestGroupCtors, bind, Except.bind, hI.lookup c, hq, unwrapOr, pure,
          Except.pure]
        rw [if_pos (by simpa using hok)]
        simp only [h₁]
      · exact nomatch h
    · exact nomatch h

/-- What a frame's run needs of its walk: its run from any state whose
in-progress list holds the group. -/
@[expose] def FrameRun (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState)
    (act : List NestKey) (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  ∀ st, RInv ctx st (grpKeys us ds grp ++ act) →
    ∃ st', nestFrame ctx ops env rec syn prog (ctx.hiAt prog.length) us ds ds.length grp st
      = .ok st' ∧ RInv ctx st' (grpKeys us ds grp ++ act)

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
  {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}

/-- **A new (or re-walked) instantiation runs**: given its frame's facts and
its frame's run at the walk stack. -/
theorem nestContNew_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {old : Option Nat} {st : NestState} {act : List NestKey}
    {grp : List (Name × Expr)}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hne : grp ≠ []) (hhead : (grp.headD default).1 = c)
    (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hgrp : grp.map (·.1) = c :: nestFrameMates ctx c)
    (hfr : FrameRun ops env ctx rec syn act (nestWalkStack ctx prog ds) us ds grp) :
    ∃ k st', nestContNew ctx ops env rec syn prog kb c us ds nPc old st = .ok (k, st') ∧
      k.erase = .nested (kb != 0) ∧ RInv ctx st' act := by
  subst hnPc
  obtain ⟨⟨c', cty⟩, rest, rfl⟩ : ∃ p rest, grp = p :: rest := by
    cases grp with
    | nil => exact absurd rfl hne
    | cons p rest => exact ⟨p, rest, rfl⟩
  simp only [List.headD_cons] at hhead
  subst hhead
  obtain ⟨nI, hnI⟩ := hinst _ List.mem_cons_self
  have hmap : rest.map (·.1) = nestFrameMates ctx c' := by
    simpa using hgrp
  have hgrow := nestGrowGroup_ok (ctx := ctx) (hi := ctx.hiAt (nestWalkStack ctx prog ds).length)
    (us := us) (ds := ds) rest [(c', cty)] (fun p hp => hinst p (List.mem_cons_of_mem _ hp))
  rw [hmap] at hgrow
  obtain ⟨st₁, hf₁, hI₁⟩ := hfr { st with active := grpKeys us ds ((c', cty) :: rest) ++ st.active }
    ⟨by rw [hI.1], hI.2⟩
  obtain ⟨st₂, hacc, hact₂, hco₂⟩ := nestAcceptGroup_ok (ctx := ctx)
    (hi := ctx.hiAt (nestWalkStack ctx prog ds).length) (us := us) (ds := ds) rest
    { st₁ with active := st.active }
    (fun p hp => by
      obtain ⟨nI', h'⟩ := hinst p (List.mem_cons_of_mem _ hp)
      exact ⟨nI', p.2, h'⟩)
  simp only [nestContNew, bind, Except.bind, hnI, hgrow, List.singleton_append]
  have hf₁' : nestFrame ctx ops env rec syn (nestWalkStack ctx prog ds)
      (ctx.hiAt (nestWalkStack ctx prog ds).length) us ds ds.length ((c', cty) :: rest)
      { st with active := (List.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey))
        ((c', cty) :: rest) ++ st.active) } = .ok st₁ := hf₁
  rw [hf₁']
  simp only [List.drop_succ_cons, List.drop_zero, hacc]
  have hI₂ : RInv ctx st₂ act := ⟨by rw [hact₂]; exact hI.1, by rw [hco₂]; exact hI₁.2⟩
  cases old with
  | some q => exact ⟨_, _, rfl, rfl, hI₂.1, hI₂.2⟩
  | none => exact ⟨_, _, rfl, rfl, hI₂.1, hI₂.2⟩

/-- The preconditions of a frame walk at the walk stack (the frame rule's
facts the run's `nestContNew` reads, and the frame's run). -/
@[expose] def NewOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState)
    (act : List NestKey) (prog : List NestHole) (c : Name) (us : List Level) (ds : List Expr) :
    Prop :=
  ∃ grp : List (Name × Expr), grp ≠ [] ∧ (grp.headD default).1 = c ∧
    (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx
      (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨p.1, us, ds⟩ = .ok (nI, p.2)) ∧
    grp.map (·.1) = c :: nestFrameMates ctx c ∧
    FrameRun ops env ctx rec syn act (nestWalkStack ctx prog ds) us ds grp

theorem nestContNew_ok' {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {old : Option Nat} {st : NestState} {act : List NestKey}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hnew : NewOk ops env ctx rec syn act prog c us ds) :
    ∃ k st', nestContNew ctx ops env rec syn prog kb c us ds nPc old st = .ok (k, st') ∧
      k.erase = .nested (kb != 0) ∧ RInv ctx st' act := by
  obtain ⟨grp, hne, hhead, hinst, hgrp, hfr⟩ := hnew
  exact nestContNew_ok hI hnPc hne hhead hinst hgrp hfr

/-- **A fresh instantiation met runs.** -/
theorem nestContKey_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {st : NestState} {act : List NestKey}
    (hI : RInv ctx st act) (hnPc : ds.length = nPc)
    (hfresh : ∀ h ∈ prog, h.key ≠ ⟨c, us, ds⟩) (hact : (⟨c, us, ds⟩ : NestKey) ∉ act)
    (hnew : NewOk ops env ctx rec syn act prog c us ds) :
    ∃ k st', nestContKey ctx ops env rec syn prog kb c us ds nPc st = .ok (k, st') ∧
      k.erase = .nested (kb != 0) ∧ RInv ctx st' act := by
  unfold nestContKey
  have hprog : prog.any (·.key == (⟨c, us, ds⟩ : NestKey)) = false := by
    rw [List.any_eq_false]
    intro h hh
    simpa using hfresh h hh
  have hactc : st.active.contains ⟨c, us, ds⟩ = false := by
    rw [hI.1]; simpa using hact
  rw [if_neg (by rw [hprog, hactc]; simp)]
  split
  · rename_i q _
    split
    · exact ⟨_, _, rfl, rfl, hI.1, hI.2⟩
    · exact nestContNew_ok' hI hnPc hnew
  · exact nestContNew_ok' hI hnPc hnew

/-- **The container case runs.** -/
theorem nestCont_ok {prog : List NestHole} {kb : Nat} {c : Name} {us : List Level}
    {args : List Expr} {st : NestState} {act : List NestKey} {L : List (ConstantVal × Nat)}
    {nPc nI : Nat} {cty : Expr}
    (hI : RInv ctx st act) (hC : nestContainer ctx c = some (nPc, L))
    (hlen : args.length = nPc + nI) (hquot : c ≠ quotName)
    (hidx : ∀ x ∈ args.drop nPc, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
    (hds : ∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨c, us, args.take nPc⟩
      = .ok (nI, cty))
    (hfresh : ∀ h ∈ prog, h.key ≠ ⟨c, us, args.take nPc⟩)
    (hact : (⟨c, us, args.take nPc⟩ : NestKey) ∉ act)
    (hnew : NewOk ops env ctx rec syn act prog c us (args.take nPc)) :
    ∃ k st', nestCont ctx ops env rec syn prog kb c us args st = .ok (k, st') ∧
      k.erase = .nested (kb != 0) ∧ RInv ctx st' act := by
  unfold nestCont
  simp only [bind, Except.bind, hI.lookup c, hC, unwrapOr, pure, Except.pure]
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
  simp only [hnI]
  rw [if_pos (by simp [hlen])]
  exact nestContKey_ok (hI.insert c) (by simp; omega) hfresh hact hnew

/-- **A scanned key in progress is skipped.** -/
theorem nestSynKey_skip {prog : List NestHole} {skip : List NestKey} {key : NestKey}
    {st : NestState} {act : List NestKey} (hI : RInv ctx st act)
    (hds : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hin : (∃ h ∈ prog, h.key = key) ∨ key ∈ act) :
    nestSynKey ctx ops env rec syn prog skip key st = .ok st := by
  unfold nestSynKey
  rw [if_neg (by
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    rw [List.all_eq_true]
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hds x hx)]
  rw [if_pos (by
    rcases hin with ⟨h, hh, rfl⟩ | hin
    · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨h, hh, rfl⟩)
    · simp only [Bool.or_eq_true, hI.1, List.contains_iff_mem]
      exact Or.inr hin)]
  rfl

/-- **A scanned key walked runs.** -/
theorem nestSynKey_walk {prog : List NestHole} {skip : List NestKey} {key : NestKey}
    {st : NestState} {act : List NestKey} {L : List (ConstantVal × Nat)} (hI : RInv ctx st act)
    (hds : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hnm : ctx.names.contains key.cname = false) (hquot : key.cname ≠ quotName)
    (hC : nestContainer ctx key.cname = some (key.ds.length, L))
    (hnew : NewOk ops env ctx rec syn act prog key.cname key.lvls key.ds) :
    ∃ st', nestSynKey ctx ops env rec syn prog skip key st = .ok st' ∧ RInv ctx st' act := by
  unfold nestSynKey
  rw [if_neg (by
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    rw [List.all_eq_true]
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hds x hx)]
  split
  · exact ⟨st, rfl, hI⟩
  rw [if_neg (by rw [hnm, Bool.false_or]; simpa using hquot)]
  have hI₀ := hI.insert key.cname
  rw [hI.lookup key.cname, hC]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  split
  · rename_i q' _
    split
    · exact ⟨_, rfl, hI₀.1, hI₀.2⟩
    · obtain ⟨k, st', h, -, hI'⟩ := nestContNew_ok' (kb := 0) (old := some q') hI₀ rfl hnew
      simp only [bind, Except.bind]
      rw [h]
      exact ⟨st', rfl, hI'⟩
  · obtain ⟨k, st', h, -, hI'⟩ := nestContNew_ok' (kb := 0) (old := none) hI₀ rfl hnew
    simp only [bind, Except.bind]
    rw [h]
    exact ⟨st', rfl, hI'⟩

/-- **The claim of (B) at a judgment**: the corresponding run, at every
fuel at least the index, from every state the judgment's in-progress list
describes, succeeds with the judgment's outputs. -/
@[expose] def RunOK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (n : Nat) : PosJR → Prop
  | .field act prog dep kb e k nf => ∀ fuel, n ≤ fuel → ∀ st, RInv ctx st act →
      ∃ k' st', nestPos ops env ctx fuel prog dep kb e st = .ok (k', nf, st') ∧ k'.erase = k ∧
        RInv ctx st' act
  | .tele act prog base nF j cur ks nds res => ∀ fuel, n ≤ fuel → ∀ st, RInv ctx st act →
      ∃ ks' st', (∀ err, nestFields (nestPos ops env ctx fuel) (nestSyn ops env ctx fuel) prog base
          err nF j cur st = .ok (ks', nds, res, st')) ∧ ks'.map (·.erase) = ks ∧ RInv ctx st' act
  | .ctors act prog hi us ds sub cs => ∀ fuel, n ≤ fuel → ∀ st, RInv ctx st act →
      ∃ st', nestCtors ctx ops env (nestPos ops env ctx fuel) (nestSyn ops env ctx fuel) prog hi us
          ds ds.length sub cs st = .ok st' ∧ RInv ctx st' act
  | .frame act prog us ds grp => ∀ fuel, n ≤ fuel →
      FrameRun ops env ctx (nestPos ops env ctx fuel) (nestSyn ops env ctx fuel) act prog us ds grp
  | .synKeys act prog _ keys => ∀ fuel, n ≤ fuel → ∀ skip st, RInv ctx st act →
      ∃ st', nestSynKeys ctx ops env (nestPos ops env ctx fuel) (nestSyn ops env ctx fuel) prog skip
          keys st = .ok st' ∧ RInv ctx st' act

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
    {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}
    {n : Nat} {act : List NestKey} {prog : List NestHole} {c : Name} {us : List Level}
    {ds : List Expr} {grp : List (Name × Expr)}
    (h : PosDR ops env ctx n (.frame act (nestWalkStack ctx prog ds) us ds grp))
    (hhead : (grp.headD default).1 = c)
    (hrun : FrameRun ops env ctx rec syn act (nestWalkStack ctx prog ds) us ds grp) :
    NewOk ops env ctx rec syn act prog c us ds := by
  obtain ⟨hne, hinst, hgrp⟩ := h.frame_inv
  rw [hhead] at hgrp
  exact ⟨grp, hne, hhead, hinst, hgrp, hrun⟩

/-- **(B), THE COMPLETENESS OF THE WALK AGAINST ITS DERIVATION.**  A
`PosDR` derivation at fuel index `n` makes the corresponding run succeed at
every fuel `≥ n`, with the derivation's kinds and normal forms. -/
theorem posDR_run {n : Nat} {J : PosJR} (h : PosDR ops env ctx n J) : RunOK ops env ctx n J := by
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
    · rw [nestPos]
      simp only [hw, bind, Except.bind]
      rw [if_neg (by simpa using hocc)]
      simp only [hfn]
      rw [if_pos (by simp [hlo, hhi])]
      rw [if_pos (by
        simp only [Bool.and_eq_true, beq_iff_eq, hlen, hpar, List.all_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, true_and]
        exact hfree)]
      split
      · simp [Expr.getAppFn] at hfn
      · rfl
    · by_cases hkb : kb = 0 <;> simp [hkb, NestFieldKind.erase]
  | @frameHole n act prog dep kb e w i ty h hw hocc hfn hlo hhi hk hle hpar hfree har =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨.inProgress, st, ?_, rfl, hI⟩
    rw [nestPos]
    simp only [hw, bind, Except.bind]
    rw [if_neg (by simpa using hocc)]
    simp only [hfn]
    rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; omega)]
    rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
    simp only [hk]
    rw [if_pos (by simp [hle, hpar])]
    rw [if_pos (by
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact hfree)]
    rw [if_pos (by simp [har])]
    split
    · simp [Expr.getAppFn] at hfn
    · rfl
  | @cont n m act prog dep kb e w c us L nPc nI cty grp hw hocc hfn hnm hC hlen hquot hidx hds
      hdsw hsc hnI hfresh hact hhead hm hfr ih =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨k', st', hr, hk, hI'⟩ := nestCont_ok (rec := nestPos ops env ctx f)
      (syn := nestSyn ops env ctx f) (kb := kb) (us := us) hI hC hlen hquot hidx hds hnI hfresh hact
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
    obtain ⟨st₁, h₁, hI₁⟩ := nestGroupCtors_ok (ctx := ctx) (nPc := ds.length) _ st ctors hctors hI
    obtain ⟨st', h', hI'⟩ := ih fuel (by omega) st₁ hI₁
    obtain ⟨ty, hty⟩ := hkty
    refine ⟨st', ?_, hI'⟩
    simp only [nestFrame, bind, Except.bind, h₁, hty]
    rw [grpNews_mapIdx]
    exact h'
  | ctorsNil =>
    intro fuel _ st hI
    exact ⟨st, rfl, hI⟩
  | @ctorsCons n m₁ m₂ act prog hi us ds sub cv nF cs crest ty sv ks nds cur hnd hcrest hty hsort
      hm₁ htele hu4 hres hidx hm₂ hrest iht ihr =>
    intro fuel hf st hI
    simp only [nestCtors, bind, Except.bind]
    rw [if_pos hnd]
    simp only [hcrest, unwrapOr, pure, Except.pure, hty, hsort]
    obtain ⟨ks', st₁, h₁, hks, hI₁⟩ := iht fuel (by omega) st hI
    simp only [h₁]
    subst hks
    rw [if_neg (by
      simp only [erase_getD_bne] at hu4
      rw [hu4]; simp)]
    rw [if_pos (by simp [hres, hidx])]
    exact ihr fuel (by omega) st₁ hI₁
  | teleNil =>
    intro fuel _ st hI
    exact ⟨[], st, fun _ => rfl, rfl, hI⟩
  | @teleCons n m₁ m₂ m₃ act prog base nF j a b bm k nd ks nds res hm₁ ha hm₂ hs hm₃ hb iha ihs
      ihb =>
    intro fuel hf st hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨k₁, st₁, h₁, hk₁, hI₁⟩ := iha (f + 1) (by omega) st hI
    obtain ⟨st₂, h₂, hI₂⟩ := ihs f (by omega) (nestSkipKey k₁ st₁) st₁ hI₁
    obtain ⟨ks₂, st₃, h₃, hks₂, hI₃⟩ := ihb (f + 1) (by omega) st₂ hI₂
    refine ⟨k₁ :: ks₂, st₃, fun err => ?_, by simp [hk₁, hks₂], hI₃⟩
    simp only [nestFields, bind, Except.bind, h₁]
    rw [nestSyn, h₂]
    simp only [h₃]
    rfl
  | synNil =>
    intro fuel _ skip st hI
    exact ⟨st, rfl, hI⟩
  | synSkip hds hin hm hrest ih =>
    intro fuel hf skip st hI
    obtain ⟨st', h', hI'⟩ := ih fuel (by omega) skip st hI
    refine ⟨st', ?_, hI'⟩
    simp only [nestSynKeys, bind, Except.bind]
    rw [nestSynKey_skip hI hds hin]
    exact h'
  | synWalk _ hds hdsw hsc hnm hquot hC hhead hm₁ hfr hm₂ hrest ihf ihr =>
    intro fuel hf skip st hI
    obtain ⟨st₁, h₁, hI₁⟩ := nestSynKey_walk (skip := skip) hI hds hnm hquot hC
      (newOk_of hfr hhead (ihf fuel (by omega)))
    obtain ⟨st', h', hI'⟩ := ihr fuel (by omega) skip st₁ hI₁
    refine ⟨st', ?_, hI'⟩
    simp only [nestSynKeys, bind, Except.bind]
    rw [h₁]
    exact h'

theorem guarded_erase (k : NestFieldKind) :
    (match k with
      | .recursive _ | .reflexive _ | .nested _ _ => true
      | _ => false) = k.erase.guarded := by
  cases k <;> rfl

theorem getD_erase (ks : List NestFieldKind) (i : Nat) :
    (ks.map (·.erase)).getD i .ordinary = (ks.getD i .ordinary).erase := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

/-- **(B) at a member constructor**: its run-complete derivation at a fuel
index within the walk's input-derived fuel makes `nestMemberCtor` succeed
with the derivation's kinds and normal form. -/
theorem memberCtorDR_run {n nF : Nat} {crest tyN : Expr} {ks : List PosKind}
    (h : MemberCtorDR ops env ctx n nF crest ks tyN) (hfuel : n ≤ whnfWalkFuel crest)
    {st : NestState} (hI : RInv ctx st []) :
    ∃ ks' st', nestMemberCtor ops env ctx nF crest st = .ok (ks', tyN, st') ∧
      ks'.map (·.erase) = ks ∧ RInv ctx st' [] := by
  obtain ⟨nds, cur, hd, rfl, hu4, hres, hidx, hha⟩ := h
  obtain ⟨ks', st', h₁, hks, hI'⟩ := posDR_run hd (whnfWalkFuel crest) hfuel st hI
  refine ⟨ks', st', ?_, hks, hI'⟩
  simp only [nestMemberCtor, bind, Except.bind, h₁]
  subst hks
  rw [if_neg (by
    have hu4' : ((List.range nF).any fun i =>
        ((ks'.getD i .ordinary).erase.guarded && structUsedLater
          (closeTelescope nds (ctx.hiAt 0) cur) 0 i)) = false := by
      simpa only [getD_erase] using hu4
    intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨i, hi, hc⟩ := hc
    rw [List.any_eq_false] at hu4'
    have := hu4' i hi
    revert hc this
    generalize ks'.getD i .ordinary = k
    cases k <;> simp [NestFieldKind.erase, PosKind.guarded])]
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hres, hidx⟩)]
  rw [if_pos hha]
  rfl

/-- **(B), THE COMPLETENESS THEOREM OF THE NESTED POSITIVITY CHECK**:
every member constructor derived (`MemberCtorDR`, run-complete) within
its fuel, and M2′ (no member constant left after the abstraction), make
`nestedBlockPositivity` succeed. -/
theorem nestedBlockPositivity_complete {holes : List Expr} (hh : nestHoles ctx = some holes)
    {ctorss : List (List (ConstantVal × Nat))}
    (hall : ∀ cs ∈ ctorss, ∀ c ∈ cs, ∃ crest,
      instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
      (∃ n ks tyN, n ≤ whnfWalkFuel crest ∧ MemberCtorDR ops env ctx n c.2 crest ks tyN) ∧
      (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) :
    ∃ r, nestedBlockPositivity ops env ctx ctorss = .ok r := by
  have hmem : ∀ (cs : List (ConstantVal × Nat)) (st : NestState), RInv ctx st [] →
      (∀ c ∈ cs, ∃ crest,
        instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
        (∃ n ks tyN, n ≤ whnfWalkFuel crest ∧ MemberCtorDR ops env ctx n c.2 crest ks tyN) ∧
        (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) →
      ∃ (r : List (List NestFieldKind) × List Expr) (st' : NestState),
        nestMemberCtors ops env ctx holes cs st = .ok (r.1, r.2, st') ∧ RInv ctx st' [] := by
    intro cs
    induction cs with
    | nil => intro st hI _; exact ⟨([], []), st, rfl, hI⟩
    | cons c cs ih =>
      intro st hI hc
      obtain ⟨crest, hcr, ⟨n, ks, tyN, hle, hd⟩, hm2⟩ := hc c List.mem_cons_self
      obtain ⟨ks', st₁, h₁, -, hI₁⟩ := memberCtorDR_run hd hle hI
      obtain ⟨r, st', h₂, hI'⟩ := ih st₁ hI₁ (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))
      refine ⟨(ks' :: r.1, tyN :: r.2), st', ?_, hI'⟩
      simp only [nestMemberCtors, bind, Except.bind, hcr, unwrapOr, pure, Except.pure, h₁]
      simp only [nestNoMemberConst, hm2, Bool.false_eq_true, if_false, pure, Except.pure, h₂]
  have hblk : ∀ (css : List (List (ConstantVal × Nat))) (st : NestState), RInv ctx st [] →
      (∀ cs ∈ css, ∀ c ∈ cs, ∃ crest,
        instPisWith ctx.params (nestAbstract ctx holes c.1.type) = some crest ∧
        (∃ n ks tyN, n ≤ whnfWalkFuel crest ∧ MemberCtorDR ops env ctx n c.2 crest ks tyN) ∧
        (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false) →
      ∃ (r : List (List (List NestFieldKind)) × List (List Expr)) (st' : NestState),
        nestBlockCtors ops env ctx holes css st = .ok (r.1, r.2, st') := by
    intro css
    induction css with
    | nil => intro st _ _; exact ⟨([], []), st, rfl⟩
    | cons cs css ih =>
      intro st hI hc
      obtain ⟨r₁, st₁, h₁, hI₁⟩ := hmem cs st hI (hc cs List.mem_cons_self)
      obtain ⟨r₂, st', h₂⟩ := ih st₁ hI₁ (fun cs' hcs' => hc cs' (List.mem_cons_of_mem _ hcs'))
      refine ⟨(r₁.1 :: r₂.1, r₁.2 :: r₂.2), st', ?_⟩
      simp only [nestBlockCtors, bind, Except.bind, h₁, h₂]
      rfl
  obtain ⟨r, st', h⟩ := hblk ctorss {} ⟨rfl, fun _ _ h => by simp at h⟩ hall
  simp only [nestedBlockPositivity, bind, Except.bind, hh, unwrapOr, pure, Except.pure, h]
  exact ⟨_, rfl⟩

/-! ## `PosDR` refines `PosD` -/

/-- A run-complete judgment's `PosD` judgment. -/
@[expose] def PosJR.erase : PosJR → PosJ
  | .field _ prog dep kb e k nf => .field prog dep kb e k nf
  | .tele _ prog base nF j cur ks nds res => .tele prog base nF j cur ks nds res
  | .ctors _ prog hi us ds sub cs => .ctors prog hi us ds sub cs
  | .frame _ prog us ds grp => .frame prog us ds grp
  | .synKeys _ prog e _ => .syn prog e

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
  | cont hw hocc hfn hnm hC hlen hquot hidx hds hdsw hsc hnI hfresh hact hhead hm hfr ih =>
    obtain ⟨ts, hd⟩ := ih
    rcases walkStack_split hdsw hhead hfr hd with ⟨-, nI', hnI', hhd, hd'⟩ |
      ⟨-, hfree, hdsw', hmem, hd'⟩
    · have heq := hnI'.symm.trans hnI
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      rw [heq.2] at hhd
      exact ⟨_, .contNew hw hocc hfn hnm hC hlen hquot hidx hds hdsw hnI hhd hsc hd'⟩
    · exact ⟨_, .contHit hw hocc hfn hnm hC hlen hquot hidx
        (fun x hx => ⟨(hds x hx).1, hfree x hx⟩) hdsw' hnI hmem hd'⟩
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty _ _ ih =>
    obtain ⟨ts, hd⟩ := ih
    exact ⟨ts, .frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hd⟩
  | ctorsNil => exact ⟨[], .ctorsNil⟩
  | ctorsCons hnd hcrest hty hsort _ _ hu4 hres hidx _ _ iht ihr =>
    obtain ⟨ts, ht⟩ := iht
    obtain ⟨ts', hr⟩ := ihr
    exact ⟨ts ++ ts', .ctorsCons hnd hcrest hty hsort ht hu4 hres hidx hr⟩
  | teleNil => exact ⟨[], .teleNil⟩
  | teleCons _ _ _ _ _ _ iha ihs ihb =>
    obtain ⟨ts, ha⟩ := iha
    obtain ⟨tss, hs⟩ := ihs
    obtain ⟨ts', hb⟩ := ihb
    exact ⟨ts ++ (tss ++ ts'), .teleCons ha hs hb⟩
  | synNil => exact ⟨[], .synNil⟩
  | synSkip _ _ _ _ ih => exact ih
  | synWalk hsrc hds hdsw hsc hnm hquot hC hhead _ hfr _ _ ihf ihr =>
    obtain ⟨ts, hd⟩ := ihf
    obtain ⟨ts', hr⟩ := ihr
    rcases walkStack_split hdsw hhead hfr hd with ⟨-, nI', hnI', hhd, hd'⟩ |
      ⟨-, hfree, hdsw', hmem, hd'⟩
    · exact ⟨_, .synNew hsrc hnm hquot hC hds hdsw hnI' hhd hsc hd' hr⟩
    · exact ⟨_, .synHit hsrc hnm hquot hC (fun x hx => ⟨(hds x hx).1, hfree x hx⟩) hdsw' hmem hd'
        hr⟩

/-- A run-complete member constructor is a `PosD` member constructor. -/
theorem memberCtorDR_posD {n nF : Nat} {crest tyN : Expr} {ks : List PosKind}
    (h : MemberCtorDR ops env ctx n nF crest ks tyN) :
    ∃ ts, MemberCtorD ops env ctx nF crest ks tyN ts := by
  obtain ⟨nds, cur, hd, htyN, hu4, hres, hidx, hha⟩ := h
  obtain ⟨ts, hd'⟩ := posDR_posD hd
  exact ⟨ts, nds, cur, hd', htyN, hu4, hres, hidx, hha⟩

end Helpers

end ConLeche
