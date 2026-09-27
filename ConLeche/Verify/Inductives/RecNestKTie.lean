module
import ConLeche.Verify.Inductives.LayoutKSpec
public import ConLeche.Verify.Inductives.PosDerivK
import ConLeche.Verify.Inductives.ClassNf
import ConLeche.Verify.ExceptBind
public import ConLeche.Verify.Inductives.RecNestKRun
import ConLeche.Verify.Inductives.PosNfK
public import ConLeche.Verify.Inductives.UseOkK
import ConLeche.Verify.Inductives.UseOkKRun
import ConLeche.Verify.Inductives.PosDerivKInv
public import ConLeche.Verify.Inductives.RecCheckRun
public section

/-!
# The recursor route's layouts are the re-run positivity check's nodes (PRIMREC / NESTKN-NL)

Piece (v) of the node lemma (DESIGN.md "PRIMREC / NESTKN-RP", round 2): the determinism
ties between the recursor check's nested route (`Kernel/Inductives/RecNestK.lean`) and the
key-named positivity derivation its re-run (`homesPosRK`, `NestRouteRun.pos`) gives.

* `nestLayoutK_congr` — the layout function sees a key only through its canonical group,
  levels and parameters;
* `layNfsRK_tie` — the route's field normal forms at a layout are the derivation's
  telescopes (`posDK_node_nf`, fuel monotonicity);
* `contLayRK_spec` — a container layout of the route, unfolded at the layout function's
  value;
* `NestRouteRun.contLay_node` — every container layout of the route's final state is the
  layout of a node the re-run DERIVED at `UseOkK`, given that the canonical groups are
  consistent (`GroupsOkK`, from the model's `LfpCover.all`).
-/

namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The layout function sees a key only through its group, levels and parameters**
(it canonicalises the head, `nestLayoutK`). -/
theorem nestLayoutK_congr (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (look : Name → Option (Nat × List (ConstantVal × Nat))) {k0 k1 : NestKey}
    (hg : groupOfK ctx k0.cname = groupOfK ctx k1.cname) (hl : k0.lvls = k1.lvls)
    (hd : k0.ds = k1.ds) :
    nestLayoutK ops env ctx look k0 = nestLayoutK ops env ctx look k1 := by
  obtain ⟨a, as, hcons⟩ : ∃ a as, groupOfK ctx k1.cname = a :: as := by
    cases h : groupOfK ctx k1.cname with
    | nil => exact absurd h (groupOfK_ne_nil (ctx := ctx) k1.cname)
    | cons a as => exact ⟨a, as, rfl⟩
  unfold nestLayoutK
  rw [hg, hcons]
  simp only [List.headD, hl, hd]

section Nfs

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hk : UseHookK}

/-- **The recursor check's field normal forms at a layout are the derivation's**
(`layNfsRK` runs `nestTeleNf` at the crest's own fuel; the derivation's telescope is
`nestTeleNf`'s value at every fuel above a bound, `posDK_node_nf`, and a run that
succeeds keeps its value at more fuel, `nestTeleNf_fuel_mono`). -/
theorem layNfsRK_tie {L : LayoutK} {met : List Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (crs : List Expr) (nfs : List (List Expr)),
      layNfsRK ops env ctx L.hi cs crs = .ok nfs →
      (∀ x ∈ cs.zip crs, ∃ ks nds cur, PosDKH ops env ctx hk (.tele L met x.1.2 0 x.2 ks nds cur) ∧
        ∃ F, ∀ fuel, F ≤ fuel →
          nestTeleNf ops env ctx.names ctx.nP L.hi fuel L.hi x.1.2 0 x.2 = .ok (nds, cur)) →
      nfs.length = (cs.zip crs).length ∧
      ∀ (j : Nat) (x : (ConstantVal × Nat) × Expr), (cs.zip crs)[j]? = some x → ∃ ks nds cur,
        PosDKH ops env ctx hk (.tele L met x.1.2 0 x.2 ks nds cur) ∧ nfs[j]? = some (nds.map (·.1))
  | c :: cs, cr :: crs, nfs, h, hd => by
    unfold layNfsRK at h
    obtain ⟨⟨nds', cur'⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨rest, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := layNfsRK_tie cs crs rest h2 fun x hx => hd x (List.mem_cons_of_mem _ hx)
    obtain ⟨ks, nds, cur, hD, F, hF⟩ := hd (c, cr) List.mem_cons_self
    have e1 := nestTeleNf_fuel_mono (Nat.le_max_left (whnfWalkFuel cr) F) _ _ _ h1
    rw [hF _ (Nat.le_max_right _ _)] at e1
    obtain ⟨rfl, rfl⟩ : nds = nds' ∧ cur = cur' := by simpa using e1
    refine ⟨by simp [hlen], fun j x hx => ?_⟩
    cases j with
    | zero =>
      obtain rfl : x = (c, cr) := by simpa using hx.symm
      exact ⟨ks, nds, cur, hD, rfl⟩
    | succ j => exact hall j x (by simpa using hx)
  | [], _, nfs, h, _ => by
    simp only [layNfsRK, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun j x hx => by simp at hx⟩
  | _ :: _, [], nfs, h, _ => by
    simp only [layNfsRK, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun j x hx => by simp at hx⟩

end Nfs

section Lay

variable {ops : CheckerOps CheckM} {env : Env}

/-- **A container layout of the recursor route, unfolded** at the layout function's value
`lo` for its key: the positivity check's layout, its group's constructors split by member,
every member's field normal forms `layNfsRK` at the layout. -/
theorem contLayRK_spec {h : Nat} {H : HomeRK} {kc : NestKey} {l : LayRK} {lo : LayoutOutK}
    (hr : contLayRK ops env h H kc = .ok l)
    (hlo : nestLayoutK ops env H.ctx (nestContainer H.ctx) kc = .ok lo) :
    l.home = h ∧ l.key = some kc ∧ l.L = lo.L ∧ l.mems = lo.L.grp ∧ l.merged = lo.merged ∧
      l.famPs = lo.famPs ∧
      l.holeTys = H.holes.map Expr.fvarTypeD ++ lo.L.famTys ++ lo.ginfo.map (·.2.2) ∧
      ∃ ctorsG, lo.L.grp.mapM (m := CheckM)
          (fun g => unwrapOr ((nestContainer H.ctx g).map (·.2)) nestNonValid) = .ok ctorsG ∧
        l.ctors = ctorsG ∧ l.crests = splitByRK ctorsG lo.crests ∧
        (ctorsG.zip (splitByRK ctorsG lo.crests)).mapM (m := CheckM)
          (fun (cs, crs) => layNfsRK ops env H.ctx lo.L.hi cs crs) = .ok l.nfs := by
  unfold contLayRK at hr
  obtain ⟨lo', h1, hr⟩ := exceptBind_ok hr
  rw [hlo] at h1
  obtain rfl := (Except.ok.inj h1).symm
  obtain ⟨ctorsG, h2, hr⟩ := exceptBind_ok hr
  obtain ⟨nfs, h3, hr⟩ := exceptBind_ok hr
  dsimp only at hr
  split at hr
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain rfl := pureRK_ok hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ctorsG, h2, rfl, rfl, h3⟩
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain rfl := pureRK_ok hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ctorsG, h2, rfl, rfl, h3⟩

/-- **The canonical groups are consistent**: every mate of a stored container's group has
that group (at a context reading an environment whose recorded blocks list their members,
`LfpCover.all`; the model side discharges it). -/
@[expose] def GroupsOkK (ctx : NestCtx) : Prop :=
  ∀ C, ctx.names.contains C = false → C ≠ quotName → ∀ n ∈ groupOfK ctx C,
    groupOfK ctx n = groupOfK ctx C

/-- **Every container layout of the route is a node of the re-run positivity check**
(route R): the re-run's cache holds its key (`homesPosRK`), the cache invariant gives the
node's derivation at `UseOkK` (`nestBlockCtorsGoK_deriv`), and the route's layout is the
layout function's value at the node's key (`posDK_node_nf`, `nestLayoutK_congr` along the
group, `GroupsOkK`). -/
theorem NestRouteRun.contLay_node {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : NestRouteRun ops fe p cvTas ctorsAs out) {i : Nat} {l : LayRK}
    (hl : R.st.lays[i]? = some l) {kc : NestKey} (hk : l.key = some kc) {H : HomeRK}
    (hH : R.st.homes[l.home]? = some H) (hcl : CtxTysClosed H.ctx) (hG : GroupsOkK H.ctx) :
    ∃ kn lo met, PosDKH ops fe.env H.ctx (UseOkK ops fe.env H.ctx) (.node kn lo met) ∧
      nestLayoutK ops fe.env H.ctx (nestContainer H.ctx) kc = .ok lo ∧
      contLayRK ops fe.env l.home H kc = .ok l ∧
      kc.cname ∈ lo.ginfo.map (·.1) ∧ kc.lvls = kn.lvls ∧ kc.ds = kn.ds ∧
      (H.ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName) := by
  -- the route built it at its key
  obtain ⟨H', hH', hcase⟩ := R.good.2.1 i l hl
  rw [hH] at hH'
  obtain rfl := Option.some.inj hH'
  have hcont : contLayRK ops fe.env l.home H kc = .ok l := by
    rcases hcase with ⟨hn, -⟩ | ⟨kc', hk', hr⟩
    · rw [hk] at hn; exact absurd hn (by simp)
    · rw [hk] at hk'; obtain rfl := Option.some.inj hk'; exact hr
  -- the re-run's cache holds its key
  obtain ⟨ks, ns, pst, hrun, hcache⟩ := R.pos l.home H hH
  have hany := hcache l (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hl)) rfl kc hk
  obtain ⟨nd, hnd, hkey'⟩ : ∃ nd ∈ pst.cache.toList, nd.key = kc := by
    obtain ⟨j, hj, hk⟩ : ∃ (j : Nat) (h : j < pst.cache.size), (pst.cache[j]'h).key = kc := by
      simpa using hany
    exact ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem hj), hk⟩
  obtain ⟨hI, -⟩ := nestBlockCtorsGoK_deriv (hookOkK_useOkK hcl) H.ctors {} ks ns pst hrun
    derivCacheK_empty
  obtain ⟨kn, lo, hD, hgrp, hlv, hds, -, -, -, -, -, -, -, hmem⟩ := hI.2 nd hnd
  rw [hkey'] at hgrp hlv hds
  -- the layout function's value at the node's key is the route's at its key
  obtain ⟨hlay, -⟩ := posDK_node_nf hD
  have hspec := nestLayoutK_spec hlay
  have hin : kc.cname ∈ groupOfK H.ctx kn.cname := by
    rw [← hspec.2.2.1, ← hspec.2.2.2.2.1]; exact hgrp
  have hg := hG kn.cname hmem.1 hmem.2 kc.cname hin
  have hlo : nestLayoutK ops fe.env H.ctx (nestContainer H.ctx) kc = .ok lo := by
    rw [nestLayoutK_congr ops fe.env H.ctx _ hg hlv hds]; exact hlay
  exact ⟨kn, lo, nd.met, hD, hlo, hcont, hgrp, hlv, hds, hmem⟩

/-- **The positivity facts the node lemma consumes, as ONE hypothesis** (lane lead,
NESTKN-NL round 6: route R — the recursor check re-running the positivity check — is
REJECTED; per-node facts will be PERSISTED at each home's install and supplied here): every
container layout of the route's state is the layout function's value at its key, at a
node with a key-named positivity derivation at `UseOkK`, its key in the node's group at the
node's levels and parameters, the node's head no member and not `Quot`.
`NestRouteRun.nodeFacts` discharges it from today's re-run; the node lemma reads only
this. -/
@[expose] def RouteNodeFactsK (ops : CheckerOps CheckM) (env : Env) (st : RouteRK) : Prop :=
  ∀ (i : Nat) (l : LayRK), st.lays[i]? = some l → ∀ kc, l.key = some kc → ∀ H,
    st.homes[l.home]? = some H →
    ∃ kn lo met, PosDKH ops env H.ctx (UseOkK ops env H.ctx) (.node kn lo met) ∧
      nestLayoutK ops env H.ctx (nestContainer H.ctx) kc = .ok lo ∧
      kc.cname ∈ lo.ginfo.map (·.1) ∧ kc.lvls = kn.lvls ∧ kc.ds = kn.ds ∧
      (H.ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName)

/-- Today's discharge of `RouteNodeFactsK` (route R, to be replaced by the persisted
facts). -/
theorem NestRouteRun.nodeFacts {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : NestRouteRun ops fe p cvTas ctorsAs out)
    (hcl : ∀ (h : Nat) (H : HomeRK), R.st.homes[h]? = some H → CtxTysClosed H.ctx)
    (hG : ∀ (h : Nat) (H : HomeRK), R.st.homes[h]? = some H → GroupsOkK H.ctx) :
    RouteNodeFactsK ops fe.env R.st := by
  intro i l hl kc hk H hH
  obtain ⟨kn, lo, met, hD, hlo, -, hgrp, hlv, hds, hmem⟩ :=
    R.contLay_node hl hk hH (hcl _ _ hH) (hG _ _ hH)
  exact ⟨kn, lo, met, hD, hlo, hgrp, hlv, hds, hmem⟩

end Lay

/-- **The per-component parameter check, as run**: the two spines have one length, and each
pair was inferred on both sides and found defeq at `d`. -/
theorem paramsDefEqRK_ok {ops : CheckerOps CheckM} {env : Env} {d : Nat} {cn : Name} :
    ∀ {as bs : List Expr}, paramsDefEqRK ops env d cn as bs = .ok () →
      as.length = bs.length ∧ ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        (∃ ta, ops.inferType env d a = .ok ta) ∧ (∃ tb, ops.inferType env d b = .ok tb) ∧
        ops.isDefEq env d a b = .ok true
  | [], [], _ => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | [], _ :: _, h => by unfold paramsDefEqRK at h; exact absurd h throwRK_ne_ok
  | _ :: _, [], h => by unfold paramsDefEqRK at h; exact absurd h throwRK_ne_ok
  | a :: as, b :: bs, h => by
    unfold paramsDefEqRK at h
    obtain ⟨ta, hta, h⟩ := exceptBind_ok h
    obtain ⟨tb, htb, h⟩ := exceptBind_ok h
    obtain ⟨eq, heq, h⟩ := exceptBind_ok h
    split at h
    · next hbt =>
      subst hbt
      obtain ⟨hl, hall⟩ := paramsDefEqRK_ok h
      refine ⟨by simp [hl], fun i a' b' ha hb => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha hb
        exact ⟨⟨ta, hta⟩, ⟨tb, htb⟩, heq⟩
      | succ i => exact hall i a' b' (by simpa using ha) (by simpa using hb)
    · obtain ⟨_, h, _⟩ := exceptBind_ok h
      exact absurd h throwRK_ne_ok

/-- **A rule's calls, as the route recomputes them, are the rule check's** (piece (v),
`ruleCallsRK` against the rule's run `TargetRuleRun`): the same prefix and field
variables, the same field telescopes and the same `ih` entries, in order — the route
recomputes the frame with the rule check's own functions, at a family agreeing on the
frame's fields. -/
theorem ruleCallsRK_tie {mode : CheckMode} {F : Nat} {feR feT : FEnv} {p : BlockShape}
    {formerTys : List Expr} {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (Q : TargetRuleRun mode F feR feT p formerTys fam cvR rP recTy M c rhs out)
    {fam' : TargetFamily} (hfam : fam'.recNames = fam.recNames ∧ fam'.rlvls = fam.rlvls ∧
      fam'.recTys = fam.recTys ∧ fam'.mIs = fam.mIs ∧ fam'.rPs = fam.rPs)
    {cvRi : ConstantVal} (hty : cvRi.type = recTy) {fe : FEnv} (hfe : fe.env = feT.env)
    {ci : Nat} {calls : List CallRK}
    (h : ruleCallsRK (fueledOps mode F) fe p formerTys fam' cvRi rP ci M c out = .ok calls) :
    calls = Q.ihs.toList.map fun ih =>
      ⟨ci, c.1.name, Q.fvsPref, Q.fvsF, Q.fnorm.map fun t => t.piBinders.1, rP + c.2, ih⟩ := by
  unfold ruleCallsRK at h
  obtain ⟨⟨rbs, body⟩, hsb, h⟩ := exceptBind_ok h
  obtain ⟨⟨fvsPref, oP⟩, hpf, h⟩ := exceptBind_ok h
  obtain ⟨crest, hcr, h⟩ := exceptBind_ok h
  obtain ⟨⟨fvsF, cb⟩, hff, h⟩ := exceptBind_ok h
  replace hsb := unwrapOrRK_ok hsb
  replace hpf := unwrapOrRK_ok hpf
  replace hcr := unwrapOrRK_ok hcr
  replace hff := unwrapOrRK_ok hff
  rw [Q.hstrip] at hsb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsb)
  rw [hty, Q.hpref] at hpf
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpf)
  rw [Q.hcrest] at hcr
  obtain rfl := Option.some.inj hcr
  rw [Q.hfld] at hff
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hff)
  dsimp only at h
  obtain ⟨fnorm, hfn, h⟩ := exceptBind_ok h
  rw [hfe] at hfn
  have hfn' : fnorm = Q.fnorm := by
    have := Q.hfnorm
    simp only [fueledOps] at hfn this
    rw [hfn] at this
    exact Except.ok.inj this
  subst hfn'
  obtain ⟨⟨bodyO, ihs⟩, hab, h⟩ := exceptBind_ok h
  replace hab := unwrapOrRK_ok hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfam
  have hab' := Q.habs
  simp only [targetFrameOf] at hab'
  rw [h1, h2, h3, h4, h5] at hab
  rw [hab] at hab'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hab')
  exact (pureRK_ok h).symm

/-- **The `j`-th rule's calls are among a recursor's** (`recCallsRK` runs `ruleCallsRK` on
every (constructor, rule) pair in order). -/
theorem recCallsRK_at {ops : CheckerOps CheckM} {fe : FEnv} {p : BlockShape}
    {formerTys : List Expr} {fam : TargetFamily} {cvRi : ConstantVal} {rP : Nat}
    {M : TargetMajor} :
    ∀ {ci : Nat} {cs : List (ConstantVal × Nat)} {rs : List Expr} {calls : List CallRK},
    recCallsRK ops fe p formerTys fam cvRi rP M ci cs rs = .ok calls →
    ∀ {j : Nat} {cA : ConstantVal × Nat} {rhs : Expr}, cs[j]? = some cA → rs[j]? = some rhs →
      ∃ a, ruleCallsRK ops fe p formerTys fam cvRi rP (ci + j) M cA rhs = .ok a ∧
        ∀ x ∈ a, x ∈ calls
  | ci, c :: cs, r :: rs, calls, h, j, cA, rhs, hc, hr => by
    unfold recCallsRK at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain rfl := pureRK_ok h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr
      subst hc hr
      exact ⟨a, ha, fun x hx => List.mem_append_left _ hx⟩
    | succ j =>
      obtain ⟨a', ha', hsub⟩ := recCallsRK_at hb (j := j) (by simpa using hc) (by simpa using hr)
      refine ⟨a', by rw [show ci + (j + 1) = ci + 1 + j by omega]; exact ha', fun x hx =>
        List.mem_append_right _ (hsub x hx)⟩
  | _, [], _, _, _, j, _, _, hc, _ => by simp at hc
  | _, _ :: _, [], _, _, j, _, _, _, hr => by simp at hr

/-- **A class's calls, from the route's run**: the family's `mapM` gives class `c` the
calls `recCallsRK` computes at its recursor, rule and major. -/
theorem nestCalls_at {ops : CheckerOps CheckM} {fe : FEnv} {p : BlockShape}
    {formerTys : List Expr} {fam : TargetFamily} :
    ∀ {xs : List ((ConstantVal × TargetMajor × List Expr) × RecShape)}
      {calls : List (List CallRK)},
    xs.mapM (fun ((cvRi, M, rhss), rc) =>
      recCallsRK ops fe p formerTys fam cvRi rc.rP M 0 M.ctors rhss) = .ok calls →
    ∀ {c : Nat} {x : (ConstantVal × TargetMajor × List Expr) × RecShape}, xs[c]? = some x →
      recCallsRK ops fe p formerTys fam x.1.1 x.2.rP x.1.2.1 0 x.1.2.1.ctors x.1.2.2
        = .ok (calls.getD c [])
  | x0 :: xs, calls, h, c, x, hx => by
    rw [List.mapM_cons] at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain rfl := pureRK_ok h
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ha
    | succ c =>
      simp only [List.getElem?_cons_succ] at hx
      simpa using nestCalls_at hb hx
  | [], _, _, c, x, hx => by simp at hx

/-- **The read-back at a parameter variable** is the instance's parameter. -/
theorem rbInstRK_param (H : HomeRK) (I : InstRK) (lay : LayRK) (fvsF : List Expr) {i : Nat}
    (ty : Expr) (hi : i < H.ctx.nP) (hl : i < I.ds.length) :
    rbInstRK H I lay fvsF (.fvar i ty) = I.ds[i] := by
  unfold rbInstRK lvlRK
  split <;> simp [Expr.replaceFVars, Expr.instantiateLevelParams, hi, hl,
    show i < H.ctx.nP + H.ctx.names.length by omega]

/-- **The instance map at a parameter variable** is the instance's parameter. -/
theorem relocRK_param (H : HomeRK) (I : InstRK) (hs : List Expr) {i : Nat} (ty : Expr)
    (hi : i < H.ctx.nP) (hl : i < I.ds.length) :
    relocRK H I hs (.fvar i ty) = I.ds[i] := by
  unfold relocRK lvlRK
  split <;> simp [Expr.replaceFVars, Expr.instantiateLevelParams, hi, hl]

end ConLeche
