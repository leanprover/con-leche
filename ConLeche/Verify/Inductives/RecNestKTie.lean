module
public import ConLeche.Kernel.Inductives.RecNestK
import ConLeche.Verify.Inductives.LayoutKSpec
public import ConLeche.Verify.Inductives.PosDerivK
import ConLeche.Verify.Inductives.ClassNf
import ConLeche.Verify.ExceptBind
public import ConLeche.Verify.Inductives.RecNestKRun
import ConLeche.Verify.Inductives.PosNfK
public import ConLeche.Verify.Inductives.UseOkK
import ConLeche.Verify.Inductives.UseOkKRun
import ConLeche.Verify.Inductives.PosDerivKInv
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

end Lay

end ConLeche
