module

public import ConLeche.Model.Inductives.NestHomeReach
public import ConLeche.Model.Inductives.TargetNodeCalls
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.TargetCallTie
import ConLeche.Model.Inductives.NestShallow
import ConLeche.Model.Inductives.TargetCallEntry
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.ExceptBind
import ConLeche.Model.Inductives.PosDerivMono

public section

/-!
# The node route's calls at a home closure (PRIMREC / NESTHOME)

`nestedNodeCallsG` (`TargetNodeCalls.lean`) asks, for a layer `S` of the
family's classes and a node filter `okN`, where each class's constructor
normal forms come from (`hN0`, `hND`), what an outside callee is
(`hOut`), and at which nodes a call lands (`hokFrame`, `hokKid`).  At a
family the recursor check reads off its home closure (`homeClosure`,
`Kernel/Inductives/RecHome.lean`) instead of the walk, those are the
closure's facts (`HomeFacts`), read back into the walk by
`home_reach_good`: a class of `S` is related exactly to the empty-stack
node at its own key (`homeOkN`), its normal forms are the recomputed
ones — the record there (`reach_nf`) — and a call on a field lands where
the closure recomputed the callee (`homeConsistent`,
`homePairConsistent`).
-/

namespace ConLeche.Model

open ConLeche

/-! ## Keys up to annotations, at the empty stack -/

/-- A key parameter below the members' holes reads back at any stack as
at the empty one. -/
theorem nestHoleConst_below_hiAt0 {ctx : NestCtx} (occ : List NestHole) {v : Nat}
    (hv : v < ctx.hiAt 0) : nestHoleConst ctx occ v = nestHoleConst ctx [] v := by
  unfold nestHoleConst
  by_cases h0 : ctx.nP ≤ v ∧ v < ctx.hiAt 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    rw [if_neg (by intro h; simp [NestCtx.hiAt] at h hv; omega),
      if_neg (by intro h; simp [NestCtx.hiAt] at h; omega)]

/-- Erasure-equal lists, from their erasures. -/
theorem erasedEqL_of_eraseMap : ∀ {as bs : List Expr},
    as.map homeErase = bs.map homeErase → Expr.ErasedEqL as bs
  | [], [], _ => trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨ConLeche.Expr.eraseFVarTys_eq_iff.mp h.1, erasedEqL_of_eraseMap h.2⟩

/-- **The syntactic class → node relation, at an empty-stack key, is the
closure's erased comparison.** -/
theorem erasedEqL_nodeRb_iff {ctx : NestCtx} {occ : List NestHole} {ds ks : List Expr}
    (hks : ∀ x ∈ ks, x.fvarsBelow (ctx.hiAt 0)) :
    Expr.ErasedEqL ds (ks.map (nodeRb ctx occ)) ↔ ds.map homeErase = ks.map (homeRb ctx) := by
  have hrb : ks.map (nodeRb ctx occ) = ks.map (·.replaceFVars (nestHoleConst ctx [])) := by
    refine List.map_congr_left fun x hx => ?_
    have hb := hks x hx
    have hbo : x.fvarsBelow (ctx.hiAt occ.length) :=
      Expr.fvarsBelow_mono (by simp [NestCtx.hiAt]) hb
    rw [← concrete_eq_nodeRb ctx occ hbo]
    exact replaceFVars_congr_below (fun v hv => nestHoleConst_below_hiAt0 occ hv) x hb
  have hrb2 : ks.map (homeRb ctx) = (ks.map (·.replaceFVars (nestHoleConst ctx []))).map homeErase := by
    simp only [List.map_map]; rfl
  rw [hrb, hrb2]
  constructor
  · intro h
    exact erasedEqL_eraseMap h
  · exact erasedEqL_of_eraseMap

/-- An empty-stack node's key lies below the members' holes. -/
theorem posNodeOk_ds_below0 {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {u : PosTree}
    (hok : PosNodeOk ops env ctx u) (hanc : u.anc = []) :
    ∀ x ∈ u.key.ds, x.fvarsBelow (ctx.hiAt 0) := by
  obtain ⟨-, -, -, -, hws, hcase⟩ := hok
  intro x hx
  rcases hcase with ⟨hao, -⟩ | ⟨-, hds⟩
  · have := (hws x hx).1
    rw [← hao, hanc] at this
    exact Expr.WScoped.fvarsBelow this
  · exact Expr.fvarB_le (hds x hx).1

/-! ## The closure's facts, and the node filter they give -/

section Home

variable {F : Nat} {envI : Env} {ctx : NestCtx} {holes : List Expr} {ns : List PosTree}
  {Cs : List HomeClass} {R : List (Option HomeReach)}
  {out : List (ConstantVal × TargetMajor × List Expr)} {S : Nat → Prop}

/-- **What the recursor check's home closure establishes** for the layer
`S` (the run of `homeClosure` at the walk's environment, and the checks
the switch reads): the classes are the family's majors, every class of
`S` is reached, reachable and expanded, the closure is consistent at `S`
(a leaf naming a class of `S` gives its key; one key per container
instance), and a class of `S` carries the recomputed entries. -/
structure HomeFacts (F : Nat) (envI : Env) (ctx : NestCtx) (holes : List Expr)
    (ns : List PosTree) (Cs : List HomeClass) (R : List (Option HomeReach))
    (out : List (ConstantVal × TargetMajor × List Expr)) (S : Nat → Prop) : Prop where
  W : HomeWalk F envI ctx holes ns Cs
  hholes : nestHoles ctx = some holes
  hparams : ∀ x ∈ ctx.params, ∃ i ty, x = .fvar i ty ∧ i < ctx.nP
  hclos : homeClosure (fueledOps .verified F) envI ctx holes Cs = .ok R
  hlen : Cs.length = (tgtRs out).length
  hind : ∀ c, c < (tgtRs out).length → (Cs.getD c default).ind = (tgtMajor out c).ind
  hlvls : ∀ c, c < (tgtRs out).length → (Cs.getD c default).lvls = (tgtMajor out c).lvls
  hds : ∀ c, c < (tgtRs out).length → (Cs.getD c default).ds = (tgtMajor out c).ds
  hmember : ∀ c, c < (tgtRs out).length → (Cs.getD c default).member = (tgtMajor out c).member
  hctorsM : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member.isSome = true →
    (Cs.getD c default).ctors = (tgtMajor out c).ctors
  hS : ∀ c, S c → c < (tgtRs out).length ∧ homeReachable ctx (Cs.getD c default) = true ∧
    ∃ r, R.getD c none = some r ∧ r.expands = true
  hcons : ∀ a r, R.getD a none = some r → r.expands = true → ∀ e ∈ r.nfs, ∀ l, some l ∈ e.leaves →
    ∀ c, S c → ∀ k, homeLeafKey ctx (Cs.getD a default) r.key (Cs.getD c default) l = some k →
      ∃ rc, R.getD c none = some rc ∧ rc.key = k
  hpair : ∀ a c, S a → S c → (Cs.getD a default).member = none →
    (Cs.getD a default).ind = (Cs.getD c default).ind →
    (Cs.getD a default).lvls = (Cs.getD c default).lvls →
    (Cs.getD a default).ds.map homeErase = (Cs.getD c default).ds.map homeErase →
    ∀ ra rc, R.getD a none = some ra → R.getD c none = some rc → ra.key = rc.key
  hnfs : ∀ c, S c → ∀ r, R.getD c none = some r →
    (tgtMajor out c).nfs = some (r.nfs.map (·.entry))

/-- **The node filter of a home closure**: a class is related to the
empty-stack node at exactly the key the closure recomputed it at. -/
@[expose] def homeOkN (R : List (Option HomeReach)) (c : Nat) (u : PosTree) : Prop :=
  u.anc = [] ∧ ∃ r, R.getD c none = some r ∧ r.key = some u.key.ds

variable (H : HomeFacts F envI ctx holes ns Cs R out S)
include H

omit H in
theorem home_hMode : (∀ c u, homeOkN R c u) ∨ ∀ c u, u ∈ ns → homeOkN R c u → u.anc = [] :=
  Or.inr fun _ _ _ h => h.1

/-- **An outside class of the layer names a member and is none.** -/
theorem home_hOut {names : List Name} (hnames : ctx.names = names) :
    ∀ c', c' < (tgtRs out).length → S c' → (tgtMajor out c').member = none →
      (tgtMajor out c').ind ∉ names ∧
      ∃ x ∈ (tgtMajor out c').ds, x.nestOcc names 0 0 = true := by
  intro c' hc' hS hMo
  obtain ⟨-, hreach, -⟩ := H.hS c' hS
  unfold homeReachable at hreach
  rw [H.hmember c' hc', hMo, H.hind c' hc', H.hds c' hc', hnames] at hreach
  simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true, List.any_eq_true] at hreach
  obtain ⟨⟨-, hnm⟩, x, hx, hocc⟩ := hreach
  refine ⟨fun h => ?_, x, hx, hocc⟩
  have : names.contains (tgtMajor out c').ind = true := List.contains_iff_mem.mpr h
  rw [this] at hnm
  exact nomatch hnm

/-- **A class of the frame's own group lands at the frame's node.** -/
theorem home_hokFrame :
    ∀ c c' u, c < (tgtRs out).length → S c → c' < (tgtRs out).length → S c' →
      u ∈ ns → homeOkN R c u → NodeMajor ctx (tgtMajor out c) u →
      NodeMajor ctx (tgtMajor out c') u → homeOkN R c' u := by
  intro c c' u hc hSc hc' hSc' hu hok hNM hNM'
  obtain ⟨hanc, r, hr, hkey⟩ := hok
  obtain ⟨-, hreachc, -⟩ := H.hS c hSc
  obtain ⟨-, -, rc', hrc', -⟩ := H.hS c' hSc'
  have hmo := hNM.1
  have hmates : (nestFrameMates ctx (tgtMajor out c).ind).isEmpty = true := by
    unfold homeReachable at hreachc
    rw [H.hmember c hc, hmo, H.hind c hc] at hreachc
    simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hreachc
    exact hreachc.1.1
  have hg := H.W.hgrp u hu _ hNM.2.1 hmates
  have hind' : (tgtMajor out c').ind = (tgtMajor out c).ind := by
    have := hNM'.2.1; rw [hg] at this; simpa using this
  have hbelow := posNodeOk_ds_below0 (H.W.hok u hu) hanc
  have he1 := (erasedEqL_nodeRb_iff hbelow).mp hNM.2.2.2
  have he2 := (erasedEqL_nodeRb_iff hbelow).mp hNM'.2.2.2
  have hk := H.hpair c c' hSc hSc' (by rw [H.hmember c hc, hmo])
    (by rw [H.hind c hc, H.hind c' hc', hind'])
    (by rw [H.hlvls c hc, H.hlvls c' hc', hNM.2.2.1, hNM'.2.2.1])
    (by rw [H.hds c hc, H.hds c' hc', he1, he2]) r rc' hr hrc'
  exact ⟨hanc, rc', hrc', by rw [← hk, hkey]⟩

/-- A class of the layer is good, at the key the closure reached it at. -/
theorem home_good {c : Nat} (hSc : S c) :
    ∃ r, R.getD c none = some r ∧ r.expands = true ∧ ReachGood F envI ctx holes ns Cs c r := by
  obtain ⟨-, -, r, hr, hexp⟩ := H.hS c hSc
  exact ⟨r, hr, hexp, home_reach_good H.W H.hclos c r hr⟩

/-- The walk's parameters read back as themselves. -/
theorem home_params_rb : ctx.params.map (·.replaceFVars (nestHoleConst ctx [])) = ctx.params := by
  conv => rhs; rw [← List.map_id ctx.params]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨i, ty, rfl, hi⟩ := H.hparams x hx
  simp only [Expr.replaceFVars, nestHoleConst_lt_nP hi, Option.getD_none, id]

omit H in
/-- An input of a successful `mapM` has its output among the outputs. -/
theorem except_mapM_of_mem {α β ε : Type} {f : α → Except ε β} {l : List α} {r : List β}
    (h : l.mapM f = .ok r) {a : α} (ha : a ∈ l) : ∃ b ∈ r, f a = .ok b := by
  obtain ⟨hlen, hall⟩ := except_mapM_ok h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨b, hb, hf⟩ := hall i l[i] (List.getElem?_eq_getElem hi)
  exact ⟨b, List.mem_of_getElem? hb, hf⟩

/-- **The members' normal forms, recomputed, are node `0`'s** (`hN0`). -/
theorem home_hN0 :
    ∀ c, c < (tgtRs out).length → S c → (tgtMajor out c).member.isSome = true →
      ∀ cA ∈ (tgtMajor out c).ctors, ∀ holes' crest ks nds cur ts,
      nestHoles ctx = some holes' →
      instPisWith ctx.params (nestAbstract ctx holes' cA.1.type) = some crest →
      PosD (fueledOps .verified F) envI ctx (.tele [] (ctx.hiAt 0) cA.2 0 crest ks nds cur) ts →
      ∃ L, (tgtMajor out c).nfs = some L ∧
        (⟨cA.1.name, ctx.lps.map .param, ctx.params, (closeTelescope nds (ctx.hiAt 0)
          cur).replaceFVars (nestHoleConst ctx [])⟩ : NestCtorNf) ∈ L := by
  intro c hc hSc hmem cA hcA holes' crest ks nds cur ts hholes' hcrest hd
  rw [H.hholes] at hholes'
  obtain rfl := Option.some.inj hholes'
  obtain ⟨r, hr, -, hg⟩ := home_good H hSc
  obtain ⟨-, hrun, hkey⟩ := hg
  have hk : r.key = none := by
    cases hk : r.key with
    | none => rfl
    | some _ =>
      rw [hk] at hkey
      have := hkey.1
      rw [H.hmember c hc] at this
      rw [this] at hmem; exact nomatch hmem
  rw [hk] at hrun
  simp only [homeClassNfs] at hrun
  rw [H.hctorsM c hc hmem] at hrun
  obtain ⟨e, he, hfe⟩ := except_mapM_of_mem hrun hcA
  have heq := ConLeche.nestMemberCtorNf_eq hcrest hd (fun _ => rfl) hfe
  refine ⟨_, H.hnfs c hSc r hr, List.mem_map.mpr ⟨e, he, ?_⟩⟩
  rw [heq]
  simp only [nestClassCtorNfOf, nestCtorNf, home_params_rb H]

/-- **A frame's constructor, recomputed, is among its class's reached
constructors**: at a class of the layer related to its empty-stack node,
the telescope the walk derived for a constructor of the node's group. -/
theorem home_frame_mem {c : Nat} {u : PosTree} (hc : c < (tgtRs out).length)
    (hu : u ∈ ns) (hNM : NodeMajor ctx (tgtMajor out c) u) (hok : homeOkN R c u)
    {ctors : List (ConstantVal × Nat)} {x : ConstantVal × Nat} {crest cur : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts' : List PosTree}
    (hgc : groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some ctors) (hx : x ∈ ctors)
    (hcr : instPisWith u.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams
        u.key.lvls).replaceConsts (grpSub u.key.lvls (ctx.hiAt u.anc.length) u.grp)) = some crest)
    (hd : PosD (fueledOps .verified F) envI ctx
        (.tele ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc)
          (ctx.hiAt u.anc.length + u.grp.length) x.2 0 crest ks nds cur) ts') :
    ∃ r, R.getD c none = some r ∧
      nestClassCtorNfOf ctx ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++
        u.anc) (ctx.hiAt u.anc.length + u.grp.length) u.key.lvls u.key.ds x.1 nds cur ∈ r.nfs := by
  obtain ⟨hanc, r, hr, hkey⟩ := hok
  obtain ⟨-, hrun, hgood⟩ := home_reach_good H.W H.hclos c r hr
  rw [hkey] at hrun hgood
  obtain ⟨hmo, hmates, -, -⟩ := hgood
  simp only [homeClassNfs] at hrun
  obtain ⟨grp, hgrpR, hrun⟩ := exceptBind_ok hrun
  have hmates0 : nestFrameMates ctx (Cs.getD c default).ind = [] := by simpa using hmates
  obtain ⟨hfr, -, -, -, -, -⟩ := H.W.hok u hu
  rw [hanc] at hfr hcr hd
  obtain ⟨hne, -, ⟨L, hL⟩, hinst, -⟩ := posD_frame_inv hfr
  have hindc : (Cs.getD c default).ind = (tgtMajor out c).ind := H.hind c hc
  have hgnames := H.W.hgrp u hu _ hNM.2.1 (by rw [← hindc]; exact hmates)
  obtain ⟨cty, hug⟩ : ∃ cty, u.grp = [((tgtMajor out c).ind, cty)] := by
    cases hg : u.grp with
    | nil => rw [hg] at hne; exact absurd rfl hne
    | cons p ps =>
      rw [hg] at hgnames
      simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hgnames
      obtain ⟨h1, rfl⟩ := hgnames
      exact ⟨p.2, by rw [← h1]⟩
  have hlvC : (Cs.getD c default).lvls = u.key.lvls := by rw [H.hlvls c hc, hNM.2.2.1]
  have hgrpEq : grp = u.grp := by
    unfold nestClassGroup at hgrpR
    obtain ⟨q, hq, hgrow⟩ := exceptBind_ok hgrpR
    rw [hmates0] at hgrow
    simp only [nestGrowGroup, pure, Except.pure, Except.ok.injEq] at hgrow
    subst hgrow
    obtain ⟨nI, hnI⟩ := hinst ((tgtMajor out c).ind, cty) (by rw [hug]; simp)
    rw [← hindc, ← hlvC] at hnI
    simp only [List.length_nil] at hnI
    rw [hq] at hnI
    simp only [Except.ok.injEq] at hnI
    subst hnI
    rw [hug, hindc]
  subst hgrpEq
  have hhd : (u.grp.headD default).1 = (tgtMajor out c).ind := by rw [hug]; rfl
  rw [hhd, ← hindc, H.W.hcont c (H.hlen ▸ hc) (by rw [H.hmember c hc]; exact hNM.1)] at hL
  simp only [Option.some.injEq, Prod.mk.injEq] at hL
  have hgc' : groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some (Cs.getD c default).ctors := by
    rw [hug]
    simp only [List.map_cons, List.map_nil, groupCtors, ← hindc,
      H.W.hcont c (H.hlen ▸ hc) (by rw [H.hmember c hc]; exact hNM.1), hL.1, beq_self_eq_true,
      Bool.true_or, if_true, Option.map_some, List.append_nil]
  rw [hgc'] at hgc
  obtain rfl := Option.some.inj hgc
  obtain ⟨e, he, hfe⟩ := except_mapM_of_mem hrun hx
  have hcr' : instPisWith u.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams
      (Cs.getD c default).lvls).replaceConsts (grpSub (Cs.getD c default).lvls (ctx.hiAt 0) u.grp))
      = some crest := by rw [hlvC]; simpa using hcr
  have hd' : PosD (fueledOps .verified F) envI ctx
      (.tele ((grpNews (Cs.getD c default).lvls u.key.ds (ctx.hiAt 0) u.grp).reverse ++ [])
        (ctx.hiAt 0 + u.grp.length) x.2 0 crest ks nds cur) ts' := by
    rw [hlvC]; simpa using hd
  have heq := ConLeche.nestFrameCtorNf_eq hcr' hd' (fun _ => rfl) hfe
  refine ⟨r, hr, ?_⟩
  rw [heq, hlvC] at he
  rw [hanc]
  simpa using he

/-- **A frame's normal forms, recomputed, are its record** (`hND`). -/
theorem home_hND :
    ∀ c u, c < (tgtRs out).length → S c → u ∈ ns → NodeMajor ctx (tgtMajor out c) u →
      homeOkN R c u →
      ∀ ctors (x : ConstantVal × Nat) crest ks nds cur ts',
      groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some ctors → x ∈ ctors →
      instPisWith u.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams
        u.key.lvls).replaceConsts (grpSub u.key.lvls (ctx.hiAt u.anc.length) u.grp)) = some crest →
      PosD (fueledOps .verified F) envI ctx
        (.tele ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc)
          (ctx.hiAt u.anc.length + u.grp.length) x.2 0 crest ks nds cur) ts' →
      ∃ L, (tgtMajor out c).nfs = some L ∧
        nestCtorNf ctx ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc)
          (ctx.hiAt u.anc.length + u.grp.length) u.key.lvls u.key.ds x.1 nds cur ∈ L := by
  intro c u hc hSc hu hNM hok ctors x crest ks nds cur ts' hgc hx hcr hd
  obtain ⟨r, hr, he⟩ := home_frame_mem H hc hu hNM hok hgc hx hcr hd
  exact ⟨_, H.hnfs c hSc r hr, List.mem_map.mpr ⟨_, he, nestClassCtorNfOf_entry _ _ _ _ _ _ _⟩⟩

/-- **The class's recomputed constructor at a walked telescope of its
node**: at a class of the layer, related to node `0` (a member class) or
to its empty-stack node, the telescope the walk derived there for the
constructor `j` (`NodeCrest`) is among the class's recomputed
constructors, read as `nestClassCtorNfOf`. -/
theorem home_nf_at {c j b nF : Nat} {prog : List NestHole} {crest cur : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts : List PosTree}
    (hc : c < (tgtRs out).length) (hSc : S c)
    (hrel : (b = 0 ∧ (tgtMajor out c).member.isSome = true) ∨
      (0 < b ∧ b ≤ ns.length ∧ NodeMajor ctx (tgtMajor out c) (ns.getD (b - 1) default) ∧
        homeOkN R c (ns.getD (b - 1) default)))
    (hcrId : NodeCrest ctx ctx.params ns (tgtMajor out c) j b prog nF crest)
    (hd : PosD (fueledOps .verified F) envI ctx
      (.tele prog (ctx.hiAt prog.length) nF 0 crest ks nds cur) ts) :
    ∃ r, R.getD c none = some r ∧ r.expands = true ∧ ∃ us ds cv hi,
      nestClassCtorNfOf ctx prog hi us ds cv nds cur ∈ r.nfs := by
  obtain ⟨r, hr, hexp, hg⟩ := home_good H hSc
  refine ⟨r, hr, hexp, ?_⟩
  obtain ⟨-, hrun, hgood⟩ := hg
  rcases hcrId with ⟨hb0, hprog, cA, holes', hcA, hholes', hcrest, hnF⟩ |
    ⟨u, x, ctors, hb0, hub, hprog, hgc, hx, -, hcr, hnF⟩
  · -- node `0`
    have hmem : (tgtMajor out c).member.isSome = true := by
      rcases hrel with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    subst hprog hnF
    rw [H.hholes] at hholes'
    obtain rfl := Option.some.inj hholes'
    have hk : r.key = none := by
      cases hk : r.key with
      | none => rfl
      | some _ =>
        rw [hk] at hgood
        have := hgood.1
        rw [H.hmember c hc] at this
        rw [this] at hmem; exact nomatch hmem
    rw [hk] at hrun
    simp only [homeClassNfs] at hrun
    rw [H.hctorsM c hc hmem] at hrun
    obtain ⟨e, he, hfe⟩ := except_mapM_of_mem hrun (List.mem_of_getElem? hcA)
    have heq := ConLeche.nestMemberCtorNf_eq hcrest hd (fun _ => rfl) hfe
    exact ⟨_, _, _, _, heq ▸ he⟩
  · -- a derived node, related at exactly its key
    obtain ⟨hbl, hNM, hok⟩ : b ≤ ns.length ∧ NodeMajor ctx (tgtMajor out c) u ∧ homeOkN R c u := by
      rcases hrel with ⟨h, -⟩ | ⟨-, hbl, hNM, h⟩
      · omega
      · rw [hub] at hNM h; exact ⟨hbl, hNM, h⟩
    have hu : u ∈ ns := by
      rw [← hub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _
    subst hprog hnF
    have hhi : ctx.hiAt ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++
        u.anc).length = ctx.hiAt u.anc.length + u.grp.length := by
      simp only [NestCtx.hiAt, List.length_append, List.length_reverse, grpNews, List.length_map]
      omega
    rw [hhi] at hd
    obtain ⟨r', hr', he⟩ := home_frame_mem H hc hu hNM hok hgc hx hcr hd
    rw [hr] at hr'
    obtain rfl := Option.some.inj hr'
    exact ⟨_, _, _, _, he⟩

/-- **A call on a field lands at its node's key** (`hokKid`): at a class
of the layer related to its node, a container node of a walked field
related to a class of the layer is related at the key the closure
recomputed that class at — the field is shallow (the class is
expanded), so the node is derived at the empty stack, its key is the
field's leaf's parameters, and the closure is consistent there. -/
theorem home_hokKid :
    ∀ c j b prog nF crest ks nds cur ts, c < (tgtRs out).length → S c →
      ((b = 0 ∧ (tgtMajor out c).member.isSome = true) ∨
        (0 < b ∧ b ≤ ns.length ∧ NodeMajor ctx (tgtMajor out c) (ns.getD (b - 1) default) ∧
          homeOkN R c (ns.getD (b - 1) default))) →
      NodeCrest ctx ctx.params ns (tgtMajor out c) j b prog nF crest →
      PosD (fueledOps .verified F) envI ctx
        (.tele prog (ctx.hiAt prog.length) nF 0 crest ks nds cur) ts →
      ∀ i nd, nds[i]?.map (·.1) = some nd → ∀ e k tsi,
      PosD (fueledOps .verified F) envI ctx (.field prog (ctx.hiAt prog.length + i) 0 e k nd) tsi →
      ∀ u'' ∈ tsi, u''.occ = prog → u'' ∈ ns → ∀ c', c' < (tgtRs out).length → S c' →
        NodeMajor ctx (tgtMajor out c') u'' → homeOkN R c' u'' := by
  intro c j b prog nF crest ks nds cur ts hc hSc hrel hcrId hd i nd hnd e k tsi hfd u'' hu''m
    _ hu''ns c' hc' hSc' hNM'
  obtain ⟨r, hr, hexp, us, ds, cv, hi, he⟩ := home_nf_at H hc hSc hrel hcrId hd
  obtain ⟨q, hq, rfl⟩ : ∃ q, nds[i]? = some q ∧ q.1 = nd := by
    cases h : nds[i]? with
    | none => rw [h] at hnd; exact nomatch hnd
    | some q => rw [h, Option.map_some] at hnd; exact ⟨q, rfl, Option.some.inj hnd⟩
  have hdep : ctx.hiAt prog.length ≤ ctx.hiAt prog.length + i := by omega
  have hsh : nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) q.1 = true :=
    shallow_of_nfOf (List.all_eq_true.mp hexp _ he) q (List.mem_of_getElem? hq)
  have hanc := posD_field_anc_nil hfd hdep hsh u'' hu''m
  obtain ⟨hhead, hpar, -, hoccN⟩ := posD_field_node_leaf hfd hdep u'' hu''m
  have hleaf : some q.1.piLeaf ∈ (nestClassCtorNfOf ctx prog hi us ds cv nds cur).leaves := by
    simp only [nestClassCtorNfOf, List.mem_map]
    exact ⟨q, List.mem_of_getElem? hq, by rw [if_pos hoccN]⟩
  -- the callee's class: an outside class of one container alone
  have hMo' := hNM'.1
  obtain ⟨-, hreach', -⟩ := H.hS c' hSc'
  have hmates' : (nestFrameMates ctx (tgtMajor out c').ind).isEmpty = true := by
    unfold homeReachable at hreach'
    rw [H.hmember c' hc', hMo', H.hind c' hc'] at hreach'
    simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hreach'
    exact hreach'.1.1
  have hok'' := H.W.hok u'' hu''ns
  have hg'' := H.W.hgrp u'' hu''ns _ hNM'.2.1 hmates'
  have hcn : u''.key.cname = (tgtMajor out c').ind := by
    have := hok''.2.1; rw [hg''] at this; simpa using this
  obtain ⟨hfr'', -, -, -, -, -⟩ := hok''
  obtain ⟨hne'', -, ⟨L'', hL''⟩, -, -⟩ := posD_frame_inv hfr''
  have hhd'' : (u''.grp.headD default).1 = (tgtMajor out c').ind := by
    cases hg : u''.grp with
    | nil => rw [hg] at hne''; exact absurd rfl hne''
    | cons p ps =>
      rw [hg] at hg''
      simp only [List.map_cons, List.cons.injEq] at hg''
      simp only [List.headD_cons]; exact hg''.1
  have hmo'' : (Cs.getD c' default).member = none := by rw [H.hmember c' hc', hMo']
  rw [hhd'', ← H.hind c' hc', H.W.hcont c' (H.hlen ▸ hc') hmo''] at hL''
  simp only [Option.some.injEq, Prod.mk.injEq] at hL''
  have hbelow := posNodeOk_ds_below0 (H.W.hok u'' hu''ns) hanc
  have hkey : homeLeafKey ctx (Cs.getD c default) r.key (Cs.getD c' default) q.1.piLeaf =
      some (some u''.key.ds) := by
    have hnPc : (Cs.getD c' default).nPc = u''.key.ds.length := by rw [hL''.1]
    have ha : q.1.piLeaf.getAppArgs.take (Cs.getD c' default).nPc = u''.key.ds := by
      rw [hnPc, hpar]
    have hbv : ∀ x ∈ u''.key.ds, x.bvarB = 0 := fun x hx => ((H.W.hok u'' hu''ns).2.2.2.2.1 x hx).2
    unfold homeLeafKey
    rw [hhead]
    simp only
    rw [ha, if_pos]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hmo'']; rfl
    · rw [H.hind c' hc', hcn]; exact beq_self_eq_true _
    · rw [H.hlvls c' hc', hNM'.2.2.1]; exact beq_self_eq_true _
    · rw [hnPc]; exact beq_self_eq_true _
    · refine List.all_eq_true.mpr fun x hx => ?_
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨hbv x hx, by rw [Expr.fvarB_eq]; exact Expr.fvarsBelow_iff.mp (hbelow x hx)⟩
    · rw [H.hds c' hc', (erasedEqL_nodeRb_iff hbelow).mp hNM'.2.2.2]; exact beq_self_eq_true _
  obtain ⟨rc, hrc, hrck⟩ := H.hcons c r hr hexp _ he _ hleaf c' hSc' _ hkey
  exact ⟨hanc, rc, hrc, hrck⟩

end Home

end ConLeche.Model
