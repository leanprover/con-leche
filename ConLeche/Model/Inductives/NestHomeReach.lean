module

public import ConLeche.Kernel.Inductives.RecHome
import ConLeche.Verify.Inductives.RecHomeRun
import ConLeche.Verify.Inductives.ClassNf
public import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Model.Inductives.NestShallow
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.ExceptBind
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.Inductives.PosAnn
import ConLeche.Model.Inductives.PosDerivMono

public section

/-!
# The home closure is the walk's (PRIMREC / NESTHOME)

The recursor check's home closure (`homeClosure`,
`Kernel/Inductives/RecHome.lean`) recomputes, class by class, the
constructor normal forms the positivity walk records — run at the walk's
own environment, so the recomputation IS the record (`ClassNf.lean`, no
environment tie).  This module reads the closure back into the walk's
derivation:

* `ReachGood` — a reached class is a member class recomputed in the
  members' layout, or an outside class whose key is the key of a node the
  walk derived at the EMPTY stack, its group the class's container alone;
* `home_reach_good` — every class the closure reaches is good: the start
  (member classes) trivially, a round by the leaf that named the class —
  a member hole names a member class, the frame's own hole the parent's
  node, a container instance the node the walk derived at that field
  (`posD_field_node_leaf`), at the EMPTY stack because the parent is
  shallow (`posD_field_anc_nil`);
* `reach_nf` — a good class's recomputed constructors are the walk's
  derived telescopes read as `nestClassCtorNfOf` (`nestMemberCtorNf_eq`,
  `nestFrameCtorNf_eq`).
-/

namespace ConLeche.Model

open ConLeche

/-! ## Walk lemmas: a hole-carrying field with a container leaf has its node -/

/-- What a field judgment's derivation says of a hole-carrying normal
form whose leaf is constant-headed: the derivation made a node. -/
@[expose] def FieldNodeExists (ctx : NestCtx) : PosJ → List PosTree → Prop
  | .field prog dep _ _ _ nd, ts => ctx.hiAt prog.length ≤ dep →
      nd.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true →
      ∀ n us, nd.piLeaf.getAppFn = .const n us → ∃ u, u ∈ ts
  | _, _ => True

theorem posD_field_node_exists {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → FieldNodeExists ctx j ts := by
  intro j ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    unfold FieldNodeExists
    intro _ hnf
    split at hnf
    · rw [hocc] at hnf; exact nomatch hnf
    · rename_i he; exact absurd hnf he
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    unfold FieldNodeExists at ih ⊢
    intro hdep hnf n us hfn
    have hnb : nb.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true := by
      have := hnf
      simp only [Expr.nestOcc, ha, Bool.false_or] at this
      rwa [nestOcc_abstract1 (by omega)] at this
    obtain ⟨k', hk'⟩ := piLeaf_abstract1 (d := dep) nb 0
    have e1 : (Expr.forallE a (nb.abstract1 dep) bm).piLeaf = (nb.abstract1 dep 0).piLeaf := rfl
    rw [e1, hk', getAppFn_abstract1] at hfn
    have hfn' : nb.piLeaf.getAppFn = .const n us := by
      cases h' : nb.piLeaf.getAppFn with
      | fvar i ty =>
        rw [h'] at hfn; simp only [Expr.abstract1] at hfn
        split at hfn <;> exact nomatch hfn
      | const n' us' => rw [h'] at hfn; simp only [Expr.abstract1] at hfn; exact hfn
      | _ => rw [h'] at hfn; simp only [Expr.abstract1] at hfn; exact nomatch hfn
    exact ih (by omega) hnb n us hfn'
  | @hole prog dep kb e w i ty hw hocc hfn =>
    unfold FieldNodeExists
    intro _ _ n us hfn'
    have hwp : ∀ a b m, w ≠ .forallE a b m := fun a b m h => by
      subst h; simp [Expr.getAppFn] at hfn
    have hpl : w.piLeaf = w := by cases w with
      | forallE a b m => exact absurd rfl (hwp a b m)
      | _ => rfl
    rw [hpl, hfn] at hfn'; exact nomatch hfn'
  | @frameHole prog dep kb e w i ty h hw hocc hfn =>
    unfold FieldNodeExists
    intro _ _ n us hfn'
    have hwp : ∀ a b m, w ≠ .forallE a b m := fun a b m h => by
      subst h; simp [Expr.getAppFn] at hfn
    have hpl : w.piLeaf = w := by cases w with
      | forallE a b m => exact absurd rfl (hwp a b m)
      | _ => rfl
    rw [hpl, hfn] at hfn'; exact nomatch hfn'
  | contNew => unfold FieldNodeExists; intro _ _ _ _ _; exact ⟨_, List.mem_singleton_self _⟩
  | contHit => unfold FieldNodeExists; intro _ _ _ _ _; exact ⟨_, List.mem_singleton_self _⟩
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil => trivial
  | teleCons => trivial
  | synNil => trivial
  | synNew => trivial
  | synHit => trivial

end ConLeche.Model

/-! ## The walk's facts the closure reads -/

namespace ConLeche.Model

open ConLeche

/-- A listed node's nodes are listed, its kids' being. -/
theorem nodes_mem_of_kids {ns : List PosTree} (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns) :
    ∀ (n : Nat) (t : PosTree), t.height ≤ n → t ∈ ns → ∀ u ∈ t.nodes, u ∈ ns := by
  intro n
  induction n with
  | zero => intro t ht; have := PosTree.height_pos t; omega
  | succ n ih =>
    intro t ht htn u hu
    rcases PosTree.mem_nodes.mp hu with rfl | hu
    · exact htn
    · obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
      exact ih k (by have := PosTree.height_kid hk; omega) (hkids t htn k hk) u hku

/-- The nodes below listed roots are listed. -/
theorem forest_mem_of_kids {ns : List PosTree} (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    {ts : List PosTree} (hts : ∀ t ∈ ts, t ∈ ns) : ∀ u ∈ PosTree.forest ts, u ∈ ns := by
  intro u hu
  obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
  exact nodes_mem_of_kids hkids _ k (Nat.le_refl _) (hts k hk) u hku


/-! ## The table, read back into the walk -/

section Reach

variable {F : Nat} {envI : Env} {ctx : NestCtx} {holes : List Expr} {ns : List PosTree}
  {ctorsAs : List (List (ConstantVal × Nat))}

/-- **The walk's facts the table reads**: the listed nodes (their
derivations, closed under kids), the member constructors' derivations
(their nodes listed), and a listed group whose member has no group-mates
is that member alone. -/
structure HomeWalk (F : Nat) (envI : Env) (ctx : NestCtx) (holes : List Expr)
    (ns : List PosTree) (ctorsAs : List (List (ConstantVal × Nat))) : Prop where
  hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI ctx t
  hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns
  hmem : ∀ t, t < ctx.names.length → ∀ cA ∈ ctorsAs.getD t [], ∀ crest,
      instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest →
      ∃ ks nds cur ts, PosD (fueledOps .verified F) envI ctx
          (.tele [] (ctx.hiAt 0) cA.2 0 crest ks nds cur) ts ∧ ∀ u ∈ PosTree.forest ts, u ∈ ns
  hgrp : ∀ t ∈ ns, ∀ I ∈ t.grp.map (·.1), (nestFrameMates ctx I).isEmpty = true →
    t.grp.map (·.1) = [I]

/-- **An entry of the table, read in the walk**: its recomputation at its
key, and — at a member entry — the member's constructors in the members'
layout; at a container entry, its container's constructors and a
listed node derived at the EMPTY stack at exactly its key, its group
the container alone. -/
@[expose] def EntryGood (F : Nat) (envI : Env) (ctx : NestCtx) (holes : List Expr)
    (ns : List PosTree) (ctorsAs : List (List (ConstantVal × Nat))) (e : HomeEntry) : Prop :=
  homeEntryNfs (fueledOps .verified F) envI ctx holes e.ind e.lvls e.ctors e.key = .ok e.nfs ∧
  match e.key with
  | none => ∃ t, e.mem = some t ∧ t < ctx.names.length ∧ e.ctors = ctorsAs.getD t []
  | some a => e.mem = none ∧ nestContainer ctx e.ind = some (e.nPc, e.ctors) ∧
      (nestFrameMates ctx e.ind).isEmpty = true ∧ ctx.names.contains e.ind = false ∧
      ∃ u ∈ ns, u.anc = [] ∧ u.key.ds = a ∧ u.key.lvls = e.lvls ∧ u.grp.map (·.1) = [e.ind]

/-- **A good entry's recomputed constructors are the walk's**: each is
`nestClassCtorNfOf` of a constructor telescope the walk derived at the
entry's node — node `0`'s (the members' layout) or its empty-stack
node's frame — its nodes listed. -/
theorem entry_nf (W : HomeWalk F envI ctx holes ns ctorsAs) {e : HomeEntry}
    (hg : EntryGood F envI ctx holes ns ctorsAs e) {n : NestClassCtorNf} (hn : n ∈ e.nfs) :
    ∃ (prog : List NestHole) (us : List Level) (ds : List Expr) (cv : ConstantVal) (nF : Nat)
      (crest : Expr) (ks : List PosKind) (nds : List (Expr × BinderMeta)) (cur : Expr)
      (ts : List PosTree),
      (cv, nF) ∈ e.ctors ∧
      PosD (fueledOps .verified F) envI ctx (.tele prog (ctx.hiAt prog.length) nF 0 crest ks nds cur)
        ts ∧
      n = nestClassCtorNfOf ctx prog (ctx.hiAt prog.length) us ds cv nds cur ∧
      (∀ u ∈ PosTree.forest ts, u ∈ ns) ∧
      ((e.key = none ∧ prog = [] ∧
          instPisWith ctx.params (nestAbstract ctx holes cv.type) = some crest) ∨
        ∃ u ∈ ns, u.anc = [] ∧ e.key = some u.key.ds ∧ u.key.lvls = us ∧ u.key.ds = ds ∧
          prog = (grpNews us ds (ctx.hiAt 0) u.grp).reverse ∧
          instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
            (grpSub us (ctx.hiAt 0) u.grp)) = some crest) := by
  obtain ⟨hrun, hkey⟩ := hg
  cases hk : e.key with
  | none =>
    rw [hk] at hrun hkey
    obtain ⟨t, -, ht, hct⟩ := hkey
    obtain ⟨x, hx, hfx⟩ := except_mapM_mem hrun hn
    obtain ⟨cv, nF⟩ := x
    simp only [nestMemberCtorNf] at hfx
    cases hcr : instPisWith ctx.params (nestAbstract ctx holes cv.type) with
    | none => rw [hcr] at hfx; exact nomatch hfx
    | some crest =>
      obtain ⟨ks, nds, cur, ts, hd, hts⟩ := W.hmem t ht (cv, nF) (hct ▸ hx) crest hcr
      have hfx' : nestMemberCtorNf (fueledOps .verified F) envI ctx holes cv nF = .ok n := by
        simp only [nestMemberCtorNf]; exact hfx
      have heq := ConLeche.nestMemberCtorNf_eq hcr hd (fun _ => rfl) hfx'
      exact ⟨[], ctx.lps.map .param, ctx.params, cv, nF, crest, ks, nds, cur, ts, hx, hd, heq, hts,
        Or.inl ⟨rfl, rfl, hcr⟩⟩
  | some dsW =>
    rw [hk] at hrun hkey
    obtain ⟨-, hcont, hmates, -, u, hu, hanc, hds, hlv, hgrp⟩ := hkey
    obtain ⟨hfr, hcn, -, -, -, -⟩ := W.hok u hu
    rw [hanc] at hfr
    simp only [homeEntryNfs] at hrun
    obtain ⟨grp, hgrpR, hrun⟩ := exceptBind_ok hrun
    have hmates0 : nestFrameMates ctx e.ind = [] := by simpa using hmates
    obtain ⟨hne, -, ⟨L, hL⟩, hinst, -⟩ := posD_frame_inv hfr
    have hug : ∃ cty, u.grp = [(e.ind, cty)] := by
      cases hg : u.grp with
      | nil => rw [hg] at hne; exact absurd rfl hne
      | cons p ps =>
        rw [hg] at hgrp
        simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hgrp
        obtain ⟨h1, rfl⟩ := hgrp
        exact ⟨p.2, by rw [← h1]⟩
    obtain ⟨cty, hug⟩ := hug
    have hgrpEq : grp = u.grp := by
      unfold nestClassGroup at hgrpR
      obtain ⟨q, hq, hgrow⟩ := exceptBind_ok hgrpR
      rw [hmates0] at hgrow
      simp only [nestGrowGroup, pure, Except.pure, Except.ok.injEq] at hgrow
      subst hgrow
      obtain ⟨nI, hnI⟩ := hinst (e.ind, cty) (by rw [hug]; simp)
      rw [hlv, hds] at hnI
      simp only [List.length_nil] at hnI
      rw [hq] at hnI
      simp only [Except.ok.injEq] at hnI
      subst hnI
      rw [hug]
    subst hgrpEq
    obtain ⟨x, hx, hfx⟩ := except_mapM_mem hrun hn
    obtain ⟨cv, nF⟩ := x
    have hfx' := hfx
    simp only [nestFrameCtorNf] at hfx
    cases hcr : instPisWith dsW ((cv.type.instantiateLevelParams cv.levelParams
        e.lvls).replaceConsts (grpSub e.lvls (ctx.hiAt 0) u.grp)) with
    | none => rw [hcr] at hfx; exact nomatch hfx
    | some crest =>
      have hhd : (u.grp.headD default).1 = e.ind := by rw [hug]; rfl
      rw [hhd] at hL
      have hctorsL : e.ctors = L := by
        rw [hL] at hcont
        simp only [Option.some.injEq, Prod.mk.injEq] at hcont; exact hcont.2.symm
      have hgc : groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some L := by
        rw [hug]
        simp only [List.map_cons, List.map_nil, groupCtors, hL, beq_self_eq_true, Bool.true_or,
          if_true, Option.map_some, List.append_nil]
      have hxL : (cv, nF) ∈ L := hctorsL ▸ hx
      have hcr' : instPisWith u.key.ds ((cv.type.instantiateLevelParams cv.levelParams
          u.key.lvls).replaceConsts (grpSub u.key.lvls (ctx.hiAt ([] : List NestHole).length) u.grp))
          = some crest := by
        rw [hlv, hds]; exact hcr
      obtain ⟨ks, nds, cur, ts, hd, hts⟩ := posD_frame_ctor hfr hgc hxL hcr'
      simp only [List.length_nil, List.append_nil] at hd
      rw [hlv, hds] at hd
      have hd' : PosD (fueledOps .verified F) envI ctx
          (.tele ((grpNews e.lvls dsW (ctx.hiAt 0) u.grp).reverse ++ [])
            (ctx.hiAt 0 + u.grp.length) nF 0 crest ks nds cur) ts := by
        rw [List.append_nil]; exact hd
      have hlen : ctx.hiAt (grpNews e.lvls dsW (ctx.hiAt 0) u.grp).reverse.length
          = ctx.hiAt 0 + u.grp.length := by
        simp only [List.length_reverse, grpNews, List.length_map, NestCtx.hiAt]; omega
      have heq := ConLeche.nestFrameCtorNf_eq hcr hd' (fun _ => rfl) hfx'
      refine ⟨(grpNews e.lvls dsW (ctx.hiAt 0) u.grp).reverse,
        e.lvls, dsW, cv, nF, crest, ks, nds, cur, ts, hx, ?_, ?_, ?_, ?_⟩
      · rw [hlen]; exact hd
      · rw [hlen]; exact heq
      · exact fun u' hu' => forest_mem_of_kids W.hkids (fun t ht => W.hkids u hu t ht) u'
          (hts u' hu')
      · exact Or.inr ⟨u, hu, hanc, by rw [hds], hlv, hds, rfl, hcr⟩

/-- A leaf of a recomputed constructor is a hole-carrying field's leaf. -/
theorem leaves_of_nfOf {ctx : NestCtx} {prog : List NestHole} {hi : Nat} {us : List Level}
    {ds : List Expr} {cv : ConstantVal} {nds : List (Expr × BinderMeta)} {cur l : Expr}
    (hl : some l ∈ (nestClassCtorNfOf ctx prog hi us ds cv nds cur).leaves) :
    ∃ (i : Nat) (q : Expr × BinderMeta), nds[i]? = some q ∧
      q.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true ∧ q.1.piLeaf = l := by
  simp only [nestClassCtorNfOf, List.mem_map] at hl
  obtain ⟨q, hq, hql⟩ := hl
  split at hql
  · rename_i hocc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    exact ⟨i, _, List.getElem?_eq_getElem hi, hocc, Option.some.inj hql⟩
  · exact nomatch hql

/-- A shallow recomputed constructor's fields are shallow. -/
theorem shallow_of_nfOf {ctx : NestCtx} {prog : List NestHole} {hi : Nat} {us : List Level}
    {ds : List Expr} {cv : ConstantVal} {nds : List (Expr × BinderMeta)} {cur : Expr}
    (hs : (nestClassCtorNfOf ctx prog hi us ds cv nds cur).shallow = true) :
    ∀ q ∈ nds, nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) q.1 = true := by
  simp only [nestClassCtorNfOf, List.all_eq_true] at hs
  exact hs

/-- **Every entry of the table is good** (see the module docstring). -/
theorem homeTable_good (W : HomeWalk F envI ctx holes ns ctorsAs) {m : Nat} {T : List HomeEntry}
    (h : homeTableAt (fueledOps .verified F) envI ctx holes ctorsAs m = .ok T) :
    ∀ e ∈ T, EntryGood F envI ctx holes ns ctorsAs e := by
  refine homeTable_inv (fun t nfs ht hn => ⟨hn, t, rfl, ht, rfl⟩) ?_ h
  intro e hge hexp n hn l hl I us a nPc ctors hleaf nfs hrun
  refine ⟨hrun, ?_⟩
  -- the leaf's checks
  unfold homeLeafNew at hleaf
  split at hleaf
  · rename_i I' us' hfn
    split at hleaf
    · exact nomatch hleaf
    rename_i hnm
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true] at hnm
    split at hleaf
    · rename_i nPc' ctors' hcont
      dsimp only at hleaf
      split at hleaf
      · rename_i hck
        simp only [Option.some.injEq, Prod.mk.injEq] at hleaf
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hleaf
        simp only [Bool.and_eq_true, beq_iff_eq] at hck
        refine ⟨rfl, hcont, by simpa using hnm.2, hnm.1, ?_⟩
        -- the parent's constructor, as the walk derived it
        obtain ⟨prog, us0, ds0, cv, nF, crest, ks, nds, cur, ts, -, hd, rfl, hts, -⟩ :=
          entry_nf W hge hn
        obtain ⟨i, q, hq, hocc, rfl⟩ := leaves_of_nfOf hl
        obtain ⟨-, hnl, xs, hop, hall⟩ := posD_tele_open hd
        have hi : i < nF := by rw [← hnl]; exact (List.getElem?_eq_some_iff.mp hq).1
        have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length _ hop
        obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨k, nd, ts', -, hnd, hfd, hts'⟩ := hall i x hx
        rw [hq, Option.map_some] at hnd
        obtain rfl := Option.some.inj hnd
        have hdep : ctx.hiAt prog.length ≤ ctx.hiAt prog.length + 0 + i := by omega
        obtain ⟨u', hu'⟩ := posD_field_node_exists hfd hdep hocc I' us' hfn
        obtain ⟨hhead, hpar, -⟩ := posD_field_node_leaf hfd hdep u' hu'
        have hsh : nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) q.1 = true :=
          shallow_of_nfOf (List.all_eq_true.mp hexp _ hn) q (List.mem_of_getElem? hq)
        have hanc := posD_field_anc_nil hfd hdep hsh u' hu'
        have hu'ns : u' ∈ ns := hts u' (PosTree.mem_forest_iff.mpr
          ⟨u', hts' u' hu', PosTree.mem_nodes.mpr (Or.inl rfl)⟩)
        rw [hfn] at hhead
        simp only [Expr.const.injEq] at hhead
        obtain ⟨hIc, hus⟩ := hhead
        obtain ⟨hfr', hcn', -, -, -, -⟩ := W.hok u' hu'ns
        rw [← hIc] at hcn'
        have hgrp' := W.hgrp u' hu'ns I' hcn' (by simpa using hnm.2)
        obtain ⟨hne', -, ⟨L', hL'⟩, -, -⟩ := posD_frame_inv hfr'
        have hhd' : (u'.grp.headD default).1 = I' := by
          cases hg : u'.grp with
          | nil => rw [hg] at hne'; exact absurd rfl hne'
          | cons p ps =>
            rw [hg] at hgrp'
            simp only [List.map_cons, List.cons.injEq] at hgrp'
            simp only [List.headD_cons]; exact hgrp'.1
        rw [hhd', hcont] at hL'
        simp only [Option.some.injEq, Prod.mk.injEq] at hL'
        refine ⟨u', hu'ns, hanc, ?_, hus.symm, hgrp'⟩
        rw [← hpar, hL'.1]
      · exact nomatch hleaf
    · exact nomatch hleaf
  · exact nomatch hleaf

end Reach

end ConLeche.Model
