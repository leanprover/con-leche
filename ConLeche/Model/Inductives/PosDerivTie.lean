module

public import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Model.Inductives.BlockCover
public import ConLeche.Model.Inductives.TargetNodeRb
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Model.Inductives.TargetClass
import ConLeche.Cached.EnvBound
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.HoleBack
import ConLeche.Verify.Inductives.ReplaceApps
public import ConLeche.Model.Inductives.TargetRuleData

public section

/-!
# Every recursor class is a node — by construction

The recursor check resolves every recursor's major first (stage (b),
`targetMajorOf`) and SEEDS the positivity walk with every outside class it
resolved (`checkBlockSeeds`: `nestSeedOf`, each walked at the root like a
container instance), on top of every container's whole recorded block
(N2-eager frames).  So every class of the recursor family is a node:

* a MEMBER class is the block's own (the member arm);
* an OUTSIDE class `I.{us} Ds` has its seed's derivation (`PosD.seed`), whose
  root node is the seed: its key is the class moved to the walk's
  representation (members abstracted to their holes, the recursor's
  parameter binders to the canonical variables), which READ BACK
  (`nodeRb`) is the class up to the free variables' annotations
  (`seed_readback`), so the class matches it per component
  (`targetClassMatch_self`, `NodeMajor`).

There is no tie to check: `outsideClass_reachedNode` derives it from the
seeding.  The seeds' container facts come from stage (b)'s reading at the
constructors' environment, which reads outside inductives as the formers'
environment does (`nestContainer_consBlockCtors`: the block's constructors
conclude in its members).
-/

namespace ConLeche.Model

open ConLeche

/-! ## Reached nodes -/

theorem PosTree.mem_forest_iff {u : PosTree} :
    ∀ {ts : List PosTree}, u ∈ PosTree.forest ts ↔ ∃ k ∈ ts, u ∈ k.nodes
  | [] => by simp [PosTree.forest]
  | t :: ts => by
    rw [PosTree.mem_forest_cons, PosTree.mem_forest_iff]
    simp

/-- Every node below a reached node is reached. -/
theorem PosTree.Reached.nodes {ts : List PosTree} :
    ∀ (n : Nat) (t : PosTree), t.height ≤ n → PosTree.Reached ts t →
      ∀ u ∈ t.nodes, PosTree.Reached ts u
  | 0, t, hh, _, _, _ => by
    cases t with
    | node occ anc key grp kids => simp [PosTree.height] at hh
  | n + 1, t, hh, hr, u, hu => by
    rcases PosTree.mem_nodes.mp hu with rfl | hu
    · exact hr
    · obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
      have := PosTree.height_kid hk
      exact PosTree.Reached.nodes n k (by omega) (.kid hr hk) u hku

/-- **Every node of a forest is reached** from its roots. -/
theorem PosTree.Reached.of_forest {ts : List PosTree} {u : PosTree}
    (hu : u ∈ PosTree.forest ts) : PosTree.Reached ts u := by
  obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
  exact PosTree.Reached.nodes k.height k (Nat.le_refl _) (.root hk) u hku

/-! ## The seeds, read back -/

/-- Spines of erasure-equal heads and arguments are erasure-equal. -/
theorem erasedEq_mkAppN_congr :
    ∀ {as bs : List Expr} {f g : Expr}, ConLeche.Expr.ErasedEq f g → as.length = bs.length →
      (∀ q (h₁ : q < as.length) (h₂ : q < bs.length), ConLeche.Expr.ErasedEq as[q] bs[q]) →
      ConLeche.Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN g bs)
  | [], [], _, _, hfg, _, _ => hfg
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | a :: as, b :: bs, f, g, hfg, hl, h =>
    erasedEq_mkAppN_congr (f := .app f a) (g := .app g b)
      ⟨hfg, h 0 (by simp) (by simp)⟩ (by simpa using hl)
      fun q h₁ h₂ => h (q + 1) (by simpa using h₁) (by simpa using h₂)

/-- **A seed's parameter read back**: members' whole applications to their
holes, the parameter variables to the walk's, then the holes back to their
applications gives the parameter again up to the free variables'
annotations — generically, for an abstraction `f` hitting whole
applications, a variable renaming `g` below `nP` and a read-back `h`. -/
theorem seed_readback_gen {nP k : Nat} {f : Name → List Level → Option Expr}
    {g h : Nat → Option Expr}
    (hhit : ∀ e r, e.appHole? f 0 nP = some r → ∃ j ty ty' R, r = .fvar (nP + j) ty ∧ j < k ∧
      g (nP + j) = some (.fvar (nP + j) ty') ∧ h (nP + j) = some R ∧ ConLeche.Expr.ErasedEq e R)
    (hg : ∀ i, i < nP → ∃ ty, g i = some (.fvar i ty))
    (hh : ∀ i, i < nP → h i = none) :
    ∀ x : Expr, x.fvarsBelow nP →
      ((x.replaceApps f 0 nP).replaceFVars g).fvarsBelow (nP + k) ∧
      ConLeche.Expr.ErasedEq x (((x.replaceApps f 0 nP).replaceFVars g).replaceFVars h) := by
  have hnode : ∀ e r, e.appHole? f 0 nP = some r →
      (r.replaceFVars g).fvarsBelow (nP + k) ∧
      ConLeche.Expr.ErasedEq e ((r.replaceFVars g).replaceFVars h) := by
    intro e r hr
    obtain ⟨j, ty, ty', R, rfl, hj, hgj, hhj, hE⟩ := hhit e r hr
    simp only [Expr.replaceFVars, hgj, Option.getD_some, hhj, Expr.fvarsBelow]
    exact ⟨by omega, hE⟩
  intro x
  induction x with
  | bvar i => intro _; exact ⟨trivial, rfl⟩
  | sort u => intro _; exact ⟨trivial, rfl⟩
  | lit l => intro _; exact ⟨trivial, rfl⟩
  | fvar i ty _ =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨tyP, hgi⟩ := hg i hb
    simp only [Expr.replaceApps, Expr.replaceFVars, hgi, Option.getD_some, hh i hb,
      Option.getD_none, Expr.fvarsBelow]
    exact ⟨by omega, rfl⟩
  | const c us =>
    intro _
    rw [Expr.replaceApps_const]
    split
    · rename_i r hr; exact hnode _ _ hr
    · simp only [Expr.replaceFVars, Expr.fvarsBelow]
      exact ⟨trivial, ConLeche.Expr.ErasedEq.rfl _⟩
  | app a b iha ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    rw [Expr.replaceApps_app]
    split
    · rename_i r hr; exact hnode _ _ hr
    · obtain ⟨h1, h2⟩ := iha hb.1
      obtain ⟨h3, h4⟩ := ihb hb.2
      exact ⟨⟨h1, h3⟩, h2, h4⟩
  | lam ty b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihb hb.2
    simp only [Expr.replaceApps, Expr.replaceFVars, Expr.fvarsBelow]
    exact ⟨⟨h1, h3⟩, rfl, h2, h4⟩
  | forallE ty b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihb hb.2
    simp only [Expr.replaceApps, Expr.replaceFVars, Expr.fvarsBelow]
    exact ⟨⟨h1, h3⟩, rfl, h2, h4⟩
  | letE ty v b iht ihv ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihv hb.2.1
    obtain ⟨h5, h6⟩ := ihb hb.2.2
    simp only [Expr.replaceApps, Expr.replaceFVars, Expr.fvarsBelow]
    exact ⟨⟨h1, h3, h5⟩, h2, h4, h6⟩
  | proj s i e ih =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := ih hb
    simp only [Expr.replaceApps, Expr.replaceFVars, Expr.fvarsBelow]
    exact ⟨h1, rfl, rfl, h2⟩

/-- Pointwise erasure-equality of a list and its image. -/
theorem erasedEqs_map {f : Expr → Expr} :
    ∀ (xs : List Expr), (∀ x ∈ xs, ConLeche.Expr.ErasedEq x (f x)) → ConLeche.ErasedEqs xs (xs.map f)
  | [], _ => trivial
  | x :: xs, h => ⟨h x List.mem_cons_self,
      erasedEqs_map xs fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **A seed read back is its class** up to the free variables'
annotations (`nestSeedOf`, `nodeRb` at the empty frame stack): at a walk
context whose parameters are the variables `0 ..< nP`. -/
theorem seed_readback {ctx : NestCtx} {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hpar : ∀ i, i < ctx.nP → ∃ ty, ctx.params[i]? = some (.fvar i ty))
    (hlen : ctx.params.length = ctx.nP)
    {I : Name} {us : List Level} {ds : List Expr} {nPc : Nat}
    (hds : ∀ x ∈ ds, x.fvarsBelow ctx.nP) :
    ConLeche.ErasedEqs ds ((nestSeedOf ctx holes I us ds nPc).1.ds.map (nodeRb ctx [])) := by
  have key := seed_readback_gen (nP := ctx.nP) (k := ctx.names.length)
    (f := nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP)
    (g := nestKeyMap ctx.params holes) (h := nestHoleImg ctx [])
    (fun e r hr => by
      unfold Expr.appHole? at hr
      cases hp : e.phApp? 0 ctx.nP with
      | none => rw [hp] at hr; exact nomatch hr
      | some p =>
        rw [hp, Option.bind_some] at hr
        obtain ⟨m, hm, hmc, hv, rfl⟩ := nestCanonSub_some hr
        obtain ⟨c, v⟩ := p
        simp only at hmc hv
        subst hv
        obtain ⟨args, rfl, hlenA, hvar⟩ := Expr.phApp?_spine ctx.nP hp
        obtain ⟨cv, caps, ty, -, -, hget⟩ := nestHoles_getElem? hh hm
        refine ⟨m, _, ty, Expr.mkAppN (.const (ctx.names.getD (ctx.nP + m - ctx.nP) .anonymous)
          (ctx.lps.map .param)) ctx.params, rfl, hm, ?_, ?_, ?_⟩
        · simp only [nestKeyMap, hlen, show ¬ ctx.nP + m < ctx.nP by omega, ite_false,
            show ctx.nP + m - ctx.nP = m by omega, hget]
        · simp only [nestHoleImg]
          rw [ite_eq_left ⟨by omega, by simp only [NestCtx.hiAt]; omega⟩]
        · have hc : ctx.names.getD (ctx.nP + m - ctx.nP) .anonymous = c := by
            rw [show ctx.nP + m - ctx.nP = m by omega, List.getD_eq_getElem?_getD, hmc,
              Option.getD_some]
          rw [hc]
          refine erasedEq_mkAppN_congr (ConLeche.Expr.ErasedEq.rfl _) (by rw [hlenA, hlen])
            fun q h₁ h₂ => ?_
          obtain ⟨tyq, hq⟩ := hvar q args[q] (List.getElem?_eq_getElem h₁)
          obtain ⟨typ, hp'⟩ := hpar q (by omega)
          rw [List.getElem?_eq_getElem h₂, Option.some.injEq] at hp'
          rw [hq, hp']
          simp [ConLeche.Expr.ErasedEq])
    (fun i hi => by
      obtain ⟨ty, hty⟩ := hpar i hi
      exact ⟨ty, by simp only [nestKeyMap, hlen, ite_eq_left hi, hty]⟩)
    (fun i hi => nestHoleImg_none_of_lt hi [])
  simp only [nestSeedOf, List.map_map]
  refine erasedEqs_map ds fun x hx => ?_
  exact (key x (hds x hx)).2

/-! ## Outside classes at the two environments -/

/-- **An outside inductive reads alike at the formers' and the
constructors' environments**: the block's constructors conclude in its
members (`hheads`), so none is a constructor of an inductive `I` that is
no member, and none is named `I` (stored as an inductive there). -/
theorem nestContainer_consBlockCtors {envI : Env} {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))} {names : List Name}
    (hheads : ∀ c ∈ ctorsAs.flatten, envI.find? c.1.name = none ∧
      ∀ C, (ctorEntry C (.ctorInfo c.1 nP c.2)).isSome = true → C ∈ names)
    {I : Name} (hI : I ∉ names) {cv : ConstantVal} {caps : ConLeche.IndCaps}
    (hf : (ConLeche.consBlockCtors nP ctorsAs envI).find? I = some (.indInfo cv caps)) :
    ConLeche.nestContainer (envCtx (ConLeche.consBlockCtors nP ctorsAs envI)) I
      = ConLeche.nestContainer (envCtx envI) I := by
  have hcs := consBlockCtors_consts nP ctorsAs envI
  have hnew : ∀ c ∈ (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse,
      ∃ a ∈ ctorsAs.flatten, c = .ctorInfo a.1 nP a.2 := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
    exact ⟨a, ha, rfl⟩
  have hEq : ConLeche.consBlockCtors nP ctorsAs envI
      = ⟨(ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ envI.consts⟩ :=
    by cases h : ConLeche.consBlockCtors nP ctorsAs envI; simp_all
  -- a lookup above the constructors: a new constructor (fresh below), or the old one
  have hlook : ∀ n, (ConLeche.consBlockCtors nP ctorsAs envI).find? n
      = ((ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse.find?
          (·.name == n)).or (envI.find? n) := by
    intro n; rw [hEq, find?_append]
  have hfind : envI.find? I = some (.indInfo cv caps) := by
    rw [hlook] at hf
    cases hn : (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse.find?
        (·.name == I) with
    | none => rw [hn] at hf; exact hf
    | some c =>
      rw [hn] at hf
      obtain ⟨a, -, rfl⟩ := hnew c (List.mem_of_find?_eq_some hn)
      exact nomatch hf
  refine nestContainer_congr (by rw [hf, hfind]) fun n => ?_
  simp only [ctorLook]
  rw [hlook]
  cases hn : (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse.find?
      (·.name == n) with
  | none => rfl
  | some c =>
    obtain ⟨a, ha, rfl⟩ := hnew c (List.mem_of_find?_eq_some hn)
    have hname : a.1.name = n := by
      have := List.find?_some hn
      simp only [beq_iff_eq] at this
      exact this
    have hfr : envI.find? n = none := hname ▸ (hheads a ha).1
    rw [hfr]
    simp only [Option.some_or, Option.bind_some, Option.bind_none]
    cases hent : ctorEntry I (.ctorInfo a.1 nP a.2) with
    | none => rfl
    | some _ => exact absurd ((hheads a ha).2 I (by rw [hent]; rfl)) hI

/-! ## THE COVERAGE THEOREM: every outside class is a seed's node -/

end ConLeche.Model
