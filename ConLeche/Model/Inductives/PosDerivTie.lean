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
import ConLeche.Verify.EnvBound
import ConLeche.Verify.Cached.Erase
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

/-! ## The coverage theorem's shape: `NodeMajor` at a REACHED node -/

section ReadBack

/-- `replaceFVars` at no mapped variable is the identity. -/
theorem replaceFVars_none : ∀ (e : Expr), e.replaceFVars (fun _ => none) = e
  | .bvar _ | .sort _ | .const .. | .lit _ | .fvar .. => rfl
  | .app f a => by simp [Expr.replaceFVars, replaceFVars_none f, replaceFVars_none a]
  | .lam t b _ => by simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none b]
  | .forallE t b _ => by simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none b]
  | .letE t v b => by
    simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none v, replaceFVars_none b]
  | .proj _ _ x => by simp [Expr.replaceFVars, replaceFVars_none x]

/-- The holes `p ..< p + |hs|` to the terms `hs`, positionally. -/
@[expose] def holeMap (p : Nat) (hs : List Expr) (i : Nat) : Option Expr :=
  if p ≤ i then hs[i - p]? else none

/-- `holeMap` of an empty list maps nothing. -/
theorem holeMap_nil (p : Nat) : holeMap p [] = fun _ => none := by
  funext i; simp [holeMap]

/-- One substitution step of `substAll` at a closed constant list. -/
theorem substFvarAt_replaceFVars {p : Nat} {a : Expr} {as : List Expr}
    (_ha : ∃ n us, a = .const n us) (has : ∀ c ∈ as, ∃ n us, c = .const n us) :
    ∀ (e : Expr), e.fvarsBelow (p + 1 + as.length) →
      Expr.substFvarAt p a (e.replaceFVars (holeMap (p + 1) as))
        = e.replaceFVars (holeMap p (a :: as)) := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceFVars, holeMap]
    by_cases h1 : p + 1 ≤ i
    · have hlt : i - (p + 1) < as.length := by omega
      rw [if_pos h1, List.getElem?_eq_getElem hlt, Option.getD_some, if_pos (by omega)]
      obtain ⟨n, us, hc⟩ := has _ (List.getElem_mem hlt)
      rw [hc]
      have : i - p = (i - (p + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ, List.getElem?_eq_getElem hlt, hc]
      simp [Expr.substFvarAt]
    · rw [if_neg h1]
      simp only [Option.getD_none]
      by_cases h2 : i = p
      · subst h2
        simp [Expr.substFvarAt]
      · have hlt : i < p := by omega
        rw [if_neg (by omega)]
        simp [Expr.substFvarAt, h2, show ¬ i > p by omega]
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | const _ _ => intro _; rfl
  | lit _ => intro _; rfl
  | app f b ihf ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, ihf hb.1, ihb hb.2]
  | lam t b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihb hb.2]
  | forallE t b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihb hb.2]
  | letE t v b iht ihv ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihv hb.2.1, ihb hb.2.2]
  | proj s i x ih =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, ih hb]

/-- **`substAll` at closed constants is `replaceFVars`** (below the range). -/
theorem substAll_eq_replaceFVars :
    ∀ (hs : List Expr) (p : Nat), (∀ c ∈ hs, ∃ n us, c = .const n us) →
      ∀ (e : Expr), e.fvarsBelow (p + hs.length) →
        substAll p hs e = e.replaceFVars (holeMap p hs)
  | [], p, _, e, _ => by simp [substAll, holeMap_nil, replaceFVars_none]
  | a :: as, p, hc, e, hb => by
    simp only [substAll]
    rw [substAll_eq_replaceFVars as (p + 1) (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) e
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)]
    exact substFvarAt_replaceFVars (hc a List.mem_cons_self)
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) e
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)

/-- The kernel's hole constants are `nodeHoleConsts`, positionally. -/
theorem nestHoleConst_eq_holeMap (ctx : NestCtx) (occ : List NestHole) :
    nestHoleConst ctx occ = holeMap ctx.nP (nodeHoleConsts ctx occ) := by
  funext i
  simp only [ConLeche.nestHoleConst_eq, holeMap, nodeHoleConsts, NestCtx.hiAt, Nat.add_zero]
  by_cases h1 : ctx.nP ≤ i
  · simp only [h1, true_and, if_true]
    by_cases h2 : i < ctx.nP + ctx.names.length
    · simp only [h2, if_true]
      have hlt : i - ctx.nP < ctx.names.length := by omega
      rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_map,
        List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    · simp only [h2, if_false, show ctx.nP + ctx.names.length ≤ i by omega, true_and]
      rw [List.getElem?_append_right (by simp; omega), List.length_map]
      by_cases h3 : i < ctx.nP + ctx.names.length + occ.length
      · simp only [h3, if_true, List.getElem?_map]
        congr 2
        omega
      · simp only [h3, if_false]
        rw [List.getElem?_eq_none (by simp; omega)]
  · simp [h1, show ¬ (ctx.nP + ctx.names.length ≤ i) by omega]

/-- **The kernel's concrete key is the node's key read back**, at
parameters below the occurrence's holes. -/
theorem concrete_eq_nodeRb (ctx : NestCtx) (occ : List NestHole) {x : Expr}
    (hx : x.fvarsBelow (ctx.hiAt occ.length)) :
    x.replaceFVars (nestHoleConst ctx occ) = nodeRb ctx occ x := by
  rw [nestHoleConst_eq_holeMap, nodeRb, substAll_eq_replaceFVars _ _
    (nodeHoleConsts_const ctx occ) x (by rw [nodeHoleConsts_length]; simpa [NestCtx.hiAt,
      Nat.add_assoc] using hx)]

end ReadBack

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

/-- Pointwise erasure-equality of a list and its image. -/
theorem erasedEqs_map {f : Expr → Expr} :
    ∀ (xs : List Expr), (∀ x ∈ xs, ConLeche.Expr.ErasedEq x (f x)) → ConLeche.ErasedEqs xs (xs.map f)
  | [], _ => trivial
  | x :: xs, h => ⟨h x List.mem_cons_self,
      erasedEqs_map xs fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **A seed's parameter read back**: members to their holes, then the
parameter variables to the canonical ones (whole), then the holes back to
their constants gives the parameter again up to the free variables'
annotations — generically, for any constant abstraction to fresh
variables `f`, variable renaming `g` below `nP` and read-back `h`. -/
theorem seed_readback_gen {nP k : Nat} {f : Name → List Level → Option Expr}
    {g h : Nat → Option Expr}
    (hf : ∀ c us e, f c us = some e → ∃ j ty, e = .fvar (nP + j) ty ∧ j < k ∧
      h (nP + j) = some (.const c us) ∧ g (nP + j) = none)
    (hg : ∀ i, i < nP → ∃ ty, g i = some (.fvar i ty))
    (hh : ∀ i, i < nP → h i = none) :
    ∀ x : Expr, x.fvarsBelow nP →
      ((x.replaceConsts f).replaceFVars g).fvarsBelow (nP + k) ∧
      ConLeche.Expr.ErasedEq x (((x.replaceConsts f).replaceFVars g).replaceFVars h) := by
  intro x
  induction x with
  | bvar i => intro _; exact ⟨trivial, rfl⟩
  | sort u => intro _; exact ⟨trivial, rfl⟩
  | lit l => intro _; exact ⟨trivial, rfl⟩
  | fvar i ty _ =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨tyP, hgi⟩ := hg i hb
    simp only [Expr.replaceConsts, Expr.replaceFVars, hgi, Option.getD_some, hh i hb,
      Option.getD_none, Expr.fvarsBelow]
    exact ⟨by omega, rfl⟩
  | const c us =>
    intro _
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none =>
      simp only [Option.getD_none, Expr.replaceFVars, Expr.fvarsBelow]
      exact ⟨trivial, ConLeche.Expr.ErasedEq.rfl _⟩
    | some e =>
      obtain ⟨j, ty, rfl, hj, hhj, hgj⟩ := hf c us e hc
      simp only [Option.getD_some, Expr.replaceFVars, hgj, Option.getD_none, hhj,
        Expr.fvarsBelow]
      exact ⟨by omega, ConLeche.Expr.ErasedEq.rfl _⟩
  | app a b iha ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iha hb.1
    obtain ⟨h3, h4⟩ := ihb hb.2
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  | lam ty b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihb hb.2
    exact ⟨⟨h1, h3⟩, rfl, h2, h4⟩
  | forallE ty b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihb hb.2
    exact ⟨⟨h1, h3⟩, rfl, h2, h4⟩
  | letE ty v b iht ihv ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := iht hb.1
    obtain ⟨h3, h4⟩ := ihv hb.2.1
    obtain ⟨h5, h6⟩ := ihb hb.2.2
    exact ⟨⟨h1, h3, h5⟩, h2, h4, h6⟩
  | proj s i e ih =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    obtain ⟨h1, h2⟩ := ih hb
    exact ⟨h1, rfl, rfl, h2⟩

/-- **A seed read back is its class** up to the free variables'
annotations (`nestSeedOf`, `nodeRb` at the empty frame stack): at a walk
context whose canonical variables are the variables `0 ..< nP`. -/
theorem seed_readback {ctx : NestCtx} {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hpar : ∀ i, i < ctx.nP → ∃ ty, ctx.params[i]? = some (.fvar i ty))
    (hlen : ctx.params.length = ctx.nP)
    {I : Name} {us : List Level} {ds : List Expr} {nPc : Nat}
    (hds : ∀ x ∈ ds, x.fvarsBelow ctx.nP) :
    ConLeche.ErasedEqs ds ((nestSeedOf ctx holes I us ds nPc).1.ds.map (nodeRb ctx [])) := by
  have key := seed_readback_gen (nP := ctx.nP) (k := ctx.names.length)
    (f := fun c us' =>
      if us' == ctx.lps.map .param then
        match ctx.names.findIdx? (· == c) with
        | some mm => holes[mm]?
        | none => none
      else none)
    (g := fun i => ctx.params[i]?) (h := holeMap ctx.nP (nodeHoleConsts ctx []))
    (fun c us' e he => by
      split at he
      · rename_i hus
        split at he
        · rename_i mm hmm
          obtain ⟨hmmlt, hmmeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmm
          obtain ⟨cv, caps, -, hget⟩ := nestHoles_getElem? hh hmmlt
          rw [hget] at he
          obtain rfl := Option.some.inj he
          refine ⟨mm, _, rfl, hmmlt, ?_, ?_⟩
          · simp only [holeMap, show ctx.nP ≤ ctx.nP + mm by omega, if_true,
              show ctx.nP + mm - ctx.nP = mm by omega, nodeHoleConsts, List.reverse_nil,
              List.map_nil, List.append_nil, List.getElem?_map,
              List.getElem?_eq_getElem hmmlt, Option.map_some]
            have hc : ctx.names[mm] = c := by simpa using hmmeq
            have hu : us' = ctx.lps.map .param := by simpa using hus
            rw [hc, hu]
          · exact List.getElem?_eq_none (by omega)
        · exact nomatch he
      · exact nomatch he)
    (fun i hi => hpar i hi)
    (fun i hi => by simp only [holeMap]; rw [if_neg (by omega)])
  simp only [nestSeedOf, List.map_map]
  refine erasedEqs_map ds fun x hx => ?_
  obtain ⟨hb, he⟩ := key x (hds x hx)
  show ConLeche.Expr.ErasedEq x (nodeRb ctx [] _)
  rw [nodeRb, substAll_eq_replaceFVars _ _ (nodeHoleConsts_const ctx []) _
    (by rw [nodeHoleConsts_length, List.length_nil, Nat.add_zero]; exact hb)]
  exact he

/-! ## Outside classes at the two environments -/

/-- **An outside inductive reads alike at the formers' and the
constructors' environments**: the block's constructors conclude in its
members (`hheads`), so none is a constructor of an inductive `I` that is
no member, and none is named `I` (stored as an inductive there). -/
theorem nestContainer_consBlockCtors {envI : Env} {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))} {names : List Name}
    (hheads : ∀ c ∈ ctorsAs.flatten, ∀ C, (ctorEntry C (.ctorInfo c.1 nP c.2)).isSome = true →
      C ∈ names)
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
  have hfind : envI.find? I = some (.indInfo cv caps) := by
    have hf' := hf
    rw [show (ConLeche.consBlockCtors nP ctorsAs envI)
      = ⟨(ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ envI.consts⟩
      from by cases h : ConLeche.consBlockCtors nP ctorsAs envI; simp_all] at hf'
    rw [find?_append] at hf'
    cases hn : (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse.find?
        (·.name == I) with
    | none => rw [hn] at hf'; exact hf'
    | some c =>
      rw [hn] at hf'
      obtain ⟨a, -, rfl⟩ := hnew c (List.mem_of_find?_eq_some hn)
      exact nomatch hf'
  rw [nestContainer_eq, nestContainer_eq]
  show (match (ConLeche.consBlockCtors nP ctorsAs envI).find? I with
      | some (.indInfo _ caps) =>
        nestPick caps ((ConLeche.consBlockCtors nP ctorsAs envI).consts.filterMap (ctorEntry I))
      | _ => none) = (match envI.find? I with
      | some (.indInfo _ caps) => nestPick caps (envI.consts.filterMap (ctorEntry I))
      | _ => none)
  have hnil : (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse.filterMap
      (ctorEntry I) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hnew c hc
    cases hent : ctorEntry I (.ctorInfo a.1 nP a.2) with
    | none => rfl
    | some _ => exact absurd (hheads a ha I (by rw [hent]; rfl)) hI
  rw [hf, hfind, hcs, List.filterMap_append, hnil, List.nil_append]

/-! ## THE COVERAGE THEOREM: every outside class is a seed's node -/

end ConLeche.Model
