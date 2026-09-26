module

public import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Model.Inductives.PosDerivSem
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# An invariant of the terms the positivity walk reads, at its nodes' keys

A property `P` of terms that the walk's term operations keep — raw
subterms, the opening of a `Π` body at a variable above the block's
holes, the kernel's whnf, and the instantiation of a frame's
constructors (`hcrest`, the one step that reads the environment) —
holds of every parameter of every node key a derivation makes, once it
holds of the derivation's input (`posD_inv`).  Instances: the low
variables are the walk's canonical ones, and the constants lie in a
scope (`NestHomeKeys.lean`).
-/

namespace ConLeche

/-- The invariant at every node key of a forest. -/
@[expose] def NodesInv (P : Expr → Prop) (ts : List PosTree) : Prop :=
  ∀ u ∈ PosTree.forest ts, ∀ x ∈ u.key.ds, P x

/-- The invariant at a judgment: from its input to its nodes. -/
@[expose] def InvJ (P : Expr → Prop) (lo : Nat) : PosJ → List PosTree → Prop
  | .field _ dep _ e _ _, ts => lo ≤ dep → P e → NodesInv P ts
  | .tele _ base _ _ cur _ _ _, ts => lo ≤ base → P cur → NodesInv P ts
  | .ctors _ hi us ds sub cs, ts => lo ≤ hi → (∀ x ∈ ds, P x) →
      (∀ x ∈ cs, ∀ crest, instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams
        us).replaceConsts sub) = some crest → P crest) → NodesInv P ts
  | .frame _ _ ds _, ts => (∀ x ∈ ds, P x) → NodesInv P ts
  | .syn _ e, ts => P e → NodesInv P ts

section Inv

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {P : Expr → Prop}

theorem NodesInv.nil : NodesInv P [] := fun _ h => nomatch h

theorem NodesInv.append {ts ts' : List PosTree} (h : NodesInv P ts) (h' : NodesInv P ts') :
    NodesInv P (ts ++ ts') := fun u hu => by
  rcases PosTree.mem_forest_append.mp hu with hu | hu
  · exact h u hu
  · exact h' u hu

theorem NodesInv.node {occ anc : List NestHole} {key : NestKey} {grp : List (Name × Expr)}
    {ts : List PosTree} (hk : ∀ x ∈ key.ds, P x) (h : NodesInv P ts) :
    NodesInv P [.node occ anc key grp ts] := fun u hu => by
  simp only [PosTree.forest, List.append_nil] at hu
  rcases PosTree.mem_nodes.mp hu with rfl | hu
  · exact hk
  · exact h u hu

/-- **The invariant holds at every node key of a derivation** (see the
module docstring). -/
theorem posD_inv (lo : Nat) (hlo : lo ≤ ctx.hiAt 0)
    (hsub : ∀ s e, Expr.SubOf s e → P e → P s)
    (hinst : ∀ b a d, lo ≤ d → P b → P a → P (b.instantiate1 (.fvar d a)))
    (hwhnf : ∀ d e w, ops.whnf env d e = .ok w → P e → P w)
    (hcrest : ∀ (prog : List NestHole) (us : List Level) (ds : List Expr)
      (grp : List (Name × Expr)) (ctors : List (ConstantVal × Nat)),
      grp ≠ [] → (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨p.1, us, ds⟩ = .ok (nI, p.2)) →
      groupCtors ctx ds.length (grp.map (·.1)) = some ctors → (∀ x ∈ ds, P x) →
      ∀ x ∈ ctors, ∀ crest, instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams
        us).replaceConsts (grpSub us (ctx.hiAt prog.length) grp)) = some crest → P crest) :
    ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → InvJ P lo j ts := by
  intro j ts h
  induction h with
  | const => intro _ _; exact NodesInv.nil
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    intro hdep he
    have hw' := hwhnf _ _ _ hw he
    exact ih (by omega) (hinst _ _ _ hdep (hsub _ _ (.piB a bm (.refl b)) hw')
      (hsub _ _ (.piT b bm (.refl a)) hw'))
  | hole => intro _ _; exact NodesInv.nil
  | frameHole => intro _ _; exact NodesInv.nil
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      hdsw hnI hhead hsc hfr hdeep ih =>
    intro _ he
    have hw' := hwhnf _ _ _ hw he
    have hk : ∀ x ∈ w.getAppArgs.take nPc, P x := fun x hx =>
      hsub _ _ (Model.Expr.SubOf.of_mem_getAppArgs (List.mem_of_mem_take hx)) hw'
    exact NodesInv.node hk (ih hk)
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      hdsw hnI hmem hfr ih =>
    intro _ he
    have hw' := hwhnf _ _ _ hw he
    have hk : ∀ x ∈ w.getAppArgs.take nPc, P x := fun x hx =>
      hsub _ _ (Model.Expr.SubOf.of_mem_getAppArgs (List.mem_of_mem_take hx)) hw'
    exact NodesInv.node hk (ih hk)
  | @frame prog us ds grp ctors ts hne hhd hhdC hnd hinst hblk hgrp hctors hkty hwalk ih =>
    intro hds
    refine ih (by simp only [NestCtx.hiAt] at hlo ⊢; omega) hds ?_
    exact hcrest prog us ds grp ctors hne hinst hctors hds
  | ctorsNil => intro _ _ _; exact NodesInv.nil
  | @ctorsCons prog hi us ds sub cv nF cs crest ty sv ks nds cur ts ts' hnd hcrest' hty hsort
      htele hu4 hres hidx hrest iht ihr =>
    intro hhi hds hcs
    exact (iht hhi (hcs _ List.mem_cons_self _ hcrest')).append
      (ihr hhi hds fun x hx => hcs x (List.mem_cons_of_mem _ hx))
  | teleNil => intro _ _; exact NodesInv.nil
  | @teleCons prog base nF j a b bm k nd ks nds res ts tss ts' ha hs hb iha ihs ihb =>
    intro hbase hcur
    have hA := hsub _ _ (.piT b bm (.refl a)) hcur
    have hB := hsub _ _ (.piB a bm (.refl b)) hcur
    exact (iha (by omega) hA).append ((ihs hA).append
      (ihb hbase (hinst _ _ _ (by omega) hB hA)))
  | synNil => intro _; exact NodesInv.nil
  | @synNew prog e n us ds L nI cty grp ts ts' hsrc hnm hquot hC hds hdsw hnI hhead hsc hfr
      hrest ihf ihr =>
    intro he
    obtain ⟨s, hs, hsk⟩ := hsrc
    have hk : ∀ x ∈ (⟨n, us, ds⟩ : NestKey).ds, P x := fun x hx =>
      hsub _ _ (Model.Expr.SubOf.trans
        (Model.Expr.SubOf.of_mem_getAppArgs (nestSynApp?_ds hsk x hx)) hs) he
    have h1 : NodesInv P [.node prog prog ⟨n, us, ds⟩ grp ts] := NodesInv.node hk (ihf hk)
    exact fun u hu => by
      have := (h1.append (ihr he)) u (by simpa using hu)
      exact this
  | @synHit prog e n us ds L grp ts ts' hsrc hnm hquot hC hds hdsw hmem hfr hrest ihf ihr =>
    intro he
    obtain ⟨s, hs, hsk⟩ := hsrc
    have hk : ∀ x ∈ (⟨n, us, ds⟩ : NestKey).ds, P x := fun x hx =>
      hsub _ _ (Model.Expr.SubOf.trans
        (Model.Expr.SubOf.of_mem_getAppArgs (nestSynApp?_ds hsk x hx)) hs) he
    have h1 : NodesInv P [.node prog [] ⟨n, us, ds⟩ grp ts] := NodesInv.node hk (ihf hk)
    exact fun u hu => by
      have := (h1.append (ihr he)) u (by simpa using hu)
      exact this

end Inv

end ConLeche
