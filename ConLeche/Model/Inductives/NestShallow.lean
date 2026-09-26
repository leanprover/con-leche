module

public import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.TargetCallWalk
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Cached.Erase

public section

/-!
# A shallow field lands at a node derived at the EMPTY stack

`nestLeafShallow lo hi nd` (`Kernel/Inductives/FieldNf.lean`): the walked
normal form's `Π`-leaf, when it is a container instance, mentions no
frame hole of `[lo, hi)`.  At a field derived under the frames `prog`,
with `lo = hiAt 0` and `hi = hiAt prog.length`, every container node the
field's derivation makes is then derived at the EMPTY stack
(`posD_field_anc_nil`): a `contNew` node carries a parameter mentioning a
frame hole (`PosD.contNew`'s `hdeep`), which a shallow leaf does not
have.  This is what lets a recursor call on such a field land at a node
the rec check can recompute (`ClassNf.lean`).
-/

namespace ConLeche

open Expr

/-- The head of an abstracted application is the abstracted head. -/
theorem getAppFn_abstract1 {d : Nat} :
    ∀ (x : Expr) (k : Nat), (x.abstract1 d k).getAppFn = x.getAppFn.abstract1 d k
  | .app f a, k => by
    simp only [Expr.abstract1, Expr.getAppFn]
    exact getAppFn_abstract1 f k
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _ _, _
  | .forallE _ _ _, _ | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => by
    simp only [Expr.abstract1, Expr.getAppFn]
    try (split <;> rfl)

/-- The shallowness test below the binders: a term that is no `Π` is its
own leaf. -/
theorem nestLeafShallow_of_notPi {lo hi : Nat} {y : Expr} (hy : ∀ a b m, y ≠ .forallE a b m) :
    nestLeafShallow lo hi y = (match y.getAppFn with
      | .const _ _ => !y.nestOcc [] lo hi
      | _ => true) := by
  have hp : y.piLeaf = y := by
    cases y with
    | forallE a b m => exact absurd rfl (hy a b m)
    | _ => rfl
  unfold nestLeafShallow; rw [hp]; rfl

/-- The shallowness test of a term that is no `Π` does not see the
abstraction of a variable outside its hole range. -/
theorem nestLeafShallow_abstract1_notPi {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi)) {x : Expr}
    (hx : ∀ a b m, x ≠ .forallE a b m) (k : Nat) :
    nestLeafShallow lo hi (x.abstract1 d k) = nestLeafShallow lo hi x := by
  have hx' : ∀ a b m, x.abstract1 d k ≠ .forallE a b m := by
    intro a b m h
    cases x with
    | forallE a' b' m' => exact hx a' b' m' rfl
    | fvar i ty =>
      simp only [Expr.abstract1] at h
      split at h <;> exact nomatch h
    | _ => simp [Expr.abstract1] at h
  rw [nestLeafShallow_of_notPi hx', nestLeafShallow_of_notPi hx, getAppFn_abstract1]
  cases hf : x.getAppFn with
  | const n us => simp [Expr.abstract1, Model.nestOcc_abstract1 hd]
  | fvar i ty =>
    simp only [Expr.abstract1]
    by_cases hi : i = d
    · simp only [if_pos hi]
    · simp only [if_neg hi]
  | _ => rfl

/-- A shallowness test does not see the abstraction of a variable
outside its hole range. -/
theorem nestLeafShallow_abstract1 {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi)) :
    ∀ (x : Expr) (k : Nat), nestLeafShallow lo hi (x.abstract1 d k) = nestLeafShallow lo hi x := by
  intro x
  induction x with
  | forallE a b m _ ihb =>
    intro k
    have e1 : nestLeafShallow lo hi (Expr.forallE a b m) = nestLeafShallow lo hi b := rfl
    have e2 : nestLeafShallow lo hi ((Expr.forallE a b m).abstract1 d k)
        = nestLeafShallow lo hi (b.abstract1 d (k + 1)) := rfl
    rw [e1, e2, ihb]
  | bvar => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | fvar => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | sort => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | const => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | lit => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | app => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | lam => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | letE => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)
  | proj => exact nestLeafShallow_abstract1_notPi hd (fun _ _ _ h => nomatch h)

/-- No variable lies in an empty range. -/
theorem nestOcc_nil_self (lo : Nat) : ∀ (x : Expr), x.nestOcc [] lo lo = false := by
  intro x
  induction x <;> simp_all [Expr.nestOcc]

/-- At an empty frame range every field is shallow. -/
theorem nestLeafShallow_self (lo : Nat) (nd : Expr) : nestLeafShallow lo lo nd = true := by
  unfold nestLeafShallow
  split <;> simp [nestOcc_nil_self]

/-- A term below `hi` mentioning no variable of `[lo, hi)` is below `lo`. -/
theorem fvarsBelow_of_nestOcc {lo hi : Nat} :
    ∀ (x : Expr), x.fvarsBelow hi → x.nestOcc [] lo hi = false → x.fvarsBelow lo := by
  intro x
  induction x with
  | fvar i ty _ =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc, decide_eq_false_iff_not, not_and] at h1 h2 ⊢
    by_cases h : lo ≤ i
    · exact absurd h1 (Nat.not_lt.mpr (Nat.le_of_not_lt (h2 h)))
    · omega
  | app f a ihf iha =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨ihf h1.1 h2.1, iha h1.2 h2.2⟩
  | lam t b m iht ihb =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨iht h1.1 h2.1, ihb h1.2 h2.2⟩
  | forallE t b m iht ihb =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨iht h1.1 h2.1, ihb h1.2 h2.2⟩
  | letE t v b iht ihv ihb =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨iht h1.1 h2.1.1, ihv h1.2.1 h2.1.2, ihb h1.2.2 h2.2⟩
  | proj s i e ih =>
    intro h1 h2
    simp only [Expr.fvarsBelow, Expr.nestOcc] at h1 h2 ⊢
    exact ih h1 h2
  | bvar => intro _ _; trivial
  | sort => intro _ _; trivial
  | const => intro _ _; trivial
  | lit => intro _ _; trivial

/-- What a field judgment's derivation says of its container nodes at a
shallow normal form: every one is derived at the EMPTY stack. -/
@[expose] def FieldShallowNodes (ctx : NestCtx) : PosJ → List PosTree → Prop
  | .field prog dep _ _ _ nd, ts => ctx.hiAt prog.length ≤ dep →
      nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) nd = true → ∀ u ∈ ts, u.anc = []
  | _, _ => True

/-- **A shallow field's container nodes are derived at the EMPTY stack**
(see the module docstring). -/
theorem posD_field_anc_nil {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → FieldShallowNodes ctx j ts := by
  intro j ts h
  induction h with
  | const => unfold FieldShallowNodes; intro _ _ u hu; exact nomatch hu
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    unfold FieldShallowNodes at ih ⊢
    intro hdep hsh u hu
    have e1 : nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) (.forallE a (nb.abstract1 dep) bm)
        = nestLeafShallow (ctx.hiAt 0) (ctx.hiAt prog.length) (nb.abstract1 dep) := rfl
    rw [e1, nestLeafShallow_abstract1 (by omega)] at hsh
    exact ih (by omega) hsh u hu
  | hole => unfold FieldShallowNodes; intro _ _ u hu; exact nomatch hu
  | frameHole => unfold FieldShallowNodes; intro _ _ u hu; exact nomatch hu
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hC hlen hquot hidx hds hdsw
      hnI hhead hsc hfr hdeep _ =>
    unfold FieldShallowNodes
    intro _ hsh u hu
    simp only [List.mem_singleton] at hu
    subst hu
    show prog = []
    have hwp : ∀ a b m, w ≠ .forallE a b m := fun a b m h => by
      subst h; simp [Expr.getAppFn] at hfn
    rw [nestLeafShallow_of_notPi hwp, hfn] at hsh
    have hno : w.nestOcc [] (ctx.hiAt 0) (ctx.hiAt prog.length) = false := by simpa using hsh
    rw [← Expr.mkAppN_getApp w, Model.nestOcc_mkAppN, Bool.or_eq_false_iff,
      List.any_eq_false] at hno
    have hall : ((w.getAppArgs.take nPc).all fun x => x.fvarB ≤ ctx.hiAt 0) = true := by
      rw [List.all_eq_true]
      intro x hx
      have h1 := Expr.fvarB_le (hds x hx).2
      have h2 : x.nestOcc [] (ctx.hiAt 0) (ctx.hiAt prog.length) = false := by
        have := hno.2 x (List.mem_of_mem_take hx); simpa using this
      have h3 := fvarsBelow_of_nestOcc x h1 h2
      simpa [Expr.fvarB_eq] using Expr.fvarsBelow_iff.mp h3
    rw [hall] at hdeep
    exact nomatch hdeep
  | contHit =>
    unfold FieldShallowNodes
    intro _ _ u hu
    simp only [List.mem_singleton] at hu
    subst hu; rfl
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil => trivial
  | teleCons => trivial
  | synNil => trivial
  | synNew => trivial
  | synHit => trivial

/-! ## A walked field's container node is its leaf's key -/

/-- `abstract1` at or above a term's variables is the identity. -/
theorem abstract1_eq_self_of_below : ∀ {e : Expr} {d k : Nat},
    Expr.fvarsBelow d e → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k hb <;>
    simp_all only [Expr.fvarsBelow, Expr.abstract1]
  rw [if_neg (by omega)]

/-- The arguments of an abstracted application are the abstracted
arguments. -/
theorem getAppArgs_abstract1 {d : Nat} :
    ∀ (x : Expr) (k : Nat), (x.abstract1 d k).getAppArgs = x.getAppArgs.map (·.abstract1 d k)
  | .app f a, k => by
    simp only [Expr.abstract1, Expr.getAppArgs, getAppArgs_abstract1 f k, List.map_append,
      List.map_cons, List.map_nil]
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lam _ _ _, _
  | .forallE _ _ _, _ | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => by
    simp [Expr.abstract1, Expr.getAppArgs]
  | .fvar i ty, k => by
    simp only [Expr.abstract1]
    split <;> simp [Expr.getAppArgs]

/-- The leaf of an abstracted telescope is its leaf abstracted (one
binder deeper per `Π`). -/
theorem piLeaf_abstract1 {d : Nat} :
    ∀ (x : Expr) (k : Nat), ∃ k', (x.abstract1 d k).piLeaf = x.piLeaf.abstract1 d k'
  | .forallE a b m, k => by
    obtain ⟨k', h⟩ := piLeaf_abstract1 b (k + 1)
    exact ⟨k', by simpa [Expr.abstract1, Expr.piLeaf] using h⟩
  | .fvar i ty, k => by
    refine ⟨k, ?_⟩
    show ((Expr.fvar i ty).abstract1 d k).piLeaf = (Expr.fvar i ty).abstract1 d k
    simp only [Expr.abstract1]
    split <;> rfl
  | .bvar _, k | .sort _, k | .const _ _, k | .lam _ _ _, k | .letE _ _ _, k | .lit _, k
  | .proj _ _ _, k | .app _ _, k => ⟨k, rfl⟩

/-- What a field judgment's derivation says of its container nodes'
keys: each is the normal form's leaf's head and parameters. -/
@[expose] def FieldNodeLeaf (ctx : NestCtx) : PosJ → List PosTree → Prop
  | .field prog dep _ _ _ nd, ts => ctx.hiAt prog.length ≤ dep → ∀ u ∈ ts,
      nd.piLeaf.getAppFn = .const u.key.cname u.key.lvls ∧
      nd.piLeaf.getAppArgs.take u.key.ds.length = u.key.ds ∧
      (∀ x ∈ u.key.ds, x.fvarsBelow (ctx.hiAt prog.length)) ∧
      nd.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
  | _, _ => True

/-- **A walked field's container node is its leaf's key.** -/
theorem posD_field_node_leaf {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → FieldNodeLeaf ctx j ts := by
  intro j ts h
  induction h with
  | const => unfold FieldNodeLeaf; intro _ u hu; exact nomatch hu
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    unfold FieldNodeLeaf at ih ⊢
    intro hdep u hu
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) u hu
    obtain ⟨k', hk'⟩ := piLeaf_abstract1 (d := dep) nb 0
    have e1 : (Expr.forallE a (nb.abstract1 dep) bm).piLeaf = (nb.abstract1 dep 0).piLeaf := rfl
    rw [e1, hk', getAppFn_abstract1, h1, getAppArgs_abstract1, ← List.map_take, h2]
    refine ⟨by simp [Expr.abstract1], ?_, h3, ?_⟩
    rotate_left
    · simp only [Expr.nestOcc, Model.nestOcc_abstract1 (show ¬ (ctx.nP ≤ dep ∧
        dep < ctx.hiAt prog.length) by omega), h4, Bool.or_true]
    have : u.key.ds.map (·.abstract1 dep k') = u.key.ds.map id :=
      List.map_congr_left fun x hx =>
        abstract1_eq_self_of_below (Expr.fvarsBelow_mono (by omega) (h3 x hx))
    rw [this, List.map_id]
  | hole => unfold FieldNodeLeaf; intro _ u hu; exact nomatch hu
  | frameHole => unfold FieldNodeLeaf; intro _ u hu; exact nomatch hu
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hC hlen hquot hidx hds
      hdsw hnI hhead hsc hfr hdeep _ =>
    unfold FieldNodeLeaf
    intro _ u hu
    simp only [List.mem_singleton] at hu
    subst hu
    have hwp : ∀ a b m, w ≠ .forallE a b m := fun a b m h => by
      subst h; simp [Expr.getAppFn] at hfn
    have hpl : w.piLeaf = w := by cases w with
      | forallE a b m => exact absurd rfl (hwp a b m)
      | _ => rfl
    simp only [PosTree.key]
    refine ⟨by rw [hpl, hfn], by rw [hpl]; simp, fun x hx => Expr.fvarB_le (hds x hx).2, hocc⟩
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hC hlen hquot hidx hds
      hdsw hnI hmem hfr _ =>
    unfold FieldNodeLeaf
    intro _ u hu
    simp only [List.mem_singleton] at hu
    subst hu
    have hwp : ∀ a b m, w ≠ .forallE a b m := fun a b m h => by
      subst h; simp [Expr.getAppFn] at hfn
    have hpl : w.piLeaf = w := by cases w with
      | forallE a b m => exact absurd rfl (hwp a b m)
      | _ => rfl
    simp only [PosTree.key]
    refine ⟨by rw [hpl, hfn], by rw [hpl]; simp, fun x hx => Expr.fvarsBelow_mono
      (by simp [NestCtx.hiAt]) (Expr.fvarB_le (hds x hx).2), hocc⟩
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil => trivial
  | teleCons => trivial
  | synNil => trivial
  | synNew => trivial
  | synHit => trivial

/-! ## A frame's constructors, derived -/

/-- **A frame's constructor telescope, derived**: at a derived frame, every
constructor of its group, instantiated as the frame instantiates it, has
its telescope derived, its nodes among the frame's. -/
theorem posD_frame_ctor {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ts : List PosTree} (h : PosD ops env ctx (.frame prog us ds grp) ts)
    {ctors : List (ConstantVal × Nat)}
    (hc : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {x : ConstantVal × Nat} (hx : x ∈ ctors) {crest : Expr}
    (hcr : instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt prog.length) grp)) = some crest) :
    ∃ ks nds cur ts', PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt prog.length) grp).reverse
        ++ prog) (ctx.hiAt prog.length + grp.length) x.2 0 crest ks nds cur) ts' ∧
      ∀ t ∈ PosTree.forest ts', t ∈ PosTree.forest ts := by
  cases h with
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hwalk =>
    rw [hctors] at hc
    obtain rfl := Option.some.inj hc
    exact go hwalk hx hcr
where
  go {prog' : List NestHole} {hi : Nat} {sub : Name → List Level → Option Expr} :
      ∀ {cs : List (ConstantVal × Nat)} {ts : List PosTree},
      PosD ops env ctx (.ctors prog' hi us ds sub cs) ts → x ∈ cs →
      instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      ∃ ks nds cur ts', PosD ops env ctx (.tele prog' hi x.2 0 crest ks nds cur) ts' ∧
        ∀ t ∈ PosTree.forest ts', t ∈ PosTree.forest ts := by
    intro cs ts hcs hx hcr
    cases hcs with
    | ctorsNil => exact nomatch hx
    | @ctorsCons _ _ _ _ _ cv nF cs' crest' ty sv ks nds cur ts₁ ts₂ hnd hcrest' hty hsort htele
        hu4 hres hidx hrest =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hcr] at hcrest'
        obtain rfl := Option.some.inj hcrest'
        exact ⟨ks, nds, cur, ts₁, htele, fun t ht => PosTree.mem_forest_append.mpr (Or.inl ht)⟩
      · obtain ⟨ks', nds', cur', ts', h1, h2⟩ := go hrest hx' hcr
        exact ⟨ks', nds', cur', ts', h1,
          fun t ht => PosTree.mem_forest_append.mpr (Or.inr (h2 t ht))⟩

end ConLeche
