module

public import ConLeche.Model.Inductives.TargetNodePres
public import ConLeche.Model.Inductives.TargetNodeTie
import ConLeche.Verify.Inductives.PosAnn

public section

/-!
# The node presentation over a NODE LIST

`TgtNodePres` (`TargetNodePres.lean`) asks, per node, a recorded clause,
a level assignment, a true frame and a depth, and a class → node
relation along which the class data are the node's.  This module fixes
that STATIC part from a list `ns` of positivity nodes (`PosTree`):

* node `0` is the block itself — its datum `d.toLfp`, the level
  assignment `ψ`, the frame of the prefix's first `nP` values; every
  MEMBER class is related to it;
* node `b + 1` is `ns[b]` — the block `lfpSel` selects for its key's
  container (`nodeψ`, `nodeFr`: the read-back); an OUTSIDE class
  is related to it when its major is the node's key read back
  (`NodeMajor`);
* the relation carries the class's guard (so the prefix spine has the
  rule prefix's length, which the read-back frame needs);
* a node's depth is the list's height bound minus its tree's height (node `0` is the
  root).

`tgtNodePres_of_list` builds the presentation from the static facts
(the class tie, `tgtNodeTie`, at every related pair — its node premises
as `NodeListFacts`) and the DYNAMIC part as premises stated at the
list's data (`nlDb`, `nlψ`, `nlFr`, `nlDp`, `nlRel`): the admissible
frames `Adm` with `hAdm`/`top`/`trans`, and the calls `hcall`.  The
presentation covers every guarded class once every guarded OUTSIDE
class's major is some node's key read back (`NodeListCover`, the form
`outsideClass_reachedNode` takes).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level NestCtx NestHole NestKey PosTree TargetMajor
  ConstantVal BlockShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The list's data -/

section Data

variable {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (d : BlockData V)
  (ns : List PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- Node `b`'s recorded clause: the block at `0`, the selected block of
`ns[b - 1]`'s container above. -/
@[expose] noncomputable def nlDb (b : Nat) : LfpDatum V :=
  if b = 0 then d.toLfp else lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname

/-- Node `b`'s level assignment. -/
@[expose] def nlψ (envC : Env) (ns : List PosTree) (ψ : Name → Nat) (b : Nat) : Name → Nat :=
  if b = 0 then ψ else nodeψ envC ψ (ns.getD (b - 1) default)

/-- Node `b`'s TRUE frame at the prefix spine `xs`. -/
@[expose] noncomputable def nlFr (b : Nat) : Nat → V :=
  if b = 0 then consList (xs.take d.nP) ρ
  else nodeFr mpC.base2.acval envC ctx ψ ρ xs (ns.getD (b - 1) default)

/-- A strict bound of every depth: the list's greatest height, plus two. -/
@[expose] def nlDd (ns : List PosTree) : Nat := (ns.map (·.height)).foldr max 0 + 2

/-- Node `b`'s depth (`0` the root): the bound minus its tree's height, so a
kid is deeper than its parent and an owner shallower than the nodes it owns
holes of (a cache hit's kids occur at its own group's frames only, so
the stack's length is not monotone along kids). -/
@[expose] def nlDp (ns : List PosTree) (b : Nat) : Nat :=
  if b = 0 then 0 else nlDd ns - (ns.getD (b - 1) default).height

end Data

section Rel

variable {envC : Env} (acval : Name → (Name → Nat) → AnnotTerm) (ctx : NestCtx)
  (d : BlockData V) (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr))
  (ns : List PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- **The class → node relation**: the class is guarded at the prefix
spine, and either a member class at node `0` or an outside class whose
major is node `b`'s key read back, at a node `okN` admits (every node for
the walk-read check; the nodes derived at the EMPTY stack for a check
that recomputes the classes' normal forms, `ClassNf.lean`), the class one
`okC` admits (every class; a layer's). -/
@[expose] def nlRel (envC : Env) (okC : Nat → Prop) (okN : Nat → PosTree → Prop) (c b : Nat) :
    Prop :=
  tgtClsG d acval envC p out ψ ρ xs c ∧
    (((tgtMajor out c).member.isSome = true ∧ b = 0) ∨
      (0 < b ∧ b ≤ ns.length ∧ NodeMajor ctx (tgtMajor out c) (ns.getD (b - 1) default) ∧
        okN c (ns.getD (b - 1) default))) ∧ okC c

end Rel

/-! ## The static facts -/

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact nomatch h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem height_le_nlDd {ns : List PosTree} {t : PosTree} (ht : t ∈ ns) : t.height + 2 ≤ nlDd ns := by
  have := le_foldr_max (List.mem_map_of_mem (f := (·.height)) ht)
  unfold nlDd; omega

theorem nlDp_lt (ns : List PosTree) (b : Nat) (hb : b < ns.length + 1) : nlDp ns b < nlDd ns := by
  unfold nlDp
  split
  · unfold nlDd; omega
  · have := PosTree.height_pos (ns.getD (b - 1) default)
    have h2 : (ns.getD (b - 1) default).height + 2 ≤ nlDd ns := by
      refine height_le_nlDd ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _
    omega

/-- A selected block is recorded, once the default is. -/
theorem lfpSel_mem_blocks {env : Env} {mp : EnvModelM V μ env} {D0 : LfpDatum V}
    (hD0 : D0 ∈ mp.lfpBlocks) (n : Name) : lfpSel mp D0 n ∈ mp.lfpBlocks := by
  classical
  unfold lfpSel
  split
  · rename_i h; exact (Classical.choose_spec h).1
  · exact hD0

/-- **The node facts the class tie reads** (`tgtNodeTie`'s node premises),
at every node of the list. -/
structure NodeListFacts {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx)
    (ns : List PosTree) : Prop where
  /-- the key's container and every group member lie in one recorded block -/
  blk : ∀ t ∈ ns, ∀ n ∈ t.grp.map (·.1),
    ∃ D ∈ mpC.lfpBlocks, t.key.cname ∈ D.names ∧ n ∈ D.names
  /-- the group's level parameters are the container's -/
  lps : ∀ t ∈ ns, ∀ n ∈ t.grp.map (·.1), lpsOf envC t.key.cname = lpsOf envC n
  /-- the stack's hole constants are stored at arity -/
  read : ∀ t ∈ ns, NodeHolesRead envC ctx t.occ
  /-- the key's parameters are scoped at the stack's depth -/
  ws : ∀ t ∈ ns, ∀ x ∈ t.key.ds, Expr.WScoped (ctx.nP + (nodeHoleConsts ctx t.occ).length) x
  /-- and read there, at every level assignment -/
  sp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
    (ctx.nP + (nodeHoleConsts ctx t.occ).length) t.key.ds dsa

/-- **Coverage in `NodeMajor` form** (`outsideClass_reachedNode`'s
shape): every guarded outside class's major is some listed
node's key read back. -/
@[expose] def NodeListCover (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (ctx : NestCtx) (d : BlockData V) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ns : List PosTree) (ψ : Name → Nat)
    (ρ : Nat → V) (xs : List V) : Prop :=
  ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
    tgtClsG d acval envC p out ψ ρ xs c → ∃ t ∈ ns, NodeMajor ctx (tgtMajor out c) t

/-- **The presentation's DYNAMIC part over a node list**: the admissible
frames, their three kit facts, and the calls — stated at the list's data. -/
structure TgtNodeDyn (μ : CheckMode) (F : Nat) {envC : Env} (mpC : EnvModelM V μ envC)
    (ctx : NestCtx) (d : BlockData V) (p : BlockShape) (formerTys : List Expr)
    (out : List (ConstantVal × TargetMajor × List Expr)) (Dc : Nat → LfpDatum V)
    (mc : Nat → Nat) (cvc : Nat → ConstantVal) (ns : List PosTree) (ψ : Name → Nat)
    (ρ : Nat → V) (xs : List V) (S : Nat → Prop) (okN : Nat → PosTree → Prop) where
  Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop
  hAdm : ∀ b, b < ns.length + 1 → ∀ G ρ', Adm b G ρ' →
    Sat V ((nlDb mpC d ns b).params (nlψ envC ns ψ b)).reverse ρ' ∧
      ∀ c, c < (nlDb mpC d ns b).N → (nlDb mpC d ns b).idx (nlψ envC ns ψ b) ρ' c
        = (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b) c
  top : ∀ b, b < ns.length + 1 → ∀ G, (∀ b' c t y, b' < ns.length + 1 →
      nlDp ns b' < nlDp ns b → c < (nlDb mpC d ns b').N →
      t ∈ˢ (nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c →
      y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b')
        (nlFr mpC ctx d ns ψ ρ xs b') c) t → G b' c t y) →
    Adm b G (nlFr mpC ctx d ns ψ ρ xs b)
  trans : ∀ b, b < ns.length + 1 → ∀ G,
    (∀ b' c t y, G b' c t y →
      y ∈ˢ app ((lfpSClause (nlDb mpC d ns b') (nlψ envC ns ψ b')
        ((nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b'))).carrier
        (nlFr mpC ctx d ns ψ ρ xs b') c) t) →
    ∀ ρ', Adm b G ρ' → ∀ Y,
    InTupleSpace ((nlDb mpC d ns b).w (nlψ envC ns ψ b)) (nlDb mpC d ns b).N
      ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y →
    TupleLe (nlDb mpC d ns b).N
      ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y
      ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) →
    ∀ t c j fs, c < (nlDb mpC d ns b).N → (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) ρ' Y t c j fs →
      (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)
        ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) t c j fs
  hcall : ∀ c b, c < (tgtRs out).length →
    nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC S okN c b → ∀ t j fs,
    t ∈ˢ (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)
      (tgtClsM mc p out c) →
    (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)
      ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) t
      (tgtClsM mc p out c) j fs →
    ∀ c' t' y, c' < (tgtRs out).length → S c' →
      t' ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC p out ψ ρ xs c' →
      y ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC p out ψ ρ xs c') t' →
      tgtCall μ F (mkFEnv envC) p formerTys out mpC.base2.acval envC ψ
        (tgtClsTup d Dc mc cvc p out ψ) ρ xs c j fs (tagged c' t' y) →
      ∃ b', nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC S okN c' b' ∧
        NodeLands (ns.length + 1) (nlDb mpC d ns) (nlψ envC ns ψ)
          (nlFr mpC ctx d ns ψ ρ xs) (nlDp ns) Adm b (tgtClsM mc p out c) t j fs b'
          (tgtClsM mc p out c') t' y

/-! ## A clause's own `trans`, and the fit's dependence on the tuple -/

section Dyn

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V} {ψ : Name → Nat}

/-- **`trans` at the TRUE frame itself** (node `0`, whose only admissible
frame is its true one): the clause's `fitsMono` along `Y ≤ carrier`. -/
theorem lfp_trans_self (hcl : LfpClause acval D) {F : Nat → V}
    (hsat : Sat V (D.params ψ).reverse F) {Y : Nat → V}
    (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ F) Y)
    (hle : TupleLe D.N (D.idx ψ F) Y (D.carrier ψ F)) {t : V} {c j : Nat} {fs : List V}
    (hc : c < D.N) (hf : D.HFits ψ F Y t c j fs) : D.HFits ψ F (D.carrier ψ F) t c j fs :=
  hcl.fitsMono ψ F hsat Y _ hY (lfpTuple_mem _ _ _ _) hle c hc t j fs hf

/-- **The hole fit reads the tuple only at the members**: the hole frame
holds one hole value per MEMBER (`LfpDatum.frame`), each reading its own
component. -/
theorem LfpDatum.frame_congr_members {ρp X X' : Nat → V} (h : ∀ m, m < D.k → X m = X' m) :
    D.frame ψ ρp X = D.frame ψ ρp X' := by
  unfold LfpDatum.frame
  congr 1
  refine List.map_congr_left fun m hm => ?_
  have hmk : m < D.k := List.mem_range.mp hm
  unfold LfpDatum.holeVal
  rw [h m hmk]

theorem LfpDatum.hfits_congr_members {ρp X X' : Nat → V} (h : ∀ m, m < D.k → X m = X' m)
    {t : V} {c j : Nat} {fs : List V} : D.HFits ψ ρp X t c j fs ↔ D.HFits ψ ρp X' t c j fs := by
  unfold LfpDatum.HFits
  rw [LfpDatum.frame_congr_members h]

end Dyn

section Build

variable {envC : Env} {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V}
  {p : BlockShape} {formerTys : List Expr} {out : List (ConstantVal × TargetMajor × List Expr)}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal} {ns : List PosTree}
  {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {F : Nat}

theorem getD_mem_of_lt {ns : List PosTree} {b : Nat} (h0 : 0 < b) (hb : b ≤ ns.length) :
    ns.getD (b - 1) default ∈ ns := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.getElem_mem _

/-- **The class tie at a related pair** (outside arm: `tgtNodeTie`). -/
theorem nlRel_tie (hcov : LfpCover mpC [])
    (hF : NodeListFacts mpC ctx ns)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    (hnP : ∀ c, c < (tgtRs out).length → ctx.nP ≤ tgtRP p c)
    (hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC p (tgtRs out) ψ c).length = tgtRP p c)
    {okC : Nat → Prop} {okN : Nat → PosTree → Prop} {c b : Nat} (hc : c < (tgtRs out).length)
    (hR : nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC okC okN c b) :
    tgtClsD d Dc out c = nlDb mpC d ns b ∧ tgtClsψ cvc out ψ c = nlψ envC ns ψ b ∧
      tgtClsFr d mpC.base2.acval envC p out ψ ρ xs c = nlFr mpC ctx d ns ψ ρ xs b := by
  obtain ⟨hg, ⟨hm, rfl⟩ | ⟨h0, hbl, hNM, -⟩, -⟩ := hR
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [tgtClsD, tgtClsψ, tgtClsFr, hm, if_true, nlDb, nlψ, nlFr]
  · have hb0 : b ≠ 0 := by omega
    simp only [nlDb, nlψ, nlFr, hb0, if_false]
    have ht := getD_mem_of_lt h0 hbl
    have hMo : (tgtMajor out c).member = none := hNM.1
    have hxs : xs.length = tgtRP p c := by
      have hg' := hg
      simp only [tgtClsG, hMo, Option.isSome_none, Bool.false_eq_true, if_false] at hg'
      rw [SpineFit.length_eq hg', hpd c hc]
    obtain ⟨dsa, hsp⟩ := hF.sp _ ht ψ
    obtain ⟨D, hD, h1, h2⟩ := hF.blk _ ht _ hNM.2.1
    have hlps := hF.lps _ ht _ hNM.2.1
    exact tgtNodeTie hcov (hcls c hc hMo) (hsel c hc hMo) hNM ⟨D, hD, h1, h2⟩ hlps
      (hF.read _ ht) (hF.ws _ ht) hsp (hnP c hc) hxs

/-- **THE NODE PRESENTATION OVER A NODE LIST**, its static part proved,
its dynamic part (`Adm`, `hAdm`, `top`, `trans`, `hcall`) the premises;
its relation is `nlRel` at `okN`. -/
theorem tgtNodePres_of_list {S : Nat → Prop} {okN : Nat → PosTree → Prop} (hcov : LfpCover mpC []) (hd0 : d.toLfp ∈ mpC.lfpBlocks)
    (hF : NodeListFacts mpC ctx ns)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    (hnP : ∀ c, c < (tgtRs out).length → ctx.nP ≤ tgtRP p c)
    (hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC p (tgtRs out) ψ c).length = tgtRP p c)
    (hmemk : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member.isSome = true →
      p.recTgtAt c < d.toLfp.N)
    (hnCt : ∀ c, c < (tgtRs out).length →
      blockRecNCt (tgtRs out) c = (tgtClsD d Dc out c).nctors (tgtClsM mc p out c))
    (Dy : TgtNodeDyn μ F mpC ctx d p formerTys out Dc mc cvc ns ψ ρ xs S okN) :
    ∃ P : TgtNodePres μ F envC mpC.base2.acval p formerTys out d Dc mc cvc ψ ρ xs S,
      ∀ c b, P.Rel c b ↔ nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC S okN c b := by
  have htie := fun (c b : Nat) (hc : c < (tgtRs out).length)
      (hR : nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC S okN c b) =>
    nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel hnP hpd hc hR
  have hmemB : ∀ b, b < ns.length + 1 → nlDb mpC d ns b ∈ mpC.lfpBlocks := by
    intro b _
    unfold nlDb
    split
    · exact hd0
    · exact lfpSel_mem_blocks hd0 _
  refine ⟨{
    nC := ns.length + 1
    Db := nlDb mpC d ns
    ψb := nlψ envC ns ψ
    frb := nlFr mpC ctx d ns ψ ρ xs
    dp := nlDp ns
    Dd := nlDd ns
    hD := nlDp_lt ns
    Adm := Dy.Adm
    hcl := fun b hb => mpC.lfpClause_of_mem (hmemB b hb)
    hAdm := Dy.hAdm
    top := Dy.top
    trans := Dy.trans
    Rel := nlRel mpC.base2.acval ctx d p out ns ψ ρ xs envC S okN
    mOf := fun c _ => tgtClsM mc p out c
    hb := fun c b _ hR => by
      obtain ⟨-, ⟨-, rfl⟩ | ⟨-, hbl, -⟩, -⟩ := hR
      · omega
      · omega
    hm := fun c b hc hR => by
      have hD := (htie c b hc hR).1
      rw [← hD]
      obtain ⟨-, ⟨hm, rfl⟩ | ⟨-, -, hNM, -⟩, -⟩ := hR
      · simp only [tgtClsD, tgtClsM, hm, if_true]
        exact hmemk c hc hm
      · have hMo := hNM.1
        have hMo' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
        have hcl := hcls c hc hMo
        simp only [tgtClsD, tgtClsM, hMo', Bool.false_eq_true, if_false]
        exact Nat.lt_of_lt_of_le hcl.hmm (mpC.lfpClause_of_mem hcl.hD).kN
    hDb := fun c b hc hR => (htie c b hc hR).1
    hψb := fun c b hc hR => (htie c b hc hR).2.1
    hfr := fun c b hc hR => (htie c b hc hR).2.2
    hmc := fun _ _ _ _ => rfl
    hG := fun _ _ _ hR => hR.1
    hnCt := fun c b hc hR t j fs hf => by
      rw [hnCt c hc, (htie c b hc hR).1]
      exact hf.1
    hcall := Dy.hcall }, fun _ _ => Iff.rfl⟩

/-- **The node presentation over a node list, reading every node and
every call**: it covers every guarded class once `NodeListCover` holds. -/
theorem tgtNodePres_of_list_hex (hcov : LfpCover mpC []) (hd0 : d.toLfp ∈ mpC.lfpBlocks)
    (hF : NodeListFacts mpC ctx ns)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    (hnP : ∀ c, c < (tgtRs out).length → ctx.nP ≤ tgtRP p c)
    (hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC p (tgtRs out) ψ c).length = tgtRP p c)
    (hmemk : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member.isSome = true →
      p.recTgtAt c < d.toLfp.N)
    (hnCt : ∀ c, c < (tgtRs out).length →
      blockRecNCt (tgtRs out) c = (tgtClsD d Dc out c).nctors (tgtClsM mc p out c))
    (Dy : TgtNodeDyn μ F mpC ctx d p formerTys out Dc mc cvc ns ψ ρ xs (fun _ => True)
      (fun _ _ => True))
    (hcover : NodeListCover mpC.base2.acval envC ctx d p out ns ψ ρ xs) :
    ∃ P : TgtNodePres μ F envC mpC.base2.acval p formerTys out d Dc mc cvc ψ ρ xs
        (fun _ => True),
      TgtNodeHex P := by
  obtain ⟨P, hP⟩ := tgtNodePres_of_list hcov hd0 hF hcls hsel hnP hpd hmemk hnCt Dy
  refine ⟨P, fun c hc hg => ?_⟩
  by_cases hm : (tgtMajor out c).member.isSome = true
  · exact ⟨0, (hP c 0).mpr ⟨hg, Or.inl ⟨hm, rfl⟩, trivial⟩⟩
  · have hMo : (tgtMajor out c).member = none := by
      cases h : (tgtMajor out c).member with
      | none => rfl
      | some _ => rw [h] at hm; exact absurd rfl hm
    obtain ⟨t, ht, hNM⟩ := hcover c hc hMo hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    refine ⟨i + 1, (hP c (i + 1)).mpr ⟨hg, Or.inr ⟨by omega, by omega, ?_, trivial⟩, trivial⟩⟩
    rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
    exact hNM

end Build

end ConLeche.Model
