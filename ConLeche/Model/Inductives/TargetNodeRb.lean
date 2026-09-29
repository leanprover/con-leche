module

public import ConLeche.Model.Inductives.HoleSubst
import ConLeche.Verify.Inductives.NestCallSyn
public import ConLeche.Verify.Inductives.NestNfScope
public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Inductives.ContSubst
public import ConLeche.Model.Inductives.ContN2
public import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Verify.Inductives.PosNodes
public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.ContFrame

public section

/-!
# A node's key, READ BACK

The positivity walk keys a node by its instantiation in the walk's
representation (`PosTree.key`): the block's parameters at the variables
`0 ..< nP`, member `t`'s hole at `nP + t`, the `i`-th hole of the frames at
its occurrence (`occ.reverse[i]`) at `hiAt 0 + i`.  A recursor major
(`TargetMajor`) names the same instantiation CONCRETELY.  Every hole stands
for a WHOLE application — a member hole for the member at the block's own
levels applied to the block's parameters, a frame's hole for its group
member at the frame's key applied to the key's parameters, read back — so
the key READ BACK is the key with those applications substituted for the
holes: the kernel's own read-back (`nestHoleImg`, `nodeRb`), and the class
→ node relation (`NodeMajor`) is the recursor check's class match against
the read-back key: the major is a member of the node's group, its levels
and parameters match the key's per component (`ClassMatches`).

The read-back is ONE parallel substitution up to the variables'
annotations (`nodeRb_erasedEq_substFvars`: parameters to themselves, holes
to their applications, `nodeImg`), whose images all read at one depth
`rP ≥ nP` (a recursor's prefix); so a read-back key's reading is the key's
own reading at the substituted valuation (`denoteMeta_substFvars`):
`interp_readback`, `keyFrame_readback`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole NestKey PosTree TargetMajor)

universe w

/-! ## The read-back, syntactically -/

/-- **A key's term read back** at its frame stack `occ`: every hole
replaced by the whole application it stands for (the kernel's
`nestHoleImg`). -/
@[expose] def nodeRb (ctx : NestCtx) (occ : List NestHole) (e : Expr) : Expr :=
  e.replaceFVars (ConLeche.nestHoleImg ctx occ)

/-- No hole's read-back below the parameters' range. -/
theorem nestHoleImg_none_of_lt {ctx : NestCtx} {i : Nat} (hi : i < ctx.nP) :
    ∀ prog : List NestHole, ConLeche.nestHoleImg ctx prog i = none
  | [] => by simp only [ConLeche.nestHoleImg]; rw [if_neg (by omega)]
  | h :: prog => by
    simp only [ConLeche.nestHoleImg]
    rw [if_neg (by simp [NestCtx.hiAt]; omega)]
    exact nestHoleImg_none_of_lt hi prog

/-- A hole's read-back does not see the frames above it. -/
theorem nestHoleImg_append {ctx : NestCtx} (X anc : List NestHole) {v : Nat}
    (hv : v < ctx.hiAt anc.length) :
    ConLeche.nestHoleImg ctx (X ++ anc) v = ConLeche.nestHoleImg ctx anc v := by
  induction X with
  | nil => rfl
  | cons h X ih =>
    simp only [List.cons_append, ConLeche.nestHoleImg]
    rw [if_neg (by simp [NestCtx.hiAt, List.length_append] at hv ⊢; omega)]
    exact ih

/-- **The read-back's images**, as one substitution: a parameter variable
stays (annotated `Sort 0`), a hole its application. -/
@[expose] def nodeImg (ctx : NestCtx) (occ : List NestHole) (i : Nat) : Expr :=
  if i < ctx.nP then .fvar i (.sort .zero) else (ConLeche.nestHoleImg ctx occ i).getD default

/-- **The read-back is one parallel substitution**, up to the variables'
annotations, below the frame stack's holes. -/
theorem nodeRb_erasedEq_substFvars {ctx : NestCtx} {occ : List NestHole} {D : Nat}
    {x : Expr} (hx : x.fvarsBelow (ctx.hiAt occ.length)) :
    Expr.ErasedEq (nodeRb ctx occ x) (Expr.substFvars (ctx.hiAt occ.length) D (nodeImg ctx occ) x) := by
  refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) x hx
  by_cases h1 : v < ctx.nP
  · rw [nestHoleImg_none_of_lt h1]
    simp only [nodeImg, if_pos h1, Option.getD_none]
    simp [Expr.ErasedEq]
  · obtain ⟨e, he⟩ := ConLeche.nestHoleImg_isSome (Nat.le_of_not_lt h1) occ hv
    simp only [nodeImg, if_neg h1, he, Option.getD_some]
    exact Expr.ErasedEq.rfl _

/-- **A class matches an instantiation** (`targetClassMatch` passed, at the
verified fueled instantiation): levels up to `Level.isEquivList`, every
parameter defeq with the members abstracted, over the class's
recursor-prefix openers. -/
@[expose] def ClassMatches (F : Nat) (envC : Env) (p : ConLeche.BlockShape)
    (formerTys : List Expr) (M : TargetMajor) (lvls : List Level) (eds : List Expr) : Prop :=
  ConLeche.targetClassMatch (ConLeche.fueledOps .verified F) envC p formerTys M.pfvs M.lvls M.ds
    lvls eds = .ok true

/-- **The class → node relation**: the (outside) major names a member of
the node's group and MATCHES the node's key read back, per component
(`ClassMatches`, ruling 2026-09-27). -/
@[expose] def NodeMajor (F : Nat) (envC : Env) (p : ConLeche.BlockShape) (formerTys : List Expr)
    (ctx : NestCtx) (M : TargetMajor) (t : PosTree) : Prop :=
  M.member = none ∧ M.ind ∈ t.grp.map (·.1) ∧
    ClassMatches F envC p formerTys M t.key.lvls (t.key.ds.map (nodeRb ctx t.occ))

/-! ## The read-back, read -/

section Read

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **The read-back's images, read** at the depth `d`. -/
@[expose] noncomputable def nodeImgX (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (occ : List NestHole) (d : Nat) : Nat → AnnotTerm :=
  fun i => (denoteMeta m.acval env φ d (nodeImg ctx occ i)).getD .prf

/-- **The images are scoped** at the block's parameters (a parameter
variable, or an application mentioning only the canonical parameters), so
they read at every depth `rP ≥ nP` where they read at all. -/
theorem nodeImg_hs (m : EnvModel V env) {ctx : NestCtx} {occ : List NestHole} {rP : Nat}
    (hPr : ctx.nP ≤ rP) (hpar : ∀ x ∈ ctx.params, ConLeche.ScB ctx.nP x)
    (hsc : ConLeche.ProgScB ctx occ)
    (hread : ∀ i, i < ctx.hiAt occ.length →
      ∃ x, denoteMeta m.acval env φ rP (nodeImg ctx occ i) = some x) :
    ∀ i, i < ctx.hiAt occ.length → Expr.WScoped rP (nodeImg ctx occ i) ∧
      (nodeImg ctx occ i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ rP (nodeImg ctx occ i) = some (nodeImgX m φ ctx occ rP i) := by
  intro i hi
  have hsb : ConLeche.ScB ctx.nP (nodeImg ctx occ i) := by
    unfold nodeImg
    split
    · rename_i h1
      exact ConLeche.ScB.fvar h1 (ConLeche.ScB.sort i _)
    · rename_i h1
      obtain ⟨e, he⟩ := ConLeche.nestHoleImg_isSome (Nat.le_of_not_lt h1) occ hi
      rw [he, Option.getD_some]
      exact (ConLeche.nestHoleImg_scb hpar occ hsc).1 i e he
  obtain ⟨x, hx⟩ := hread i hi
  refine ⟨Expr.WScoped.mono hPr hsb.1, hsb.2, ?_⟩
  unfold nodeImgX
  rw [hx]; rfl

/-- **One read-back term, read**: at a depth `rP` where the images read, the
read-back term's reading is the term's own reading at the substituted
valuation. -/
theorem interp_readback (m : EnvModel V env) {ctx : NestCtx} {occ : List NestHole} {rP : Nat}
    (hs : ∀ i, i < ctx.hiAt occ.length → Expr.WScoped rP (nodeImg ctx occ i) ∧
      (nodeImg ctx occ i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ rP (nodeImg ctx occ i) = some (nodeImgX m φ ctx occ rP i))
    {e : Expr} (he : Expr.WScoped (ctx.hiAt occ.length) e) {ea : AnnotTerm}
    (hea : denoteMeta m.acval env φ (ctx.hiAt occ.length) e = some ea) (σ : Nat → V) :
    ∃ eb, denoteMeta m.acval env φ rP (nodeRb ctx occ e) = some eb ∧
      interp V σ eb = interp V (substE V (substTau (ctx.hiAt occ.length) rP
        (nodeImgX m φ ctx occ rP)) 0 σ) ea := by
  have hfb : Expr.fvarsBelow (ctx.hiAt occ.length) e := he.fvarsBelow
  rw [denoteMeta_erasedEq (nodeRb_erasedEq_substFvars (D := rP) hfb) rP]
  have h := denoteMeta_substFvars m hs e 0 (by rw [Nat.add_zero]; exact hfb)
  rw [Nat.add_zero, Nat.add_zero, hea, Option.map_some] at h
  exact ⟨_, h, interp_substAV V _ _ _ _⟩

/-- **THE READ-BACK FRAME**: a major whose parameters are a key's read
back (up to erasure), read at a depth `rP` where the images read, has the
key frame the key has at the substituted valuation. -/
theorem keyFrame_readback (m : EnvModel V env) {ctx : NestCtx} {occ : List NestHole} {rP : Nat}
    (hs : ∀ i, i < ctx.hiAt occ.length → Expr.WScoped rP (nodeImg ctx occ i) ∧
      (nodeImg ctx occ i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ rP (nodeImg ctx occ i) = some (nodeImgX m φ ctx occ rP i)) :
    ∀ {ds : List Expr} {dsa : List AnnotTerm} {dsM : List Expr},
      (∀ x ∈ ds, Expr.WScoped (ctx.hiAt occ.length) x) →
      DenoteMetaSpine m.acval env φ (ctx.hiAt occ.length) ds dsa →
      Expr.ErasedEqL dsM (ds.map (nodeRb ctx occ)) → ∀ σ : Nat → V,
      keyFrame (dsM.map fun x => (denoteMeta m.acval env φ rP x).getD default) rP σ
        = keyFrame dsa (ctx.hiAt occ.length)
            (substE V (substTau (ctx.hiAt occ.length) rP (nodeImgX m φ ctx occ rP)) 0 σ) := by
  intro ds dsa dsM hws hsp hE σ
  have htl : (fun j => σ (j + rP)) = fun j => substE V (substTau (ctx.hiAt occ.length) rP
      (nodeImgX m φ ctx occ rP)) 0 σ (j + ctx.hiAt occ.length) := by
    funext j
    have := substE_substTau (V := V) (nP := 0) (k := ctx.hiAt occ.length) (D' := rP)
      (nodeImgX m φ ctx occ rP) σ
    rw [Nat.zero_add] at this
    rw [this, show j + ctx.hiAt occ.length = j + ((List.range (ctx.hiAt occ.length)).map fun mm =>
      interp V σ (nodeImgX m φ ctx occ rP (0 + mm))).length by simp, consList_apply_add]
    simp
  unfold keyFrame
  rw [htl]
  congr 1
  rw [List.map_map]
  induction hsp generalizing dsM with
  | nil =>
    match dsM, hE with
    | [], _ => rfl
  | @cons a v as' vs ha _ ih =>
    match dsM, hE with
    | mm :: ms, hE =>
      obtain ⟨hm, hms⟩ := hE
      obtain ⟨eb, heb, hint⟩ := interp_readback m hs (hws a List.mem_cons_self) ha σ
      simp only [List.map_cons, Function.comp_apply]
      rw [denoteMeta_erasedEq hm rP, heb, Option.getD_some, hint,
        ih (fun x hx => hws x (List.mem_cons_of_mem _ hx)) hms]

end Read

end ConLeche.Model
