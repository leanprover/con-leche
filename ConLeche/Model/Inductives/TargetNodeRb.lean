module

public import ConLeche.Model.Inductives.HoleSubst
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
`0 ..< nP`, member `t` at the hole `nP + t`, the `i`-th hole of the
frames at its occurrence (`occ.reverse[i]`) at `hiAt 0 + i`.  A recursor
major (`TargetMajor`) names the same instantiation CONCRETELY: members
and enclosing containers as constants.  Every hole stands for ONE
constant — a member for itself at the block's own levels, a frame's
hole for its group member at the frame's key levels — so the key READ
BACK is the key with those constants substituted for the holes
(`nodeRb`, `substAll`), and the class → node relation (`NodeMajor`)
is the recursor check's class match against the read-back key: the major
is a member of the node's group, its levels and parameters match the
key's per component (`ClassMatches`).

The reading of a read-back key is the key's own reading at the TRUE
valuation — the parameters, then each hole at its constant's value
(`nodeTrueVal`): `keyFrame_readback` (the substitution lemma iterated,
`denoteMeta_substAll`, then `interp_instAll`).  That is the class tie's
frame (`tgtClsFr` at an outside major) at a node: no recursion down the
forest is needed, a hole's true value is its constant's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole NestKey PosTree TargetMajor)

universe w

/-! ## The read-back, syntactically -/

/-- **The constants the holes at the frame stack `occ` stand for**: the
members at the block's own levels (holes `nP ..< hiAt 0`), then each
frame hole's group member at its key's levels (`hiAt 0 + i` ↦
`occ.reverse[i]`). -/
@[expose] def nodeHoleConsts (ctx : NestCtx) (occ : List NestHole) : List Expr :=
  ctx.names.map (fun n => Expr.const n (ctx.lps.map Level.param)) ++
    occ.reverse.map fun h => Expr.const h.key.cname h.key.lvls

theorem nodeHoleConsts_length (ctx : NestCtx) (occ : List NestHole) :
    (nodeHoleConsts ctx occ).length = ctx.names.length + occ.length := by
  simp [nodeHoleConsts]

theorem nodeHoleConsts_const (ctx : NestCtx) (occ : List NestHole) :
    ∀ a ∈ nodeHoleConsts ctx occ, ∃ n us, a = Expr.const n us := by
  intro a ha
  simp only [nodeHoleConsts, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨n, -, rfl⟩ | ⟨h, -, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- **A key's term read back** at its frame stack `occ`: every hole
replaced by its constant. -/
@[expose] def nodeRb (ctx : NestCtx) (occ : List NestHole) (e : Expr) : Expr :=
  substAll ctx.nP (nodeHoleConsts ctx occ) e

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
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The true valuation at a frame stack**: the parameters (the prefix
spine's first `nP` values), then every hole at its constant's value. -/
@[expose] noncomputable def nodeTrueVal (nP : Nat) (hv : List AnnotTerm) (xs : List V)
    (ρ : Nat → V) : Nat → V :=
  consList (xs.take nP ++ hv.map (interp V ρ)) ρ

/-- **One read-back term, read**: at a prefix spine of length `rP ≥ nP`,
the read-back term's reading is the term's own reading at the true
valuation. -/
theorem interp_readback
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {nP rP : Nat} (hPr : nP ≤ rP) {as : List Expr} {hv : List AnnotTerm}
    (hl : as.length = hv.length)
    (has : ∀ (i : Nat) (a : Expr) (x : AnnotTerm), as[i]? = some a → hv[i]? = some x →
      Expr.WScoped 0 a ∧ a.looseBVarsBounded 0 = true ∧
        ∀ d, denoteMeta acval env φ d a = some x)
    (hcl : ∀ x ∈ hv, ∀ σ σ' : Nat → V, interp V σ x = interp V σ' x)
    {e : Expr} (he : Expr.WScoped (nP + as.length) e) {ea : AnnotTerm}
    (hea : denoteMeta acval env φ (nP + as.length) e = some ea)
    (xs : List V) (hxs : xs.length = rP) (ρ : Nat → V) :
    ∃ eb, denoteMeta acval env φ rP (substAll nP as e) = some eb ∧
      interp V (consList xs ρ) eb = interp V (nodeTrueVal nP hv xs ρ) ea := by
  have hfb : Expr.fvarsBelow (rP + as.length) e :=
    (Expr.WScoped.mono (by omega) he).fvarsBelow
  rw [denoteMeta_substAll hacl hainst as hv hl has nP rP e hPr hfb,
    denoteMeta_lift hacl he (rP + as.length) (by omega), hea]
  refine ⟨_, rfl, ?_⟩
  have hsplit : consList xs ρ = consList (xs.drop nP) (consList (xs.take nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hdl : (xs.drop nP).length = rP - nP := by rw [List.length_drop, hxs]
  rw [hsplit, show rP - nP = (xs.drop nP).length from hdl.symm,
    interp_instAll hv (hv.map (interp V ρ)) (by simp)
      (fun i x h hx hh σ => by
        rw [List.getElem?_map, hx, Option.map_some, Option.some.injEq] at hh
        subst hh
        exact hcl x (List.mem_of_getElem? hx) σ ρ) _ (xs.drop nP) (consList (xs.take nP) ρ),
    show rP + as.length - (nP + as.length) = (xs.drop nP).length by omega,
    interp_liftN_consList, nodeTrueVal, consList_append]

/-- **THE READ-BACK FRAME**: a major whose parameters are a key's read
back (up to erasure), read at a prefix spine of length `rP ≥ nP`, has the
key frame the key has at the true valuation. -/
theorem keyFrame_readback
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {nP rP : Nat} (hPr : nP ≤ rP) {as : List Expr} {hv : List AnnotTerm}
    (hl : as.length = hv.length)
    (has : ∀ (i : Nat) (a : Expr) (x : AnnotTerm), as[i]? = some a → hv[i]? = some x →
      Expr.WScoped 0 a ∧ a.looseBVarsBounded 0 = true ∧
        ∀ d, denoteMeta acval env φ d a = some x)
    (hcl : ∀ x ∈ hv, ∀ σ σ' : Nat → V, interp V σ x = interp V σ' x) :
    ∀ {ds : List Expr} {dsa : List AnnotTerm} {dsM : List Expr},
      (∀ x ∈ ds, Expr.WScoped (nP + as.length) x) →
      DenoteMetaSpine acval env φ (nP + as.length) ds dsa →
      Expr.ErasedEqL dsM (ds.map (substAll nP as)) →
      ∀ (xs : List V), xs.length = rP → ∀ ρ : Nat → V,
      keyFrame (dsM.map fun x => (denoteMeta acval env φ rP x).getD default) rP (consList xs ρ)
        = keyFrame dsa (nP + as.length) (nodeTrueVal nP hv xs ρ) := by
  intro ds dsa dsM hws hsp hE xs hxs ρ
  have htl : (fun j => consList xs ρ (j + rP)) = fun j => nodeTrueVal nP hv xs ρ (j + (nP + as.length)) := by
    funext j
    have h1 : consList xs ρ (j + rP) = ρ j := by rw [← hxs, consList_apply_add]
    have h2 : (xs.take nP ++ hv.map (interp V ρ)).length = nP + as.length := by
      simp [List.length_take, hxs, hl]; omega
    rw [h1, nodeTrueVal, ← h2, consList_apply_add]
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
    | m :: ms, hE =>
      obtain ⟨hm, hms⟩ := hE
      obtain ⟨eb, heb, hint⟩ := interp_readback hacl hainst hPr hl has hcl
        (hws a List.mem_cons_self) ha xs hxs ρ
      simp only [List.map_cons, Function.comp_apply]
      rw [denoteMeta_erasedEq hm rP, heb, Option.getD_some, hint,
        ih (fun x hx => hws x (List.mem_cons_of_mem _ hx)) hms]

end Read

end ConLeche.Model
