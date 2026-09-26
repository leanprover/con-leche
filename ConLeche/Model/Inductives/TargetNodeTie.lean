module

public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Model.Inductives.TargetClasses

public section

/-!
# The class tie at a node, from the read-back

A node of the positivity walk (`PosTree`) presents its instantiation as
ONE recorded clause: the block `lfpSel` selects for the key's container
(`lfpSel`), at the key's levels (`nodeψ`), at the key frame read at the
TRUE valuation (`nodeFr`: the parameters, then every hole at its
constant's value, `nodeTrueVal`).  An outside recursor class whose major
is the node's key read back (`NodeMajor`) has exactly these data
(`tgtNodeTie`): its block by the canonical selection (a group-mate of the
key's container is in the same recorded block), its levels by the key's,
its frame by `keyFrame_readback`.  This is the SEMANTIC tie of the node
presentation (`TgtNodePres.hDb/hψb/hfr`) at a syntactically related pair.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole NestKey PosTree TargetMajor ConstantVal
  BlockShape CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- A stored constant's level parameters (`[]` if none). -/
@[expose] def lpsOf (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

section Node

variable (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ctx : NestCtx)
  (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- The holes' constants at a frame stack, read (closed terms). -/
@[expose] def nodeHv (occ : List NestHole) : List AnnotTerm :=
  (nodeHoleConsts ctx occ).map fun a => (denoteMeta acval envC ψ 0 a).getD default

/-- **A node's level assignment**: the key's levels over its container's
level parameters. -/
@[expose] def nodeψ (t : PosTree) : Name → Nat :=
  Level.substFn ψ (lpsOf envC t.key.cname) t.key.lvls

/-- **A node's TRUE frame**: its key's parameters read at its stack's
depth, at the true valuation. -/
@[expose] noncomputable def nodeFr (t : PosTree) : Nat → V :=
  keyFrame (t.key.ds.map fun x =>
      (denoteMeta acval envC ψ (ctx.nP + (nodeHoleConsts ctx t.occ).length) x).getD default)
    (ctx.nP + (nodeHoleConsts ctx t.occ).length)
    (nodeTrueVal ctx.nP (nodeHv acval envC ctx ψ t.occ) xs ρ)

end Node

/-- **The holes' constants are read** at a stack: every one stored, at its
level parameters' arity. -/
@[expose] def NodeHolesRead (envC : Env) (ctx : NestCtx) (occ : List NestHole) : Prop :=
  ∀ a ∈ nodeHoleConsts ctx occ, ∃ n us ci, a = Expr.const n us ∧ envC.find? n = some ci ∧
    us.length = ci.toConstantVal.levelParams.length

/-- Read holes read at every depth to their `nodeHv` entry. -/
theorem nodeHv_reads {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env} {ctx : NestCtx}
    {ψ : Name → Nat} {occ : List NestHole} (h : NodeHolesRead envC ctx occ) :
    ∀ (i : Nat) (a : Expr) (x : AnnotTerm), (nodeHoleConsts ctx occ)[i]? = some a →
      (nodeHv acval envC ctx ψ occ)[i]? = some x →
      Expr.WScoped 0 a ∧ a.looseBVarsBounded 0 = true ∧
        ∀ d, denoteMeta acval envC ψ d a = some x := by
  intro i a x ha hx
  obtain ⟨n, us, ci, rfl, hf, hl⟩ := h _ (List.mem_of_getElem? ha)
  rw [nodeHv, List.getElem?_map, ha, Option.map_some, Option.some.injEq,
    denoteMeta_const hf hl, Option.getD_some] at hx
  subst hx
  exact ⟨by simp [Expr.WScoped], rfl, fun d => denoteMeta_const hf hl⟩

/-- **THE CLASS TIE AT A NODE**: an outside recursor class whose major is
the node's key read back (`NodeMajor`), guarded at the prefix spine
`xs` (so `xs` is the rule prefix), with the canonically selected block,
reads the node's block, levels and true frame. -/
theorem tgtNodeTie {envC : Env} {mpC : EnvModelM V μ envC} {ex : List Name}
    (hcov : LfpCover mpC ex) {D0 : LfpDatum V} {d : BlockData V} {Dc : Nat → LfpDatum V}
    {mc : Nat → Nat} {cvc : Nat → ConstantVal} {p : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} {ctx : NestCtx} {t : PosTree} {c : Nat}
    (hcls : TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : Dc c = lfpSel mpC D0 (tgtMajor out c).ind)
    (hR : NodeMajor ctx (tgtMajor out c) t)
    -- the node's facts
    (hblk : ∃ D ∈ mpC.lfpBlocks, t.key.cname ∈ D.names ∧ (tgtMajor out c).ind ∈ D.names)
    (hlps : lpsOf envC t.key.cname = lpsOf envC (tgtMajor out c).ind)
    (hread : NodeHolesRead envC ctx t.occ)
    (hws : ∀ x ∈ t.key.ds, Expr.WScoped (ctx.nP + (nodeHoleConsts ctx t.occ).length) x)
    {dsa : List AnnotTerm}
    (hsp : DenoteMetaSpine mpC.base2.acval envC ψ (ctx.nP + (nodeHoleConsts ctx t.occ).length)
      t.key.ds dsa)
    -- the prefix
    (hnP : ctx.nP ≤ tgtRP p c) (hxs : xs.length = tgtRP p c) :
    tgtClsD d Dc out c = lfpSel mpC D0 t.key.cname ∧
    tgtClsψ cvc out ψ c = nodeψ envC ψ t ∧
    tgtClsFr d mpC.base2.acval envC p out ψ ρ xs c = nodeFr mpC.base2.acval envC ctx ψ ρ xs t := by
  obtain ⟨hMo, -, hlv, hE⟩ := hR
  have hMo' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨D, hD, h1, h2⟩ := hblk
    simp only [tgtClsD, hMo', Bool.false_eq_true, if_false, hsel]
    exact lfpSel_eq_of_mem hcov D0 hD h1 h2
  · obtain ⟨caps, hf⟩ := hcls.hfind
    have hl : (cvc c).levelParams = lpsOf envC (tgtMajor out c).ind := by
      simp only [lpsOf, hf]; rfl
    simp only [tgtClsψ, hMo', Bool.false_eq_true, if_false, nodeψ, hl, hlps, hlv]
  · have hsp' := hsp
    have hdsa : dsa = t.key.ds.map fun x =>
        (denoteMeta mpC.base2.acval envC ψ (ctx.nP + (nodeHoleConsts ctx t.occ).length) x).getD
          default := denoteMetaSpine_eq_map hsp
    simp only [tgtClsFr, hMo', Bool.false_eq_true, if_false, tgtOutDsa, nodeFr]
    rw [← hdsa]
    have hlen : (nodeHoleConsts ctx t.occ).length = (nodeHv mpC.base2.acval envC ctx ψ t.occ).length := by
      simp [nodeHv]
    have := keyFrame_readback (V := V) mpC.base2.acval_closed (acval_inst_self mpC.base2) hnP hlen
      (nodeHv_reads hread)
      (fun x hx σ σ' => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        obtain ⟨n, us, ci, rfl, hf, hl⟩ := hread a ha
        rw [denoteMeta_const hf hl, Option.getD_some]
        exact acval_interp_closed mpC.base2 n _ σ σ')
      hws hsp' hE xs hxs ρ
    exact this

end ConLeche.Model
