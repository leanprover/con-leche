module

public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetDefeqTie
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.Level
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The class tie at a node, from the read-back

A node of the positivity walk (`PosTree`) presents its instantiation as
ONE recorded clause: the block `lfpSel` selects for the key's container
(`lfpSel`), at the key's levels (`nodeψ`), at the key frame read at the
TRUE valuation (`nodeFr`: the parameters, then every hole at its
constant's value, `nodeTrueVal`).  An outside recursor class whose major
matches the node's key read back (`NodeMajor`) has exactly these data
(`tgtNodeTie`): its block by the canonical selection (a group-mate of the
key's container is in the same recorded block), its levels by the key's
up to `Level.isEquivList` (one level assignment), its frame because its
parameters read as the read-back key's (the match's defeq soundness,
`TargetDefeqTie.lean`, handed in as `hfr`) and those read as the key at
the true valuation (`keyFrame_readback`).  This is the SEMANTIC tie of
the node presentation (`TgtNodePres.hDb/hψb/hfr`) at a related pair.
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

/-- **The true valuation at a frame stack**: the prefix spine's first `nP`
values (the parameters), then every hole at its read-back's value at the
prefix. -/
@[expose] noncomputable def nodeTrueVal (nP : Nat) (hv : List AnnotTerm) (xs : List V)
    (ρ : Nat → V) : Nat → V :=
  consList (xs.take nP ++ hv.map (interp V (consList xs ρ))) ρ

section Node

variable (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ctx : NestCtx)
  (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- **The holes' read-backs at a frame stack**, read at the depth `d`
(every hole's whole application, over the block's parameters). -/
@[expose] def nodeHv (occ : List NestHole) (d : Nat) : List AnnotTerm :=
  (List.range (ctx.hiAt occ.length - ctx.nP)).map fun i =>
    (denoteMeta acval envC ψ d (nodeImg ctx occ (ctx.nP + i))).getD .prf

/-- **A node's level assignment**: the key's levels over its container's
level parameters. -/
@[expose] def nodeψ (t : PosTree) : Name → Nat :=
  Level.substFn ψ (lpsOf envC t.key.cname) t.key.lvls

/-- **A node's TRUE frame**: its key's parameters read at its stack's
depth, at the true valuation. -/
@[expose] noncomputable def nodeFr (t : PosTree) : Nat → V :=
  keyFrame (t.key.ds.map fun x =>
      (denoteMeta acval envC ψ (ctx.hiAt t.occ.length) x).getD default)
    (ctx.hiAt t.occ.length)
    (nodeTrueVal ctx.nP (nodeHv acval envC ctx ψ t.occ xs.length) xs ρ)

end Node

/-- **The holes' read-backs are read** at a stack, at every depth above the
parameters. -/
@[expose] def NodeHolesRead (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (ctx : NestCtx) (occ : List NestHole) : Prop :=
  (∀ x ∈ ctx.params, ConLeche.ScB ctx.nP x) ∧ ConLeche.ProgScB ctx occ ∧
  ∀ (ψ : Name → Nat) (d : Nat), ctx.nP ≤ d → ∀ i, i < ctx.hiAt occ.length →
    ∃ x, denoteMeta acval envC ψ d (nodeImg ctx occ i) = some x

omit [SetTheory V] in
/-- A read-back image at a longer stack is the shorter one's below it. -/
theorem nodeImg_suffix (ctx : NestCtx) (X anc : List NestHole) {v : Nat}
    (hv : v < ctx.hiAt anc.length) :
    nodeImg ctx (X ++ anc) v = nodeImg ctx anc v := by
  unfold nodeImg
  split
  · rfl
  · rw [ConLeche.nestHoleImg_suffix X anc hv]

omit [SetTheory V] in
theorem progScB_suffix {ctx : NestCtx} :
    ∀ (X anc : List NestHole), ConLeche.ProgScB ctx (X ++ anc) → ConLeche.ProgScB ctx anc
  | [], _, h => h
  | _ :: X, anc, h => progScB_suffix X anc h.2

omit [SetTheory V] in
/-- A read stack's suffix is read. -/
theorem NodeHolesRead.suffix {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {ctx : NestCtx} {X anc : List NestHole} (h : NodeHolesRead acval envC ctx (X ++ anc)) :
    NodeHolesRead acval envC ctx anc :=
  ⟨h.1, progScB_suffix X anc h.2.1, fun ψ d hd i hi => by
    rw [← nodeImg_suffix ctx X anc hi]
    exact h.2.2 ψ d hd i (by simp only [NestCtx.hiAt, List.length_append] at hi ⊢; omega)⟩

/-- Read holes are scoped, bvar-closed and read at every depth above the
parameters (`nodeImg_hs`'s premise). -/
theorem NodeHolesRead.hs {envC : Env} {m : EnvModel V envC} {ctx : NestCtx} {occ : List NestHole}
    (h : NodeHolesRead m.acval envC ctx occ) (ψ : Name → Nat) {d : Nat} (hd : ctx.nP ≤ d) :
    ∀ i, i < ctx.hiAt occ.length → Expr.WScoped d (nodeImg ctx occ i) ∧
      (nodeImg ctx occ i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval envC ψ d (nodeImg ctx occ i) = some (nodeImgX m ψ ctx occ d i) :=
  nodeImg_hs m hd h.1 h.2.1 (h.2.2 ψ d hd)

/-- **A spine read back, read**: at a depth `rP` where the images read, a
spine's read-back reads to terms whose values are the spine's own readings
at the substituted valuation. -/
theorem readback_spine {env : Env} (m : EnvModel V env) {φ : Name → Nat} {ctx : NestCtx}
    {occ : List NestHole} {rP : Nat}
    (hs : ∀ i, i < ctx.hiAt occ.length → Expr.WScoped rP (nodeImg ctx occ i) ∧
      (nodeImg ctx occ i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ rP (nodeImg ctx occ i) = some (nodeImgX m φ ctx occ rP i))
    (σ : Nat → V) :
    ∀ {ds : List Expr} {dsa : List AnnotTerm}, (∀ x ∈ ds, Expr.WScoped (ctx.hiAt occ.length) x) →
      DenoteMetaSpine m.acval env φ (ctx.hiAt occ.length) ds dsa →
      ∃ ebs, DenoteMetaSpine m.acval env φ rP (ds.map (nodeRb ctx occ)) ebs ∧
        ebs.map (interp V σ) = dsa.map (interp V
          (substE V (substTau (ctx.hiAt occ.length) rP (nodeImgX m φ ctx occ rP)) 0 σ))
  | [], [], _, .nil => ⟨[], .nil, rfl⟩
  | x :: ds, a :: dsa, hws, .cons ha hsp => by
    obtain ⟨eb, heb, hint⟩ := interp_readback m hs (hws x List.mem_cons_self) ha σ
    obtain ⟨ebs, hsp', hmap⟩ := readback_spine m hs σ
      (fun y hy => hws y (List.mem_cons_of_mem _ hy)) hsp
    exact ⟨eb :: ebs, .cons heb hsp', by simp only [List.map_cons, hint, hmap]⟩

/-- **The substituted valuation of the read-back IS the true valuation** at
a prefix spine of the substitution's depth. -/
theorem substE_trueVal {n rP nP : Nat} (x : Nat → AnnotTerm) {xs : List V} (ρ : Nat → V)
    (hxs : xs.length = rP) (hnP : nP ≤ n) (hnPr : nP ≤ rP)
    (hpar : ∀ v, v < nP → x v = .bvar (rP - 1 - v)) :
    substE V (substTau n rP x) 0 (consList xs ρ)
      = consList (xs.take nP ++ ((List.range (n - nP)).map fun i => x (nP + i)).map
          (interp V (consList xs ρ))) ρ := by
  have h := substE_substTau (V := V) (nP := 0) (k := n) (D' := rP) x (consList xs ρ)
  simp only [Nat.zero_add, Nat.not_lt_zero, ite_false, Nat.sub_zero] at h
  rw [h]
  have htl : (fun q => consList xs ρ (q + rP)) = ρ := by
    funext q; rw [← hxs, consList_apply_add]
  rw [htl]
  congr 1
  rw [show n = nP + (n - nP) by omega, List.range_add, List.map_append,
    show nP + (n - nP) - nP = n - nP by omega, List.map_map, List.map_map]
  congr 1
  refine List.ext_getElem (by simp [hxs]; omega) fun v h1 h2 => ?_
  have hv : v < nP := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  have hvx : v < xs.length := by omega
  rw [hpar v hv, interp_bvar, consList_getD_of_lt _ _ _ (by omega)]
  subst hxs
  rw [show xs.length - 1 - (xs.length - 1 - v) = v by omega, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hvx, Option.getD_some]

/-- **The read-back valuation at a node's stack IS its true valuation.** -/
theorem substE_nodeImgX_trueVal {envC : Env} (m : EnvModel V envC) (ψ : Name → Nat)
    {ctx : NestCtx} {occ : List NestHole} {xs : List V} (ρ : Nat → V)
    (hnP : ctx.nP ≤ xs.length) :
    substE V (substTau (ctx.hiAt occ.length) xs.length (nodeImgX m ψ ctx occ xs.length)) 0
        (consList xs ρ)
      = nodeTrueVal ctx.nP (nodeHv m.acval envC ctx ψ occ xs.length) xs ρ := by
  rw [substE_trueVal _ ρ rfl (by simp only [NestCtx.hiAt]; omega) hnP (fun v hv => by
    simp only [nodeImgX, nodeImg, ite_eq_left hv, denoteMeta_fvar, Option.getD_some])]
  rfl

theorem erasedEqL_refl : ∀ (l : List Expr), Expr.ErasedEqL l l
  | [] => trivial
  | a :: l => ⟨Expr.ErasedEq.rfl a, erasedEqL_refl l⟩

/-- **THE CLASS TIE AT A NODE**: an outside recursor class whose major
matches the node's key read back (`NodeMajor`), its parameters reading
as the read-back key's at the prefix spine `xs` (`hfr`), with the
canonically selected block, reads the node's block, levels and true
frame. -/
theorem tgtNodeTie {envC : Env} {mpC : EnvModelM V μ envC} {ex : List Name}
    (hcov : LfpCover mpC ex) {D0 : LfpDatum V} {d : BlockData V} {Dc : Nat → LfpDatum V}
    {mc : Nat → Nat} {cvc : Nat → ConstantVal} {p : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} {ctx : NestCtx} {t : PosTree} {c : Nat} {F : Nat} {formerTys : List Expr}
    (hcls : TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : Dc c = lfpSel mpC D0 (tgtMajor out c).ind)
    (hR : NodeMajor F envC p formerTys ctx (tgtMajor out c) t)
    (hfr : (tgtMajor out c).ds.map (fun x => interp V (consList xs ρ)
        ((denoteMeta mpC.base2.acval envC ψ (tgtRP p c) x).getD default))
      = (t.key.ds.map (nodeRb ctx t.occ)).map (fun x => interp V (consList xs ρ)
        ((denoteMeta mpC.base2.acval envC ψ (tgtRP p c) x).getD default)))
    -- the node's facts
    (hblk : ∃ D ∈ mpC.lfpBlocks, t.key.cname ∈ D.names ∧ (tgtMajor out c).ind ∈ D.names)
    (hlps : lpsOf envC t.key.cname = lpsOf envC (tgtMajor out c).ind)
    (hread : NodeHolesRead mpC.base2.acval envC ctx t.occ)
    (hws : ∀ x ∈ t.key.ds, Expr.WScoped (ctx.hiAt t.occ.length) x)
    {dsa : List AnnotTerm}
    (hsp : DenoteMetaSpine mpC.base2.acval envC ψ (ctx.hiAt t.occ.length) t.key.ds dsa)
    -- the prefix
    (hnP : ctx.nP ≤ tgtRP p c) (hxs : xs.length = tgtRP p c) :
    tgtClsD d Dc out c = lfpSel mpC D0 t.key.cname ∧
    tgtClsψ cvc out ψ c = nodeψ envC ψ t ∧
    tgtClsFr d mpC.base2.acval envC p out ψ ρ xs c = nodeFr mpC.base2.acval envC ctx ψ ρ xs t := by
  obtain ⟨hMo, -, hCM⟩ := hR
  have hlv := (ConLeche.targetClassMatch_true hCM).1
  have hMo' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨D, hD, h1, h2⟩ := hblk
    simp only [tgtClsD, hMo', Bool.false_eq_true, ite_false, hsel]
    exact lfpSel_eq_of_mem hcov D0 hD h1 h2
  · obtain ⟨caps, hf⟩ := hcls.hfind
    have hl : (cvc c).levelParams = lpsOf envC (tgtMajor out c).ind := by
      simp only [lpsOf, hf]; rfl
    simp only [tgtClsψ, hMo', Bool.false_eq_true, ite_false, nodeψ, hl, hlps]
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlv ψ)
  · have hdsa : dsa = t.key.ds.map fun x =>
        (denoteMeta mpC.base2.acval envC ψ (ctx.hiAt t.occ.length) x).getD default :=
      denoteMetaSpine_eq_map hsp
    simp only [tgtClsFr, hMo', Bool.false_eq_true, ite_false, tgtOutDsa, nodeFr]
    rw [← hdsa]
    rw [keyFrame_eq_of_params (dsa₂ := (t.key.ds.map (nodeRb ctx t.occ)).map fun x =>
      (denoteMeta mpC.base2.acval envC ψ (tgtRP p c) x).getD default) (by
        simpa [List.map_map, Function.comp_def] using hfr)]
    have := keyFrame_readback (V := V) mpC.base2 (hread.hs ψ hnP) hws hsp (erasedEqL_refl _)
      (consList xs ρ)
    rw [this, ← hxs, substE_nodeImgX_trueVal mpC.base2 ψ ρ (by omega)]

end ConLeche.Model
