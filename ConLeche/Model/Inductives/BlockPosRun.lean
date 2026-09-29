module

public import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Rules.Inputs
public import ConLeche.Verify.Inductives.PositivityInv
public import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.NestPosRed
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Kit
import ConLeche.Semantics.Tower.SumTower
import ConLeche.Model.Annot.BitRename

public section

/-!
# Positivity from the install's run

The consumer's premise, proved: at a uniform block's install every
member constructor is POSITIVE along the tuple order at the hole frame
(`LfpDatum.CtorPos (tupRel ψ ρp)`), from the positivity stage's run
(`checkBlockPositivity`, `DeclBlockRun` conjunct 3).  Per constructor
(`blockCtorPos_of_walk`):

* the walk's term — the stored constructor type, members abstracted to
  their holes, parameters at the head former's opened variables — READS
  as the Π-tower over the clause's fields with holes ending in the
  component's hole at the parameters and the result indices (the
  datum's reading fact `BlockAbsRead`: the walk's term is the canonical
  crest up to erasure, `canonCrest_of_walk`);
* its context is the parameters' telescope (member 0's former) then one
  hole per member, typed by the member's stored type (`CtxOk`, through
  `ctxOk_of_openers`); the reading is graded there because U2 INFERRED
  the term at that context (`infer_sound`);
* the tuple order at the hole frame is a hole relation for that context
  (`HoleRel`): the frames satisfy it (a hole value inhabits its member's
  type, `LfpDatum.holeVal_mem`), agree off the holes and grow at every
  member hole (`LfpDatum.holeOn_tupRel`);
* so the walk's derivation (`MemberCtorD`, monotone by
  `memberCtorD_mono`, under `ContCover` when a kind is a container)
  makes every field positive under the earlier ones and the result
  indices hole-free — `CtorPos`, read off the Π-tower
  (`piPosThen_mkPisAV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  NestFieldKind BlockParts BlockShape instPisWith nestAbstract nestHoles
  openPisAtFvars fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Reading pieces -/

/-- A Π-tower's domains are graded along it. -/
theorem wellDenotedV_mkPisAV_dom :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {Δa : List AnnotTerm} {B : AnnotTerm},
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (mkPisAV ab B)) →
      ∀ (i : Nat) (x : Nat × Nat × AnnotTerm), ab[i]? = some x →
      ∀ ρ : Nat → V, Sat V (((ab.take i).map (·.2.2)).reverse ++ Δa) ρ →
        WellDenotedV V ρ x.2.2
  | [], _, _, _, i, x, hx, _, _ => by simp at hx
  | y :: ab, Δa, B, h, 0, x, hx, ρ, hρ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact (Rules.WellDenotedV.hoist_pi (V := V) h).1 ρ (by simpa using hρ)
  | y :: ab, Δa, B, h, i + 1, x, hx, ρ, hρ => by
    simp only [List.getElem?_cons_succ] at hx
    refine wellDenotedV_mkPisAV_dom (Rules.WellDenotedV.hoist_pi (V := V) h).2 i x hx ρ ?_
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ

/-- A spine of values fits a spine of closed types componentwise. -/
theorem spineFit_range_closed {T : Nat → AnnotTerm} {f : Nat → V} :
    ∀ (k : Nat), (∀ t, t < k → ∀ σ : Nat → V, f t ∈ˢ interp V σ (T t)) →
      ∀ ρ : Nat → V, SpineFit ρ ((List.range k).map T) ((List.range k).map f)
  | 0, _, _ => trivial
  | k + 1, h, ρ => by
    rw [List.range_succ, List.map_append, List.map_append]
    exact (spineFit_range_closed k (fun t ht => h t (by omega)) ρ).append
      ⟨h k (by omega) _, trivial⟩

/-! ## One constructor -/

/-- **What a member constructor's walk context reads of the carrier**:
the `k` formers stored with their data, and every constructor's reading
— no constructor need be stored yet (`BlockCtorsCore` gives it at any
stage, `BlockCtorsCore.holeCtx`; the formers' pass gives it at the dummy
carrier). -/
@[expose] def BlockHoleCtxFacts {env : Env} (m : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTas : List ConstantVal) (p₁ : BlockShape) (isRec : Bool) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      BlockCtorRead m d lps c j cA ∧ BlockAbsRead m d lps c j cA) ∧
  -- every constructor at the block's own level parameters (the root
  -- frame's key levels)
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA → cA.1.levelParams = lps)

theorem BlockCtorsCore.holeCtx {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (h : BlockCtorsCore m d lps cvTas p₁ isRec A nc)
    (hlpsA : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.levelParams = lps) : BlockHoleCtxFacts m d lps cvTas p₁ isRec :=
  ⟨fun c cvTb hc => ⟨(h.1 c cvTb hc).1, (h.1 c cvTb hc).2.2.2⟩,
    fun c j cA hj => ⟨(h.2.2.1 c j cA hj).2.2.1, (h.2.2.1 c j cA hj).2.2.2⟩, hlpsA⟩

omit [SetTheory V] in
/-- **Every stored constructor at the block's own levels** (the root
frame's key levels), positionally over the run's constructor list. -/
theorem ctorLps_of {d : BlockData V} {lps : List Name}
    (hlpsA : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.levelParams = lps) {p : BlockParts} (hlps : p.lps = lps)
    {ctorsAs : List (List (ConstantVal × Nat))} (hlenCA : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = p.lps := by
  intro c cs hc cA hcA
  have hck : c < d.k := by rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hc).1
  rw [hctorsAs c hck] at hc
  obtain rfl := Option.some.inj hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
  rw [hlps]; exact hlpsA c j cA hj

theorem BlockHoleCtxFacts.ctorLps {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec) {p : BlockParts} (hlps : p.lps = lps)
    {ctorsAs : List (List (ConstantVal × Nat))} (hlenCA : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = p.lps :=
  ctorLps_of hcore.2.2 hlps hlenCA hctorsAs

/-- **The root frame's arity, from the formers' data**: every member's
stored former (found under its name) is a syntactic telescope of its
parameters and indices (`FormerData.syn`), so `nestArity` reads
`nP + nIdx` (`NestArityOk`). -/
theorem nestArityOk_of_formers {env : Env} {m : EnvModel V env} {d : BlockData V}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    {p : BlockParts} (hnames : p.memberNames = d.memberNames)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (fvsP : List Expr) : ConLeche.NestArityOk (p.nestCtx fvsP env.find?) := by
  intro t ht
  have ht' : t < d.k := by rw [hk]; simpa [BlockParts.nestCtx, hnames] using ht
  obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht')⟩
  obtain ⟨hfind, hFD⟩ := hF t cvTb hcvb
  have hname : (p.nestCtx fvsP env.find?).names.getD t .anonymous = cvTb.name := by
    show p.memberNames.getD t .anonymous = _
    rw [hnames]; exact hN.1 t cvTb hcvb
  obtain ⟨bs, s, hsyn⟩ := hFD.syn
  unfold ConLeche.nestArity
  rw [hname]
  show (match env.find? cvTb.name with
    | some (.indInfo cv _) => cv.type.piBinders.1.length
    | _ => 0) = _
  rw [hfind]
  simp only
  rw [ConLeche.stripPis_sort_piBinders_length _ hsyn]
  show d.nP + d.nIdxAt t = p.nP + p.nIdxs.getD t 0
  rw [hnP, hnIdxs]; rfl

theorem BlockHoleCtxFacts.nestArity {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (fvsP : List Expr) : ConLeche.NestArityOk (p.nestCtx fvsP env.find?) :=
  nestArityOk_of_formers hN hcore.1 hnames hnP hnIdxs hk fvsP

/-- **The walk's canonical context**: a term whose leaves are the
canonical parameter variables' and the member holes' leaves (the head
former's opened telescope, then one hole per member) is in the block's
hole context (`CtxOkP`, through `ctxOkP_of_openers`) with bounded leaves
— a SEED's parameters (`SeedLeaves`, `nestSeedOf`) among them. -/
theorem blockHoleCtx_canon {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes) :
    ∀ x : Expr, (∀ l ∈ x.fvarLeaves, ∃ a ∈ fvsP ++ holes, l ∈ a.fvarLeaves) →
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse x ∧ Expr.LeavesBounded x := by
  -- ## the context
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hhi : (p.nestCtx fvsP env.find?).hiAt 0 = d.nP + d.k := by
    simp only [NestCtx.hiAt, hcN, hcP, hk, Nat.add_zero]
  generalize hctx : p.nestCtx fvsP env.find? = ctx at *
  have hcPar : ctx.params = fvsP := by rw [← hctx]; rfl
  have hcF : ctx.find? = env.find? := by rw [← hctx]; rfl
  have hcI : ctx.nIdxs = d.nIdxs := by rw [← hctx]; exact hnIdxs
  have hcL : ctx.lps = lps := by rw [← hctx]; exact hlps
  rw [hnP] at hop0
  have hwf := m.wf
  have hwfF : ∀ n ci, env.find? n = some ci → ConLeche.ConstWF env ci :=
    fun n ci hf => hwf ci (List.mem_of_find?_eq_some hf)
  have hctxok : NestCtxOk ctx :=
    fun n ci hf => by rw [hcF] at hf; exact (hwfF n ci hf).1
  -- ## the head former and the members' formers
  have hcv0' : cvTas[0]? = some cvTa0 := by rwa [List.head?_eq_getElem?] at hcv0
  obtain ⟨hfind0, hFD0⟩ := hF 0 cvTa0 hcv0'
  have hT0f : cvTa0.type.hasFvar = false := (hwfF _ _ hfind0).1
  have hT0b : cvTa0.type.looseBVarsBounded 0 = true := (hwfF _ _ hfind0).2.2.2.1
  have hlenF : fvsP.length = d.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  -- ## the holes
  have hlenH : holes.length = d.k := by rw [nestHoles_length hholes, hcN, hk]
  have hhole : ∀ t, t < d.k → ∃ cvTb, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
      holes[t]? = some (.fvar (d.nP + t) cvTb.type) := by
    intro t ht
    obtain ⟨cv, caps, hf, hget⟩ :=
      nestHoles_getElem? hholes (show t < ctx.names.length by rw [hcN, ← hk]; exact ht)
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    obtain ⟨hfb, hFDt⟩ := hF t cvTb hcvb
    have hname : ctx.names.getD t .anonymous = cvTb.name := by
      rw [hcN]; exact hN.1 t cvTb hcvb
    rw [hname, hcF, hfb] at hf
    simp only [Option.some.injEq, ConstantInfo.indInfo.injEq] at hf
    obtain ⟨hcv, -⟩ := hf
    subst hcv
    refine ⟨cvTb, hcvb, hFDt, (hwfF _ _ hfb).1, (hwfF _ _ hfb).2.2.2.1, ?_⟩
    rw [hget, hcP]
  have hholeMem : ∀ x ∈ holes, ∃ t, t < d.k ∧ ∃ cvTb, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
      x = .fvar (d.nP + t) cvTb.type := by
    intro x hx
    obtain ⟨t, htx⟩ := List.getElem?_of_mem hx
    have ht : t < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp htx).1
    obtain ⟨cvTb, h1, h2, h3, h4, h5⟩ := hhole t ht
    rw [htx] at h5
    exact ⟨t, ht, cvTb, h1, h2, h3, h4, Option.some.inj h5⟩
  -- ## the frame
  have hparW : ∀ x ∈ ctx.params, Expr.WScoped (ctx.hiAt 0) x := by
    intro x hx
    rw [hcPar] at hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hilt : i < d.nP := by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hw := (ConLeche.openPisAtFvars_WScoped d.nP cvTa0.type 0 hop0
      (Expr.WScoped.of_not_hasFvar hT0f)).1 x hx
    obtain ⟨ty, rfl⟩ := hidxF i x hi
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by rw [hhi]; omega, hw.2⟩
  have hholesOk : ∀ x ∈ holes, Expr.WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
    intro x hx
    obtain ⟨t, ht, cvTb, -, -, hf, -, rfl⟩ := hholeMem x hx
    refine ⟨?_, _, _, rfl⟩
    simp only [Expr.WScoped]
    exact ⟨by rw [hhi]; omega, Expr.WScoped.of_not_hasFvar hf⟩
  have hbF := (ConLeche.Verify.openPisAtFvars_bounded d.nP hop0 hT0b).2
  have hlbF : ∀ x ∈ fvsP ++ holes, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbF x hx
    · obtain ⟨t, -, cvTb, -, -, -, hb, rfl⟩ := hholeMem x hx
      exact hb
  -- ## the context: the parameters (member 0's former), then one hole per member
  have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
  have hlenParams : (d.params ψ).length = d.nP := by
    simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
  let holeTy : Nat → AnnotTerm := fun t => mkPisAV (d.ppsM t ψ) (.sort (d.resSort.eval ψ))
  let L : List AnnotTerm := d.params ψ ++ (List.range d.k).map holeTy
  have hLlen : L.length = d.nP + d.k := by simp [L, hlenParams]
  have hLpar : ∀ i, i < d.nP → L.getD i default = (d.params ψ).getD i default := by
    intro i hi
    simp only [L, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlenParams]; exact hi)]
  have hLhole : ∀ t, t < d.k → L.getD (d.nP + t) default = holeTy t := by
    intro t ht
    simp only [L, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [hlenParams]; omega), hlenParams,
      show d.nP + t - d.nP = t by omega, List.getElem?_map, List.getElem?_range ht]
    rfl
  have hholeClosed : ∀ t, t < d.k → Term.bvarsBelow 0 (holeTy t).erase := by
    intro t ht
    obtain ⟨cvTb, -, hFDt, -⟩ := hhole t ht
    have := mkPisAV_below_of (C := .sort (d.resSort.eval ψ)) (hFDt.below ψ) (by simp [AnnotTerm.erase, Term.bvarsBelow])
    simpa using this
  have hshape : ∀ (i : Nat) (x : Expr), (fvsP ++ holes)[i]? = some x → ∃ ty, x = .fvar i ty := by
    intro i x hx
    by_cases hi : i < d.nP
    · rw [List.getElem?_append_left (by rw [hlenF]; exact hi)] at hx
      obtain ⟨ty, h⟩ := hidxF i x hx
      exact ⟨ty, by rw [h, Nat.zero_add]⟩
    · rw [List.getElem?_append_right (by rw [hlenF]; omega), hlenF] at hx
      have ht : i - d.nP < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cvTb, -, -, -, -, h⟩ := hhole (i - d.nP) ht
      rw [hx] at h
      exact ⟨cvTb.type, by rw [Option.some.inj h]; congr 1; omega⟩
  have hdoms : ∀ (i : Nat) (x : Expr), (fvsP ++ holes)[i]? = some x →
      denoteMeta m.acval env ψ i (Expr.fvarTypeD x) = some (L.getD i default) := by
    obtain ⟨pps, b, hst, -, -, hbind⟩ := denoteMeta_openPis d.nP hop0 (hFD0.read ψ)
    rw [stripPisAV_mkPisAV_take d.nP _ _ (by rw [hlenP0]; omega)] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    intro i x hx
    by_cases hi : i < d.nP
    · rw [List.getElem?_append_left (by rw [hlenF]; exact hi)] at hx
      obtain ⟨q, hq, -, hqd⟩ := hbind i x hx
      rw [Nat.zero_add] at hqd
      rw [hqd, hLpar i hi]
      simp only [BlockData.params, List.getD_eq_getElem?_getD, List.getElem?_map, hq]
      rfl
    · rw [List.getElem?_append_right (by rw [hlenF]; omega), hlenF] at hx
      have ht : i - d.nP < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cvTb, -, hFDt, hf, -, h⟩ := hhole (i - d.nP) ht
      rw [hx] at h
      obtain rfl := Option.some.inj h
      rw [show i = d.nP + (i - d.nP) by omega, hLhole _ ht]
      exact denoteMeta_depth_of_closed m.acval_closed hf
        (fun k => ConLeche.Semantics.liftN_eq_self_of_closed (hholeClosed _ ht) k 1)
        (hFDt.read ψ) _
  have hws : ∀ x ∈ fvsP ++ holes, Expr.WScoped (d.nP + d.k) x := by
    intro x hx
    rw [← hhi]
    rcases List.mem_append.mp hx with hx | hx
    · exact hparW x (by rw [hcPar]; exact hx)
    · exact (hholesOk x hx).1
  have hent : ∀ i, i < d.nP + d.k → L.reverse[d.nP + d.k - 1 - i]? = some (L.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by rw [hLlen]; omega), hLlen,
      show d.nP + d.k - 1 - (d.nP + d.k - 1 - i) = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hLlen]; exact hi)]
    rfl
  have hokA : ∀ i, i < d.nP + d.k → ∀ σ : Nat → V, Sat V (L.reverse.drop (d.nP + d.k - i)) σ →
      WellDenotedV V σ (L.getD i default) := by
    intro i hi σ hdrop
    by_cases hiP : i < d.nP
    · rw [List.drop_reverse, hLlen, show d.nP + d.k - (d.nP + d.k - i) = i by omega] at hdrop
      have htake : L.take i = ((d.ppsM 0 ψ).take i).map (·.2.2) := by
        have h1 : L.take i = (d.params ψ).take i :=
          List.take_append_of_le_length (by rw [hlenParams]; omega)
        rw [h1, BlockData.params, ← List.map_take, List.take_take,
          Nat.min_eq_left (show i ≤ d.nP by omega)]
      rw [htake] at hdrop
      obtain ⟨x, hx⟩ : ∃ x, (d.ppsM 0 ψ)[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenP0]; omega)⟩
      have hgd := wellDenotedV_mkPisAV_dom (Δa := []) (fun ρ _ => hFD0.okTy ψ ρ) i x hx _
        (by rw [List.append_nil]; exact hdrop)
      rw [hLpar i hiP]
      simp only [BlockData.params, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_take_of_lt hiP, hx]
      exact hgd
    · obtain ⟨cvTb, -, hFDt, -⟩ := hhole (i - d.nP) (by omega)
      rw [show i = d.nP + (i - d.nP) by omega, hLhole _ (by omega)]
      exact hFDt.okTy ψ _
  intro x hx
  have hLeq : L = d.holeCtx ψ := rfl
  rw [← hLeq]
  have hleafx : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP ++ holes := by
    intro l hl
    obtain ⟨a, ha, hla⟩ := hx l hl
    rcases List.mem_append.mp ha with ha | ha
    · rcases ConLeche.Verify.openPisAtFvars_leaves d.nP hop0 l (Or.inr ⟨a, ha, hla⟩) with h3 | h3
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hT0f] at h3; exact absurd h3 List.not_mem_nil
      · exact List.mem_append_left _ h3
    · obtain ⟨t, -, cvTb, -, -, hf, -, rfl⟩ := hholeMem a ha
      simp only [Expr.fvarLeaves, Expr.fvarLeaves_eq_nil_of_not_hasFvar hf, List.mem_cons,
        List.not_mem_nil, or_false] at hla
      subst hla
      exact List.mem_append_right _ ha
  refine ⟨ctxOkP_of_openers (by rw [List.length_reverse, hLlen]) hshape hws hdoms
      hleafx (fun l hl => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem (hleafx l hl)
        obtain ⟨ty, hty⟩ := hshape q _ hq
        injection hty with h1 _
        rw [h1]
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [List.length_append, hlenF, hlenH] at this
        exact this)
      hent hokA, fun l hl => by simpa [Expr.fvarTypeD] using hlbF _ (hleafx l hl)⟩

/-- **A member constructor's walk context**: the walk's term
— the stored constructor type, members abstracted to their holes,
parameters at the head former's opened variables — reads as the Π-tower
over the clause's fields with holes ending in the component's hole at the
parameters and the result indices (the datum's reading fact
`BlockAbsRead`, at the canonical crest the walk's term is up to erasure,
`canonCrest_of_walk`); its context is
the parameters' telescope then one hole per member, typed by the member's
stored type (`CtxOkP`, through `ctxOkP_of_openers`); the reading is
GRADED there because U2 inferred the term at that context
(`infer_sound`); and the model's hole frame at every tuple of the tuple
space satisfies that context (a hole value inhabits its member's type,
`LfpDatum.holeVal_mem`).  The positivity proof and the hole chains'
grading (`BlockHoleGrade.lean`) both start here. -/
theorem blockWalkCtx {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes)
    {cA : ConstantVal × Nat}
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find?) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find?).hiAt 0) crest = .ok ty)
    {tyN : Expr} {ksD : List ConLeche.NestFieldKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find?)
      cA.2 crest ksD tyN ts)
    {ca : AnnotTerm} (hca₀ : denoteMeta m.acval env ψ (d.nP + d.k) crest = some ca) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      (p.nestCtx fvsP env.find?).hiAt 0 = d.nP + d.k ∧
      ca = mkPisAV abD B ∧
      denoteMeta m.acval env ψ (d.nP + d.k) tyN = some (mkPisAV abN B) ∧
      abD.length = cA.2 ∧ abN.length = cA.2 ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      Rules.Frame (d.nP + d.k) crest ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse crest ∧
      Rules.Graded V (d.holeCtx ψ).reverse ca ∧
      Rules.Frame (d.nP + d.k) tyN ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse tyN ∧
      Rules.Graded V (d.holeCtx ψ).reverse (mkPisAV abN B) ∧
      FieldsEqOn V (d.holeCtx ψ).reverse (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Rules.LeavesSub tyN crest ∧ ConstsBound env tyN ∧
      (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
        ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
          Sat V (d.holeCtx ψ).reverse (d.toLfp.frame ψ ρp X)) := by
  -- ## the context
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hhi : (p.nestCtx fvsP env.find?).hiAt 0 = d.nP + d.k := by
    simp only [NestCtx.hiAt, hcN, hcP, hk, Nat.add_zero]
  generalize hctx : p.nestCtx fvsP env.find? = ctx at *
  have hcPar : ctx.params = fvsP := by rw [← hctx]; rfl
  have hcF : ctx.find? = env.find? := by rw [← hctx]; rfl
  have hcI : ctx.nIdxs = d.nIdxs := by rw [← hctx]; exact hnIdxs
  have hcL : ctx.lps = lps := by rw [← hctx]; exact hlps
  rw [hnP] at hop0
  have hwf := m.wf
  have hwfF : ∀ n ci, env.find? n = some ci → ConLeche.ConstWF env ci :=
    fun n ci hf => hwf ci (List.mem_of_find?_eq_some hf)
  have hctxok : NestCtxOk ctx :=
    fun n ci hf => by rw [hcF] at hf; exact (hwfF n ci hf).1
  -- ## the head former and the members' formers
  have hcv0' : cvTas[0]? = some cvTa0 := by rwa [List.head?_eq_getElem?] at hcv0
  obtain ⟨hfind0, hFD0⟩ := hF 0 cvTa0 hcv0'
  have hT0f : cvTa0.type.hasFvar = false := (hwfF _ _ hfind0).1
  have hT0b : cvTa0.type.looseBVarsBounded 0 = true := (hwfF _ _ hfind0).2.2.2.1
  have hlenF : fvsP.length = d.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  -- ## the holes
  have hlenH : holes.length = d.k := by rw [nestHoles_length hholes, hcN, hk]
  have hhole : ∀ t, t < d.k → ∃ cvTb, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
      holes[t]? = some (.fvar (d.nP + t) cvTb.type) := by
    intro t ht
    obtain ⟨cv, caps, hf, hget⟩ :=
      nestHoles_getElem? hholes (show t < ctx.names.length by rw [hcN, ← hk]; exact ht)
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    obtain ⟨hfb, hFDt⟩ := hF t cvTb hcvb
    have hname : ctx.names.getD t .anonymous = cvTb.name := by
      rw [hcN]; exact hN.1 t cvTb hcvb
    rw [hname, hcF, hfb] at hf
    simp only [Option.some.injEq, ConstantInfo.indInfo.injEq] at hf
    obtain ⟨hcv, -⟩ := hf
    subst hcv
    refine ⟨cvTb, hcvb, hFDt, (hwfF _ _ hfb).1, (hwfF _ _ hfb).2.2.2.1, ?_⟩
    rw [hget, hcP]
  have hholeMem : ∀ x ∈ holes, ∃ t, t < d.k ∧ ∃ cvTb, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
      x = .fvar (d.nP + t) cvTb.type := by
    intro x hx
    obtain ⟨t, htx⟩ := List.getElem?_of_mem hx
    have ht : t < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp htx).1
    obtain ⟨cvTb, h1, h2, h3, h4, h5⟩ := hhole t ht
    rw [htx] at h5
    exact ⟨t, ht, cvTb, h1, h2, h3, h4, Option.some.inj h5⟩
  -- ## the reading
  have hca : denoteMeta m.acval env ψ (ctx.hiAt 0) crest = some ca := by rw [hhi]; exact hca₀
  -- ## the frame
  have hparW : ∀ x ∈ ctx.params, Expr.WScoped (ctx.hiAt 0) x := by
    intro x hx
    rw [hcPar] at hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hilt : i < d.nP := by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hw := (ConLeche.openPisAtFvars_WScoped d.nP cvTa0.type 0 hop0
      (Expr.WScoped.of_not_hasFvar hT0f)).1 x hx
    obtain ⟨ty, rfl⟩ := hidxF i x hi
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by rw [hhi]; omega, hw.2⟩
  have hholesOk : ∀ x ∈ holes, Expr.WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
    intro x hx
    obtain ⟨t, ht, cvTb, -, -, hf, -, rfl⟩ := hholeMem x hx
    refine ⟨?_, _, _, rfl⟩
    simp only [Expr.WScoped]
    exact ⟨by rw [hhi]; omega, Expr.WScoped.of_not_hasFvar hf⟩
  have hW : Expr.WScoped (ctx.hiAt 0) crest :=
    memberCrest_wscoped hholesOk hparW hCf (by rw [hcPar]; exact hcrest)
  -- the leaves are the parameters' and the holes' variables
  have hleaf : ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP ++ holes := by
    intro l hl
    rcases fvarLeaves_instPisWith hcrest l hl with h1 | ⟨a, ha, h2⟩
    · obtain ⟨c', us, r, hr, hlr⟩ := fvarLeaves_replaceConsts_closed _ hCf l h1
      have hrm : r ∈ holes := by
        split at hr
        · split at hr
          · exact List.mem_of_getElem? hr
          · exact nomatch hr
        · exact nomatch hr
      obtain ⟨t, -, cvTb, -, -, hf, -, rfl⟩ := hholeMem r hrm
      simp only [Expr.fvarLeaves, Expr.fvarLeaves_eq_nil_of_not_hasFvar hf, List.mem_cons,
        List.not_mem_nil, or_false] at hlr
      subst hlr
      exact List.mem_append_right _ hrm
    · rcases ConLeche.Verify.openPisAtFvars_leaves d.nP hop0 l (Or.inr ⟨a, ha, h2⟩) with h3 | h3
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hT0f] at h3; exact absurd h3 List.not_mem_nil
      · exact List.mem_append_left _ h3
  have hbF := (ConLeche.Verify.openPisAtFvars_bounded d.nP hop0 hT0b).2
  have hlbF : ∀ x ∈ fvsP ++ holes, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbF x hx
    · obtain ⟨t, -, cvTb, -, -, -, hb, rfl⟩ := hholeMem x hx
      exact hb
  have hB : crest.looseBVarsBounded 0 = true := by
    refine looseBVarsBounded_instPisWith (fun x hx => ?_) ?_ hcrest
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hidxF i x hi
      rfl
    · refine looseBVarsBounded_replaceConsts (fun c' us r hr => ?_) _ 0 hCb
      split at hr
      · split at hr
        · obtain ⟨-, i, ty, rfl⟩ := hholesOk r (List.mem_of_getElem? hr)
          rfl
        · exact nomatch hr
      · exact nomatch hr
  have hfr : Rules.Frame (ctx.hiAt 0) crest :=
    ⟨hW, hB, fun l hl => by simpa [Expr.fvarTypeD] using hlbF _ (hleaf l hl)⟩
  -- ## the context: the parameters (member 0's former), then one hole per member
  have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
  have hlenParams : (d.params ψ).length = d.nP := by
    simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
  let holeTy : Nat → AnnotTerm := fun t => mkPisAV (d.ppsM t ψ) (.sort (d.resSort.eval ψ))
  let L : List AnnotTerm := d.params ψ ++ (List.range d.k).map holeTy
  have hLlen : L.length = d.nP + d.k := by simp [L, hlenParams]
  have hLpar : ∀ i, i < d.nP → L.getD i default = (d.params ψ).getD i default := by
    intro i hi
    simp only [L, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlenParams]; exact hi)]
  have hLhole : ∀ t, t < d.k → L.getD (d.nP + t) default = holeTy t := by
    intro t ht
    simp only [L, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [hlenParams]; omega), hlenParams,
      show d.nP + t - d.nP = t by omega, List.getElem?_map, List.getElem?_range ht]
    rfl
  have hholeClosed : ∀ t, t < d.k → Term.bvarsBelow 0 (holeTy t).erase := by
    intro t ht
    obtain ⟨cvTb, -, hFDt, -⟩ := hhole t ht
    have := mkPisAV_below_of (C := .sort (d.resSort.eval ψ)) (hFDt.below ψ) (by simp [AnnotTerm.erase, Term.bvarsBelow])
    simpa using this
  have hCP : CtxOkP m ψ (ctx.hiAt 0) L.reverse crest := by
    rw [hhi]
    refine (blockHoleCtx_canon (ψ := ψ) hN hF hnames hlps hnP hnIdxs hk hcv0 (by rw [hnP]; exact hop0)
      (by rw [hctx]; exact hholes) crest fun l hl => ⟨_, hleaf l hl, ?_⟩).1
    simp [Expr.fvarLeaves]
  have hC : CtxOk m ψ (ctx.hiAt 0) L.reverse crest := hCP.toCtxOk
  -- ## U2: the reading is graded at that context
  have hIS : Rules.InferSemFull m ψ (ctx.hiAt 0) crest ty :=
    Rules.infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hinf)
  obtain ⟨-, -, ta, -, hgr, -⟩ := hIS hfr hC hca
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hsatFrame : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      Sat V L.reverse (d.toLfp.frame ψ ρp X) := by
    intro ρp hs X hX
    simp only [L, List.reverse_append]
    refine sat_of_spineFit hs (spineFit_range_closed d.k (fun t ht σ => ?_) ρp)
    obtain ⟨cvTb, -, hFDt, -⟩ := hhole t ht
    have hab : (d.ppsM t ψ).map (·.2.2) = d.toLfp.pars t ψ ++ d.toLfp.ids t ψ := by
      show _ = ((d.ppsM t ψ).take d.nP).map (·.2.2) ++ ((d.ppsM t ψ).drop d.nP).map (·.2.2)
      rw [← List.map_append, List.take_append_drop]
    have hmem := LfpDatum.holeVal_mem hkN hX ht hab (hFDt.bits ψ)
    show _ ∈ˢ interp V σ (mkPisAV (d.ppsM t ψ) (.sort (d.resSort.eval ψ)))
    rw [interp_closed V (hholeClosed t ht) σ (shiftE (d.toLfp.pars t ψ).length 0 ρp)]
    exact hmem
  -- ## the normal form reads like the crest (the walk's semantic link)
  obtain ⟨abD, abN, B, hcaE, hNE, hlD, hlN, hbits, hEq, hgN, hfrN, hsubN⟩ :=
    memberCtorD_red hin hd hfr hCP hca hgr
  have hLeq : L = d.holeCtx ψ := rfl
  have hCPN := hCP.of_subset hsubN
  rw [hhi] at hfr hCP hfrN hCPN hNE
  rw [hLeq] at hCP hgr hCPN hgN hEq hsatFrame
  -- ## the normal form names only stored constants (its leaves are the crest's)
  have hcbx : ∀ x ∈ fvsP ++ holes, ConstsBound env x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact constsBound_of_constsResolve _
        ((openPisAtFvars_constsResolve d.nP (hwfF _ _ hfind0).2.2.1 hop0).1 x hx)
    · obtain ⟨t, -, cvTb, hcvb, -, -, -, rfl⟩ := hholeMem x hx
      obtain ⟨hfb, -⟩ := hF t cvTb hcvb
      exact constsBound_fvar.mpr (constsBound_of_constsResolve _ (hwfF _ _ hfb).2.2.1)
  have hcbN : ConstsBound env tyN := constsBound_of_read _ tyN hNE fun l hl =>
    constsBound_fvar.mp (hcbx _ (hleaf l (hsubN l hl)))
  exact ⟨abD, abN, B, hhi, hcaE, hNE, hlD, hlN, hbits, hfr, hCP, hgr, hfrN, hCPN, hgN, hEq, hsubN,
    hcbN, hsatFrame⟩

/-- **A member constructor's walk context, at the datum**: `blockWalkCtx`
at the datum's reading fact (`BlockAbsRead`): the crest reads as the
canonical crest does, the normal form as the datum's fields with holes. -/
theorem blockCtorHoleCtx {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find?) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find?).hiAt 0) crest = .ok ty)
    {tyN : Expr} {ksD : List ConLeche.NestFieldKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find?)
      cA.2 crest ksD tyN ts)
    (hnf : d.nfFF c j = tyN) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)),
      (p.nestCtx fvsP env.find?).hiAt 0 = d.nP + d.k ∧
      denoteMeta m.acval env ψ (d.nP + d.k) crest
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      denoteMeta m.acval env ψ (d.nP + d.k) tyN
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      abN.map (·.2.2) = d.absF ψ c j ∧ abD.length = cA.2 ∧ abN.length = cA.2 ∧
      Rules.Frame (d.nP + d.k) crest ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse crest ∧
      Rules.Graded V (d.holeCtx ψ).reverse (mkPisAV abD (AnnotTerm.mkAppN
        (.bvar (cA.2 + (d.k - 1 - c))) (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      Rules.Frame (d.nP + d.k) tyN ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse tyN ∧
      Rules.Graded V (d.holeCtx ψ).reverse (mkPisAV abN (AnnotTerm.mkAppN
        (.bvar (cA.2 + (d.k - 1 - c))) (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      FieldsEqOn V (d.holeCtx ψ).reverse (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
        ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
          Sat V (d.holeCtx ψ).reverse (d.toLfp.frame ψ ρp X)) := by
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hcL : (p.nestCtx fvsP env.find?).lps = lps := hlps
  have hcPar : (p.nestCtx fvsP env.find?).params = fvsP := rfl
  have hlenF : fvsP.length = d.nP := by
    rw [← hnP]; exact ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  have hlenH : holes.length = d.k := by rw [nestHoles_length hholes, hcN, hk]
  -- the reading: the datum's reading fact at the canonical crest, which the
  -- walk's term is up to erasure
  obtain ⟨-, A, hA, hR⟩ := (hcore.2.1 c j cA hcj).2
  obtain ⟨ab, abN, hAr, hNr, hlab, hlabN, -, hab, -⟩ := hR ψ
  rw [hnf] at hNr
  obtain ⟨A', hA', herased⟩ := canonCrest_of_walk (ctx := p.nestCtx fvsP env.find?)
    (k := d.k)
    (fun i x hx => by rw [hcPar] at hx; simpa using hidxF i x hx)
    (by rw [hcPar, hlenF, hcP])
    (fun t x hx => by
      have ht : t < (p.nestCtx fvsP env.find?).names.length := by
        rw [← nestHoles_length hholes]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cv, caps, -, hget⟩ := nestHoles_getElem? hholes ht
      rw [hget] at hx
      exact ⟨_, (Option.some.inj hx).symm⟩)
    (by rw [nestHoles_length hholes, hcN, hk]) hcrest
  rw [hcN, hcL, hcP, hA] at hA'
  obtain rfl := Option.some.inj hA'
  have hca : denoteMeta m.acval env ψ (d.nP + d.k) crest
      = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
          (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) := by
    rw [denoteMeta_erasedEq herased]; exact hAr
  obtain ⟨abD, abN', B, hhi, hcaE, hNE, hlD, hlN, -, hfr, hCP, hgr, hfrN, hCPN, hgN, hEq, -, -,
    hsatFrame⟩ := blockWalkCtx hin hN hcore.1 hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hCf hCb
      hcrest hinf hd hca
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (hlab.trans hlD.symm) hcaE
  rw [hNr] at hNE
  obtain ⟨rfl, -⟩ := mkPisAV_inj (hlabN.trans hlN.symm) (Option.some.inj hNE)
  exact ⟨ab, abN, hhi, hca, hNr, hab, hlab, hlabN, hfr, hCP, hgr, hfrN, hCPN, hgN, hEq, hsatFrame⟩

/-- **A member constructor is positive along the tuple order at the
hole frame**, from its walk's derivation (`MemberCtorD`) and its U2
typing (`inferTypeCore` at the holes' context), both at the formers'
environment. -/
theorem blockCtorPos_of_walk {env : Env} {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    {ψ : Name → Nat} (hin : Rules.RulesInputs V mp.base2 ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find?) holes cA.1.type) = some crest)
    {tyN : Expr}
    {ksD : List ConLeche.NestFieldKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find?)
      cA.2 crest ksD tyN ts)
    (hcovk : (∃ k ∈ ksD, k.flat = false) → ContCover mp (p.nestCtx fvsP env.find?))
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find?).hiAt 0) crest = .ok ty)
    (hnf : d.nfFF c j = tyN)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp) :
    d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  obtain ⟨ab, abN, hhi, hca, -, hab, habLen, -, hfr, hCP, hgr, -, -, -, hEq, hsatFrame⟩ :=
    blockCtorHoleCtx hin hN hcore hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hcj
      hCf hCb hcrest hinf hd hnf
  generalize hL : d.holeCtx ψ = L at hCP hgr hEq hsatFrame
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hcI : (p.nestCtx fvsP env.find?).nIdxs = d.nIdxs := hnIdxs
  rw [← hhi] at hca hgr hfr hCP
  generalize hctx : p.nestCtx fvsP env.find? = ctx at *
  -- ## the tuple order at the hole frame is a hole relation of that context
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hFDof : ∀ t, t < d.k → ∃ cvTb,
      FormerData mp.base2 cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) := by
    intro t ht
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    exact ⟨cvTb, (hcore.1 t cvTb hcvb).2⟩
  have hR : HoleRel mp.base2 ψ ctx [] (ctx.hiAt 0) L.reverse (d.toLfp.tupRel ψ ρp) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- dom
      rintro _ _ ⟨X, Y, hX, hY, -, rfl, rfl⟩
      exact ⟨hsatFrame ρp hs X hX, hsatFrame ρp hs Y hY⟩
    · -- agree
      intro σ σ' hr i hi
      refine LfpDatum.tupRel_agreeOff hr i ?_
      show d.k ≤ i
      refine Nat.le_of_not_lt fun hlt => hi ?_
      simp only [holeP, List.length_nil, hhi, hcP]
      omega
    · -- member
      intro t ht
      have ht' : t < d.k := by rw [hcN, ← hk] at ht; exact ht
      have hmo := LfpDatum.holeOn_tupRel hkN (ψ := ψ) (ρp := ρp) (show t < d.toLfp.k from ht')
      obtain ⟨cvTb, hFDt⟩ := hFDof t ht'
      have har : (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length
          = ctx.nP + ctx.nIdxs.getD t 0 := by
        show (((d.ppsM t ψ).take d.nP).map (·.2.2)).length
          + (((d.ppsM t ψ).drop d.nP).map (·.2.2)).length = _
        simp only [List.length_map, List.length_take, List.length_drop, hFDt.len ψ, hcP, hcI]
        show _ = d.nP + d.nIdxAt t
        omega
      rw [har, show d.toLfp.k - 1 - t = ctx.hiAt 0 - 1 - (ctx.nP + t) by
        rw [hhi, hcP]; show d.k - 1 - t = _; omega] at hmo
      exact hmo
    · -- frame
      intro i hk' h
      simp at h
    · -- scoped
      intro i hk' h
      simp at h
  -- ## the walk is positive, read off the Π-tower
  have hpos := memberCtorD_mono mp hin hd hcovk hfr hCP hca hgr hR
  rw [← habLen] at hpos
  obtain ⟨htele, i', vs, heq, hvs⟩ := piPosThen_mkPisAV ab _ _ hpos
  -- through the link, onto the normal form's fields (the datum's)
  obtain ⟨hteleN, hU⟩ := FieldsEqOn.teleMonoOn hEq (fun ρ ρ' hr => hR.dom ρ ρ' hr) htele
  rw [hab] at hteleN hU
  rw [hU] at hvs
  refine ⟨hteleN, fun e he => hvs e ?_⟩
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  rw [hcP, List.drop_append_of_le_length (by simp [paramBvarsAt]),
    List.drop_eq_nil_of_le (by simp [paramBvarsAt]), List.nil_append]
  exact he

/-! ## The block -/

/-- **The positivity stage, derived, at the formers' environment**
(`checkBlockPositivity_deriv` with its scoping premises discharged by the
environment's well-formedness): every stored constructor's
member-abstracted crest is derived, with the run's kinds and normal
form, and the stage's other checks (`checkBlockPositivity_inv_gen`: the
crest typed, the normal form's level parameters and fields' sorts,
M2′). -/
theorem checkBlockPositivity_derivM {env : Env} (hwf : ConLeche.EnvWF env) {F : Nat}
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)}
    {pos : ConLeche.NestState}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find? p cvTas ctorsAs = .ok (kinds, nfs, pos))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false)
    (hAr : ∀ fvsP, ConLeche.NestArityOk (p.nestCtx fvsP env.find?))
    (hlpsC : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = p.lps) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP env.find?) = some holes ∧
      (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
          instPisWith fvsP (nestAbstract (p.nestCtx fvsP env.find?) holes cA.1.type)
            = some crest ∧
          ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find?)
            cA.2 crest ks ((nfs.getD c []).getD j default) ts ∧
          (kinds.getD c []).getD j [] = ks ∧
          (∃ ty, (fueledOps .verified F).inferType env
            ((p.nestCtx fvsP env.find?).hiAt 0) crest = .ok ty) ∧
          ((nfs.getD c []).getD j default).allLevelParamsDefined p.lps = true ∧
          (∃ xq sorts, openPisAtFvars cA.2 ((nfs.getD c []).getD j default)
              ((p.nestCtx fvsP env.find?).hiAt 0) = some xq ∧
            ConLeche.checkStructFieldSortsI (fueledOps .verified F) env
              (Level.isEquiv p.resSort .zero == some true) false p.resSort
              ((p.nestCtx fvsP env.find?).hiAt 0) xq.1 [] cA.2 = .ok sorts) ∧
          (nestAbstract (p.nestCtx fvsP env.find?) holes cA.1.type).nestOcc
            (p.nestCtx fvsP env.find?).names 0 0 = false ∧
          ConLeche.TreeRec (fueledOps .verified F) env (p.nestCtx fvsP env.find?)
            pos.ctorNfs.toList ts) ∧
      ConLeche.CtorsRecRoot (fueledOps .verified F) env (p.nestCtx fvsP env.find?) holes
        pos.ctorNfs.toList ctorsAs := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, h⟩ :=
    ConLeche.checkBlockPositivity_deriv (fun dep e w hw hws => ConLeche.whnf_WScoped hwf F hw hws)
      hrun
  obtain ⟨cvTa0', fvsP', rest', holes', h1', h2', h3', hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun hlpsC
  rw [h1] at h1'
  obtain rfl := Option.some.inj h1'
  rw [h2] at h2'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using h2'
  rw [h3] at h3'
  obtain rfl := Option.some.inj h3'
  have hpar : ∀ x ∈ fvsP, Expr.WScoped ((p.nestCtx fvsP env.find?).hiAt 0) x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hw := (ConLeche.openPisAtFvars_WScoped p.nP cvTa0.type 0 h2
      (Expr.WScoped.of_not_hasFvar (hT0 _ h1))).1 x hx
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 i _ hi
    have hilt : i < p.nP := by
      rw [← ConLeche.Verify.openPisAtFvars_length _ h2]; exact (List.getElem?_eq_some_iff.mp hi).1
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by simp only [NestCtx.hiAt, BlockParts.nestCtx]; omega, hw.2⟩
  obtain ⟨hmem, hroot, -⟩ := h (fun n ci hf => (hwf ci (List.mem_of_find?_eq_some hf)).1)
    (hAr fvsP) hpar hcl hlpsC
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun c cs hc j cA hj => ?_, hroot⟩
  obtain ⟨crest, ks, ts, hcr, hd, hks, htr⟩ := hmem c cs hc j cA hj
  obtain ⟨crest', tyN, hcr', hnf, hty, hlp, hsorts, hocc⟩ := hall c cs hc j cA hj
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  subst hnf
  exact ⟨crest, ks, ts, hcr, hd, hks, hty, hlp, hsorts, hocc, htr⟩

end ConLeche.Model
