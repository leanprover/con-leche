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
import ConLeche.Model.Inductives.BlockCtorReads
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.NatEqs

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
  NestFieldKind BlockParts BlockShape instPisWith nestHoles
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
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA → cA.1.levelParams = lps) ∧
  -- every member's parameter telescope is satisfied where the block's is
  (∀ t, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
    Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ)

theorem BlockCtorsCore.holeCtx {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (h : BlockCtorsCore m d lps cvTas p₁ isRec A nc)
    (hlpsA : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.levelParams = lps)
    (hparsT : ∀ t, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ) :
    BlockHoleCtxFacts m d lps cvTas p₁ isRec :=
  ⟨fun c cvTb hc => ⟨(h.1 c cvTb hc).1, (h.1 c cvTb hc).2.2.2⟩,
    fun c j cA hj => ⟨(h.2.2.1 c j cA hj).2.2.1, (h.2.2.1 c j cA hj).2.2.2⟩, hlpsA, hparsT⟩

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
  ctorLps_of hcore.2.2.1 hlps hlenCA hctorsAs

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

/-- The tail of a Π-tower past its first `n` binders is graded under
them. -/
theorem wellDenotedV_mkPisAV_drop :
    ∀ (n : Nat) {ab : List (Nat × Nat × AnnotTerm)} {Δa : List AnnotTerm} {B : AnnotTerm},
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (mkPisAV ab B)) →
      ∀ ρ : Nat → V, Sat V (((ab.take n).map (·.2.2)).reverse ++ Δa) ρ →
        WellDenotedV V ρ (mkPisAV (ab.drop n) B)
  | 0, _, _, _, h, ρ, hρ => by simpa using h ρ (by simpa using hρ)
  | _ + 1, [], _, _, h, ρ, hρ => by simpa using h ρ (by simpa using hρ)
  | n + 1, y :: ab, Δa, B, h, ρ, hρ =>
    wellDenotedV_mkPisAV_drop n (Rules.WellDenotedV.hoist_pi (V := V) h).2 ρ
      (by simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ)

/-- A spine of values fits a spine of types each lifted past the earlier
entries, when each value inhabits its type at the base frame. -/
theorem spineFit_range_lift {T : Nat → AnnotTerm} {f : Nat → V} {ρ : Nat → V} :
    ∀ (k : Nat), (∀ t, t < k → f t ∈ˢ interp V ρ (T t)) →
      SpineFit ρ ((List.range k).map fun t => (T t).liftN t 0) ((List.range k).map f)
  | 0, _ => trivial
  | k + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append]
    refine (spineFit_range_lift k (fun t ht => h t (by omega))).append ⟨?_, trivial⟩
    have hsh := shiftE_consList ((List.range k).map f) ρ
    rw [List.length_map, List.length_range] at hsh
    rw [interp_liftN, hsh]
    exact h k (by omega)

/-- **A member's hole type**: its stored former (a closed telescope of the
parameters and indices, `FormerData`) instantiated at the head former's
opened parameter variables reads, at any depth above them, as its index
tower over the parameters; its leaves are the parameters'. -/
theorem formerHoleTy_at {env : Env} {m : EnvModel V env} {cvTb : ConstantVal} {nP nI : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvTb (nP + nI) resSort pps) (hcl : cvTb.type.hasFvar = false)
    (hb : cvTb.type.looseBVarsBounded 0 = true) (hcr : cvTb.type.constsResolve env = true)
    {fvsP : List Expr} (hlen : fvsP.length = nP)
    (hidx : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → ∃ ty, x = .fvar i ty)
    (hws : ∀ x ∈ fvsP, Expr.WScoped nP x)
    (hcbP : ∀ x ∈ fvsP, ConstsBound env x)
    {ty : Expr} (hty : instPisWith fvsP cvTb.type = some ty) :
    (∀ (ψ : Name → Nat) (D : Nat), nP ≤ D → denoteMeta m.acval env ψ D ty
      = some ((mkPisAV ((pps ψ).drop nP) (.sort (resSort.eval ψ))).liftN (D - nP) 0)) ∧
    Expr.WScoped nP ty ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
    ∀ l ∈ ty.fvarLeaves, ∃ a ∈ fvsP, l ∈ a.fvarLeaves := by
  have hEq : Expr.ErasedEqL fvsP (canonParams nP) :=
    erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => by simpa using hidx i x hx)
      (fun i x hx => ⟨.sort .zero, by rw [canonParams_getElem? hx, Nat.zero_add]⟩)
      (by rw [hlen, canonParams_length])
  obtain ⟨A, hA, hoA⟩ := instPisWith_erasedEq hEq (Expr.ErasedEq.rfl _) hty
  obtain ⟨bs, s, hsyn⟩ := hFD.syn
  refine ⟨fun ψ D hD => ?_, ?_, ?_, ?_, fun l hl => ?_⟩
  · obtain ⟨ty', hty', -, hread⟩ := formerHoleTy_read m.acval_closed (ψ := ψ) hcl
      (stripPis_isSome_of_le (Nat.le_add_right nP nI) (by rw [hsyn]; rfl))
      (by rw [hFD.len ψ]; omega) (hFD.read ψ)
    rw [hA] at hty'
    obtain rfl := Option.some.inj hty'
    rw [denoteMeta_erasedEq hoA, hread D hD]
  · exact ConLeche.wscoped_instPisWith hws (Expr.WScoped.of_not_hasFvar hcl) hty
  · refine looseBVarsBounded_instPisWith (fun x hx => ?_) hb hty
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    obtain ⟨t, rfl⟩ := hidx i x hi
    rfl
  · exact constsBound_instPisWith hcbP (constsBound_of_constsResolve _ hcr) hty
  · rcases fvarLeaves_instPisWith hty l hl with h | h
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl] at h; exact absurd h List.not_mem_nil
    · exact h

/-- **A member's former applied to the block's parameters** at a frame
satisfying its own parameter telescope inhabits its index tower there. -/
theorem formerApp_mem {μ : ConLeche.CheckMode} {env : Env} (mp : EnvModelM V μ env)
    {cvTb : ConstantVal} {caps : ConLeche.IndCaps} {nP nI : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hfind : env.find? cvTb.name = some (.indInfo cvTb caps))
    (hFD : FormerData mp.base2 cvTb (nP + nI) resSort pps) (ψ : Name → Nat) {ρ : Nat → V}
    (hs : Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρ) :
    (frameIdx nP ρ).foldl app (interp V ρ (mp.base2.acval cvTb.name ψ))
      ∈ˢ interp V ρ (mkPisAV ((pps ψ).drop nP) (.sort (resSort.eval ψ))) := by
  have hlenT : (((pps ψ).take nP).map (·.2.2)).length = nP := by
    simp [hFD.len ψ]
  generalize hρ₀ : shiftE nP 0 ρ = ρ₀
  have hfm := mp.mem_type _ (List.mem_of_find?_eq_some hfind) ψ _ (hFD.read ψ) ρ₀
  rw [← List.take_append_drop nP (pps ψ), mkPisAV_append'] at hfm
  have hfit : SpineFit ρ₀ (((pps ψ).take nP).map (·.2.2)) (frameIdx nP ρ) := by
    have := spineFit_frameIdx_of_sat hs
    rw [hlenT] at this
    rw [← hρ₀]; exact this
  have hf₂ := foldl_app_mem_mkPisAV_pos (fun d hd => hFD.bits ψ d (List.mem_of_mem_take hd))
    hfit hfm
  rw [show consList (frameIdx nP ρ) ρ₀ = ρ by rw [← hρ₀]; exact consList_frameIdx nP ρ] at hf₂
  rw [acval_interp_closed mp.base2 _ ψ ρ ρ₀]
  exact hf₂

omit [SetTheory V] in
/-- A crest at a key of variables is bvar-closed when the stored type is. -/
theorem looseBVarsBounded_nestCrest {names : List Name} {us : List Level}
    {ds holes : List Expr} {cty crest : Expr} (hb : cty.looseBVarsBounded 0 = true)
    (hds : ∀ x ∈ ds ++ holes, ∃ i ty, x = .fvar i ty)
    (h : ConLeche.nestCrest names us ds holes cty = some crest) :
    crest.looseBVarsBounded 0 = true := by
  unfold ConLeche.nestCrest at h
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
  unfold ConLeche.nestCanonCrest at hA
  obtain ⟨e0, he, rfl⟩ := Option.map_eq_some_iff.mp hA
  refine looseBVarsBounded_replaceFVars (fun i r hr => ?_) _ 0
    (Expr.looseBVarsBounded_replaceApps (fun c us' r hr => ?_) _ 0
      (looseBVarsBounded_instPisWith (fun x hx => ?_) hb he))
  · unfold ConLeche.nestKeyMap at hr
    have hmem : r ∈ ds ++ holes := by
      split at hr
      · exact List.mem_append_left _ (List.mem_of_getElem? hr)
      · exact List.mem_append_right _ (List.mem_of_getElem? hr)
    obtain ⟨i, ty, rfl⟩ := hds r hmem
    rfl
  · obtain ⟨m, -, -, -, rfl⟩ := ConLeche.nestCanonSub_some hr
    rfl
  · simp only [ConLeche.nestPhs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rfl

/-- **The walk's canonical context**: a term whose leaves are the
canonical parameter variables' and the member holes' leaves (the head
former's opened telescope, then one hole per member, each typed by its
former at the parameters) is in the block's hole context (`CtxOkP`,
through `ctxOkP_of_openers`) with bounded leaves — a SEED's parameters
(`SeedLeaves`, `nestSeedOf`) among them.  Every leaf is itself one of
those variables. -/
theorem blockHoleCtx_canon {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    {d : BlockData V} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    (hparsT : ∀ t, t < d.k → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames)
    (hnP : p.nP = d.nP) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes) :
    ∀ x : Expr, (∀ l ∈ x.fvarLeaves, ∃ a ∈ fvsP ++ holes, l ∈ a.fvarLeaves) →
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse x ∧ Expr.LeavesBounded x ∧
      (∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP ++ holes) ∧
      (∀ l ∈ x.fvarLeaves, ConstsBound env l.2) := by
  -- ## the context
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  generalize hctx : p.nestCtx fvsP env.find? = ctx at *
  have hcPar : ctx.params = fvsP := by rw [← hctx]; rfl
  have hcF : ctx.find? = env.find? := by rw [← hctx]; rfl
  rw [hnP] at hop0
  have hwf := m.wf
  have hwfF : ∀ n ci, env.find? n = some ci → ConLeche.ConstWF env ci :=
    fun n ci hf => hwf ci (List.mem_of_find?_eq_some hf)
  -- ## the head former
  have hcv0' : cvTas[0]? = some cvTa0 := by rwa [List.head?_eq_getElem?] at hcv0
  obtain ⟨hfind0, hFD0⟩ := hF 0 cvTa0 hcv0'
  have hT0f : cvTa0.type.hasFvar = false := (hwfF _ _ hfind0).1
  have hT0b : cvTa0.type.looseBVarsBounded 0 = true := (hwfF _ _ hfind0).2.2.2.1
  have hlenF : fvsP.length = d.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  have hidxF' : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → ∃ ty, x = .fvar i ty :=
    fun i x hx => by simpa using hidxF i x hx
  have hwsF : ∀ x ∈ fvsP, Expr.WScoped d.nP x := by
    intro x hx
    have := (ConLeche.openPisAtFvars_WScoped d.nP cvTa0.type 0 hop0
      (Expr.WScoped.of_not_hasFvar hT0f)).1 x hx
    simpa using this
  have hcbF : ∀ x ∈ fvsP, ConstsBound env x := fun x hx => constsBound_of_constsResolve _
    ((openPisAtFvars_constsResolve d.nP (hwfF _ _ hfind0).2.2.1 hop0).1 x hx)
  have hleafF : ∀ x ∈ fvsP, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP := by
    intro x hx l hl
    rcases ConLeche.Verify.openPisAtFvars_leaves d.nP hop0 l (Or.inr ⟨x, hx, hl⟩) with h3 | h3
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hT0f] at h3; exact absurd h3 List.not_mem_nil
    · exact h3
  -- ## the holes
  have hlenH : holes.length = d.k := by rw [nestHoles_length hholes, hcN, hk]
  have hhole : ∀ t, t < d.k → ∃ cvTb ty, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      (∀ D, d.nP ≤ D → denoteMeta m.acval env ψ D ty
        = some ((mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.resSort.eval ψ))).liftN (D - d.nP) 0)) ∧
      Expr.WScoped d.nP ty ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
      (∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP) ∧
      holes[t]? = some (.fvar (d.nP + t) ty) := by
    intro t ht
    obtain ⟨cv, caps, ty, hf, hty, hget⟩ :=
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
    rw [hcPar] at hty
    obtain ⟨hrd, hw, hb, hcb, hlf⟩ := formerHoleTy_at hFDt (hwfF _ _ hfb).1
      (hwfF _ _ hfb).2.2.2.1 (hwfF _ _ hfb).2.2.1 hlenF hidxF' hwsF hcbF hty
    refine ⟨cvTb, ty, hcvb, hFDt, hrd ψ, hw, hb, hcb, fun l hl => ?_, by rw [hget, hcP]⟩
    obtain ⟨a, ha, hla⟩ := hlf l hl
    exact hleafF a ha l hla
  have hholeMem : ∀ x ∈ holes, ∃ t, t < d.k ∧ ∃ cvTb ty, cvTas[t]? = some cvTb ∧
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) ∧
      (∀ D, d.nP ≤ D → denoteMeta m.acval env ψ D ty
        = some ((mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.resSort.eval ψ))).liftN (D - d.nP) 0)) ∧
      Expr.WScoped d.nP ty ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
      (∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsP) ∧
      x = .fvar (d.nP + t) ty := by
    intro x hx
    obtain ⟨t, htx⟩ := List.getElem?_of_mem hx
    have ht : t < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp htx).1
    obtain ⟨cvTb, ty, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hhole t ht
    rw [htx] at h8
    exact ⟨t, ht, cvTb, ty, h1, h2, h3, h4, h5, h6, h7, Option.some.inj h8⟩
  have hbF := (ConLeche.Verify.openPisAtFvars_bounded d.nP hop0 hT0b).2
  have hlbF : ∀ x ∈ fvsP ++ holes, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbF x hx
    · obtain ⟨t, -, cvTb, ty, -, -, -, -, hb, -, -, rfl⟩ := hholeMem x hx
      exact hb
  have hcbT : ∀ x ∈ fvsP ++ holes, ConstsBound env (Expr.fvarTypeD x) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hidxF' i x hi
      exact constsBound_fvar.mp (hcbF _ hx)
    · obtain ⟨t, -, cvTb, ty, -, -, -, -, -, hcb, -, rfl⟩ := hholeMem x hx
      exact hcb
  -- ## the context: the parameters (member 0's former), then one hole per member
  have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
  have hlenParams : (d.params ψ).length = d.nP := by
    simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
  let holeTy : Nat → AnnotTerm := fun t =>
    (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))).liftN t 0
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
  have hshape : ∀ (i : Nat) (x : Expr), (fvsP ++ holes)[i]? = some x → ∃ ty, x = .fvar i ty := by
    intro i x hx
    by_cases hi : i < d.nP
    · rw [List.getElem?_append_left (by rw [hlenF]; exact hi)] at hx
      exact hidxF' i x hx
    · rw [List.getElem?_append_right (by rw [hlenF]; omega), hlenF] at hx
      have ht : i - d.nP < d.k := by rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cvTb, ty, -, -, -, -, -, -, -, h⟩ := hhole (i - d.nP) ht
      rw [hx] at h
      exact ⟨ty, by rw [Option.some.inj h]; congr 1; omega⟩
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
      obtain ⟨cvTb, ty, -, -, hrd, -, -, -, -, h⟩ := hhole (i - d.nP) ht
      rw [hx] at h
      obtain rfl := Option.some.inj h
      rw [show i = d.nP + (i - d.nP) by omega, hLhole _ ht]
      show denoteMeta m.acval env ψ (d.nP + (i - d.nP)) ty = _
      rw [hrd _ (Nat.le_add_right _ _), show d.nP + (i - d.nP) - d.nP = i - d.nP by omega]
      rfl
  have hws : ∀ x ∈ fvsP ++ holes, Expr.WScoped (d.nP + d.k) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Expr.WScoped.mono (by omega) (hwsF x hx)
    · obtain ⟨t, ht, cvTb, ty, -, -, -, hw, -, -, -, rfl⟩ := hholeMem x hx
      simp only [Expr.WScoped]
      exact ⟨by omega, Expr.WScoped.mono (by omega) hw⟩
  have hent : ∀ i, i < d.nP + d.k → L.reverse[d.nP + d.k - 1 - i]? = some (L.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by rw [hLlen]; omega), hLlen,
      show d.nP + d.k - 1 - (d.nP + d.k - 1 - i) = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hLlen]; exact hi)]
    rfl
  have hokA : ∀ i, i < d.nP + d.k → ∀ σ : Nat → V, Sat V (L.reverse.drop (d.nP + d.k - i)) σ →
      WellDenotedV V σ (L.getD i default) := by
    intro i hi σ hdrop
    rw [List.drop_reverse, hLlen, show d.nP + d.k - (d.nP + d.k - i) = i by omega] at hdrop
    by_cases hiP : i < d.nP
    · have htake : L.take i = ((d.ppsM 0 ψ).take i).map (·.2.2) := by
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
    · obtain ⟨cvTb, ty, -, hFDt, -⟩ := hhole (i - d.nP) (by omega)
      have ht : i - d.nP < d.k := by omega
      generalize htt : i - d.nP = t at ht hFDt
      have hi' : i = d.nP + t := by omega
      subst hi'
      rw [hLhole _ ht]
      have htake : L.take (d.nP + t) = d.params ψ ++ (List.range t).map holeTy := by
        simp only [L]
        rw [List.take_append, List.take_of_length_le (by rw [hlenParams]; omega), hlenParams,
          show d.nP + t - d.nP = t by omega, ← List.map_take, List.take_range, Nat.min_eq_left (Nat.le_of_lt ht)]
      rw [htake, List.reverse_append] at hdrop
      have hsP := Sat_drop hdrop t
      rw [List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
        List.nil_append] at hsP
      have hsh : shiftE t 0 σ = fun j => σ (j + t) := by
        funext j; simp [shiftE]
      refine (WellDenotedV_liftN V t _ 0 σ).mpr ?_
      rw [hsh]
      have hsT := hparsT t ht _ hsP
      have := wellDenotedV_mkPisAV_drop d.nP (Δa := []) (fun ρ _ => hFDt.okTy ψ ρ) _
        (by rw [List.append_nil]; exact hsT)
      exact this
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
    · obtain ⟨t, -, cvTb, ty, -, -, -, -, -, -, hlf, rfl⟩ := hholeMem a ha
      simp only [Expr.fvarLeaves, List.mem_cons] at hla
      rcases hla with hla | hla
      · subst hla
        exact List.mem_append_right _ ha
      · exact List.mem_append_left _ (hlf l hla)
  refine ⟨ctxOkP_of_openers (by rw [List.length_reverse, hLlen]) hshape hws hdoms
      hleafx (fun l hl => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem (hleafx l hl)
        obtain ⟨ty, hty⟩ := hshape q _ hq
        injection hty with h1 _
        rw [h1]
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [List.length_append, hlenF, hlenH] at this
        exact this)
      hent hokA, fun l hl => by simpa [Expr.fvarTypeD] using hlbF _ (hleafx l hl), hleafx,
    fun l hl => by simpa [Expr.fvarTypeD] using hcbT _ (hleafx l hl)⟩

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
    {d : BlockData V} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    (hparsT : ∀ t, t < d.k → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames)
    (hnP : p.nP = d.nP) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes)
    {cA : ConstantVal × Nat}
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : ConLeche.nestCrest (p.nestCtx fvsP env.find?).names (p.lps.map .param) fvsP holes
      cA.1.type = some crest)
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
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hhi : (p.nestCtx fvsP env.find?).hiAt 0 = d.nP + d.k := by
    simp only [NestCtx.hiAt, hcN, hcP, hk, Nat.add_zero]
  have hlenH : holes.length = d.k := by rw [nestHoles_length hholes, hcN, hk]
  -- ## the crest's leaves are the parameters' and the holes' variables
  have hleafs : ∀ l ∈ crest.fvarLeaves, ∃ a ∈ fvsP ++ holes, l ∈ a.fvarLeaves :=
    ConLeche.fvarLeaves_nestCrest hCf (by rw [hlenH, hcN, hk]; exact Nat.le_refl _) hcrest
  obtain ⟨hCP, hLB, hleaf, hcbl⟩ := blockHoleCtx_canon (ψ := ψ) hN hF hparsT hnames hnP
    hk hcv0 hop0 hholes crest hleafs
  have hshapeH : ∀ x ∈ fvsP ++ holes, ∃ i ty, x = .fvar i ty := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 i x hi
      exact ⟨_, _, rfl⟩
    · obtain ⟨i, cv, caps, ty, -, -, rfl⟩ := nestHoles_mem hholes x hx
      exact ⟨_, _, rfl⟩
  have hW : Expr.WScoped (d.nP + d.k) crest :=
    Expr.WScoped_of_leaves crest fun l hl => ⟨(hCP.2 l hl).1, (hCP.2 l hl).2.1⟩
  have hB : crest.looseBVarsBounded 0 = true := looseBVarsBounded_nestCrest hCb hshapeH hcrest
  have hfr : Rules.Frame (d.nP + d.k) crest := ⟨hW, hB, hLB⟩
  have hC : CtxOk m ψ (d.nP + d.k) (d.holeCtx ψ).reverse crest := hCP.toCtxOk
  -- ## U2: the reading is graded at that context
  rw [hhi] at hinf
  have hIS : Rules.InferSemFull m ψ (d.nP + d.k) crest ty :=
    Rules.infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hinf)
  obtain ⟨-, -, ta, -, hgr, -⟩ := hIS hfr hC hca₀
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hsatFrame : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      Sat V (d.holeCtx ψ).reverse (d.toLfp.frame ψ ρp X) := by
    intro ρp hs X hX
    simp only [BlockData.holeCtx, List.reverse_append]
    refine sat_of_spineFit hs (spineFit_range_lift d.k (fun t ht => ?_))
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    obtain ⟨-, hFDt⟩ := hF t cvTb hcvb
    exact LfpDatum.holeVal_mem hkN hX ht (ab := (d.ppsM t ψ).drop d.nP) rfl
      (fun x hx => hFDt.bits ψ x (List.mem_of_mem_drop hx))
  -- ## the normal form reads like the crest (the walk's semantic link)
  rw [← hhi] at hfr hCP hca₀
  obtain ⟨abD, abN, B, hcaE, hNE, hlD, hlN, hbits, hEq, hgN, hfrN, hsubN⟩ :=
    memberCtorD_red hin hd hfr hCP hca₀ hgr
  have hCPN := hCP.of_subset hsubN
  rw [hhi] at hfr hCP hfrN hCPN hNE
  -- ## the normal form names only stored constants (its leaves are the crest's)
  have hcbN : ConstsBound env tyN := constsBound_of_read _ tyN hNE fun l hl =>
    hcbl l (hsubN l hl)
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
    (hnP : p.nP = d.nP) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find?) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : ConLeche.nestCrest (p.nestCtx fvsP env.find?).names (p.lps.map .param) fvsP holes
      cA.1.type = some crest)
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
            (d.absE ψ c j))) ∧
      denoteMeta m.acval env ψ (d.nP + d.k) tyN
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (d.absE ψ c j))) ∧
      abN.map (·.2.2) = d.absF ψ c j ∧ abD.length = cA.2 ∧ abN.length = cA.2 ∧
      Rules.Frame (d.nP + d.k) crest ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse crest ∧
      Rules.Graded V (d.holeCtx ψ).reverse (mkPisAV abD (AnnotTerm.mkAppN
        (.bvar (cA.2 + (d.k - 1 - c))) (d.absE ψ c j))) ∧
      Rules.Frame (d.nP + d.k) tyN ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse tyN ∧
      Rules.Graded V (d.holeCtx ψ).reverse (mkPisAV abN (AnnotTerm.mkAppN
        (.bvar (cA.2 + (d.k - 1 - c))) (d.absE ψ c j))) ∧
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
    (fun i x hx => by rw [hcPar] at hx; simpa using hidxF i x hx)
    (by rw [hcPar, hlenF, hcP])
    (fun t x hx => by
      have ht : t < (p.nestCtx fvsP env.find?).names.length := by
        rw [← nestHoles_length hholes]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cv, caps, ty', -, -, hget⟩ := nestHoles_getElem? hholes ht
      rw [hget] at hx
      exact ⟨_, (Option.some.inj hx).symm⟩)
    hcrest
  rw [hcN, hcL, hcP, hA] at hA'
  obtain rfl := Option.some.inj hA'
  have hca : denoteMeta m.acval env ψ (d.nP + d.k) crest
      = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
          (d.absE ψ c j))) := by
    rw [denoteMeta_erasedEq herased]; exact hAr
  obtain ⟨abD, abN', B, hhi, hcaE, hNE, hlD, hlN, -, hfr, hCP, hgr, hfrN, hCPN, hgN, hEq, -, -,
    hsatFrame⟩ := blockWalkCtx hin hN hcore.1 (fun t ht ρ h => hcore.2.2.2 t ht ψ ρ h) hnames
      hnP hk hcv0 hop0 hholes hCf hCb hcrest hinf hd hca
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
    (hcrest : ConLeche.nestCrest (p.nestCtx fvsP env.find?).names (p.lps.map .param) fvsP holes
      cA.1.type = some crest)
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
    blockCtorHoleCtx hin hN hcore hnames hlps hnP hk hcv0 hop0 hholes hcj
      hCf hCb hcrest hinf hd hnf
  generalize hL : d.holeCtx ψ = L at hCP hgr hEq hsatFrame
  have hcN : (p.nestCtx fvsP env.find?).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find?).nP = d.nP := hnP
  have hcI : (p.nestCtx fvsP env.find?).nIdxs = d.nIdxs := hnIdxs
  rw [← hhi] at hca hfr hCP
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
      have har : (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0 := by
        show (((d.ppsM t ψ).drop d.nP).map (·.2.2)).length = _
        simp only [List.length_map, List.length_drop, hFDt.len ψ, hcI]
        show _ = d.nIdxAt t
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
          ConLeche.nestCrest (p.nestCtx fvsP env.find?).names (p.lps.map .param) fvsP holes
            cA.1.type = some crest ∧
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
          (∃ A, ConLeche.nestCanonCrest (p.nestCtx fvsP env.find?).names (p.lps.map .param) p.nP
              cA.1.type = some A ∧ A.nestOcc (p.nestCtx fvsP env.find?).names 0 0 = false) ∧
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
