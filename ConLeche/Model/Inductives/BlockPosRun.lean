module

public import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Rules.Inputs
public import ConLeche.Verify.Inductives.PositivityInv
public import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Annot.BitClosed
import ConLeche.Semantics.Tower.FixWire
import ConLeche.Model.Inductives.StructRead
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Semantics.Kit
import ConLeche.Semantics.Tower.TowerWire
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Capstone
import ConLeche.Verify.BetaGate

public section

/-!
# Positivity from the install's run (lane HOLE2, checkpoint (c))

The consumer's premise, proved: at a uniform block's install every
member constructor is POSITIVE along the tuple order at the hole frame
(`LfpDatum.CtorPos (tupRel ψ ρp)`), from the positivity stage's run
(`checkBlockPositivity`, `DeclBlockRun` conjunct 7b).  Per constructor
(`blockCtorPos_of_walk`):

* the walk's term — the stored constructor type, members abstracted to
  their holes, parameters at the head former's opened variables — READS
  as the Π-tower over the clause's fields with holes ending in the
  component's hole at the parameters and the result indices
  (`blockCtor_walkRead`, `BlockHoleRead.lean`);
* its context is the parameters' telescope (member 0's former) then one
  hole per member, typed by the member's stored type (`CtxOk`, through
  `ctxOk_of_openers`); the reading is graded there because U2 INFERRED
  the term at that context (`infer_sound`);
* the tuple order at the hole frame is a hole relation for that context
  (`HoleRel`): the frames satisfy it (a hole value inhabits its member's
  type, `LfpDatum.holeVal_mem`), agree off the holes and grow at every
  member hole (`LfpDatum.holeOn_tupRel`);
* so `nestMemberCtor_sem_flat` (no container kind) makes every field
  positive under the earlier ones and the result indices hole-free —
  `CtorPos`, read off the Π-tower (`piPosThen_mkPisAV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  NestFieldKind BlockParts BlockShape instPisWith nestAbstract nestHoles nestMemberCtor
  openPisAtFvars fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Reading pieces -/

/-- Two lists of variables at the same consecutive indices are
erasure-equal. -/
theorem erasedEqL_of_fvarIdx :
    ∀ (as bs : List Expr) (o : Nat),
      (∀ (i : Nat) (x : Expr), as[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      (∀ (i : Nat) (x : Expr), bs[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      as.length = bs.length → Expr.ErasedEqL as bs
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: as, b :: bs, o, ha, hb, h => by
    obtain ⟨ta, rfl⟩ := ha 0 a rfl
    obtain ⟨tb, rfl⟩ := hb 0 b rfl
    refine ⟨rfl, erasedEqL_of_fvarIdx as bs (o + 1) (fun i x hx => ?_) (fun i x hx => ?_)
      (by simpa using h)⟩
    · obtain ⟨ty, hty⟩ := ha (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩
    · obtain ⟨ty, hty⟩ := hb (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩

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
      BlockCtorRead m d lps c j cA)

theorem BlockCtorsCore.holeCtx {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (h : BlockCtorsCore m d lps cvTas p₁ isRec A nc) : BlockHoleCtxFacts m d lps cvTas p₁ isRec :=
  ⟨fun c cvTb hc => ⟨(h.1 c cvTb hc).1, (h.1 c cvTb hc).2.2.2⟩,
    fun c j cA hj => (h.2.2.1 c j cA hj).2.2⟩

/-- **A member constructor's walk context** (lane HOLE2): the walk's term
— the stored constructor type, members abstracted to their holes,
parameters at the head former's opened variables — reads as the Π-tower
over the clause's fields with holes ending in the component's hole at the
parameters and the result indices (`blockCtor_walkRead`); its context is
the parameters' telescope then one hole per member, typed by the member's
stored type (`CtxOkP`, through `ctxOkP_of_openers`); the reading is
GRADED there because U2 inferred the term at that context
(`infer_sound`); and the model's hole frame at every tuple of the tuple
space satisfies that context (a hole value inhabits its member's type,
`LfpDatum.holeVal_mem`).  The positivity proof and the hole chains'
grading (`BlockHoleGrade.lean`) both start here. -/
theorem blockCtorHoleCtx {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hc : c < d.k) (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty) :
    ∃ (ab : List (Nat × Nat × AnnotTerm)) (L : List AnnotTerm),
      (p.nestCtx fvsP env.find? env.consts).hiAt 0 = d.nP + d.k ∧
      denoteMeta m.acval env ψ (d.nP + d.k) crest
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      ab.map (·.2.2) = d.absF ψ c j ∧
      Rules.Frame (d.nP + d.k) crest ∧
      CtxOkP m ψ (d.nP + d.k) L.reverse crest ∧
      Rules.Graded V L.reverse (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
        ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
          Sat V L.reverse (d.toLfp.frame ψ ρp X)) := by
  -- ## the context
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hhi : (p.nestCtx fvsP env.find? env.consts).hiAt 0 = d.nP + d.k := by
    simp only [NestCtx.hiAt, hcN, hcP, hk, Nat.add_zero]
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at *
  have hcPar : ctx.params = fvsP := by rw [← hctx]; rfl
  have hcF : ctx.find? = env.find? := by rw [← hctx]; rfl
  have hcI : ctx.nIdxs = d.nIdxs := by rw [← hctx]; exact hnIdxs
  have hcL : ctx.lps = lps := by rw [← hctx]; exact hlps
  rw [hnP] at hop0
  have hwf := m.wf
  have hwfF : ∀ n ci, env.find? n = some ci → ConLeche.ConstWF env ci :=
    fun n ci hf => hwf ci (List.mem_of_find?_eq_some hf)
  have hctxok : NestCtxOk ctx :=
    ⟨fun ci hci => by rw [← hctx] at hci; exact (hwf ci hci).1,
     fun n ci hf => by rw [hcF] at hf; exact (hwfF n ci hf).1⟩
  -- ## the head former and the members' formers
  have hcv0' : cvTas[0]? = some cvTa0 := by rwa [List.head?_eq_getElem?] at hcv0
  obtain ⟨hfind0, hFD0⟩ := hcore.1 0 cvTa0 hcv0'
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
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2.2]; exact ht)⟩
    obtain ⟨hfb, hFDt⟩ := hcore.1 t cvTb hcvb
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
  -- ## the reading: the Π-tower over the fields with holes
  have hD₀ : BlockCtorDataI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := hcore.2 c j cA hcj
  have hpar : Expr.ErasedEqL ctx.params (d.fvsPF c j) := by
    rw [hcPar]
    refine erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => hidxF i x hx) (fun i x hx => ?_)
      (by rw [hlenF, hD₀.pLen])
    obtain ⟨ty, h⟩ := hD₀.pIdx i x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hholes' : ∀ t, t < d.k → ∃ ty, holes[t]? = some (.fvar (d.nP + t) ty) := by
    intro t ht
    obtain ⟨cvTb, -, -, -, -, h⟩ := hhole t ht
    exact ⟨_, h⟩
  have htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k := fun l _ => by
    rw [← hN.2.2.2]; exact hN.2.1 c j l
  obtain ⟨ab, hca, hab⟩ := blockCtor_walkRead (m := m) hcj hD₀ hcN hcL hcP hk hpar
    (fun x hx => by
      obtain ⟨t, -, cvTb, -, -, -, -, rfl⟩ := hholeMem x hx
      exact ⟨_, _, rfl⟩)
    hholes' hnd hfresh htgt hc (Expr.WScoped.of_not_hasFvar hCf) ψ (by rw [hcPar]; exact hcrest)
  rw [← hhi] at hca
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
  have hCP : CtxOkP m ψ (ctx.hiAt 0) L.reverse crest := by
    rw [hhi]
    exact ctxOkP_of_openers (by rw [List.length_reverse, hLlen]) hshape hws hdoms
      hleaf (fun l hl => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem (hleaf l hl)
        obtain ⟨ty, hty⟩ := hshape q _ hq
        injection hty with h1 _
        rw [h1]
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [List.length_append, hlenF, hlenH] at this
        exact this)
      hent hokA
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
  rw [hhi] at hca hgr hfr hCP
  exact ⟨ab, L, hhi, hca, hab, hfr, hCP, hgr, hsatFrame⟩

/-- **A member constructor is positive along the tuple order at the
hole frame**, from its walk (`nestMemberCtor`, flat kinds) and its U2
typing (`inferTypeCore` at the holes' context), both at the formers'
environment. -/
theorem blockCtorPos_of_walk {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockCtorsCore m d lps cvTas p₁ isRec A 0)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hc : c < d.k) (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {st₀ st₁ : NestState} {ks : List NestFieldKind} {tyN : Expr}
    (hm : nestMemberCtor (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts) cA.2
      crest st₀ = .ok (ks, tyN, st₁))
    (hks : ∀ k ∈ ks, k.flat = true)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp) :
    d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  obtain ⟨ab, L, hhi, hca, hab, hfr, hCP, hgr, hsatFrame⟩ :=
    blockCtorHoleCtx hin hN hcore.holeCtx hnames hlps hnP hnIdxs hk hnd hfresh hcv0 hop0 hholes hc hcj
      hCf hCb hcrest hinf
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hcI : (p.nestCtx fvsP env.find? env.consts).nIdxs = d.nIdxs := hnIdxs
  rw [← hhi] at hca hgr hfr hCP
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at *
  have hD₀ := (hcore.2.2.1 c j cA hcj).2.2
  -- ## the tuple order at the hole frame is a hole relation of that context
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hFDof : ∀ t, t < d.k → ∃ cvTb,
      FormerData m cvTb (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) := by
    intro t ht
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2.2]; exact ht)⟩
    exact ⟨cvTb, (hcore.1 t cvTb hcvb).2.2.2⟩
  have hR : HoleRel m ψ ctx [] (ctx.hiAt 0) L.reverse (d.toLfp.tupRel ψ ρp) := by
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
  have hpos := nestMemberCtor_sem_flat hin ctx F hm hks hfr hCP hca hgr hR
  have habLen : ab.length = cA.2 := by
    have h1 := congrArg List.length hab
    rw [List.length_map] at h1
    rw [h1, BlockData.absF, List.length_map, List.length_range]
    have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hD₀.len ψ]
    omega
  rw [← habLen] at hpos
  obtain ⟨htele, i', vs, heq, hvs⟩ := piPosThen_mkPisAV ab _ _ hpos
  rw [hab] at htele hvs
  refine ⟨htele, fun e he => hvs e ?_⟩
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  rw [hcP, List.drop_append_of_le_length (by simp [paramBvarsAt]),
    List.drop_eq_nil_of_le (by simp [paramBvarsAt]), List.nil_append]
  exact he

/-! ## The block -/

/-- **Every member constructor of a uniform block is positive along the
tuple order at the hole frame**, from the install's positivity stage
(`DeclBlockRun` conjunct 7b) at the formers' environment. -/
theorem blockCtorPos_of_run {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true) {env : Env}
    (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockCtorsCore mp.base2 d lps cvTas p₁ isRec A 0)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs = .ok ())
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hnd : d.memberNames.Nodup) (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    (hinst : d.nInst = 0)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c))
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv hrun
  intro ψ ρp hs c hc j hj
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    omega
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  obtain ⟨crest, hcrest, ⟨st₀, ks, tyN, st₁, hm, hks⟩, ⟨ty, hty⟩, -⟩ :=
    hall c (d.ctorsM c) (hctorsAs c hck) j _ hcj
  obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
  exact blockCtorPos_of_walk (Rules.RulesInputs.ofSem mp ψ) hN hcore hnames hlps hnP hnIdxs hk
    hnd hfresh hcv0 hop0 hholes hck hcj hCf hCb hcrest hm hks hty hs

end ConLeche.Model
