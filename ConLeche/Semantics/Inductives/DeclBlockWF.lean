module

public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.Cached.TargetRecC

@[expose] public section

/-!
# The uniform install keeps the environment well formed, at k members

The inductive kind's half of the declaration fold's well-formedness (`declWFStepRun`,
`Semantics/DeclWF.lean`), off the run record `BlockRun` alone, model-free.  Each stage reads the
environment the stage before it left:

* the `k` formers (`direct_block_inds_wf`), each checked as a constant, or as declared when its
  member reads as recognised;
* the constructors (`direct_block_ctors_wf`), each checked as a constant at the formers'
  environment;
* the stream's recursors (`declBlockRun_recsWF`, through `streamRecs_recsWF`), checked against the
  generated ones at the constructors' environment;
* the projection tables (`blockTables_wf`, `EnvWF.pushTables`), each checked at the
  constructors' environment (`checkStructProjTable_tableWF`), which the recursors' environment
  extends.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level ConstantVal ConstantInfo ProjTable BlockShape MemberShape
  TargetMajor NestCtx ClassRead EnvWF TableWF fueledOps mkFEnv consBlockCtors consBlockRecsT
  blockTables checkBlockTables checkBlockRec streamRecsCheck blockNestCtx checkBlockClasses
  checkStructProjTable structProjBodies)

/-- **The recursors' stage keeps well-formedness**: the stream's recursors, checked against the
generated ones at the constructors' environment `envC`. -/
theorem declBlockRun_recsWF {F : Nat} {env₁ envC : Env} (henvC : EnvWF envC) {p₁ : BlockShape}
    {block : List ConstantInfo} {nestedBit : Bool} {ctx : NestCtx} {holes : List Expr}
    {rd : ClassRead} {Ms : List TargetMajor} {tbl : List ConLeche.NestCtorNf}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hctx : blockNestCtx (m := ConLeche.CheckM) p₁ env₁.find? = .ok (ctx, holes))
    (hcls : checkBlockClasses (fueledOps .verified F) (mkFEnv env₁) p₁ ctx.params = .ok (rd, Ms))
    (hRec : checkBlockRec (m := ConLeche.CheckM) (fueledOps .verified F) envC p₁ nestedBit
      ctx.params tbl rd Ms block = .ok out)
    (hS : streamRecsCheck (m := ConLeche.CheckM) (fueledOps .verified F) .plain
      (mkFEnv (consBlockRecsT p₁ 0 out envC)) p₁.recs out = .ok ()) :
    EnvWF (consBlockRecsT p₁ 0 (ConLeche.streamRecs p₁.recs out) envC) := by
  have hRec' : ConLeche.genRecCheck (ConLeche.ShadowOps.fueled .verified F) (mkFEnv envC) p₁
      nestedBit ctx.params tbl rd Ms block = .ok out := hRec
  -- one parameter variable per parameter
  have hpl : ctx.params.length = p₁.nP := by
    obtain ⟨cvTa0, fvsP, rest, -, hop, rfl, -⟩ := ConLeche.blockNestCtx_inv hctx
    exact ConLeche.Verify.openPisAtFvars_length _ hop
  -- an outside class's parameters are the block's
  have hMs : ∀ M ∈ Ms, ConLeche.ClassOutParams p₁.nP M := by
    intro M hM
    obtain ⟨C⟩ := ConLeche.checkBlockClasses_run hcls
    obtain ⟨hlenK, hallK⟩ := ConLeche.classMajors_run C.hMs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
    obtain ⟨key, hkey⟩ : ∃ key, C.keys[i]? = some key := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨M', hM', ⟨R⟩⟩ := hallK i key hkey
    obtain rfl := Option.some.inj (hi.symm.trans hM')
    cases R.major with
    | member => intro h; exact nomatch h
    | outside I us nPc nIdx ctors sI hfn ht hnq hct hdsLen hdsSc => exact fun _ => ⟨hdsLen, hdsSc⟩
  exact ConLeche.Cached.streamRecs_recsWF henvC hRec' hpl hMs hS

/-- **Every table the block installs is well formed** at any environment extending the one its
check ran at. -/
theorem blockTables_wf {p : BlockShape} {E E' : Env}
    (hdom : ∀ n, (E.find? n).isSome = true → (E'.find? n).isSome = true) :
    ∀ {l : List MemberShape}, (∀ ms ∈ l, ms.declared.name = ms.cvT.name) →
      checkBlockTables (m := ConLeche.CheckM) p E l = .ok () →
      ∀ t ∈ blockTables p l, TableWF E' t
  | [], _, _, t, ht => nomatch ht
  | ms :: rest, hn, h, t, ht => by
    have hrest : ∀ t ∈ blockTables p rest, TableWF E' t := by
      refine blockTables_wf hdom (fun ms' hm => hn ms' (List.mem_cons_of_mem _ hm)) ?_
      unfold checkBlockTables at h
      obtain ⟨_, -, h⟩ := ConLeche.exceptBind_ok h
      exact h
    simp only [blockTables] at ht
    split at ht
    · next c hc =>
      split at ht
      · next bodies hb =>
        rcases List.mem_cons.mp ht with rfl | ht
        · have hchk := ConLeche.checkBlockTables_inv h ms List.mem_cons_self c hc
          rw [hn ms List.mem_cons_self] at hb ⊢
          exact TableWF.mono hdom (ConLeche.checkStructProjTable_tableWF hchk hb)
        · exact hrest t ht
      · exact hrest t ht
    · exact hrest t ht

/-- **The uniform install's stages keep well-formedness.**  `hdecl`/`hname` are what each member's
reduction (`MemberAt`) establishes. -/
theorem declBlockRun_envWF {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (henv : EnvWF env)
    (hdecl : ∀ ms ∈ p₀.members, ConLeche.MemberDeclaredWF env ms)
    (hname : ∀ ms ∈ p₀.members, ms.cvT.name = ms.declared.name)
    (h : DeclBlockRun F env block p₀ env₂) : EnvWF env₂ := by
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds, nfs, pos, st, isorts, out,
    hInd, hCtors, hctx, hcls, -, -, -, -, hRec, -, hS, hTbl, rfl⟩ := h
  have henv₁ := (ConLeche.direct_block_inds_wf henv hdecl hInd).1
  have henvC : EnvWF (consBlockCtors p₁.nP p₁.memberCtors env₁) :=
    ConLeche.direct_block_ctors_wf henv₁ hCtors
  have henvR := declBlockRun_recsWF henvC hctx hcls hRec hS
  refine EnvWF.pushTables henvR fun t ht => blockTables_wf
    (fun n hn => ConLeche.Cached.find?_consBlockRecsT_le n hn) (fun ms hm => ?_) hTbl t
    (List.mem_reverse.mp ht)
  rw [ConLeche.checkBlockInds_members hInd] at hm
  exact (hname ms hm).symm

/-- **A block's run keeps well-formedness.** -/
theorem blockRun_envWF {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockShape}
    (henv : EnvWF env) (h : BlockRun F env block p₀ env₂) : EnvWF env₂ := by
  obtain ⟨ms, -, hall, -, hR⟩ := h
  exact declBlockRun_envWF henv (fun m hm => (hall m hm).declaredWF) (fun m hm => (hall m hm).name) hR

end ConLeche.Semantics
