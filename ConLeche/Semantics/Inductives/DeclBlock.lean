module

public import ConLeche.Verify.Inductives.BlockInv

@[expose] public section

/-!
# `DeclBlockRun`: the inductive declaration relation at k members

The uniform arm of `checkDecl`'s `.indDecl` clause (`checkBlock`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), recorded as a run
relation: the two distinct-name guards, the k type formers' run (constant check,
official's telescope loop, the result sort, and — from member 1 on —
official's two agreements), the constructors' runs per member at the
environment holding ALL the formers, the kinds classified against the
whole member list, the capability record the block owes, every member's index binders' sorts, the kinds
re-checked on the stored constructors at the TARGET each carries, the
recursor stage, and the install spine (the constructors consed, the
recursors consed with their rules, a projection table per
structure-like member).

**The recursor stage is one opaque conjunct** — `checkBlockRec … =
.ok rs`, the generated recursor stage (`genRecCheck`, on the raw
`block`: its pins read the stream's recursor records).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  BlockShape BlockParts MemberShape NestFieldKind RecRule fueledOps
  checkBlockInds checkBlockCtors checkBlockPositivity checkBlockIdxSorts
  checkBlockRec checkBlockTables checkBlockPass checkBlockTail checkBlock
  consBlockCtors consBlockRecs consBlockRecsT blockCapsAt
  blockNestedBit blockRawRec BlockPass TargetMajor NestKey NestState)

/-- **The uniform inductive declaration, as checked**: the stage runs
of `checkBlock`.  `env` is the pre-block environment; `p₀` the
recognised record; the one pass runs at official's `is_rec`
(`blockRawRec`). -/
def DeclBlockRun (μ : CheckMode) (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTas : List ConstantVal) (p₁ : BlockShape) (p : BlockParts)
    (ctorsAs : List (List (ConstantVal × Nat))) (sortsss : List (List (List Level)))
    (ctx : NestCtx) (holes : List Expr) (rd : ClassRead) (Ms : List TargetMajor)
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) (pos st : NestState)
    (isorts : List (List Level))
    (out : List (ConstantVal × TargetMajor × List Expr)),
    -- 1  the k formers: the constant check, official's telescope loop, the
    --    sort, official's two agreements from member 1 on, then all k consed
    checkBlockInds (m := ConLeche.CheckM) (fueledOps μ F) env p₀ isRec
      = .ok (env₁, cvTas, p₁) ∧
    p = p₀.complete p₁ ∧
    -- 2  the constructors, per member, at the environment holding all k formers,
    --    each stored as declared
    checkBlockCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok (ctorsAs, sortsss) ∧
    -- 3  the walk's context; the classes the stream's recursor family eliminates
    --    (read off its raw recursor types, each checked as a major)
    blockNestCtx (m := ConLeche.CheckM) p.toBlockShape cvTas env₁.find?
      = .ok (ctx, holes) ∧
    checkBlockClasses (fueledOps μ F) (mkFEnv env₁) env₁ p.toBlockShape ctx.params ctorsAs
      = .ok (rd, Ms) ∧
    -- 4  the positivity function on the stored constructors (the root frame), and
    --    their member-abstracted types typed at the holes' context; its field
    --    kinds are the block's `is_rec`, its normal forms the model's fields
    --    with holes; then every outside class walked from its state
    checkBlockPositivity (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁.find? p
      cvTas ctorsAs = .ok (kinds, nfs, pos) ∧
    nestSeeds (fueledOps μ F) env₁ ctx (classSeeds ctx holes Ms) pos = .ok st ∧
    -- 5  the formers carry the record at official's `is_rec`, the syntactic one
    isRec = blockRawRec p₀ ∧
    -- 6  every member's index binders' sorts
    checkBlockIdxSorts (m := ConLeche.CheckM) (fueledOps μ F) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts ∧
    -- 7  the recursor stage: the GENERATED recursors, one per record of the
    --    stream's family, on the classes and the walk's table (the block's
    --    container bit)
    checkBlockRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consBlockCtors p.nP ctorsAs env₁) p (blockNestedBit p.toBlockShape kinds)
      ctx.params st.ctorNfs.toList rd Ms block cvTas = .ok out ∧
    -- 8  the install spine: the recursors with their rules at their majors,
    --    then the tables
    checkBlockTables (m := ConLeche.CheckM) p.toBlockShape
      (p.members.zip (ctorsAs.zip sortsss))
      (consBlockRecsT (consBlockCtors p.nP ctorsAs env₁).find?
        (·.constsResolve (consBlockCtors p.nP ctorsAs env₁)) p.toBlockShape 0 out
        (consBlockCtors p.nP ctorsAs env₁)) = .ok env₂

/-- **The uniform install's run**: the pass at official's `is_rec` and
the install after it. -/
theorem declBlockRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockParts}
    (h : checkBlock (m := ConLeche.CheckM) (fueledOps μ F) env block p₀ = .ok env₂) :
    DeclBlockRun μ F env block p₀ env₂ := by
  rw [ConLeche.checkBlock] at h
  simp only [bind, Except.bind] at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg =>
    rw [ite_eq_right hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [ite_eq_left hnd] at h
  try simp only [bind, Except.bind] at h
  cases hP : checkBlockPass (m := ConLeche.CheckM) (fueledOps μ F) env p₀ (blockRawRec p₀) with
  | error e => rw [hP] at h; exact nomatch h
  | ok q =>
  rw [hP] at h
  dsimp only at h
  obtain ⟨p₁, ctx, holes, pos, st, hInd, hCtors, hctx, hcls, hK, hst, hpar, htbl, hp⟩ :=
    ConLeche.checkBlockPass_inv hP
  obtain ⟨isorts, rs, hsorts, hRec, hTbl⟩ := ConLeche.checkBlockTail_inv h
  rw [hpar, htbl] at hRec
  refine ⟨hnd.1, hnd.2, blockRawRec p₀, q.env₁, q.cvTas, p₁, q.p, q.ctorsAs, q.sortsss, ctx,
    holes, q.rd, q.cls, q.kinds, q.nfs, pos, st, isorts, rs, hInd, hp, ?_, ?_, ?_, ?_, hst, rfl,
    hsorts, hRec, hTbl⟩
  · rw [hp]; exact hCtors
  · rw [hp]; exact hctx
  · rw [hp]; exact hcls
  · rw [hp]; exact hK

end ConLeche.Semantics
