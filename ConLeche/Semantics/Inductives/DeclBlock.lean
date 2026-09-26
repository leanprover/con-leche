module

public import ConLeche.Verify.Inductives.BlockInv

@[expose] public section

/-!
# `DeclBlockRun`: the uniform inductive declaration relation at k
members (the uniform inductive route, milestone M4)

The uniform arm of `checkDecl`'s `.indDecl` clause (`checkBlock`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), recorded as a run
relation exactly as `DeclNativeRun` records the one-member one: the two
distinct-name guards, the k type formers' run (constant check,
official's telescope loop, the result sort, and — from member 1 on —
official's two agreements), the constructors' runs per member at the
environment holding ALL the formers, the kinds classified against the
whole member list, the capability record the block owes, the
elimination restriction, every member's index binders' sorts, the kinds
re-checked on the stored constructors at the TARGET each carries, the
recursor stage, and the install spine (the constructors consed, the
recursors consed with their rules, a projection table per
structure-like member).

**The recursor stage is one opaque conjunct** — `checkBlockRec … =
.ok rs`, the target CHECK (`checkBlockRecT`, on the raw `block`: its
pins read the stream's recursor records) followed by the reject-only
conformance check.

At ONE member the uniform installer IS the one-member installer
(`checkBlock_one`), so the same run also yields a `DeclNativeRun`
at the one-member reading of the record
(`declNativeRun_of_block_one`), which is how the P tier keeps
`declNative` as its `k = 1` discharge.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  BlockShape BlockParts MemberShape NestFieldKind RecRule fueledOps
  checkBlockInds checkBlockCtors checkBlockPositivity checkBlockIdxSorts
  checkBlockRec checkBlockTables checkBlockPass checkBlockTail checkBlock
  consBlockCtors consBlockRecs consBlockRecsT blockCapsAt nestKindsFlat
  blockNestedBit blockRawRec BlockPass TargetMajor NestKey)

/-- **The uniform inductive declaration, as checked**: the stage runs
of `checkBlock`.  `env` is the pre-block environment; `p₀` the
recognised record; the one pass runs at official's `is_rec`
(`blockRawRec`). -/
def DeclBlockRun (μ : CheckMode) (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTas : List ConstantVal) (p₁ : BlockShape) (p : BlockParts)
    (ctorsAs : List (List (ConstantVal × Nat))) (sortsss : List (List (List Level)))
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) (nodes : NestNodes)
    (isorts : List (List Level))
    (out : List (ConstantVal × TargetMajor × List Expr)),
    -- 1  the k formers: the constant check, official's telescope loop, the
    --    sort, official's two agreements from member 1 on, then all k consed
    checkBlockInds (m := ConLeche.CheckM) (fueledOps μ F) env p₀ isRec
      = .ok (env₁, cvTas, p₁) ∧
    p = p₀.complete p₁ ∧
    -- 2  the constructors, per member, at the environment holding all k formers,
    --    each stored as declared (lane ALPHA1)
    checkBlockCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok (ctorsAs, sortsss) ∧
    -- 3  the positivity function on the stored constructors, and their
    --    member-abstracted types typed at the holes' context (lane HOLE2);
    --    its field kinds are the block's `is_rec`, its normal forms (lane
    --    ALPHA1) the model's fields with holes
    checkBlockPositivity (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁.find? env₁.consts p
      cvTas ctorsAs = .ok (kinds, nfs, nodes) ∧
    -- 4  the formers carry the record at official's `is_rec`, the syntactic one
    isRec = blockRawRec p₀ ∧
    -- 5  the elimination restriction (official `elim_only_at_universe_zero`)
    (p.large = true → p.resSort.isNeverZero = true ∨ (p.k < 2 ∧ p.numCtors < 2)) ∧
    -- 6  every member's index binders' sorts
    checkBlockIdxSorts (m := ConLeche.CheckM) (fueledOps μ F) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts ∧
    -- 8  the recursor stage: the target CHECK on the stream's family (outside
    --    majors at the auxiliary types, the block's container bit), then —
    --    where every kind is flat — the reject-only conformance check (on the
    --    constructors at their positivity normal forms)
    checkBlockRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consBlockCtors p.nP ctorsAs env₁) p (blockNestedBit p.toBlockShape kinds)
      (nestKindsFlat kinds) nodes block cvTas ctorsAs
      (ConLeche.blockNormalCtors p.toBlockShape ctorsAs nfs) = .ok out ∧
    -- 9  the install spine: the recursors with their rules at their majors,
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
    rw [if_neg hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  cases hP : checkBlockPass (m := ConLeche.CheckM) (fueledOps μ F) env p₀ (blockRawRec p₀) with
  | error e => rw [hP] at h; exact nomatch h
  | ok q =>
  rw [hP] at h
  dsimp only at h
  obtain ⟨p₁, hInd, hCtors, hK, hp⟩ := ConLeche.checkBlockPass_inv hP
  obtain ⟨isorts, rs, helim, hsorts, hRec, hTbl⟩ := ConLeche.checkBlockTail_inv h
  refine ⟨hnd.1, hnd.2, blockRawRec p₀, q.env₁, q.cvTas, p₁, q.p, q.ctorsAs, q.sortsss, q.kinds,
    q.nfs, q.nodes, isorts, rs, hInd, hp, ?_, ?_, rfl, helim, hsorts, hRec, hTbl⟩
  · rw [hp]; exact hCtors
  · rw [hp]; exact hK

end ConLeche.Semantics
