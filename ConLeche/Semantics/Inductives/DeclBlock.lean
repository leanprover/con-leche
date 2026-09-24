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
.ok rs` — so that milestone M5's replacement of the whole stage by a
CHECK changes that conjunct alone.

At ONE member the uniform installer IS the one-member installer
(`checkBlock_one`), so the same run also yields a `DeclNativeRun`
at the one-member reading of the record
(`declNativeRun_of_block_one`), which is how the P tier keeps
`declNative` as its `k = 1` discharge.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  BlockShape BlockParts MemberShape BlockFieldKind RecRule fueledOps
  checkBlockInds checkBlockCtors classifyBlockKinds checkBlockIdxSorts
  checkBlockRec checkBlockTables checkBlockPass checkBlockTail checkBlock
  consBlockCtors consBlockRecs blockFieldsOk blockCaps blockCapsAt blockIsRec
  blockRawRec BlockPass)

/-- **The uniform inductive declaration, as checked**: the stage runs
of `checkBlock`.  `env` is the pre-block environment; `p₀` the
recognised record; the pass the install settled on (task #268 at k
members) is the one recorded. -/
def DeclBlockRun (μ : CheckMode) (F : Nat) (env : Env)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTas : List ConstantVal) (p₁ : BlockShape) (p : BlockParts)
    (ctorsAs : List (List (ConstantVal × Nat))) (sortsss : List (List (List Level)))
    (kinds : List (List (List BlockFieldKind))) (isorts : List (List Level))
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))),
    -- 1  the k formers: the constant check, official's telescope loop, the
    --    sort, official's two agreements from member 1 on, then all k consed
    checkBlockInds (m := ConLeche.CheckM) (fueledOps μ F) env p₀ isRec
      = .ok (env₁, cvTas, p₁) ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    -- 2  the constructors, per member, at the environment holding all k formers
    checkBlockCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok (ctorsAs, sortsss) ∧
    -- 3  the kinds, classified against the WHOLE member list (the targets)
    classifyBlockKinds (m := ConLeche.CheckM) p.memberNames p.lps p.nP p.nIdxs ctorsAs
      = .ok kinds ∧
    -- 4  the capability record the block owes is the one every former carries
    (∀ i, i < p.k → blockCaps p i = blockCapsAt p₁ i isRec) ∧
    -- 5  the elimination restriction (official `elim_only_at_universe_zero`)
    (p.large = true → p.resSort.isNeverZero = true ∨ (p.k < 2 ∧ p.numCtors < 2)) ∧
    -- 6  every member's index binders' sorts
    checkBlockIdxSorts (m := ConLeche.CheckM) (fueledOps μ F) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts ∧
    -- 7  the kinds re-checked on the stored constructors, reading each field's TARGET
    blockFieldsOk env p.memberNames p.lps p.nP p.nIdxs ctorsAs p.kinds = true ∧
    -- 7b the positivity function on the stored constructors, and their
    --    member-abstracted types typed at the holes' context (lane HOLE2)
    checkBlockPositivity (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁.find? env₁.consts p
      cvTas ctorsAs = .ok () ∧
    -- 8  the recursor stage (milestone M5 replaces it by the CHECK of §4.2)
    checkBlockRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consBlockCtors p.nP ctorsAs env₁) p cvTas ctorsAs = .ok rs ∧
    -- 9  the install spine: the k recursors with their rules, then the tables
    checkBlockTables (m := ConLeche.CheckM) p.toBlockShape
      (p.members.zip (ctorsAs.zip sortsss))
      (consBlockRecs (consBlockCtors p.nP ctorsAs env₁).find? p.toBlockShape p.nP 0 rs
        (consBlockCtors p.nP ctorsAs env₁)) = .ok env₂

/-- A settled pass with the install after it is a run. -/
theorem declBlockRun_of_pass {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p₀ : BlockParts} {isRec : Bool} {q : BlockPass Env}
    (hnd : (p₀.allCtors.map (·.1.name)).Nodup) (hnm : p₀.memberNames.Nodup)
    (hP : checkBlockPass (m := ConLeche.CheckM) (fueledOps μ F) env p₀ isRec = .ok (q, true))
    (h : checkBlockTail (m := ConLeche.CheckM) (fueledOps μ F) env q = .ok env₂) :
    DeclBlockRun μ F env p₀ env₂ := by
  obtain ⟨p₁, kinds, hInd, hCtors, hK, hp, hb⟩ := ConLeche.checkBlockPass_inv hP
  obtain ⟨isorts, rs, helim, hsorts, hk, hPos, hRec, hTbl⟩ := ConLeche.checkBlockTail_inv h
  have hcaps : ∀ i, i < q.p.k → blockCaps q.p i = blockCapsAt p₁ i isRec := by
    intro i hi
    have := List.all_eq_true.mp hb.symm i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp this
  refine ⟨hnd, hnm, isRec, q.env₁, q.cvTas, p₁, q.p, q.ctorsAs, q.sortsss, kinds, isorts, rs,
    hInd, hp, ?_, ?_, hcaps, helim, hsorts, hk, hPos, hRec, hTbl⟩
  · rw [hp]; exact hCtors
  · rw [hp]; exact hK

/-- **The uniform install's run**: the settled pass — the first, or the
second where the capability record's syntactic reading overshot — and
the install after it. -/
theorem declBlockRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env} {p₀ : BlockParts}
    (h : checkBlock (m := ConLeche.CheckM) (fueledOps μ F) env p₀ = .ok env₂) :
    DeclBlockRun μ F env p₀ env₂ := by
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
  | ok r =>
  obtain ⟨q, settled⟩ := r
  rw [hP] at h
  dsimp only at h
  cases settled with
  | true => exact declBlockRun_of_pass hnd.1 hnd.2 hP (by simpa using h)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hP₂ : checkBlockPass (m := ConLeche.CheckM) (fueledOps μ F) env p₀
      (blockIsRec q.p.kinds) with
  | error e => rw [hP₂] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨q', settled'⟩ := r₂
  rw [hP₂] at h
  dsimp only at h
  cases settled' with
  | false => exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | true => exact declBlockRun_of_pass hnd.1 hnd.2 hP₂ (by simpa using h)

end ConLeche.Semantics
