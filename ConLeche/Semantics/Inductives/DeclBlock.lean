module

public import ConLeche.Verify.Inductives.BlockInv
public import ConLeche.Verify.Inductives.StreamRecsInv
import ConLeche.Verify.Cached.BlockPushes

@[expose] public section

/-!
# `DeclBlockRun`: the inductive declaration relation at k members

The uniform arm of `checkDecl`'s `.indDecl` clause (`checkBlock`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), recorded as a run
relation: the two distinct-name guards, the k type formers' run (constant check,
official's telescope loop, the result sort, and — from member 1 on —
official's two agreements), the constructors' runs per member at the
environment holding ALL the formers, the kinds classified against the
whole member list, every member's index binders' sorts, the recursor stage, the stream's recursors
against the generated ones, the projection tables' checks, and the install (`blockConstants`,
`blockTables`).

**The recursor stage is one opaque conjunct** — `checkBlockRec … =
.ok rs`, the generated recursor stage (`genRecCheck`, on the raw
`block`: its pins read the stream's recursor records).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  BlockShape BlockShape MemberShape NestFieldKind RecRule fueledOps
  checkBlockInds checkBlockCtors checkBlockPositivity checkBlockIdxSorts
  checkBlockRec checkBlockTables checkBlockPass checkBlockTail checkBlock
  consBlockCtors consBlockRecs consBlockRecsT blockCapsAt
  blockConstants blockTables streamKCheck
  blockNestedBit blockIsRec BlockPass TargetMajor NestKey NestState)

/-- **The uniform inductive declaration, as checked**: the stage runs
of `checkBlock`.  `env` is the pre-block environment; `p₀` the
recognised record; the one pass runs at official's `is_rec`
(`blockIsRec`). -/
def DeclBlockRun (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockShape) (env₂ : Env) : Prop :=
  (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup ∧
  (boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames) ∧
  ∃ (isRec : Bool) (env₁ : Env) (p₁ : BlockShape)
    (sortsss : List (List (List Level)))
    (ctx : NestCtx) (holes : List Expr) (rd : ClassRead) (Ms : List TargetMajor)
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) (pos st : NestState)
    (isorts : List (List Level))
    (out : List (ConstantVal × TargetMajor × List Expr)),
    -- 1  the k formers: the constant check, official's telescope loop, the
    --    sort, official's two agreements from member 1 on, then all k consed
    checkBlockInds (m := ConLeche.CheckM) (fueledOps .verified F) env p₀ isRec
      = .ok (env₁, p₁) ∧
    -- 2  the constructors, per member, at the environment holding all k formers,
    --    each stored as declared
    BlockCtorsRun .verified F env₁ env₁ p₁
      p₁.members sortsss ∧
    -- 3  the walk's context; the classes the stream's recursor family eliminates
    --    (read off its raw recursor types, each checked as a major)
    blockNestCtx (m := ConLeche.CheckM) p₁ env₁.find?
      = .ok (ctx, holes) ∧
    checkBlockClasses (fueledOps .verified F) (mkFEnv env₁) p₁ ctx.params = .ok (rd, Ms) ∧
    -- 4  the positivity function on the stored constructors (the root frame), and
    --    their member-abstracted types typed at the holes' context; its field
    --    kinds are the block's `is_rec`, its normal forms the model's fields
    --    with holes; then every outside class walked from its state
    PositivityRun (fueledOps .verified F) env₁ env₁.find? p₁ kinds nfs pos ∧
    nestSeeds (fueledOps .verified F) env₁ ctx (classSeeds ctx holes Ms) pos = .ok st ∧
    -- 5  the formers carry the record at official's `is_rec`, the syntactic one
    isRec = blockIsRec p₀ ∧
    -- 6  every member's index binders' sorts
    BlockIdxSortsRun .verified F env₁ p₁
      p₁.members isorts ∧
    -- 7  the recursor stage: the GENERATED recursors, one per record of the
    --    stream's family, on the classes and the walk's table (the block's
    --    container bit)
    checkBlockRec (m := ConLeche.CheckM) (fueledOps .verified F)
      (consBlockCtors p₁.nP p₁.memberCtors env₁) p₁ (blockNestedBit p₁ kinds)
      ctx.params st.ctorNfs.toList rd Ms block = .ok out ∧
    -- 8  the stream's recursors against the generated ones: their K flags, then the
    --    rest at the environment holding the generated ones
    streamKCheck (m := ConLeche.CheckM) p₁ p₁.recs out = .ok () ∧
    streamRecsCheck (m := ConLeche.CheckM) (fueledOps .verified F) .plain
      (mkFEnv (consBlockRecsT p₁ 0 out
        (consBlockCtors p₁.nP p₁.memberCtors env₁))) p₁.recs out = .ok () ∧
    -- 9  the projection tables' checks
    checkBlockTables (m := ConLeche.CheckM) p₁ (consBlockCtors p₁.nP p₁.memberCtors env₁)
      p₁.members = .ok () ∧
    -- 10 the install: the formers and constructors above, the stream's recursors, the tables
    env₂ = (consBlockRecsT p₁ 0 (ConLeche.streamRecs p₁.recs out)
      (consBlockCtors p₁.nP p₁.memberCtors env₁)).pushDelta [] (blockTables p₁ p₁.members)

/-- **The block's run**: each member at its telescope, then the stages at those members. -/
def BlockRun (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockShape) (env₂ : Env) : Prop :=
  ∃ ms : List MemberShape,
    reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env p₀.nP p₀.members = .ok ms ∧
    (∀ m ∈ ms, ConLeche.MemberAt F env p₀.nP m) ∧
    ms.map (·.declared) = p₀.members.map (·.declared) ∧
    DeclBlockRun F env block { p₀ with members := ms } env₂

theorem blockRun_of {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockShape}
    (hd : ∀ m ∈ p₀.members, m.declared = m.cvT)
    (h : checkBlock (m := ConLeche.CheckM) (fueledOps .verified F) env block p₀ = .ok env₂) :
    BlockRun F env block p₀ env₂ := by
  rw [ConLeche.checkBlock] at h
  simp only [bind, Except.bind] at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg =>
    rw [ite_eq_right hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [ite_eq_left hnd] at h
  try simp only [bind, Except.bind] at h
  by_cases hbool : boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames
  case neg =>
    rw [ite_eq_right hbool] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [ite_eq_left hbool] at h
  try simp only [bind, Except.bind] at h
  cases hms : reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env p₀.nP p₀.members with
  | error e => rw [hms] at h; exact nomatch h
  | ok ms =>
  rw [hms] at h
  simp only at h
  obtain ⟨hall, hdecl, hname, -, hctors⟩ := ConLeche.reduceMembers_inv hd hms
  have hcs : ({ p₀ with members := ms } : BlockShape).allCtors = p₀.allCtors := by
    show (ms.map (·.ctors)).flatten = (p₀.members.map (·.ctors)).flatten
    rw [hctors]
  have hnm : ({ p₀ with members := ms } : BlockShape).memberNames = p₀.memberNames := hname
  have hraw : blockIsRec ({ p₀ with members := ms } : BlockShape) = blockIsRec p₀ := by
    unfold blockIsRec
    show (ms.any _) = (p₀.members.any _)
    rw [hnm]
    have e : ∀ (l : List MemberShape) (g : List (ConstantVal × Nat) → Bool),
        l.any (fun m => g m.ctors) = (l.map (·.ctors)).any g := by
      intro l g; induction l <;> simp_all
    exact (e ms fun cs => cs.any fun c => ConLeche.Expr.piDomsMentionAny p₀.memberNames c.1.type).trans
      (by rw [hctors]; exact (e p₀.members _).symm)
  cases hP : checkBlockPass (m := ConLeche.CheckM) (fueledOps .verified F) env
      { p₀ with members := ms } (blockIsRec p₀) with
  | error e => rw [hP] at h; exact nomatch h
  | ok q =>
  rw [hP] at h
  dsimp only at h
  obtain ⟨sortsss, nfs, ctx, holes, pos, st, hInd, hCtors, hctx, hcls, hP', hst, hpar, htbl⟩ :=
    ConLeche.checkBlockPass_inv hP
  cases hTail : ConLeche.checkBlockTail (m := ConLeche.CheckM) (fueledOps .verified F) block q with
  | error e => rw [hTail] at h; exact nomatch h
  | ok u =>
  cases u
  rw [hTail] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨isorts, rs, hsorts, hRec, hK, hS, hTbl⟩ := ConLeche.checkBlockTail_inv hTail
  rw [hpar, htbl] at hRec
  refine ⟨ms, hms, hall, hdecl, ?_, ?_, ?_, blockIsRec p₀, q.env₁, q.p,
    sortsss, ctx, holes, q.rd, q.cls, q.kinds, nfs, pos, st, isorts, rs, hInd, hCtors, hctx,
    hcls, hP', hst, hraw.symm, hsorts, hRec, hK, hS, hTbl, ?_⟩
  · rw [hcs]; exact hnd.1
  · rw [hnm]; exact hnd.2
  · rw [hnm]; exact hbool
  · obtain ⟨e₁, e₂⟩ := ConLeche.blockInstall_reduced hd hms
    have hInd' := hInd
    rw [← hraw] at hInd'
    obtain ⟨hmem⟩ : PLift (q.p.members = ms) := ⟨ConLeche.checkBlockInds_members hInd'⟩
    have hlps : q.p.lps = ({ p₀ with members := ms } : BlockShape).lps := by
      obtain ⟨_, _, _, _, _, -, hq, -⟩ := ConLeche.checkBlockInds_shape hInd'
      rw [hq]
      rfl
    have hnP : q.p.nP = ({ p₀ with members := ms } : BlockShape).nP := by
      obtain ⟨_, _, _, _, _, -, hq, -⟩ := ConLeche.checkBlockInds_shape hInd'
      rw [hq]
      rfl
    have hQ : blockTables q.p q.p.members = blockTables p₀ p₀.members := by
      rw [← e₂, hmem]
      exact ConLeche.blockTables_congr hnP hlps rfl rfl rfl
    rw [hQ, ← h, ← e₁]
    exact ConLeche.blockInstall_of_checks (Q := blockTables p₀ p₀.members)
      hInd' hcls hRec hK hS

/-- **What a block's run installs**: the block's constants and tables, read off the group
(`blockConstants`, `blockTables`). -/
theorem blockRun_env {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockShape}
    (hd : ∀ m ∈ p₀.members, m.declared = m.cvT) (h : BlockRun F env block p₀ env₂) :
    env₂ = env.pushDelta (blockConstants p₀) (blockTables p₀ p₀.members) := by
  obtain ⟨ms, hms, -, -, hR⟩ := h
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds, nfs, pos, st, isorts, out,
    hInd, -, -, hcls, -, -, hraw, -, hRec, hK, hS, -, hfin⟩ := hR
  subst hraw
  obtain ⟨e₁, e₂⟩ := ConLeche.blockInstall_reduced hd hms
  obtain ⟨hmem⟩ : PLift (p₁.members = ms) := ⟨ConLeche.checkBlockInds_members hInd⟩
  have hlps : p₁.lps = ({ p₀ with members := ms } : BlockShape).lps := by
    obtain ⟨_, _, _, _, _, -, hq, -⟩ := ConLeche.checkBlockInds_shape hInd
    rw [hq]
    rfl
  have hnP : p₁.nP = ({ p₀ with members := ms } : BlockShape).nP := by
    obtain ⟨_, _, _, _, _, -, hq, -⟩ := ConLeche.checkBlockInds_shape hInd
    rw [hq]
    rfl
  have hQ : blockTables p₁ p₁.members = blockTables p₀ p₀.members := by
    rw [← e₂, hmem]
    exact ConLeche.blockTables_congr hnP hlps rfl rfl rfl
  rw [hfin, ← hQ, ← e₁]
  exact (ConLeche.blockInstall_of_checks (Q := blockTables p₁ p₁.members) hInd hcls hRec hK hS).symm

end ConLeche.Semantics
