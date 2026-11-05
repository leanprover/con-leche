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
def DeclBlockRun (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup ∧
  (boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames) ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTas : List ConstantVal) (p₁ : BlockShape) (p : BlockParts)
    (ctorsAs : List (List (ConstantVal × Nat))) (sortsss : List (List (List Level)))
    (ctx : NestCtx) (holes : List Expr) (rd : ClassRead) (Ms : List TargetMajor)
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) (pos st : NestState)
    (isorts : List (List Level))
    (out : List (ConstantVal × TargetMajor × List Expr)),
    -- 1  the k formers: the constant check, official's telescope loop, the
    --    sort, official's two agreements from member 1 on, then all k consed
    checkBlockInds (m := ConLeche.CheckM) (fueledOps .verified F) env p₀ isRec
      = .ok (env₁, cvTas, p₁) ∧
    p = p₀.complete p₁ ∧
    -- 2  the constructors, per member, at the environment holding all k formers,
    --    each stored as declared
    checkBlockCtors (m := ConLeche.CheckM) (fueledOps .verified F) env₁ env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok (ctorsAs, sortsss) ∧
    -- 3  the walk's context; the classes the stream's recursor family eliminates
    --    (read off its raw recursor types, each checked as a major)
    blockNestCtx (m := ConLeche.CheckM) p.toBlockShape cvTas env₁.find?
      = .ok (ctx, holes) ∧
    checkBlockClasses (fueledOps .verified F) (mkFEnv env₁) p.toBlockShape ctx.params ctorsAs
      = .ok (rd, Ms) ∧
    -- 4  the positivity function on the stored constructors (the root frame), and
    --    their member-abstracted types typed at the holes' context; its field
    --    kinds are the block's `is_rec`, its normal forms the model's fields
    --    with holes; then every outside class walked from its state
    checkBlockPositivity (m := ConLeche.CheckM) (fueledOps .verified F) env₁ env₁.find? p
      cvTas ctorsAs = .ok (kinds, nfs, pos) ∧
    nestSeeds (fueledOps .verified F) env₁ ctx (classSeeds ctx holes Ms) pos = .ok st ∧
    -- 5  the formers carry the record at official's `is_rec`, the syntactic one
    isRec = blockRawRec p₀ ∧
    -- 6  every member's index binders' sorts
    checkBlockIdxSorts (m := ConLeche.CheckM) (fueledOps .verified F) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts ∧
    -- 7  the recursor stage: the GENERATED recursors, one per record of the
    --    stream's family, on the classes and the walk's table (the block's
    --    container bit)
    checkBlockRec (m := ConLeche.CheckM) (fueledOps .verified F)
      (consBlockCtors p.nP ctorsAs env₁) p (blockNestedBit p.toBlockShape kinds)
      ctx.params st.ctorNfs.toList rd Ms block cvTas = .ok out ∧
    -- 7' the STORED recursors against the generated ones, at the generated
    --    install (task #431)
    storedRecsCheck (m := ConLeche.CheckM) (fueledOps .verified F) .plain
      (mkFEnv (consBlockRecsT p.toBlockShape 0 out
        (consBlockCtors p.nP ctorsAs env₁))) p.recs out = .ok () ∧
    -- 8  the install spine: the STORED recursors with their rules at their
    --    majors, then the tables
    checkBlockTables (m := ConLeche.CheckM) p.toBlockShape
      (p.members.zip (ctorsAs.zip sortsss))
      (consBlockRecsT p.toBlockShape 0
        (storedOut p.recs out) (consBlockCtors p.nP ctorsAs env₁)) = .ok env₂

/-- **The ordinary path's run**: the pass at official's `is_rec` and the install after it. -/
theorem declBlockRun_of {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockParts}
    (hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup)
    (hbool : boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames)
    (h : checkBlockAt (m := ConLeche.CheckM) (fueledOps .verified F) env block p₀ = .ok env₂) :
    DeclBlockRun F env block p₀ env₂ := by
  rw [ConLeche.checkBlockAt] at h
  simp only [bind, Except.bind] at h
  cases hP : checkBlockPass (m := ConLeche.CheckM) (fueledOps .verified F) env p₀ (blockRawRec p₀) with
  | error e => rw [hP] at h; exact nomatch h
  | ok q =>
  rw [hP] at h
  dsimp only at h
  obtain ⟨p₁, ctx, holes, pos, st, hInd, hCtors, hctx, hcls, hK, hst, hpar, htbl, hp⟩ :=
    ConLeche.checkBlockPass_inv hP
  obtain ⟨isorts, rs, hsorts, hRec, hS, hTbl⟩ := ConLeche.checkBlockTail_inv h
  rw [hpar, htbl] at hRec
  refine ⟨hnd.1, hnd.2, hbool, blockRawRec p₀, q.env₁, q.cvTas, p₁, q.p, q.ctorsAs, q.sortsss, ctx,
    holes, q.rd, q.cls, q.kinds, q.nfs, pos, st, isorts, rs, hInd, hp, ?_, ?_, ?_, ?_, hst, rfl,
    hsorts, hRec, hS, hTbl⟩
  · rw [hp]; exact hCtors
  · rw [hp]; exact hctx
  · rw [hp]; exact hcls
  · rw [hp]; exact hK

/-- The members' reduction keeps their names and constructors. -/
theorem reduceMembers_shape {F : Nat} {env : Env} {nP : Nat} {p₀ : BlockParts}
    {ms : List MemberShape}
    (h : reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env nP p₀.members = .ok ms) :
    ms.map (·.cvT.name) = p₀.members.map (·.cvT.name) ∧
      ({ p₀ with members := ms } : BlockParts).allCtors = p₀.allCtors := by
  have hgo : ∀ {l l' : List MemberShape},
      reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env nP l = .ok l' →
      l'.map (·.cvT.name) = l.map (·.cvT.name) ∧ l'.map (·.ctors) = l.map (·.ctors) := by
    intro l
    induction l with
    | nil => intro l' h; cases h; exact ⟨rfl, rfl⟩
    | cons m rest ih =>
      intro l' h
      simp only [reduceMembers, bind, Except.bind] at h
      cases hm : reduceMember (m := ConLeche.CheckM) (fueledOps .verified F) env nP m with
      | error e => rw [hm] at h; exact nomatch h
      | ok m' =>
      rw [hm] at h
      simp only at h
      cases hr : reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env nP rest with
      | error e => rw [hr] at h; exact nomatch h
      | ok r' =>
      rw [hr] at h
      obtain rfl : m' :: r' = l' := by simpa [pure, Except.pure] using h
      obtain ⟨h₁, h₂⟩ := ih hr
      have hmm : m'.cvT.name = m.cvT.name ∧ m'.ctors = m.ctors := by
        simp only [reduceMember] at hm
        split at hm
        · split at hm
          · simp [throw, throwThe, MonadExceptOf.throw] at hm
          simp only [bind, Except.bind] at hm
          split at hm
          · exact nomatch hm
          · split at hm
            · exact nomatch hm
            · rename_i hrf
              simp only [reducedFormer, bind, Except.bind] at hrf
              split at hrf
              · exact nomatch hrf
              · cases hrf
                split at hm
                · exact nomatch hm
                · split at hm
                  · exact nomatch hm
                  · split at hm
                    · cases hm; exact ⟨rfl, rfl⟩
                    · simp [throw, throwThe, MonadExceptOf.throw] at hm
        · cases hm; exact ⟨rfl, rfl⟩
      simp [h₁, h₂, hmm.1, hmm.2]
  obtain ⟨h₁, h₂⟩ := hgo h
  refine ⟨h₁, ?_⟩
  show (ms.map (·.ctors)).flatten = (p₀.members.map (·.ctors)).flatten
  rw [h₂]

/-- **The second path's run**: the group reduced, the containers' views on top, the ordinary run
there, and the block's constants restored at their stored formers. -/
def BlockViewedRun (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  ∃ (ms : List MemberShape) (vs : List ConstantInfo) (env₃ : Env),
    reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env p₀.nP p₀.members = .ok ms ∧
    blockViews (m := ConLeche.CheckM) (fueledOps .verified F) env
      (blockContainers env.find? p₀) = .ok vs ∧
    DeclBlockRun F ⟨vs ++ env.consts, env.tables⟩ (block.map (reducedRecord ms))
      { p₀ with members := ms } env₃ ∧
    env₂ = restoreBlock p₀ vs.length env env₃

/-- **The block's run**, on either path. -/
def BlockRun (F : Nat) (env : Env) (block : List ConstantInfo)
    (p₀ : BlockParts) (env₂ : Env) : Prop :=
  DeclBlockRun F env block p₀ env₂ ∨ BlockViewedRun F env block p₀ env₂

theorem blockRun_of {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockParts}
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
  by_cases hv : blockViewed env.find? (blockContainers env.find? p₀) p₀ = true
  · rw [ite_eq_left hv] at h
    try simp only [bind, Except.bind] at h
    cases hms : reduceMembers (m := ConLeche.CheckM) (fueledOps .verified F) env p₀.nP p₀.members with
    | error e => rw [hms] at h; exact nomatch h
    | ok ms =>
    rw [hms] at h
    simp only at h
    cases hvs : blockViews (m := ConLeche.CheckM) (fueledOps .verified F) env
        (blockContainers env.find? p₀) with
    | error e => rw [hvs] at h; exact nomatch h
    | ok vs =>
    rw [hvs] at h
    simp only at h
    cases hA : checkBlockAt (m := ConLeche.CheckM) (fueledOps .verified F)
        ⟨vs ++ env.consts, env.tables⟩ (block.map (reducedRecord ms))
        { p₀ with members := ms } with
    | error e => rw [hA] at h; exact nomatch h
    | ok env₃ =>
    rw [hA] at h
    obtain rfl : restoreBlock p₀ vs.length env env₃ = env₂ := by
      simpa [pure, Except.pure] using h
    have hnd' : (({ p₀ with members := ms } : BlockParts).allCtors.map (·.1.name)).Nodup ∧
        ({ p₀ with members := ms } : BlockParts).memberNames.Nodup := by
      have hs := reduceMembers_shape hms
      exact ⟨by rw [hs.2]; exact hnd.1, by
        show (ms.map _).Nodup; rw [hs.1]; exact hnd.2⟩
    have hb' : boolTrueName ∉ ({ p₀ with members := ms } : BlockParts).memberNames ∧
        boolFalseName ∉ ({ p₀ with members := ms } : BlockParts).memberNames := by
      have hs := reduceMembers_shape hms
      constructor
      · show boolTrueName ∉ ms.map _; rw [hs.1]; exact hbool.1
      · show boolFalseName ∉ ms.map _; rw [hs.1]; exact hbool.2
    exact .inr ⟨ms, vs, env₃, hms, hvs, declBlockRun_of hnd' hb' hA, rfl⟩
  · rw [ite_eq_right hv] at h
    exact .inl (declBlockRun_of hnd hbool h)

end ConLeche.Semantics
