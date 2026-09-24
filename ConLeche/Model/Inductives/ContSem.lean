module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Graphs

public section

/-!
# The container case of the positivity theorem (lane CONTSEM, steps 5–6)

`ContSem` — the premise `nestPos_sem` takes for its container case —
PROVED, at the kind predicate `True` and the state invariant `CacheInv`
(every looked-up container's constructor list is the environment's, and
every cached instantiation without a frame hole grows along every hole
relation at the block's own depth), from the frame lemma (`frame_sem`,
`ContWalk.lean`), the container's leaf (`monoOn_of_famLe`, `ContLeaf.lean`)
and coverage (`ContCover`, L8: every stored inductive the walk may meet
as a container is a member of a recorded block whose constructors are
the ones `nestContainer` lists; a named premise until the flip records a
clause for every inductive).  So `nestMemberCtor_sem` holds without the
container premise (`nestMemberCtor_sem_cont`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey NestHole NestState
  NestKeyInfo NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Coverage (L8, a named premise) -/

/-- A recorded block, as the container case reads it: its member names
distinct and recorded as their formers' `all`, and each member's
constructor list (`nestContainer`) its recorded constructors, in order,
at one parameter count. -/
structure ContBlockOk (env : Env) (ctx : NestCtx) (D : LfpDatum V) : Prop where
  nodup : D.names.Nodup
  all : ∀ mm, mm < D.k → ∀ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) →
    caps.all = D.names
  ctors : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
    L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
      env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2)

/-- **Coverage** (CONTSEM step 6, L8 owed): the walk's context reads the
environment, every stored inductive but `Quot` that is not a member of
the block being checked is a member of a recorded block, and every
recorded block is read as `ContBlockOk` says. -/
structure ContCover {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) : Prop where
  find : ∀ n, ctx.find? n = env.find? n
  cover : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → ctx.names.contains n = false →
    n ≠ ConLeche.quotName → ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n
  block : ∀ D ∈ mp.lfpBlocks, ContBlockOk env ctx D

/-! ## The cache invariant -/

/-- **A cached instantiation is positive** at the block's own depth: for
some recorded block holding its container (at the recorded parameter
count, the container's level parameters distinct), along every hole
relation without frames whose pairs satisfy the container's parameter
telescope at the key frames, the container's carrier grows between them. -/
@[expose] def KeyPos {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams key.lvls)).length = key.ds.length ∧
      ∀ (Δ0 : List AnnotTerm) (R00 : FrameRel V), HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δ0 R00 →
        Δ0.length = ctx.hiAt 0 → (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x) →
        ∀ dsa, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0) key.ds dsa →
        (∀ ρ ρ', R00 ρ ρ' →
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ) ∧
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ')) →
        ∀ ρ ρ', R00 ρ ρ' →
          FamLe (D.idx (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ') mm)

/-- **The cache invariant** (CONTSEM step 5). -/
@[expose] def CacheInv {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (ctx : NestCtx) (st : NestState) : Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = ConLeche.nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) → KeyPos mp φ ctx ki.key

theorem cacheInv_empty {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) :
    CacheInv mp φ ctx {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem cacheInv_ctorsOfOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) :
    CtorsOfOk ctx (CacheInv mp φ ctx) where
  lookup := by
    intro st hst c
    unfold ConLeche.nestContainerC
    split
    · rename_i r hr; exact hst.1 c r hr
    · rfl
  insert := by
    intro st hst c
    unfold ConLeche.nestContainerC
    split
    · exact hst
    · refine ⟨fun c' r h => ?_, hst.2⟩
      simp only [List.lookup] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        rw [← h]
        congr 1
        exact (beq_iff_eq.mp heq).symm
      · exact hst.1 c' r h
  mix := fun _ _ h₀ h => ⟨h.1, h₀.2⟩

end ConLeche.Model
