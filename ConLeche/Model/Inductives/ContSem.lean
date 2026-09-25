module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContN2
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Graphs
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# The container case's coverage (lane CONTSEM, steps 5–6)

Coverage (`ContCover`, L8): every stored inductive the positivity walk
may meet as a container is a member of a recorded block whose
constructors are the ones `nestContainer` lists.  The container case
itself is proved by induction on the positivity derivation
(`PosDerivMono.lean`, lane POSDERIV); this file keeps its coverage
premise and the pieces the accessibility twin (`ContAcc.lean`) shares.
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
  /-- a member WITHOUT constructors (lane RESTRICT-FIX, finding C1): the
  parameter count `nestContainer` reads for it (its former's recorded
  `IndCaps.nparams`) is the block's, and its former's level parameters
  are distinct and the block's — what the first constructor's record
  says of a member with constructors (`LfpCtorReads`, the frame's
  `Name.nodup` check) -/
  noCtors : ∀ c, c < D.k → ∀ nP', ConLeche.nestContainer ctx (D.member c) = some (nP', []) →
    ∃ cv caps, env.find? (D.member c) = some (.indInfo cv caps) ∧ cv.levelParams.Nodup ∧
      (∀ ψ, (D.params ψ).length = nP') ∧
      ∀ mm, mm < D.k → ∃ cvm capsm, env.find? (D.member mm) = some (.indInfo cvm capsm) ∧
        cvm.levelParams = cv.levelParams

/-- **Coverage** (CONTSEM step 6, L8 owed): the walk's context reads the
environment, every stored inductive but `Quot` that is not a member of
the block being checked is a member of a recorded block, and every
recorded block is read as `ContBlockOk` says. -/
structure ContCover {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) : Prop where
  find : ∀ n, ctx.find? n = env.find? n
  cover : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → ctx.names.contains n = false →
    n ≠ ConLeche.quotName → ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n
  block : ∀ D ∈ mp.lfpBlocks, ContBlockOk env ctx D

/-! ## Pieces -/

/-- The key frame seen through empty frames on top. -/
theorem keyFrame_lift (dsa : List AnnotTerm) (h : Nat) (vs : List V) (ρ : Nat → V) :
    keyFrame (dsa.map (AnnotTerm.liftN vs.length · 0)) (h + vs.length) (consList vs ρ)
      = keyFrame dsa h ρ := by
  unfold keyFrame
  rw [List.map_map]
  congr 1
  · exact List.map_congr_left fun a _ => interp_liftN_consList vs ρ a
  · funext j
    rw [show j + (h + vs.length) = (j + h) + vs.length by omega, consList_apply_add]

/-- A recorded block's names and members, from its record. -/
theorem lfp_namesLen {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) : D.names.length = D.k :=
  (mp.lfp_ok D hD).2.2.2.1

/-- The arguments' leaves are the application's. -/
theorem leaves_mkAppN_arg {l : Nat × Expr} :
    ∀ {xs : List Expr} {f x : Expr}, x ∈ xs → l ∈ x.fvarLeaves → l ∈ (Expr.mkAppN f xs).fvarLeaves
  | [], _, _, hx, _ => nomatch hx
  | y :: ys, f, x, hx, hl => by
    simp only [Expr.mkAppN]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact leaves_mkAppN_head (by simp [Expr.fvarLeaves, hl])
    · exact leaves_mkAppN_arg hx hl
where
  leaves_mkAppN_head : ∀ {xs : List Expr} {f : Expr}, l ∈ f.fvarLeaves →
      l ∈ (Expr.mkAppN f xs).fvarLeaves
    | [], _, h => h
    | y :: ys, f, h => by
      simp only [Expr.mkAppN]
      exact leaves_mkAppN_head (by simp [Expr.fvarLeaves, h])

theorem nestContainer_find {ctx : NestCtx} {C : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : ConLeche.nestContainer ctx C = some q) :
    ∃ cv caps, ctx.find? C = some (.indInfo cv caps) := by
  unfold ConLeche.nestContainer at h
  split at h
  · rename_i cv caps hf; exact ⟨cv, caps, hf⟩
  · exact nomatch h

end ConLeche.Model
