module

public import ConLeche.Model.Inductives.ContSem
public import ConLeche.Model.Cover

public section

/-!
# `ContCover` from coverage (lane L8)

NESTPLAN L8 (U6).  Coverage itself (`LfpCover`), its producers and the
fold step's shape that carries it live in `Model/Cover.lean`; this file
is `contCover_of` — how it discharges CONTSEM's `ContCover` premise
(`ContSem.lean`, `nestMemberCtor_sem_cont`) at a block's positivity
walk (`ex` = the walk's `ctx.names`).  What stands between the fold and
this: `_tmp/uniform-inds/L2L8.md`, and the L8a record in DESIGN.md.
-/

namespace ConLeche.Model
open ConLeche (Env Name ConstantInfo NestCtx)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-- **`ContCover` from coverage** — how L8 discharges CONTSEM's premise
at a block's positivity walk: the walk's context reads the environment,
the block being walked is the exemption list, and every recorded block
lists its constructors as `nestContainer` reads them (`ctors`, a fact
about the stored constructors that coverage does not carry: see
`_tmp/uniform-inds/L2L8.md`), and a member without constructors at its
recorded parameter count (`noCtors`, lane RESTRICT-FIX: the install's
`IndCaps.nparams` is the block's `nP`, its former's level parameters
the block's, distinct by `checkConstantVal`). -/
theorem contCover_of {env : Env} {mp : EnvModelM V μ env} {ctx : NestCtx}
    (h : LfpCover mp ctx.names) (hfind : ∀ n, ctx.find? n = env.find? n)
    (hctors : ∀ D ∈ mp.lfpBlocks, ∀ c, c < D.k → ∃ nP' L,
      ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2))
    (hnoCtors : ∀ D ∈ mp.lfpBlocks, ∀ c, c < D.k → ∀ nP',
      ConLeche.nestContainer ctx (D.member c) = some (nP', []) →
      ∃ cv caps, env.find? (D.member c) = some (.indInfo cv caps) ∧ cv.levelParams.Nodup ∧
        (∀ ψ, (D.params ψ).length = nP') ∧
        ∀ mm, mm < D.k → ∃ cvm capsm, env.find? (D.member mm) = some (.indInfo cvm capsm) ∧
          cvm.levelParams = cv.levelParams) :
    ContCover mp ctx where
  find := hfind
  cover := fun n cv caps hf hn hq =>
    h.cover n cv caps hf (by simpa using hn) hq
  block := fun D hD =>
    { nodup := h.nodup D hD
      all := h.all D hD
      ctors := hctors D hD
      noCtors := hnoCtors D hD }

end ConLeche.Model
