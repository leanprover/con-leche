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
at a block's positivity walk: the walk's context reads the environment
(its `find?` and its constants), the block being walked is the
exemption list, and coverage carries each recorded block's constructor
ownership (`LfpOwn`, lane COVERB), which `nestContainer` at the walk's
context reads as at the environment's (`nestContainer_ctx`). -/
theorem contCover_of {env : Env} {mp : EnvModelM V μ env} {ctx : NestCtx}
    (h : LfpCover mp ctx.names) (hfind : ∀ n, ctx.find? n = env.find? n)
    (hconsts : ctx.consts = env.consts) :
    ContCover mp ctx where
  find := hfind
  cover := fun n cv caps hf hn hq =>
    h.cover n cv caps hf (by simpa using hn) hq
  block := fun D hD =>
    { nodup := h.nodup D hD
      all := h.all D hD
      ctors := fun c hc => by
        rw [nestContainer_ctx hfind hconsts]
        exact (h.own D hD).ctors c hc
      noCtors := fun c hc nP' hL => by
        rw [nestContainer_ctx hfind hconsts] at hL
        exact (h.own D hD).noCtors c hc nP' hL }

end ConLeche.Model
