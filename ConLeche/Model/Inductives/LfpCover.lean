module

public import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Install

public section

/-!
# Coverage: every stored inductive is a member of a recorded block (lane L8)

NESTPLAN L8 (U6), charter item 2 ("the model needs only this
least-fixed-point clause from each inductive").  `LfpCover mp ex`: every
stored inductive but `Quot` and the names in `ex` (the block being
installed — its formers are stored before its clause is recorded) is a
member of a recorded block (`EnvModelM.lfpBlocks`), and every recorded
block's names are distinct, as many as its members, and its members'
stored `all` lists them.

**Not an `EnvModelM` field, and not yet threaded through the fold.**
It is FALSE while the modeller can install an `.indInfo`
(`Model/DeclInd.lean` records no clause; NESTPLAN Q-B), so it lands with
the flip (L9).  What is here: the statement, its producers and transports
(`lfpCover_empty`, `LfpCover.transport` — every extension that re-reads
no stored name and keeps the recorded list, which is what the cons
funnel `Install.lean` and the swap `Swap.lean` build — `LfpCover.pend`
for a former's cons, `LfpCover.addLfp` for the block's record), and
`contCover_of` — how it discharges CONTSEM's `ContCover` premise
(`ContSem.lean`, `nestMemberCtor_sem_cont`) at a block's positivity
walk (`ex` = the walk's `ctx.names`).  The fold-level statement and
what stands between it and this file: `_tmp/uniform-inds/L2L8.md`.
-/

namespace ConLeche.Model
open ConLeche (Env Name ConstantInfo NestCtx)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-- **Coverage** (L8's `lfp_cover`), except at the names `ex`. -/
structure LfpCover {env : Env} (mp : EnvModelM V μ env) (ex : List Name) : Prop where
  cover : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → n ∉ ex →
    n ≠ ConLeche.quotName → ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n
  nodup : ∀ D ∈ mp.lfpBlocks, D.names.Nodup
  len : ∀ D ∈ mp.lfpBlocks, D.names.length = D.k
  all : ∀ D ∈ mp.lfpBlocks, ∀ mm, mm < D.k → ∀ cv caps,
    env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names

/-- The empty environment is covered. -/
theorem lfpCover_empty : LfpCover (EnvModelM.empty V μ) [] where
  cover := fun _ _ _ h => by
    rw [show Env.empty.find? _ = none from rfl] at h; exact nomatch h
  nodup := fun _ hD => nomatch hD
  len := fun _ hD => nomatch hD
  all := fun _ hD => nomatch hD

/-- **Transport** across an extension that keeps the recorded list and
every stored constant, and stores no new inductive outside `ex'`. -/
theorem LfpCover.transport {env env' : Env} {mp : EnvModelM V μ env}
    {mp' : EnvModelM V μ env'} {ex ex' : List Name} (h : LfpCover mp ex)
    (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hfwd : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hback : ∀ n cv caps, env'.find? n = some (.indInfo cv caps) → n ∉ ex' →
      env.find? n = some (.indInfo cv caps) ∧ n ∉ ex) :
    LfpCover mp' ex' where
  cover := fun n cv caps hf hn hq => by
    obtain ⟨hf0, hn0⟩ := hback n cv caps hf hn
    rw [hL]; exact h.cover n cv caps hf0 hn0 hq
  nodup := fun D hD => h.nodup D (hL ▸ hD)
  len := fun D hD => h.len D (hL ▸ hD)
  all := fun D hD mm hmm cv caps hf => by
    rw [hL] at hD
    obtain ⟨cv0, caps0, hf0⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
    rw [hfwd _ _ hf0] at hf
    injection hf with hf
    injection hf with _ hcaps
    subst hcaps
    exact h.all D hD mm hmm _ _ hf0

/-- **A former's cons** (or any cons of a fresh constant): the new name
joins the exemption list. -/
theorem LfpCover.pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩} {ex : List Name} (h : LfpCover mp ex)
    (hfresh : env.find? c₀.name = none) (hL : mp'.lfpBlocks = mp.lfpBlocks) :
    LfpCover mp' (c₀.name :: ex) :=
  h.transport hL (fun _ _ hf => findPreserved_cons hfresh hf)
    (fun n cv caps hf hn => by
      rw [ConLeche.Env.find?_cons] at hf
      split at hf
      · rename_i heq
        exact absurd (List.mem_cons.mpr (Or.inl (by simpa using heq.symm))) hn
      · exact ⟨hf, fun h' => hn (List.mem_cons_of_mem _ h')⟩)

/-- **The block's record** (`EnvModelM.addLfp`, `declBlock`'s step at
its constructors' environment): the block's members leave the
exemption list, given its names distinct, one per member, and listed as
their formers' `all`. -/
theorem LfpCover.addLfp {env : Env} {mp : EnvModelM V μ env} {ex : List Name}
    (h : LfpCover mp ex) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names) :
    LfpCover (mp.addLfp D hL hst hrd hrdC) (ex.filter (· ∉ D.names)) where
  cover := fun n cv caps hf hn hq => by
    by_cases hD : n ∈ D.names
    · obtain ⟨mm, hmm, rfl⟩ := List.getElem_of_mem hD
      refine ⟨D, EnvModelM.mem_addLfp mp D hL hst hrd hrdC, mm, hlen ▸ hmm, ?_⟩
      simp [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm]
    · have hn0 : n ∉ ex := fun h' => hn (List.mem_filter.mpr ⟨h', by simpa using hD⟩)
      obtain ⟨D', hD', rest⟩ := h.cover n cv caps hf hn0 hq
      exact ⟨D', List.mem_cons_of_mem _ hD', rest⟩
  nodup := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hnd
    · exact h.nodup D' h'
  len := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hlen
    · exact h.len D' h'
  all := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hall
    · exact h.all D' h'

/-- **`ContCover` from coverage** — how L8 discharges CONTSEM's premise
at a block's positivity walk: the walk's context reads the environment,
the block being walked is the exemption list, and every recorded block
lists its constructors as `nestContainer` reads them (`ctors`, a fact
about the stored constructors that coverage does not carry: see
`_tmp/uniform-inds/L2L8.md`). -/
theorem contCover_of {env : Env} {mp : EnvModelM V μ env} {ctx : NestCtx}
    (h : LfpCover mp ctx.names) (hfind : ∀ n, ctx.find? n = env.find? n)
    (hctors : ∀ D ∈ mp.lfpBlocks, ∀ c, c < D.k → ∃ nP' L,
      ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2)) :
    ContCover mp ctx where
  find := hfind
  cover := fun n cv caps hf hn hq =>
    h.cover n cv caps hf (by simpa using hn) hq
  block := fun D hD =>
    { nodup := h.nodup D hD
      all := h.all D hD
      ctors := hctors D hD }

end ConLeche.Model
