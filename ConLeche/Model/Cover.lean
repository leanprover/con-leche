module

public import ConLeche.Model.Install
import ConLeche.Model.Annot.CanonCrest

public section

/-!
# Coverage, and the fold step's shape that carries it (lanes L8, L8a)

NESTPLAN L8 (U6), charter item 2 ("the model needs only this
least-fixed-point clause from each inductive").  `LfpCover mp ex`: every
stored inductive but `Quot` and the names in `ex` (the block being
installed — its formers are stored before its clause is recorded) is a
member of a recorded block (`EnvModelM.lfpBlocks`), and every recorded
block's names are distinct, as many as its members, and its members'
stored `all` lists them.

**Not an `EnvModelM` field.**  It is FALSE while the modeller can
install an `.indInfo` (`Model/DeclInd.lean` records no clause; NESTPLAN
Q-B), so the fold carries it CONDITIONALLY (`Model/Fold.lean`,
`EnvModelOk`, under `FoldCoverPB`) until the flip (L9).

**The step shape (lane L8a).**  A fold step concludes
`CoverStep mp env₂` — `∃ mp' : EnvModelM V μ env₂, LfpCover mp [] →
LfpCover mp' []`: a carrier at the step's result, together with
coverage carried from the input carrier to it.  Not the weaker
`mp.lfpBlocks ⊆ mp'.lfpBlocks ∧ …`: coverage needs, beyond the recorded
list, which inductives the step STORES (a fresh one must be recorded or
exempt) and, at a record, that the block's names are distinct and are
its members' `all` — facts of the step, available only where the step
is proved.  The implication states exactly what the fold consumes and
composes (`CoverTo.trans`).  Inside a step, the chain of conses moves
the exemption list (`CoverTo mp ex env' ex'`): a former's cons adds its
name, the block's record (`EnvModelM.addLfp`) removes its names, every
other cons keeps it (`coverA_cons`, from the cons funnel's
`∃ mp', mp'.base2.acval = …` by `EnvModelM.keepLfp`: the funnel's
carrier with the input's recorded list, re-proved at the extension).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche (Env Name ConstantInfo)

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

/-- **A fresh cons** keeping the recorded list: the exemption list may
grow, and the new constant, if an inductive, is `Quot` or exempt.  A
former's cons is `hni := Or.inr (mem_cons_self)` (`LfpCover.pend`);
every other kind is vacuous in `hni`. -/
theorem LfpCover.cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩} {ex ex' : List Name} (h : LfpCover mp ex)
    (hfresh : env.find? c₀.name = none) (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hex : ∀ n ∈ ex, n ∈ ex')
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName ∨ c₀.name ∈ ex') :
    LfpCover mp' ex' where
  cover := fun n cv caps hf hn hq => by
    rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · rename_i heq
      have hnm : c₀.name = n := by simpa using heq
      rcases hni cv caps (Option.some.inj hf) with h' | h'
      · exact absurd (hnm ▸ h') hq
      · exact absurd (hnm ▸ h') hn
    · rw [hL]; exact h.cover n cv caps hf (fun h' => hn (hex n h')) hq
  nodup := fun D hD => h.nodup D (hL ▸ hD)
  len := fun D hD => h.len D (hL ▸ hD)
  all := fun D hD mm hmm cv caps hf => by
    rw [hL] at hD
    obtain ⟨cv0, caps0, hf0⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
    rw [findPreserved_cons hfresh hf0] at hf
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
  h.cons hfresh hL (fun _ h' => List.mem_cons_of_mem _ h')
    (fun _ _ _ => Or.inr List.mem_cons_self)

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

/-- `LfpCover.addLfp` at a named result list. -/
theorem LfpCover.addLfp_to {env : Env} {mp : EnvModelM V μ env} {ex ex'' : List Name}
    (h : LfpCover mp ex) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names)
    (hex : ex.filter (· ∉ D.names) = ex'') :
    LfpCover (mp.addLfp D hL hst hrd hrdC) ex'' :=
  hex ▸ h.addLfp D hL hst hrd hrdC hnd hlen hall

/-- A one-member block's record empties the exemption list its former's
cons opened. -/
theorem filter_not_mem_self (n : Name) : [n].filter (· ∉ [n]) = [] := by
  simp

/-! ## The step shape -/

/-- **Coverage carried along a (partial) step**, from exemption list
`ex` at `mp` to `ex'` at a carrier at `env'`. -/
@[expose] def CoverTo {env : Env} (mp : EnvModelM V μ env) (ex : List Name) (env' : Env)
    (ex' : List Name) : Prop :=
  ∃ mp' : EnvModelM V μ env', LfpCover mp ex → LfpCover mp' ex'

/-- **The fold step's conclusion** (lane L8a; the module docstring). -/
abbrev CoverStep {env : Env} (mp : EnvModelM V μ env) (env' : Env) : Prop :=
  CoverTo mp [] env' []

theorem CoverTo.nonempty {env env' : Env} {mp : EnvModelM V μ env} {ex ex' : List Name}
    (h : CoverTo mp ex env' ex') : Nonempty (EnvModelM V μ env') :=
  h.elim fun mp' _ => ⟨mp'⟩

theorem CoverTo.refl {env : Env} (mp : EnvModelM V μ env) (ex : List Name) :
    CoverTo mp ex env ex := ⟨mp, id⟩

theorem CoverTo.trans {env env₁ env₂ : Env} {mp : EnvModelM V μ env}
    {ex ex₁ ex₂ : List Name} (h₁ : CoverTo mp ex env₁ ex₁)
    (h₂ : ∀ mp₁ : EnvModelM V μ env₁, CoverTo mp₁ ex₁ env₂ ex₂) : CoverTo mp ex env₂ ex₂ := by
  obtain ⟨mp₁, h₁⟩ := h₁
  obtain ⟨mp₂, h₂⟩ := h₂ mp₁
  exact ⟨mp₂, h₂ ∘ h₁⟩

/-- A step whose result is the input environment. -/
theorem CoverTo.of_eq {env env' : Env} {mp : EnvModelM V μ env} {ex : List Name}
    (h : env' = env) : CoverTo mp ex env' ex := h ▸ CoverTo.refl mp ex

/-- **The fold's form**: coverage at the input under a premise `P`
gives a carrier at the result with coverage under `P`. -/
theorem CoverTo.lift {env env' : Env} {mp : EnvModelM V μ env} {P : Prop}
    (h : CoverStep mp env') (hcov : P → LfpCover mp []) :
    ∃ mp' : EnvModelM V μ env', P → LfpCover mp' [] :=
  h.elim fun mp' h' => ⟨mp', fun hP => h' (hcov hP)⟩

/-! ## The cons funnel, keeping the recorded list -/

/-- **The cons funnel's carrier, with the input's recorded list.**  The
funnel (`declStep_preserves_of_cons*`, and every basis variant) builds
`lfpBlocks := mp.lfpBlocks` but exposes only its leaf; this rebuilds a
carrier at the same leaf with the input's list, re-proving the recorded
clauses exactly as the funnel does (`lfp_ok_transport` at a fresh cons
whose head is no projection table). -/
theorem EnvModelM.keepLfp {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      mp'.lfpBlocks = mp.lfpBlocks := by
  obtain ⟨mp', hac⟩ := h
  have hbound := ConLeche.Semantics.envWF_constsBound mp.base2.wf
  have hok := mp.lfp_ok_transport (acval' := acvalWith mp.base2.acval c₀.name A)
    (fun _ _ hf _ => findPreserved_cons hfresh hf)
    (fun n _ hf _ => acvalWith_ne fun h => by
      rw [h, hfresh] at hf; exact nomatch hf)
    (fun _ _ _ hf ψ _ hta =>
      have hm := ConLeche.Semantics.Env.find?_mem hf
      denoteMeta_cons_mono hfresh (hcross.type hm) ψ 0 (hbound _ hm).1 hta)
    (fun _ _ _ _ hf _ _ _ hA ψ _ hta =>
      have hm := ConLeche.Semantics.Env.find?_mem hf
      denoteMeta_cons_mono hfresh (canonCrest_consCrossAt (hcross.type hm) hA) ψ _
        (canonCrest_constsBound (hbound _ hm).1 hA) hta)
  exact ⟨{ mp' with
    lfpBlocks := mp.lfpBlocks
    lfp_ok := by rw [hac]; exact hok }, hac, rfl⟩

/-- **A fresh cons, through the funnel, carrying coverage** and keeping
the funnel's leaf (the chains that read it downstream: `Eq`'s). -/
theorem coverA_cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex ex' : List Name}
    (hfresh : env.find? c₀.name = none)
    (hex : ∀ n ∈ ex, n ∈ ex')
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName ∨ c₀.name ∈ ex')
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      (LfpCover mp ex → LfpCover mp' ex') := by
  obtain ⟨mp', hac, hL⟩ := EnvModelM.keepLfp hfresh (ConsCrossEnv.ofNtc hntc) h
  exact ⟨mp', hac, fun hc => hc.cons hfresh hL hex hni⟩

/-- **A fresh non-inductive cons** (or `Quot`'s), through the funnel:
coverage at the same exemption list. -/
theorem coverTo_cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h) :
    CoverTo mp ex ⟨c₀ :: env.consts⟩ ex :=
  (coverA_cons hfresh (fun _ h => h) (fun cv caps h' => Or.inl (hni cv caps h')) h hntc).imp
    fun _ h => h.2

/-- **A former's cons**, through the funnel: its name joins the
exemption list. -/
theorem coverA_pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      (LfpCover mp ex → LfpCover mp' (c₀.name :: ex)) :=
  coverA_cons hfresh (fun _ h => List.mem_cons_of_mem _ h)
    (fun _ _ _ => Or.inr List.mem_cons_self) h hntc

/-- **A former's cons**, through the funnel, as a `CoverTo`. -/
theorem coverTo_pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h) :
    CoverTo mp ex ⟨c₀ :: env.consts⟩ (c₀.name :: ex) :=
  (coverA_pend hfresh h hntc).imp fun _ h => h.2

/-- **A block's record** on a carrier whose leaf is `acval`: the block's
names leave the exemption list (`hex` names the result). -/
theorem coverTo_addLfp {env env' : Env} {mp : EnvModelM V μ env} {ex ex' ex'' : List Name}
    {acval : Name → (Name → Nat) → AnnotTerm}
    (h : ∃ mp' : EnvModelM V μ env', mp'.base2.acval = acval ∧
      (LfpCover mp ex → LfpCover mp' ex'))
    (D : LfpDatum V) (hL : LfpClause acval D) (hst : LfpStored env' D)
    (hrd : LfpReads acval env' D) (hrdC : LfpCtorReads acval env' D)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env'.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names)
    (hex : ex'.filter (· ∉ D.names) = ex'') :
    CoverTo mp ex env' ex'' := by
  obtain ⟨mp', hac, hc⟩ := h
  subst hac hex
  exact ⟨mp'.addLfp D hL hst hrd hrdC, fun h0 => (hc h0).addLfp D _ _ _ _ hnd hlen hall⟩

/-- A one-member block's names are distinct. -/
theorem nodup_one (n : Name) : [n].Nodup := by simp

omit [SetTheory V] in
/-- `LfpCover.addLfp`'s `all` premise at a one-member block: its former's
stored `all`. -/
theorem lfpAll_one {env' : Env} {D : LfpDatum V} {n : Name} {c : ConstantInfo} (hk : D.k = 1)
    (hm : D.member 0 = n) (hf0 : env'.find? n = some c)
    (hc : ∀ cv caps, c = .indInfo cv caps → caps.all = D.names) :
    ∀ mm, mm < D.k → ∀ cv caps,
      env'.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names := by
  intro mm hmm cv caps hf
  obtain rfl : mm = 0 := by omega
  rw [hm, hf0] at hf
  exact hc cv caps (Option.some.inj hf)

end ConLeche.Model
