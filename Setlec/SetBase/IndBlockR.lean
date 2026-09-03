import Setlec.SetBase.DeclEta
import Setlec.Verify.Extend.Iota

/-!
# The inductive block's **relation-level** residue (task #161 S5,
THE SEPARATION — the C4 refutation's bill, paid)

S3's stop-and-name refuted the design census's C4 at the `indDecl`
kind: `declStepS`'s ind branch takes its η-closure from the whole
`DeclIndS` obligation, whose discharge reads `hEC₁`/`hBP₁` off
`indMembersS` and `hnonrecUp` off `indRecsS` — both **model-carrying**
installs.  The S3 seal sized the repair at "two ~800-line inductions
re-run η-only".

**MEASURED, THE SIZING IS WRONG, AND THAT IS THE FINDING.**  Nothing
of the two folds' model content is needed.  Every ingredient of
`declIndS`'s second component was already relation-level and V-free —
`indMembersR_mono`/`_indNew`/`_ctorEntry`, `indRecsR_noInd`,
`projInstallR_ext`, `templatesR_ext` — and the *one* ingredient that
was not, `indRecsS`'s `hnonrecUp`, is not a consequence of the install
at all: the group's install fold accumulates on the **base**
environment (`IndRecsFoldR`'s `acc` starts at `env₂`, not at the
provisional `envSelf`), and every name it conses was checked fresh
against that base.  So the preservation is `indRecsR_keep` below —
an eight-line `find?` walk, *stronger* than `hnonrecUp` (it needs no
"not a recursor" side condition and returns an equation), and the
recursor swap never enters.

This module is model-free by construction: no `V`, no `SetTheory`, no
`EnvS`.  It holds the relation-level lemmas the block folds' syntactic
residue consists of, moved here verbatim from
`SetR/Install/{IndRecsS,IndMembersS,DeclIndS}.lean`, plus the three new
lemmas the keep-fact needs and `declIndEtaClosed`, the ind kind's
η-closure proved from `DeclIndR` alone.  `declIndS` routes its own
second component through it (one source of truth), and the P fold
consumes it instead of `declIndS memberKeyS mp.base`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-- **The block's capability pins**, from the capability record's own
definition: `indBlockCaps`' two Booleans *are* `checkEtaThm` and
`checkUnitThm`, which invert to the artifacts' shape pins.  Transpose
of `Model/Extend/Decl.lean`'s `hpinsT0`. -/
theorem etaPins_of_indBlockCaps {μ : CheckMode} {env : Env}
    {cvT cvC : ConstantVal} {nP nF : Nat} :
    EtaPins μ env cvT.name cvT.levelParams
      (indBlockCaps μ env cvT cvC nP nF) := by
  refine ⟨?_, ?_⟩
  · intro hcape
    simp only [indBlockCaps, Bool.and_eq_true] at hcape
    exact checkEtaThm_inv hcape.2
  · intro hcapu
    simp only [indBlockCaps] at hcapu
    exact checkUnitThm_inv hcapu

/-- An empty capability record pins nothing, and asks nothing. -/
theorem etaPins_empty {μ : CheckMode} {env : Env} {T : Name}
    {lps : List Name} : EtaPins μ env T lps {} :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- The projection-function fold is an `ExtEta` extension: each step
is either a no-op or one fresh `.recInfo` install. -/
theorem projInstallR_ext {μ : CheckMode} {F : Nat}
    {T ctorName : Name} {lps : List Name} {nP nF : Nat} :
    ∀ (idxs : List Nat) {env' : Env} {cval : TConstVal} {env₄ : Env}
      {cval₄ : TConstVal},
      ProjInstallR μ F T ctorName lps nP nF env' cval idxs env₄ cval₄ →
      ExtEta env' env₄ := by
  intro idxs
  induction idxs with
  | nil =>
    intro env' cval env₄ cval₄ h
    obtain ⟨rfl, -⟩ := h
    exact ExtEta.refl _
  | cons i rest ih =>
    intro env' cval env₄ cval₄ h
    obtain ⟨env'', cval'', hstep, htail⟩ := h
    refine ExtEta.trans ?_ (ih htail)
    rcases hstep with ⟨hfn, -⟩ | ⟨-, rfl, -⟩
    · obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, -, -, -, hfresh, -, -,
        -, -, -, -, -, -, -, -, -, -, rfl⟩ := hfn
      exact ExtEta.cons (Option.isNone_iff_eq_none.mp hfresh)
        (fun _ _ hh => ConstantInfo.noConfusion hh)
    · exact ExtEta.refl _

/-- The elimination-template fold is an `ExtEta` extension. -/
theorem templatesR_ext {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) {env' env₂ : Env},
      DeclIndR.TemplatesR T ctorName lps nP nF env' idxs env₂ →
      ExtEta env' env₂ := by
  intro idxs
  induction idxs with
  | nil =>
    intro env' env₂ h
    rw [h]
    exact ExtEta.refl _
  | cons i rest ih =>
    intro env' env₂ h
    obtain ⟨env'', hstep, htail⟩ := h
    refine ExtEta.trans ?_ (ih htail)
    rcases hstep with rfl | ⟨entry, hst, hix, -, -, -, hfresh, rfl⟩
    · exact ExtEta.refl _
    · refine ExtEta.cons ?_ (fun _ _ hh => ConstantInfo.noConfusion hh)
      show env'.find? (projFnName entry.structName entry.idx) = none
      rw [hst, hix]
      exact Option.isNone_iff_eq_none.mp hfresh

/-! ## The provisioning's syntactic residue -/

/-- Provisioning only extends: every member's name is checked fresh
(`ConstantValR`'s first conjunct), so earlier lookups survive. -/
theorem provisionRecsS_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ (n : Name) (ci : ConstantInfo),
        envAcc.find? n = some ci → envSelf.find? n = some ci := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h n ci hf
    obtain ⟨rfl, -, -⟩ := h
    exact hf
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h n ci hf
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, -⟩ := h
    obtain ⟨type', ⟨hfresh, -, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    exact ih hrec n ci (Env.find?_cons_of_fresh
      (c := .recInfo _ mI rP []) (Option.isNone_iff_eq_none.mp hfresh)
      hf)

/-- Provisioning only extends: stored entries stay stored. -/
theorem provisionRecsS_mem {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ c ∈ envAcc.consts, c ∈ envSelf.consts := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨rfl, -, -⟩ := h
    exact hc
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, -, hprov', -⟩ := h
    exact ih hprov' c (List.mem_cons_of_mem _ hc)

/-- No provisioned member is stored *before* the fold runs. -/
theorem provisionRecsS_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, envAcc.find? ci.name = none := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : envAcc.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · rcases hf : envAcc.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        have hnone := ih hprov' ci hci'
        rw [Env.find?_cons_of_fresh (c := .recInfo cvA mI rP [])
          hfresh hf] at hnone
        exact nomatch hnone

/-- Each provisioned member's name passes the two name guards. -/
theorem provisionRecsS_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · exact ih hprov' ci hci'

/-- …and so does every group member's. -/
theorem indRecsR_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
      reservedBasisNames.contains ci.name = false := by
  rcases h with ⟨rfl, -, -⟩ | ⟨-, -, envSelf, cvalSelf, checked,
    hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsS_nameGuards recs hprov

/-- The provisioning fold introduces no former. -/
theorem provisionRecsR_noInd {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
        envSelf.find? T = some (.indInfo cvT caps) →
        envAcc.find? T = some (.indInfo cvT caps) := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h T cvT caps hf
    obtain ⟨rfl, -, -⟩ := h
    exact hf
  | cons ci rest ih =>
    intro envAcc cval envSelf cvalSelf checked h T cvT caps hf
    obtain ⟨cvA, mI, rP, rules, rest', -, -, hrec, -⟩ := h
    have h1 := ih hrec T cvT caps hf
    rw [Env.find?_cons] at h1
    split at h1
    · exact ConstantInfo.noConfusion (Option.some.inj h1)
    · exact h1

/-- The install fold introduces no former. -/
theorem indRecsFoldR_noInd {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env}
    {cvalSelf : TConstVal} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc : Env} {cval : TConstVal} {out : Env} {cvalOut : TConstVal},
      IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf cvalSelf
        acc cval checked out cvalOut →
      ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
        out.find? T = some (.indInfo cvT caps) →
        acc.find? T = some (.indInfo cvT caps) := by
  intro checked
  induction checked with
  | nil =>
    intro acc cval out cvalOut h T cvT caps hf
    obtain ⟨rfl, -⟩ := h
    exact hf
  | cons c rest ih =>
    intro acc cval out cvalOut h T cvT caps hf
    obtain ⟨rules', -, htail⟩ := h
    have h1 := ih htail T cvT caps hf
    rw [Env.find?_cons] at h1
    split at h1
    · exact ConstantInfo.noConfusion (Option.some.inj h1)
    · exact h1

/-- The recursor phase introduces no former. -/
theorem indRecsR_noInd {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      env₃.find? T = some (.indInfo cvT caps) →
      env₂.find? T = some (.indInfo cvT caps) := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, envSelf, cvalSelf, checked, -,
    hfold⟩
  · exact fun _ _ _ hf => hf
  · exact indRecsFoldR_noInd checked hfold

/-- The install fold only extends the accumulator. -/
theorem indRecsFoldR_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env}
    {cvalSelf : TConstVal} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc : Env} {cval : TConstVal} {out : Env} {cvalOut : TConstVal},
      IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf cvalSelf
        acc cval checked out cvalOut →
      ∀ n, (acc.find? n).isSome = true →
        (out.find? n).isSome = true := by
  intro checked
  induction checked with
  | nil =>
    intro acc cval out cvalOut h n hn
    obtain ⟨rfl, -⟩ := h
    exact hn
  | cons c rest ih =>
    intro acc cval out cvalOut h n hn
    obtain ⟨rules', -, htail⟩ := h
    refine ih htail n ?_
    rw [Env.find?_cons]
    split
    · rfl
    · exact hn

/-- The recursor group only extends the environment. -/
theorem indRecsR_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ n, (env₂.find? n).isSome = true →
      (env₃.find? n).isSome = true := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, envSelf, cvalSelf, checked, -,
    hfold⟩
  · exact fun n hn => hn
  · exact indRecsFoldR_mono checked hfold

/-- No group member is stored before the group phase runs. -/
theorem indRecsR_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ ci ∈ recs, env₂.find? ci.name = none := by
  rcases h with ⟨rfl, -, -⟩ | ⟨-, -, envSelf, cvalSelf, checked,
    hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsS_fresh recs hprov

/-- Every provisioned member is stored. -/
theorem provisionRecsS_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, (envSelf.find? ci.name).isSome = true := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', -, hcvAdef, -⟩ := hmv
    rcases List.mem_cons.mp hci with rfl | hci'
    · have : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
        provisionRecsS_mono rest hprov' _ _
          (Env.find?_cons_self (.recInfo cvA mI rP []) envAcc)
      rw [show ci.name = cvA.name by rw [hcvAdef]; rfl, this]
      rfl
    · exact ih hprov' ci hci'

/-- Each provisioned member is stored rule-less in the self
environment, under a name the member check found unreserved. -/
theorem provisionRecsS_entries {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ c ∈ checked,
        envSelf.find? c.1.name
          = some (.recInfo c.1 c.2.1 c.2.2.1 []) ∧
        reservedBasisNames.contains c.1.name = false := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨-, -, rfl⟩ := h
    exact nomatch hc
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, rfl⟩ := h
    obtain ⟨type', ⟨-, hres, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨provisionRecsS_mono rest hrec _ _
        (Env.find?_cons_self (.recInfo _ mI rP []) envAcc), hres⟩
    · exact ih hrec c hc'

/-! ## The member fold's syntactic residue

The `DeclIndS` assembly needs to know what the fold *preserves*, not
just that it produces a model.  These two are the [set] analogues of
`checkIndFold_mono` / `checkIndMember_fold_names`
(`Verify/Extend/Ind.lean`); they are V-free and prove by the same
freshness chain `provisionRecsS_mono` uses. -/

/-- The member fold only extends. -/
theorem indMembersR_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (n : Name) (ci : ConstantInfo),
        env.find? n = some ci → env₂.find? n = some ci := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h n ci hf
    obtain ⟨rfl, rfl⟩ := h
    exact hf
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h n ci hf
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hfresh : env.find? cvA.name = none := by
      rw [show cvA.name = ci₀.toConstantVal.name by rw [hcvA]]
      exact Option.isNone_iff_eq_none.mp hcv.1
    cases ci₀ with
    | indInfo cv caps' =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .indInfo cvA caps) hfresh hf)
    | ctorInfo cv nP nF =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF) hfresh hf)
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- Every member the fold walks is stored at its end. -/
theorem indMembersR_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, (env₂.find? ci.name).isSome = true := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]
      cases ci₀ with
      | indInfo cv caps' =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.indInfo cvA caps) from
          indMembersR_mono rest hmatch _ _
            (Env.find?_cons_self (.indInfo cvA caps) env)]
        rfl
      | ctorInfo cv nP nF =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.ctorInfo cvA nP nF) from
          indMembersR_mono rest hmatch _ _
            (Env.find?_cons_self (.ctorInfo cvA nP nF) env)]
        rfl
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- No member is stored *before* the fold runs. -/
theorem indMembersR_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, env.find? ci.name = none := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · -- a later member is fresh in the *accumulator*, hence here
      rcases hf : env.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        cases ci₀ with
        | indInfo cv caps' =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .indInfo cvA caps)
            hfresh hf] at hnone
          exact nomatch hnone
        | ctorInfo cv nP nF =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF)
            hfresh hf] at hnone
          exact nomatch hnone
        | axiomInfo cv => exact nomatch hmatch
        | defnInfo cv v hint => exact nomatch hmatch
        | thmInfo cv v => exact nomatch hmatch
        | recInfo cv mI rP rules => exact nomatch hmatch
        | projInfo e => exact nomatch hmatch

/-- Each member's name passes `ConstantValR`'s two name guards. -/
theorem indMembersR_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- The former the fold walks is stored as an `.indInfo` at the
*block's* capability record, under an annotated `ConstantVal` with the
same name and level parameters. -/
theorem indMembersR_indEntry {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        ∃ cvA : ConstantVal, cvA.name = cv.name ∧
          cvA.levelParams = cv.levelParams ∧
          env₂.find? cv.name = some (.indInfo cvA caps) := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h cv caps₂ hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h cv caps₂ hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    have hlpsA : cvA.levelParams = ci₀.toConstantVal.levelParams := by
      rw [hcvA]
    have hfresh : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · subst heq
      refine ⟨cvA, hnameA, hlpsA, ?_⟩
      rw [show cv.name = cvA.name from hnameA.symm]
      exact indMembersR_mono rest hmatch _ _
        (Env.find?_cons_self (.indInfo cvA caps) env)
    · cases ci₀ with
      | indInfo cv' caps' => exact ih hmatch cv caps₂ hci'
      | ctorInfo cv' nP nF => exact ih hmatch cv caps₂ hci'
      | axiomInfo cv' => exact nomatch hmatch
      | defnInfo cv' v hint => exact nomatch hmatch
      | thmInfo cv' v => exact nomatch hmatch
      | recInfo cv' mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- The constructor member's stored entry, with its arities. -/
theorem indMembersR_ctorEntry {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (cv : ConstantVal) (nP nF : Nat),
        ConstantInfo.ctorInfo cv nP nF ∈ members →
        ∃ cvA : ConstantVal,
          env₂.find? cv.name = some (.ctorInfo cvA nP nF) := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h cv nP nF hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h cv nP nF hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    rcases List.mem_cons.mp hci with heq | hci'
    · subst heq
      refine ⟨cvA, ?_⟩
      rw [show cv.name = cvA.name from hnameA.symm]
      exact indMembersR_mono rest hmatch _ _
        (Env.find?_cons_self (.ctorInfo cvA nP nF) env)
    · cases ci₀ with
      | indInfo cv' caps' => exact ih hmatch cv nP nF hci'
      | ctorInfo cv' nP' nF' => exact ih hmatch cv nP nF hci'
      | axiomInfo cv' => exact nomatch hmatch
      | defnInfo cv' v hint => exact nomatch hmatch
      | thmInfo cv' v => exact nomatch hmatch
      | recInfo cv' mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- A former stored after the member fold is either one the base
already had, verbatim, or a block former carrying the fold's
capability record. -/
theorem indMembersR_indNew {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (T : Name) (cvT : ConstantVal) (caps' : IndCaps),
        env₂.find? T = some (.indInfo cvT caps') →
        env.find? T = some (.indInfo cvT caps') ∨
          (caps' = caps ∧ ∃ (cv : ConstantVal) (caps₂ : IndCaps),
            ConstantInfo.indInfo cv caps₂ ∈ members ∧ cv.name = T) := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h T cvT caps' hf
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl hf
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h T cvT caps' hf
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    cases ci₀ with
    | indInfo cv' caps'' =>
      rcases ih hmatch T cvT caps' hf with hf' | ⟨rfl, cv, caps₂,
        hmem, hcvn⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next he =>
          obtain ⟨rfl, rfl⟩ :=
            ConstantInfo.indInfo.inj (Option.some.inj hf')
          exact Or.inr ⟨rfl, cv', caps'', List.mem_cons_self,
            hnameA.symm.trans he⟩
        · exact Or.inl hf'
      · exact Or.inr ⟨rfl, cv, caps₂, List.mem_cons_of_mem _ hmem,
          hcvn⟩
    | ctorInfo cv' nP nF =>
      rcases ih hmatch T cvT caps' hf with hf' | ⟨rfl, cv, caps₂,
        hmem, hcvn⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · exact ConstantInfo.noConfusion (Option.some.inj hf')
        · exact Or.inl hf'
      · exact Or.inr ⟨rfl, cv, caps₂, List.mem_cons_of_mem _ hmem,
          hcvn⟩
    | axiomInfo cv' => exact nomatch hmatch
    | defnInfo cv' v hint => exact nomatch hmatch
    | thmInfo cv' v => exact nomatch hmatch
    | recInfo cv' mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- The fold's per-member eta data steps at a fresh, non-projection
install: `EtaPins.step` for the pins, nothing for the (environment-free)
constructor fact, and the name shape for the projection freshness. -/
theorem etaMemberData_step {μ : CheckMode} {blockNames : List Name}
    {caps : IndCaps} {env : Env} {c₀ : ConstantInfo} {n : Name}
    {lps : List Name} (hfresh : env.find? c₀.name = none)
    (hshape : c₀.name.isProjFnShape = false)
    (h : EtaPins μ env n lps caps ∧
      (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
      (caps.eta = true → 0 < caps.etaFields →
        env.find? (projFnName n 0) = none)) :
    EtaPins μ ⟨c₀ :: env.consts⟩ n lps caps ∧
      (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
      (caps.eta = true → 0 < caps.etaFields →
        (⟨c₀ :: env.consts⟩ : Env).find? (projFnName n 0) = none) :=
  ⟨EtaPins.step h.1 hfresh, h.2.1, fun he hlt => by
    rw [Env.find?_cons, if_neg (fun hh =>
      projFnName_ne_of_shape (T := n) (j := 0) hshape hh.symm)]
    exact h.2.2 he hlt⟩

/-! ## The group phase's keep-fact (task #161 S5 — the C4 bill)

`indRecsS` reports a *non-recursor* transport (`hnonrecUp`) and proves
it through the `EnvS` swap.  At the relation level the fact is both
simpler and stronger, and needs no install: `IndRecsFoldR` accumulates
on the group's **base** environment (`IndRecsR` starts the fold at
`env₂`, handing `envSelf` over only as the environment the *rules* are
checked against), and every name it conses was checked fresh against
that base by `MemberValR`.  So a base lookup that succeeds is
untouched — recursor or not. -/

/-- Every provisioned member's checked name is fresh in the group's
base environment.  `MemberValR`'s first guard, walked back through the
provisioning's own cons chain. -/
theorem provisionRecsR_checkedFresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ c ∈ checked, envAcc.find? c.1.name = none := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨-, -, rfl⟩ := h
    exact nomatch hc
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', rfl⟩ := h
    obtain ⟨type', ⟨hfresh, -, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Option.isNone_iff_eq_none.mp hfresh
    · have hnone := ih hprov' c hc'
      rw [Env.find?_cons] at hnone
      split at hnone
      · exact nomatch hnone
      · exact hnone

/-- The install fold leaves alone every name it does not cons. -/
theorem indRecsFoldR_keep {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env}
    {cvalSelf : TConstVal} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc : Env} {cval : TConstVal} {out : Env} {cvalOut : TConstVal},
      IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf cvalSelf
        acc cval checked out cvalOut →
      ∀ n : Name, (∀ c ∈ checked, c.1.name ≠ n) →
        out.find? n = acc.find? n := by
  intro checked
  induction checked with
  | nil =>
    intro acc cval out cvalOut h n _
    obtain ⟨rfl, -⟩ := h
    rfl
  | cons c rest ih =>
    intro acc cval out cvalOut h n hne
    obtain ⟨rules', -, htail⟩ := h
    rw [ih htail n (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')),
      Env.find?_cons]
    exact if_neg (hne c List.mem_cons_self)

/-- **The recursor group keeps the base environment's lookups.**
Strictly stronger than `indRecsS`'s `hnonrecUp` (no "not a recursor"
side condition, and an equation rather than an implication), and
model-free: the swap the install performs is between the *provisional*
environment and the group's output, and the fold's accumulator never
visits it. -/
theorem indRecsR_keep {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ (n : Name) (ci : ConstantInfo),
      env₂.find? n = some ci → env₃.find? n = some ci := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, envSelf, cvalSelf, checked, hprov,
    hfold⟩
  · exact fun _ _ hf => hf
  · intro n ci hf
    refine (indRecsFoldR_keep checked hfold n ?_).trans hf
    intro c hc hcn
    have hnone := provisionRecsR_checkedFresh recs hprov c hc
    rw [hcn, hf] at hnone
    exact nomatch hnone

/-- The group phase is an `ExtEta` extension. -/
theorem indRecsR_ext {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ExtEta env₂ env₃ :=
  ⟨fun n ci hf _ => indRecsR_keep h n ci hf, indRecsR_noInd h⟩

/-! ## `declIndEtaClosed` — the ind kind's η-closure, model-free -/

/-- **The inductive block preserves the η-family closure** — the second
component of `declIndS`, proved from `DeclIndR` alone.

This is the census's C4 at the one kind S3's stop-and-name found it
false of, and the finding is that no model content was ever needed:
`declIndS`'s own proof of the component reads only `indMembersR_*`,
`indRecsR_*` and the two post-member `ExtEta` folds, and the single
install-derived ingredient (`hnonrecUp`) is `indRecsR_keep` above.
`declIndS` now routes its own second component through this theorem,
and the P fold (`Interp2/FoldP.lean`) consumes it directly. -/
theorem declIndEtaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {cval : TConstVal} {block : List ConstantInfo}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndR μ F env cval block env₂) :
    EtaFamiliesClosed env₂ := by
  obtain ⟨hsplit, hmain⟩ := h
  rcases hmain with ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, harm⟩ |
    ⟨-, envM, cvalM, cval₂, hmem, hrecs⟩
  · -- the single-constructor arm
    obtain ⟨envM, cvalM, envR, cvalR, hmem, hrecs, -, -,
      envP, cvalP, hproj, htpl⟩ := harm
    -- generic in the filter's predicate, so unification takes the
    -- relation's own (writing it out does not match syntactically)
    have hmemFil : ∀ {p : ConstantInfo → Bool} {x : ConstantInfo},
        block.filter p = [x] → x ∈ block := by
      intro p x hfil
      have hx : x ∈ block.filter p := by
        rw [hfil]; exact List.mem_singleton_self _
      exact (List.mem_filter.mp hx).1
    have hCin : ConstantInfo.ctorInfo cvC nP nF ∈ block := hmemFil hCfilt
    have hCnon : ConstantInfo.ctorInfo cvC nP nF ∈ block.filter
        (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true) :=
      List.mem_filter.mpr ⟨hCin, rfl⟩
    -- the three post-member phases are `ExtEta`, so the only new
    -- former is the block's own, whose constructor is a member
    have hx : ExtEta envM env₂ :=
      ExtEta.trans (indRecsR_ext hrecs)
        (ExtEta.trans (projInstallR_ext (List.range nF) hproj)
          (templatesR_ext (List.range nF) htpl))
    intro T cvT' caps' hf he hr
    rcases indMembersR_indNew _ hmem T cvT' caps'
      (hx.2 T cvT' caps' hf) with hfE | ⟨rfl, -⟩
    · obtain ⟨cvC', hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC', hx.1 _ _ (indMembersR_mono _ hmem _ _ hfC)
        (fun _ _ _ _ hh => nomatch hh)⟩
    · obtain ⟨cvA', hfA⟩ := indMembersR_ctorEntry _ hmem cvC nP nF hCnon
      exact ⟨cvA', hx.1 _ _ hfA (fun _ _ _ _ hh => nomatch hh)⟩
  · -- the generic arm: an empty capability record
    intro T cvT' caps' hf he hr
    have hfM := indRecsR_noInd hrecs T cvT' caps' hf
    rcases indMembersR_indNew _ hmem T cvT' caps' hfM with hfE | ⟨rfl, -⟩
    · obtain ⟨cvC, hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC, indRecsR_keep hrecs _ _
        (indMembersR_mono _ hmem _ _ hfC)⟩
    · exact absurd he (by decide)


end Setlec.SetR
