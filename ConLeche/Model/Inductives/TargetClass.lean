module

public import ConLeche.Model.Cover
public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.EnvBound

public section

/-!
# The recursor's classes at a nested block (lane NESTIND, item 1)

At a nested block every recursor's major is a CLASS of the recursor
model (`graphRecPre_core`): a member of the block (the block's own
record), or an outside container at an instantiation.  An outside
class is presented by ONE recorded clause — charter item 5, "the model
uses nothing from an inductive but its lfp clause" — the recorded block
holding the major's inductive as a member, found by the carrier's
coverage (`LfpCover.cover`), whose constructors are the major's
(`LfpCover.own`: the environment's constructor entries of a recorded
member are the ones `targetCtorsOf` read).

* `targetCtorsOf_mkFEnv` — the target check's constructor reading is
  coverage's (`nestContainer` at `envCtx`);
* `targetOutsideInst_find` — an outside major's inductive is stored;
* `TgtOutCls` — an outside class's record: the recorded block `D`, the
  member `mm` that is the major's inductive (its level parameters
  distinct, F6), its constructors the major's, one for one;
* `tgtOutCls_of` — the record, from the entry's `TargetMajorRun.outside`
  and coverage.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The target check's constructor reading is coverage's.** -/
theorem targetCtorsOf_mkFEnv (env : Env) (I : Name) :
    ConLeche.targetCtorsOf (mkFEnv env) I = ConLeche.nestContainer (envCtx env) I := by
  have hf : (mkFEnv env).find? = env.find? := funext (mkFEnv_find? env)
  simp only [ConLeche.targetCtorsOf, envCtx, hf]
  rfl

/-- **An outside major's inductive is stored** (`targetOutsideInst`,
inverted at its first step). -/
theorem targetOutsideInst_find {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {r : Nat × Level}
    (h : ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe I us ds = .ok r) :
    ∃ cvI caps, fe.find? I = some (.indInfo cvI caps) := by
  unfold ConLeche.targetOutsideInst at h
  split at h
  · next cvI caps hf => exact ⟨cvI, caps, hf⟩
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- **An outside class's record** (lane NESTIND, item 1): the recursor's
major `M` is member `mm` of the recorded block `D`, the inductive stored
as `cvI`; `D`'s member `mm` has the major's constructors, one for one,
at the major's parameter count. -/
structure TgtOutCls {env : Env} (mp : EnvModelM V μ env) (M : TargetMajor) (D : LfpDatum V)
    (mm : Nat) (cvI : ConstantVal) : Prop where
  hD : D ∈ mp.lfpBlocks
  hmm : mm < D.k
  hmem : D.member mm = M.ind
  hfind : ∃ caps, env.find? M.ind = some (.indInfo cvI caps)
  /-- the inductive's level parameters are distinct (F6, `LfpOwn.lvlNodup`) -/
  hnd : cvI.levelParams.Nodup
  hnN : D.names.Nodup
  hkN : D.names.length = D.k
  hlen : M.ctors.length = D.nctors mm
  hctor : ∀ j (hj : j < M.ctors.length),
    env.find? (D.ctorName mm j) = some (.ctorInfo M.ctors[j].1 M.nPc M.ctors[j].2)


/-- An outside class's `i`-th constructor, read off the lfp clause: below
`D`'s constructor count, stored at the major's parameter count, at the
class's level parameters (every member's). -/
theorem TgtOutCls.ctor_at {env : Env} {mp : EnvModelM V μ env} {M : TargetMajor}
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal} (hcl : TgtOutCls mp M D mm cvI) {i : Nat}
    {cA : ConstantVal × Nat} (hcA : M.ctors[i]? = some cA) :
    i < D.nctors mm ∧ env.find? (D.ctorName mm i) = some (.ctorInfo cA.1 M.nPc cA.2) ∧
    cvI.levelParams = cA.1.levelParams ∧
    ∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = cA.1.levelParams := by
  obtain ⟨hiL, hcAi⟩ := List.getElem?_eq_some_iff.mp hcA
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  obtain ⟨-, -, -, hcrd⟩ := mp.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ M.nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  refine ⟨hiD, hfc0, ?_, hlpsC⟩
  obtain ⟨caps, hfI⟩ := hcl.hfind
  obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
  rw [hcl.hmem, hfI] at hfm
  injection hfm with h; injection h with h1 _
  rw [h1, hlm]

/-! ## The recorded block holding a name, canonically (lane NESTIND, session 18)

Coverage records every stored inductive in SOME block, and nothing
makes the recorded blocks unique.  The class → node tie compares data,
so an outside class and the positivity walk's node for it must read the
SAME recorded block: `lfpSel` picks one block per MEMBERS' LIST, and
the list of a covered inductive is its stored `IndCaps.all`
(`LfpCover.all`) — so two members of one block select the same one
(`lfpSel_eq_of_mem`). -/

section Sel

variable {env : Env} (mp : EnvModelM V μ env)

/-- The members' list of a recorded block holding `n` (`[]` if none). -/
@[expose] noncomputable def lfpNamesOf (n : Name) : List Name :=
  open Classical in
  if h : ∃ D ∈ mp.lfpBlocks, n ∈ D.names then (Classical.choose h).names else []

/-- **The recorded block holding `n`, canonically**: one block per
members' list (`D0` if none). -/
@[expose] noncomputable def lfpSel (D0 : LfpDatum V) (n : Name) : LfpDatum V :=
  open Classical in
  if h : ∃ D ∈ mp.lfpBlocks, D.names = lfpNamesOf mp n then Classical.choose h else D0

variable {mp}

/-- A recorded block's names are its members. -/
theorem lfp_mem_names {ex : List Name} (hcov : LfpCover mp ex) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {n : Name} (hn : n ∈ D.names) :
    ∃ mm, mm < D.k ∧ D.member mm = n := by
  obtain ⟨mm, hmm, rfl⟩ := List.getElem_of_mem hn
  refine ⟨mm, by rw [← hcov.len D hD]; exact hmm, ?_⟩
  unfold LfpDatum.member
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm, Option.getD_some]

/-- A recorded block's names, read at any of its members: the stored
`IndCaps.all`. -/
theorem lfp_names_all {ex : List Name} (hcov : LfpCover mp ex) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {n : Name} (hn : n ∈ D.names) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? n = some (.indInfo cv caps)) :
    D.names = caps.all := by
  obtain ⟨mm, hmm, rfl⟩ := lfp_mem_names hcov hD hn
  exact (hcov.all D hD mm hmm cv caps hf).symm

/-- The members' list of an inductive some recorded block holds is its
stored `all`. -/
theorem lfpNamesOf_of_mem {ex : List Name} (hcov : LfpCover mp ex) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {n : Name} (hnD : n ∈ D.names) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? n = some (.indInfo cv caps)) :
    lfpNamesOf mp n = caps.all := by
  classical
  have hex : ∃ D ∈ mp.lfpBlocks, n ∈ D.names := ⟨D, hD, hnD⟩
  unfold lfpNamesOf
  rw [dif_pos hex]
  obtain ⟨hD', hn'⟩ := Classical.choose_spec hex
  exact lfp_names_all hcov hD' hn' hf

/-- A covered inductive is held by a recorded block. -/
theorem lfp_cover_mem {ex : List Name} (hcov : LfpCover mp ex) {n : Name} {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? n = some (.indInfo cv caps)) (hn : n ∉ ex)
    (hq : n ≠ ConLeche.quotName) : ∃ D ∈ mp.lfpBlocks, n ∈ D.names := by
  obtain ⟨D, hD, mm, hmm, hmem⟩ := hcov.cover n cv caps hf hn hq
  refine ⟨D, hD, ?_⟩
  rw [← hmem]; unfold LfpDatum.member
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hcov.len D hD]; exact hmm),
    Option.getD_some]
  exact List.getElem_mem _

/-- **The selected block** of an inductive some recorded block holds:
recorded, its names the stored `all` (so it holds `n`). -/
theorem lfpSel_spec {ex : List Name} (hcov : LfpCover mp ex) (D0 : LfpDatum V) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {n : Name} (hnD : n ∈ D.names) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? n = some (.indInfo cv caps)) :
    lfpSel mp D0 n ∈ mp.lfpBlocks ∧ (lfpSel mp D0 n).names = caps.all ∧
      n ∈ (lfpSel mp D0 n).names := by
  classical
  have hDn : D.names = caps.all := lfp_names_all hcov hD hnD hf
  have hex : ∃ D ∈ mp.lfpBlocks, D.names = lfpNamesOf mp n :=
    ⟨D, hD, by rw [lfpNamesOf_of_mem hcov hD hnD hf, hDn]⟩
  unfold lfpSel
  rw [dif_pos hex]
  obtain ⟨hD', hnm⟩ := Classical.choose_spec hex
  have hnm : (Classical.choose hex).names = caps.all := hnm.trans (lfpNamesOf_of_mem hcov hD hnD hf)
  exact ⟨hD', hnm, by rw [hnm, ← hDn]; exact hnD⟩

/-- **Two members of one recorded block select the same block.** -/
theorem lfpSel_eq_of_mem {ex : List Name} (hcov : LfpCover mp ex) (D0 : LfpDatum V)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {n n' : Name} (hnD : n ∈ D.names)
    (hnD' : n' ∈ D.names) : lfpSel mp D0 n' = lfpSel mp D0 n := by
  obtain ⟨mm, hmm, rfl⟩ := lfp_mem_names hcov hD hnD
  obtain ⟨mm', hmm', rfl⟩ := lfp_mem_names hcov hD hnD'
  obtain ⟨cv, caps, hf⟩ := LfpCover.member_find hD hmm
  obtain ⟨cv', caps', hf'⟩ := LfpCover.member_find hD hmm'
  have h1 := lfpNamesOf_of_mem hcov hD hnD hf
  have h2 := lfpNamesOf_of_mem hcov hD hnD' hf'
  rw [← lfp_names_all hcov hD hnD hf] at h1
  rw [← lfp_names_all hcov hD hnD' hf'] at h2
  unfold lfpSel
  rw [h1, h2]

end Sel

/-- **The outside class at a given recorded block** holding the major's
inductive: the major's inductive is stored and not the block's
(`TargetMajorRun.outside`), and the block owns its constructors — the
ones the target check read. -/
theorem tgtOutCls_at {env : Env} {mp : EnvModelM V μ env} (hcov : LfpCover mp [])
    {mode : CheckMode} {F : Nat} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F (mkFEnv env) p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    (hmem : D.member mm = M.ind) :
    ∃ cvI, TgtOutCls mp M D mm cvI := by
  obtain ⟨sI, -, -, hnq, hct, -, -, -, hinst, -⟩ := E.outside_of hM
  obtain ⟨cvI, caps, hf⟩ := targetOutsideInst_find hinst
  rw [mkFEnv_find?] at hf
  obtain ⟨nP', L, hL, hlen, hj⟩ := (hcov.own D hD).ctors mm hmm
  rw [hmem, ← targetCtorsOf_mkFEnv, hct] at hL
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
  obtain ⟨cv', caps', hf', hnd⟩ := (hcov.own D hD).lvlNodup mm hmm
  rw [hmem, hf] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cv' ∧ caps = caps' := by simpa using hf'
  exact ⟨cvI, hD, hmm, hmem, ⟨caps, hf⟩, hnd, hcov.nodup D hD, hcov.len D hD, hlen, hj⟩

/-- **The outside class, from the entry and coverage**: the major's
inductive is stored and not the block's (`TargetMajorRun.outside`), so
the carrier's coverage records it as a member of some block, which owns
its constructors — the ones the target check read. -/
theorem tgtOutCls_of {env : Env} {mp : EnvModelM V μ env} (hcov : LfpCover mp [])
    {mode : CheckMode} {F : Nat} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F (mkFEnv env) p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    ∃ D mm cvI, TgtOutCls mp M D mm cvI := by
  obtain ⟨sI, -, -, hnq, hct, -, -, -, hinst, -⟩ := E.outside_of hM
  obtain ⟨cvI, caps, hf⟩ := targetOutsideInst_find hinst
  rw [mkFEnv_find?] at hf
  obtain ⟨D, hD, mm, hmm, hmem⟩ := hcov.cover M.ind cvI caps hf (by simp) hnq
  obtain ⟨cv, h⟩ := tgtOutCls_at hcov E hM hD hmm hmem
  exact ⟨D, mm, cv, h⟩

/-- **The outside class at the SELECTED block** (`lfpSel`). -/
theorem tgtOutCls_sel {env : Env} {mp : EnvModelM V μ env} (hcov : LfpCover mp [])
    (D0 : LfpDatum V)
    {mode : CheckMode} {F : Nat} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F (mkFEnv env) p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    ∃ mm cvI, TgtOutCls mp M (lfpSel mp D0 M.ind) mm cvI := by
  obtain ⟨sI, -, -, hnq, -, -, -, -, hinst, -⟩ := E.outside_of hM
  obtain ⟨cvI, caps, hf⟩ := targetOutsideInst_find hinst
  rw [mkFEnv_find?] at hf
  obtain ⟨D, hD, hnD⟩ := lfp_cover_mem hcov hf (by simp) hnq
  obtain ⟨hS, -, hnS⟩ := lfpSel_spec hcov D0 hD hnD hf
  obtain ⟨mm, hmm, hmem⟩ := lfp_mem_names hcov hS hnS
  obtain ⟨cv, h⟩ := tgtOutCls_at hcov E hM hS hmm hmem
  exact ⟨mm, cv, h⟩

end ConLeche.Model
