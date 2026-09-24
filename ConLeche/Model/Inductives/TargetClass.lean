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

/-- **The outside class, from the entry and coverage**: the major's
inductive is stored and not the block's (`TargetMajorRun.outside`), so
the carrier's coverage records it as a member of some block, which owns
its constructors — the ones the target check read. -/
theorem tgtOutCls_of {env : Env} {mp : EnvModelM V μ env} (hcov : LfpCover mp [])
    {mode : CheckMode} {F : Nat} {p : BlockShape} {outside nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F (mkFEnv env) p outside nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    ∃ D mm cvI, TgtOutCls mp M D mm cvI := by
  obtain ⟨sI, -, -, -, hnq, hct, -, -, -, hinst, -⟩ := E.outside_of hM
  obtain ⟨cvI, caps, hf⟩ := targetOutsideInst_find hinst
  rw [mkFEnv_find?] at hf
  obtain ⟨D, hD, mm, hmm, hmem⟩ := hcov.cover M.ind cvI caps hf (by simp) hnq
  obtain ⟨nP', L, hL, hlen, hj⟩ := (hcov.own D hD).ctors mm hmm
  rw [hmem, ← targetCtorsOf_mkFEnv, hct] at hL
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
  obtain ⟨cv', caps', hf', hnd⟩ := (hcov.own D hD).lvlNodup mm hmm
  rw [hmem, hf] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cv' ∧ caps = caps' := by simpa using hf'
  exact ⟨D, mm, cvI, hD, hmm, hmem, ⟨caps, hf⟩, hnd, hcov.nodup D hD, hcov.len D hD, hlen, hj⟩

end ConLeche.Model
