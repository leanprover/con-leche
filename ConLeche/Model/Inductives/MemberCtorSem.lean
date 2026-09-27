module

public import ConLeche.Model.Inductives.ContSem
public import ConLeche.Model.Inductives.NestPosAcc
import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Model.CtxOkP
import ConLeche.Model.Rules.Inputs

public section

/-!
# What the install reads of a member constructor's positivity derivation (PRIMREC / NESTKN-M5)

`MemberCtorSem V env ctx nF crest ks tyN` is EVERYTHING the install's
consumers (`blockWalkCtx`, `blockCtorPos_of_walk`, `blockCtorAcc_of_walk`,
`storedFieldShapes_of_walk`, `blockRunLink`, …) read of one member
constructor's walk: the syntax of its normal form (the telescope closed,
the crest opened onto the result, U4, the result's head and hole-free
indices, M3, and each opened field against its kind), and three semantic
facts, each at every model:

* `red` — the normal form READS like the crest (`memberCtorD_red`);
* `mono` — the crest is positive field by field along every hole relation
  (`memberCtorD_mono`, coverage at a container kind);
* `acc` — at a positive level, accessible field by field
  (`memberCtorD_acc`, `ContOk` — spelled out, `ContAcc.lean` sits above the
  install's run files — at a container kind).

It names no derivation and no checker run: it is the CUT between the
positivity check and the install.  Two producers exist — the path walk's
(`memberCtorD_sem`, `MemberCtorSemD.lean`, deleted at the switch) and the
key-named walk's (`memberCtorDK_sem`, `MemberCtorSemK.lean`) — so the switch
swaps the producer and touches no consumer (DESIGN "PRIMREC / NESTKN-M5").
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name NestCtx BinderMeta closeTelescope PosKind openPisAtFvars)

universe w

/-- **A member constructor's walk, as the install reads it** (see the
module docstring). -/
@[expose] def MemberCtorSem (V : Type w) [SetTheory V] (env : Env) (ctx : NestCtx) (nF : Nat)
    (crest : Expr) (ks : List PosKind) (tyN : Expr) : Prop :=
  ∃ (nds : List (Expr × BinderMeta)) (cur : Expr),
    tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
    (∃ xs, openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, cur)) ∧
    ((List.range nF).any fun i =>
      (ks.getD i .ordinary).guarded && ConLeche.structUsedLater tyN 0 i) = false ∧
    ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true ∧
    tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true ∧
    -- the normal form, opened: one output per field, its kind's syntax
    (ConLeche.EnvWF env → crest.looseBVarsBounded 0 = true →
      ∃ (xs : List Expr) (rest : Expr),
        openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest) ∧ ks.length = nF ∧
        nds.length = nF ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
          nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
          (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
          k ≠ .inProgress) ∧
    -- red: the normal form reads like the crest
    (∀ (m : EnvModel V env) (φ : Name → Nat), RulesInputs V m φ →
      Frame (ctx.hiAt 0) crest → ∀ {Δa : List AnnotTerm} {ca : AnnotTerm},
      CtxOkP m φ (ctx.hiAt 0) Δa crest →
      denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca → Graded V Δa ca →
      ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ca = mkPisAV abD B ∧ denoteMeta m.acval env φ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
        abD.length = nF ∧ abN.length = nF ∧
        abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
        FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
        Graded V Δa (mkPisAV abN B) ∧ Frame (ctx.hiAt 0) tyN ∧ LeavesSub tyN crest) ∧
    -- mono: positive along every hole relation
    (∀ {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat),
      RulesInputs V mp.base2 φ → ((∃ k ∈ ks, k.flat = false) → ContCover mp ctx) →
      Frame (ctx.hiAt 0) crest → ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest →
      denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca → Graded V Δa ca →
      HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R →
      PiPosThen (ResultIdxConst ctx.nP) nF R ca) ∧
    -- acc: accessible at a positive level
    (∀ {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat),
      RulesInputs V mp.base2 φ → ∀ {w : Nat}, w ≠ 0 →
      ((∃ k ∈ ks, k.flat = false) → ContCover mp ctx ∧ ctx.sort.eval φ = w) →
      Frame (ctx.hiAt 0) crest → ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest →
      denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca → Graded V Δa ca →
      HoleRelA mp.base2 φ ctx [] (ctx.hiAt 0) Δa R → TeleSmall w nF R ca →
      PiAccThen w ctx [] (ResultIdxConst ctx.nP) nF (ctx.hiAt 0) (nds.map (·.1)) R ca)

namespace MemberCtorSem

variable {V : Type w} [SetTheory V] {env : Env} {ctx : NestCtx} {nF : Nat} {crest : Expr}
  {ks : List PosKind} {tyN : Expr}

/-- The normal form reads like the crest. -/
theorem red (h : MemberCtorSem V env ctx nF crest ks tyN) {m : EnvModel V env} {φ : Name → Nat}
    (hin : RulesInputs V m φ) (hfr : Frame (ctx.hiAt 0) crest) {Δa : List AnnotTerm}
    {ca : AnnotTerm} (hC : CtxOkP m φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ca = mkPisAV abD B ∧ denoteMeta m.acval env φ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
      abD.length = nF ∧ abN.length = nF ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Graded V Δa (mkPisAV abN B) ∧ Frame (ctx.hiAt 0) tyN ∧ LeavesSub tyN crest := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hred, -, -⟩ := h
  exact hred m φ hin hfr hC hca hgr

/-- Positive along every hole relation. -/
theorem mono (h : MemberCtorSem V env ctx nF crest ks tyN) {μ : ConLeche.CheckMode}
    (mp : EnvModelM V μ env) {φ : Name → Nat} (hin : RulesInputs V mp.base2 φ)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContCover mp ctx) (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmono, -⟩ := h
  exact hmono mp φ hin hcov hfr hC hca hgr hR

/-- The syntax `storedFieldShapes_of_walk` reads: the crest opened onto the
result, the result's indices hole-free, M3. -/
theorem syn (h : MemberCtorSem V env ctx nF crest ks tyN) :
    ∃ rest : Expr, (∃ xs, openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, rest)) ∧
      (rest.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0))
        = true ∧
      tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true := by
  obtain ⟨-, cur, -, hop, -, -, hok, hha, -⟩ := h
  exact ⟨cur, hop, hok, hha⟩

end MemberCtorSem

end ConLeche.Model
