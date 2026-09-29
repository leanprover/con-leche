module

public import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.ClassGenScope

public section

/-!
# The generated recursor types' binder data, read (lane GENREC-CLS)

The class-side facts of the generated stage's family premise
(`GenPreSem`, `GenRecPreRun.lean`) read the STORED recursor types' binder
data (`blockRecRdsAV`).  A stored type is the generated one
(`classConstOk` stores its input), a telescope
`closeTelescope (pre ++ ifs.map g.binder ++ [(maj, g.bm)]) 0 (motive …)`
whose index binders `ifs` are the class former's index telescope at the
class's parameters (`ClassGen.major`: `instPisWith ds former`, opened at
the prefix) and whose major is `I lvls (ds ++ ifs)` — by construction,
no comparison needed.  `genRun_binders` states exactly that, at the
readings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Binders

variable {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 1600000 in
/-- **The stored binder data of recursor `c`, read**: its class `cls`'s
former instantiated at the class's parameters (`ty`), opened at the rule
prefix to the index openers `ifs`; the stored binder data are `rP + nIdx
+ 1` entries whose index entries are the readings of the openers' domains
and whose major entry is the reading of `I lvls (ds ++ ifs)` (the stored
type IS the generated one). -/
theorem genRun_binders (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ (cls : Nat) (ty : Expr) (ifs : List Expr) (body : Expr),
      genClsOf R.rd c = cls ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      ConLeche.instPisWith (tgtMajor out c).ds (R.g.formerTys.getD cls default) = some ty ∧
      ConLeche.openPisAtFvars (tgtMajor out c).nIdx ty (p.toBlockShape.rulePrefixAt c)
        = some (ifs, body) ∧
      ifs.length = (tgtMajor out c).nIdx ∧
      p.toBlockShape.rulePrefixAt c = R.g.pre.length ∧
      p.toBlockShape.majorIdxAt c = p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx ∧
      ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map (·.2.2)).length
        = p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx + 1 ∧
      (∀ (k : Nat) (x : Expr), ifs[k]? = some x →
        denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + k) x.fvarTypeD
          = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
              (·.2.2)).getD (p.toBlockShape.rulePrefixAt c + k) default)) ∧
      denoteMeta mpC.base2.acval envC ψ
          (p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx)
          (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
            ((tgtMajor out c).ds ++ ifs))
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).getD (p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx) default) := by
  obtain ⟨cls, gty, S, hgc, hM, hgty, -, hread, hmI, hRP, hst⟩ :=
    genRun_storedTy hμ R hg h mpC ψ hc
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  obtain ⟨ty, body, hty, hopI, hmajE⟩ := ConLeche.ClassGen.major_inv hmaj
  rw [← hM] at hty hopI hmajE hifl
  generalize hnds : R.g.pre ++ ifs.map R.g.binder ++ [(maj, R.g.bm)] = nds at hread hcl
  generalize hbody : Expr.mkAppN (R.g.motVar cls)
    (ifs ++ [.fvar (R.g.pre.length + ifs.length) maj]) = bd at hread hbb
  have hn : nds.length = R.g.pre.length + (tgtMajor out c).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_append, List.length_map, List.length_singleton, hifl]
  obtain ⟨fvs, o, hop, -, hdomE⟩ := open_of_erasedEq_closeTelescope nds 0 bd
    (closeTelescope nds 0 bd) hcl hbb (Expr.ErasedEq.rfl _)
  rw [hn] at hop
  obtain ⟨pps, b, hst', -, hlen, hbind⟩ := denoteMeta_openPis _ hop hread
  rw [← hM] at hst hmI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hst'))
  have hlenF : fvs.length = R.g.pre.length + (tgtMajor out c).nIdx + 1 := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop]
  -- entry `i` of the stored binder data is the reading of `nds[i]`
  have hent : ∀ i nd, i < R.g.pre.length + (tgtMajor out c).nIdx + 1 →
      nds[i]?.map (·.1) = some nd →
      denoteMeta mpC.base2.acval envC ψ i nd
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).getD i default) := by
    intro i nd hi hnd
    obtain ⟨x, hx⟩ : ∃ x, fvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨q, hq, -, hrd⟩ := hbind i x hx
    rw [Nat.zero_add, denoteMeta_erasedEq (hdomE i x nd hx hnd)] at hrd
    rw [hrd, List.getD_eq_getElem?_getD, List.getElem?_map, hq]
    rfl
  refine ⟨cls, ty, ifs, body, hgc, hM, hty, by rw [hRP]; exact hopI, hifl, hRP,
    by rw [hRP]; omega, by rw [List.length_map, hlen, hRP], ?_, ?_⟩
  · intro k x hx
    have hk : k < ifs.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [hRP]
    refine hent _ _ (by omega) ?_
    rw [← hnds, List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by simp; omega), Nat.add_sub_cancel_left, List.getElem?_map, hx]
    rfl
  · rw [hRP, ← hmajE]
    refine hent _ _ (by omega) ?_
    rw [← hnds, List.getElem?_append_right (by simp; omega)]
    simp [hifl]

end Binders

end ConLeche.Model
