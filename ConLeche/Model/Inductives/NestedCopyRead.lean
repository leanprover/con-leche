module

public import ConLeche.Model.Inductives.NestedCopyIdx
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Steps.TowerKit
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.InstLevels
import ConLeche.Semantics.Tower.FixWire
-- The `inst` kit (DESIGN §U.23 (e)): hung here until the assembly
-- `nestedPinsInst_of` consumes it (the second `inst` session).
import ConLeche.Verify.Inductives.NestedCopyRewrite
import ConLeche.Verify.Inductives.NestedCopyProv
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Model.Inductives.NestedCopyFound
public section

/-!
# The copy's constructor, read (task #315 L-B, DESIGN §U.23 (e))

`NestedCopyIdx.lean` read a copy's FORMER (a Π-tower ending in a sort).
The `inst` half of `NestedPinsIdent` reads a copy's CONSTRUCTOR — the
container's constructor at the pin, `instPis (instantiateLevelParams
J.lps lvls cc.type) Ds` — whose conclusion is not a sort.  This module
generalises the peel to an arbitrary conclusion (`peelPis_mkPisAV`: the
tower over the data past the components instantiated from cut `0`, the
conclusion instantiated at the remaining data's depth) and states the
reading of the instantiated telescope at depth `nP` from the source's
reading (`instPisILP_read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The peel at an arbitrary conclusion -/

theorem AnnotTerm.instAll_sort : ∀ (ds : List AnnotTerm) (k s : Nat),
    AnnotTerm.instAll ds k (.sort s) = .sort s
  | [], _, _ => rfl
  | d :: ds, k, s => by simp only [AnnotTerm.instAll, AnnotTerm.inst_sort, instAll_sort ds]

/-- **The peel of a Π-tower along a spine of the parameters' length**:
the tower over the remaining data instantiated from cut `0`, the
conclusion instantiated at the remaining data's depth. -/
theorem peelPis_mkPisAV :
    ∀ (ps I : List (Nat × Nat × AnnotTerm)) (vs : List AnnotTerm) (C : AnnotTerm),
      vs.length = ps.length →
      AnnotTerm.peelPis (mkPisAV (ps ++ I) C) vs
        = some (mkPisAV (instTeleP vs 0 I) (AnnotTerm.instAll vs I.length C))
  | [], I, [], C, _ => by
    simp only [List.nil_append, AnnotTerm.peelPis, instTeleP_nil, AnnotTerm.instAll]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | p :: ps, I, v :: vs, C, h => by
    simp only [List.cons_append, mkPisAV, AnnotTerm.peelPis]
    rw [inst_mkPisAV, instDomsAt_append]
    have hl : vs.length = ps.length := by simpa using h
    have hlen : vs.length = (instDomsAt v 0 ps).length := by rw [instDomsAt_length, hl]
    rw [peelPis_mkPisAV _ _ vs _ hlen, Nat.zero_add, instDomsAt_length, ← hl,
      ← Nat.zero_add vs.length, instTeleP_instDomsAt]
    simp only [AnnotTerm.instAll, List.length_append, Nat.zero_add]
    rw [show ps.length + I.length = I.length + vs.length from by omega]

/-- The sort case is `peelPis_mkPisAV_sort`. -/
theorem peelPis_mkPisAV_sort' (ps I : List (Nat × Nat × AnnotTerm)) (vs : List AnnotTerm) (s : Nat)
    (h : vs.length = ps.length) :
    AnnotTerm.peelPis (mkPisAV (ps ++ I) (.sort s)) vs
      = some (mkPisAV (instTeleP vs 0 I) (.sort s)) := by
  rw [peelPis_mkPisAV _ _ _ _ h, AnnotTerm.instAll_sort]

/-! ## The instantiated telescope, read at depth `nP` -/

/-- **The reading of a closed telescope instantiated at scoped
arguments**: `T` (closed, bounded) reading at `ψJ = substFn ψ ks us` as
`mkPisAV ppsJ C` (bounded), the arguments `Ds` (scoped at `nP`,
bounded) reading as `vs` at depth `nP`; then `instPis
(instantiateLevelParams ks us T) Ds` reads at depth `nP` as the tower
over `ppsJ` past the arguments, instantiated from cut `0`, with `C`
instantiated at the remaining depth. -/
theorem instPisILP_read (m : EnvModel V env) {ψ ψJ : Name → Nat} {nP : Nat}
    {T : Expr} (hTcl : T.hasFvar = false)
    {ks : List Name} {us : List Level} (hψJ : ψJ = Level.substFn ψ ks us)
    {ppsJ : List (Nat × Nat × AnnotTerm)} {C : AnnotTerm}
    (hread : denoteMeta m.acval env ψJ 0 T = some (mkPisAV ppsJ C))
    (hbelow : DomsBelow 0 ppsJ) (hC : Term.bvarsBelow ppsJ.length C.erase)
    {Ds : List Expr} {vs : List AnnotTerm} (hvl : vs.length ≤ ppsJ.length)
    (hDs : ∀ a ∈ Ds, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ nP Ds vs)
    {tyI : Expr} (hinst : Expr.instPis (Expr.instantiateLevelParams ks us T) Ds = some tyI) :
    denoteMeta m.acval env ψ nP tyI
      = some (mkPisAV (instTeleP vs 0 (ppsJ.drop vs.length))
          (AnnotTerm.instAll vs (ppsJ.length - vs.length) C)) := by
  have hTa : denoteMeta m.acval env ψ nP (Expr.instantiateLevelParams ks us T)
      = some (mkPisAV ppsJ C) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m) ψ nP T, ← hψJ,
      denoteMeta_lift m.acval_closed (Expr.WScoped.of_not_hasFvar (d := 0) hTcl) nP (Nat.zero_le _),
      hread]
    simp only [Option.map_some, Nat.sub_zero]
    rw [liftN_eq_self_of_closed (mkPisAV_below_of hbelow (by simpa using hC)) 0 nP]
  obtain ⟨ds, hpr⟩ := ConLeche.instPis_instPisAt Ds _ tyI hinst
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAt_peel m.acval_closed (acval_inst_self m) Ds hpr
    (Expr.WScoped.of_not_hasFvar (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hTcl))
    hDs hTa hspine
  rw [← List.take_append_drop vs.length ppsJ,
    peelPis_mkPisAV _ _ vs C (by rw [List.length_take, Nat.min_eq_left hvl]),
    List.length_drop] at hpeel
  rw [hrest, ← Option.some.inj hpeel]

end ConLeche.Model
