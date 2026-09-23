module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The recursor CHECK at k members, inverted at the NAMES

Two kernel-inversion facts about `checkBlockRecK`
(`ConLeche/Kernel/Inductives/BlockInstall.lean`), MODEL-FREE: what the
stage stores, per recursor record, and what its `checkConstantVal` run
says about the stored constant.

* `checkBlockRecK_recNames`: the name-set check ran, there is one
  stored recursor per record, and each is that record's constant
  CHECKED at the constructors' environment;
* `checkBlockRecK_cvFacts`: every stored recursor's name is fresh at
  that environment, passes the two name guards, and its (annotated)
  type mentions no empty projection slot.

They live here, below both consumers: the model tier's recursor-stage
assembly (`Model/Inductives/BlockRecAssembly.lean`) and the η-closure's
recursor freshness (`checkBlockRec_fresh`,
`Semantics/Inductives/DeclBlockEta.lean`), which may not import Model.
-/

namespace ConLeche

variable {μ : CheckMode}

/-- **The recursor stage's per-index facts**: the name-set check ran,
there is one stored recursor per RECORD, and each stored recursor is
that record's constant, CHECKED at the constructors' environment. -/
theorem checkBlockRecK_recNames {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    checkBlockRecPins (m := CheckM) p = .ok () ∧
    rs.length = p.recs.length ∧
    ∀ i, i < p.recs.length → ∃ rc r, p.recs[i]? = some rc ∧ rs[i]? = some r ∧
      r.1.name = rc.cvR.name ∧
      checkConstantVal (fueledOps μ F) envC rc.cvR = .ok r.1 ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt i ∧
      ∃ nIdx, p.toBlockShape.majorIdxAt i = p.toBlockShape.rulePrefixAt i + nIdx := by
  obtain ⟨R⟩ := checkBlockRecK_run h
  refine ⟨R.pins, R.len, fun i hil => ?_⟩
  obtain ⟨rc, r, u, hrc, hr, -, ⟨E⟩⟩ := R.tyAt' hil
  exact ⟨rc, r, hrc, hr, E.name_eq, E.hcv, E.nP_le, r.2.2.1, E.mI_eq⟩

/-- **The stored recursors' name facts and `hnoTy`**, from the
per-recursor `checkConstantVal` run: freshness at the constructors'
environment, the two name guards, and — because the stored type is the
ANNOTATED one — every `.proj` node of it sits at a stored table slot,
so an EMPTY slot is not mentioned. -/
theorem checkBlockRecK_cvFacts {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs,
      envC.find? r.1.name = none ∧
      reservedBasisNames.contains r.1.name = false ∧
      r.1.name.isProjFnShape = false ∧
      ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i r.1.type := by
  obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hname, hcv, -, -⟩ := hall i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨hfresh, hres, hpsh, -, -, hfv, type, -, -, hann, -, -, -, -, hcv'⟩ :=
    checkConstantVal_inv hcv
  have htype : r.1.type = type := by rw [hcv']
  refine ⟨by rw [hname]; exact hfresh, by rw [hname]; exact hres,
    by rw [hname]; exact hpsh, fun T i hslot => ?_⟩
  rw [htype]
  exact annotateCore_noProjAt μ hann hfv hslot

end ConLeche
