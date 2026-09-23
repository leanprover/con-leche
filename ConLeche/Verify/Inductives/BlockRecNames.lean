module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.ExceptBind

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
  unfold checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := exceptBind_ok h
  obtain ⟨-, -, h⟩ := exceptBind_ok h
  obtain ⟨-, hallT⟩ := checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := checkBlockRecsRules_facts h
  refine ⟨by cases u; exact hpins, hlenR, ?_⟩
  intro i hil
  obtain ⟨rc, r, hrc, hr, hcvRa, -⟩ := hallR i hil
  obtain ⟨rc'', cvRi, nIdx, u', hrc'', hcu, hcv, hle, hsum⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have hq := hcvRa
    rw [Nat.zero_add] at hq
    exact congrArg Prod.fst (Option.some.inj (hq.symm.trans hcvRa'))
  refine ⟨rc, r, hrc, hr, by rw [hr1, (checkConstantVal_lps hcv).1],
    by rw [hr1]; exact hcv, ?_, ?_⟩
  · rw [Nat.zero_add] at hle; exact hle
  · rw [Nat.zero_add] at hsum
    exact ⟨nIdx, hsum⟩

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
