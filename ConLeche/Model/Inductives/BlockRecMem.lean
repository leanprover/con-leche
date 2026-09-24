module

public import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Semantics.Tower.BlockRecI

public section

/-!
# The recursor leaf's MEMBERSHIP

`blockRecStaged_of`'s `hrd` (`Model/Inductives/BlockStageRec.lean`) is
reduced by `hrd_of_mem` (`Model/Inductives/BlockRecRead.lean`) to ONE
seam — *the leaf inhabits whatever its stored type reads to*:

```
hmem : ∀ r ∈ rs, ∀ ψ ta,
  denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta →
  ∀ ρ, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta
```

This module proves it, from the run and the family premise
`BlockRecPre` (`Semantics/Tower/BlockRecI.lean`), in two steps:

* **the identification** — the stored type's reading IS a Π-tower.
  The stream's recursor type is never compared with a generated form,
  so the identification is the run's own Π-peel: `checkBlockRecTys`
  succeeds only after `openPisAtFvars (mI + 1)` did, and
  `denoteMeta_openPis` opens a reading with the very `fvar`s it does,
  so `stripPisAV (mI + 1)` of the reading succeeds and
  `stripPisAV_eq_mkPis` exhibits the reading as `mkPisAV rds concl`.
  The binder data `rds` and the conclusion `concl` are therefore
  FUNCTIONS OF THE RUN (`blockRecRdsAV`, `blockRecConclAV`), which is
  what lets the recursor model state its `hTyE` at a named spelling
  rather than at an existential;
* **the seam** — `blockRecAV_facts` at `BlockRecPre` says the leaf of
  class `c` lies in `interp V ρ (RecTy c)`, and `denoteMeta` is a
  function, so the `ta` `hmem` is handed IS `RecTy c` as soon as
  `RecTy c` is the stored type's reading.

Nothing here re-proves the recursor model or a reading battery: the
two facts it needs from other modules are taken as premises in the
shape they are exported — `BlockRecPre` (`blockRecPre_graph`) and the
stage's valuation
spelling (`blockRecStaged_of`'s `acv`).
-/

namespace ConLeche.Model
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The identification: the stored type's reading IS a Π-tower

The stream's recursor type is stored AS IS, so the reading is not
compared with a generated form: it is IDENTIFIED by the run's own
Π-peel.  `rds` and `concl` are therefore functions of the run, spelled
here so that the recursor model can state its `hTyE` at a name
instead of an existential. -/

/-- The `i`-th stored recursor type's READING at `ψ` (`default` off
the list, or at a type that does not read — neither happens under the
run, `recStage_tyPis`). -/
def blockRecTyAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : AnnotTerm :=
  (rs[c]?.bind fun r => denoteMeta acval envC ψ 0 r.1.type).getD default

/-- The `i`-th recursor's BINDER DATA: the reading's `mI + 1` Π-entries
— the block's parameters, the `nP … rP-1` stretch, the indices and the
major. -/
def blockRecRdsAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((stripPisAV (p.majorIdxAt c + 1) (blockRecTyAV acval envC rs ψ c)).map (·.1)).getD []

/-- The `i`-th recursor's CONCLUSION, read under its `mI + 1`
binders. -/
def blockRecConclAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : AnnotTerm :=
  ((stripPisAV (p.majorIdxAt c + 1) (blockRecTyAV acval envC rs ψ c)).map (·.2)).getD default

theorem blockRecTyAV_eq {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {ψ : Name → Nat} {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {ta : AnnotTerm} (hr : rs[c]? = some r)
    (hta : denoteMeta acval envC ψ 0 r.1.type = some ta) :
    blockRecTyAV acval envC rs ψ c = ta := by
  simp [blockRecTyAV, hr, hta]

/-- **The family's SHARED RULE PREFIX, at the run** (stage (b')): the
first stored recursor's opened prefix is
the reference, and every other stored recursor's has its length and is
defeq to it binder by binder.

The bridge from stage (b')'s own list (the TYPE stage's checked
constant values) to the stored `rs` is the run record's
(`RecKRun.stored_fst`). -/
theorem recStage_prefixAgree {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr0 : rs[0]? = some r0) :
    ∃ (fvs0 : List Expr) (o0 : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.rulePrefixAt 0) r0.1.type 0
          = some (fvs0, o0) ∧
      ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rs[i]? = some r → 0 < i →
        p.toBlockShape.rulePrefixAt i = p.toBlockShape.rulePrefixAt 0 ∧
        ∃ (fvs : List Expr) (o : Expr),
          ConLeche.openPisAtFvars (p.toBlockShape.rulePrefixAt 0) r.1.type 0
              = some (fvs, o) ∧
          fvs0.length = fvs.length ∧
          ∀ l, l < fvs0.length →
            ConLeche.isDefEqCore μ envC F (p.toBlockShape.rulePrefixAt 0)
              ((fvs0.map Expr.fvarTypeD).getD l default)
              ((fvs.map Expr.fvarTypeD).getD l default) = .ok true := by
  obtain ⟨R⟩ := id h
  obtain ⟨fvs0, o0, hop0, hall⟩ :=
    ConLeche.checkBlockRecPrefixAgree_inv R.fam.prefixAgree (R.stored_fst hr0)
  exact ⟨fvs0, o0, hop0, fun i r hr hi => hall i r.1 (R.stored_fst hr) hi⟩

/-- **The identification**: at every `ψ`, the `i`-th stored
recursor type READS, its reading is GRADED, and it IS the Π-tower
`mkPisAV rds concl` over the run's own binder data — with the domains'
readings, the bits (`0` and at most `1`) and the conclusion's reading
at the full depth.  This is what the recursor model consumes: `hTyE` at
`RecTy ψ c := blockRecTyAV …`, `rds`/`concl` at the two named
spellings. -/
theorem recStage_tyPis {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    ∃ (fvs : List Expr) (concl : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt i + 1) r.1.type 0
          = some (fvs, concl) ∧
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type
          = some (blockRecTyAV mpC.base2.acval envC rs ψ i) ∧
      blockRecTyAV mpC.base2.acval envC rs ψ i
          = mkPisAV (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i)
              (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i) ∧
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length
          = p.toBlockShape.majorIdxAt i + 1 ∧
      (∀ pd ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i,
          pd.1 = 0 ∧ pd.2.1 ≤ 1) ∧
      (∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ pd, (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i)[j]? = some pd ∧
          pd.1 = 0 ∧ denoteMeta mpC.base2.acval envC ψ j x.fvarTypeD = some pd.2.2) ∧
      denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.majorIdxAt i + 1) concl
          = some (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (blockRecTyAV mpC.base2.acval envC rs ψ i)) := by
  obtain ⟨R⟩ := h
  obtain ⟨_, _, -, -, ⟨TE⟩⟩ := R.tyGenAt hr
  have hop := TE.hopen
  have hcv := TE.hcv
  obtain ⟨_, hru⟩ := checkConstantVal_reads (V := V) hμ mpC hcv
  obtain ⟨ta, hta, hwd, -⟩ := hru ψ
  obtain rfl : blockRecTyAV mpC.base2.acval envC rs ψ i = ta := blockRecTyAV_eq hr hta
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis _ hop hta
  have hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i = pps := by
    rw [blockRecRdsAV, blockRecTyAV_eq hr hta, hst]; rfl
  have hcon : blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i = b := by
    rw [blockRecConclAV, blockRecTyAV_eq hr hta, hst]; rfl
  refine ⟨TE.fvs, TE.concl, hop, hta, ?_, ?_, ?_, ?_, ?_, hwd⟩
  · rw [hrds, hcon]; exact (stripPisAV_eq_mkPis hst).1
  · rw [hrds]; exact hlen
  · rw [hrds]; exact fun pd hpd => stripPisAV_denoteMeta_bits _ hop hta hst pd hpd
  · rw [hrds]; exact fun j x hx => by simpa using hbind j x hx
  · rw [hcon]; simpa using hb

/-- **The recursor type's readings are BOUNDED at their own depths** —
binder `l`'s domain below `l`, the conclusion below the binder count.

A SEPARATE theorem rather than two more clauses of
`recStage_tyPis`: five sites destructure that one positionally
and none of them reads a boundedness, so widening it would make every
consumer carry what it never uses.

This is what §28's `liftDomsK_eq_self_of_bounded` and §29's `hconclB`
ask for.  The run gives it in one step: the stored type is CLOSED
(`checkConstantVal_inv`, carried through the annotation by
`annotateCore_WScoped`/`annotateCore_looseBVars`), so the opening's
own per-index scoping facts hold
(`openPisAtFvars_typeWScoped`/`openPisAtFvars_bounded`), and
`bvarsBelow_of_reading` turns a reading at depth `l` into
`bvarsBelow l`. -/
theorem recStage_tyBounds {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    (∀ l, l < (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length →
      ConLeche.Term.Term.bvarsBelow l
        (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l
          default).2.2).erase) ∧
    ConLeche.Term.Term.bvarsBelow (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length
      (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i).erase := by
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hop := TE.hopen
  have hcv := TE.hcv
  obtain ⟨_, hru⟩ := checkConstantVal_reads (V := V) hμ mpC hcv
  obtain ⟨ta, hta, -, -⟩ := hru ψ
  obtain rfl : blockRecTyAV mpC.base2.acval envC rs ψ i = ta := blockRecTyAV_eq hr hta
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis _ hop hta
  have hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i = pps := by
    rw [blockRecRdsAV, blockRecTyAV_eq hr hta, hst]; rfl
  have hcon : blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i = b := by
    rw [blockRecConclAV, blockRecTyAV_eq hr hta, hst]; rfl
  obtain ⟨-, -, -, -, hlb0, hfv0, tyA, -, -, hann, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have hrty : r.1.type = tyA := by rw [hcv']
  have hws0 : Expr.WScoped 0 r.1.type := by
    rw [hrty]
    exact ConLeche.annotateCore_WScoped _ _ hann (Expr.WScoped.of_not_hasFvar hfv0)
  have hlbT : r.1.type.looseBVarsBounded 0 = true := by
    rw [hrty]
    exact ConLeche.annotateCore_looseBVars _ _ hann hlb0
  obtain ⟨hconclB, hfvsB⟩ := ConLeche.Verify.openPisAtFvars_bounded _ hop hlbT
  obtain ⟨-, hbodyW⟩ := ConLeche.openPisAtFvars_WScoped _ _ _ hop hws0
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [hrds] at hl ⊢
    obtain ⟨x, hx⟩ : ∃ x, TE.fvs[l]? = some x := by
      refine ⟨_, List.getElem?_eq_getElem ?_⟩
      rw [ConLeche.Verify.openPisAtFvars_length _ hop, ← hlen]
      exact hl
    obtain ⟨pd, hpd, -, hread⟩ := hbind l x hx
    rw [Nat.zero_add] at hread
    rw [List.getD_eq_getElem?_getD, hpd, Option.getD_some]
    refine bvarsBelow_of_reading (m := mpC.base2) ?_ ?_ hread
    · have hw := openPisAtFvars_typeWScoped _ hop hws0 l x hx
      rwa [Nat.zero_add] at hw
    · exact hfvsB x (List.mem_of_getElem? hx)
  · rw [hrds, hcon, hlen]
    refine bvarsBelow_of_reading (m := mpC.base2) ?_ hconclB (by simpa using hb)
    rwa [Nat.zero_add] at hbodyW

/-! ## The seam: `hmem`

`blockRecAV_facts` (`Semantics/Tower/BlockRecI.lean`) says the class's
leaf lies in `interp V ρ (RecTy c)`; `denoteMeta` is a function, so
the `ta` the seam is handed IS `RecTy c` once `RecTy c` is the stored
type's reading.  `BlockRecPre` is taken as a PREMISE, in the shape
`blockRecPre_graph` (`Model/Inductives/BlockRecGraph.lean`) concludes
in. -/

/-- **`hrd_of_mem`'s `hmem`, proved.**  The `i`-th stored recursor's
leaf inhabits whatever its stored type reads to, at every `ψ` and
every `ρ`.

Three premises, each in the shape its owner exports:

* `hty` — the reading, at the spelling the family premise is stated
  at (`recStage_tyPis` gives it at
  `RecTy ψ := blockRecTyAV …`);
* `hacv` — the stage's VALUATION: the `i`-th recursor's leaf is the
  `i`-th projection of the chosen tuple (`blockRecStaged_of`'s `acv`,
  which the assembly picks);
* `hpre` — the family premise (`blockRecPre_graph`). -/
theorem hmem_of_pre {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {acv : Name → (Name → Nat) → AnnotTerm} {K : Nat} {s : (Name → Nat) → Nat}
    {RecTy : (Name → Nat) → Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    (hK : rs.length = K)
    (hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta acval envC ψ 0 r.1.type = some (RecTy ψ i))
    (hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        acv r.1.name ψ = ConLeche.Semantics.blockRecAV (s ψ) K (RecTy ψ) (eqs ψ) i)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) K (RecTy ψ) (eqs ψ) ρ) :
    ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta acval envC ψ 0 r.1.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta := by
  intro r hrmem ψ ta hta ρ
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrmem
  have hiK : i < K := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain rfl : ta = RecTy ψ i := Option.some.inj ((hta.symm.trans (hty i r hi ψ)))
  obtain ⟨a, ha, -⟩ := ConLeche.Semantics.blockRecAV_facts (hpre ψ ρ)
  obtain ⟨hmem, hval, -⟩ := ha i hiK
  rw [hacv i r hi ψ, hval]
  exact hmem

/-- **`blockRecStaged_of`'s `hrd`, end to end**: the reading and the
grading are the run's (`recStage_tyReads`), the membership is
the family premise's (`hmem_of_pre`). -/
theorem hrd_of_pre {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {acv : Name → (Name → Nat) → AnnotTerm} {K : Nat} {s : (Name → Nat) → Nat}
    {RecTy : (Name → Nat) → Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hK : rs.length = K)
    (hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some (RecTy ψ i))
    (hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        acv r.1.name ψ = ConLeche.Semantics.blockRecAV (s ψ) K (RecTy ψ) (eqs ψ) i)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) K (RecTy ψ) (eqs ψ) ρ) :
    ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) :=
  hrd_of_mem hμ mpC h (hmem_of_pre hK hty hacv hpre)

end ConLeche.Model
