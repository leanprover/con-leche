module

import ConLeche.Verify.Inductives.BlockWF
public import ConLeche.Model.Inductives.BlockRecRead
public import ConLeche.Model.Inductives.StructRead
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Semantics.Tower.BlockRecI

public section

/-!
# The recursor leaf's MEMBERSHIP (task #315, milestone M5, the Model half)

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
  what lets the regimes' lane state its `hTyE` at a named spelling
  rather than at an existential;
* **the seam** — `blockRecAV_facts` at `BlockRecPre` says the leaf of
  class `c` lies in `interp V ρ (RecTy c)`, and `denoteMeta` is a
  function, so the `ta` `hmem` is handed IS `RecTy c` as soon as
  `RecTy c` is the stored type's reading.

Nothing here re-proves a regime or a reading battery: the two lemmas
it needs of other lanes are taken as premises in the shape they
export — `BlockRecPre` (RM3's `blockRecPre_of`) and the stage's
valuation spelling (`blockRecStaged_of`'s `acv`).
-/

namespace ConLeche.Model
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The run's Π-shape

`checkBlockRecTys_inv` (`Verify/Inductives/BlockWF.lean`) exports the
per-recursor `checkConstantVal` run but not the Π-peel that precedes
it, and this lane may not touch that file; the peel is therefore
re-inverted here, in the one shape the readings need.  If the Verify
lane ever widens `checkBlockRecTys_inv`, this theorem is its
corollary and should go. -/

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- **Stage (b)'s Π-peel, inverted**: a checked recursor's stored type
binds its parameters, its `nP … rP-1` stretch, its indices and its
major — `mI + 1` binders in all — over the conclusion.  This is the
whole shape the reading needs: everything else `checkBlockRecTys`
checks is about the binders' CONTENTS. -/
theorem checkBlockRecTys_open {mode : ConLeche.CheckMode} {env : Env}
    {p : ConLeche.BlockShape} {nested : Bool} {cvTas : List ConstantVal} {F : Nat} :
    ∀ {recs : List ConLeche.RecShape} {ri : Nat}
      {cvRus : List (ConstantVal × Nat × Level)},
      ConLeche.checkBlockRecTys (ConLeche.fueledOps mode F) env p nested cvTas recs ri
          = .ok cvRus →
      ∀ i, i < recs.length → ∃ (cvRi : ConstantVal) (nIdx : Nat) (u : Level)
        (fvs : List Expr) (concl : Expr),
        cvRus[i]? = some (cvRi, nIdx, u) ∧
        ConLeche.openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi.type 0
          = some (fvs, concl)
  | [], _, cvRus, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | rc :: rest, ri, cvRus, h, i, hi => by
    unfold ConLeche.checkBlockRecTys at h
    obtain ⟨ms, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvTa, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvRi, _, h⟩ := ConLeche.exceptBind_ok h
    by_cases hle : p.nP ≤ p.rulePrefixAt ri
    case neg => rw [if_neg hle] at h; close_throw h
    rw [if_pos hle] at h
    obtain ⟨x1, hx1, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨fvs, concl⟩ := x1
    have hop : ConLeche.openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0
        = some (fvs, concl) := ConLeche.unwrapOr_ok hx1
    obtain ⟨x2, _, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨_, _⟩ := x2
    obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨maj, _, h⟩ := ConLeche.exceptBind_ok h
    by_cases hmaj : (maj.fvarTypeD.getAppFn ==
          Expr.const ms.cvT.name (p.lps.map .param) &&
        maj.fvarTypeD.getAppArgs.length == p.nP + ms.nIdx &&
        maj.fvarTypeD.getAppArgs.take p.nP == fvs.take p.nP &&
        maj.fvarTypeD.getAppArgs.drop p.nP ==
          (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx) = true
    case neg => rw [if_neg hmaj] at h; close_throw h
    rw [if_pos hmaj] at h
    obtain ⟨sty, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨u, _, h⟩ := ConLeche.exceptBind_ok h
    have key : ∀ {rs' : List (ConstantVal × Nat × Level)},
        ConLeche.checkBlockRecTys (ConLeche.fueledOps mode F) env p nested cvTas rest
            (ri + 1) = .ok rs' →
        cvRus = (cvRi, ms.nIdx, u) :: rs' →
        ∃ (cvRi' : ConstantVal) (nIdx : Nat) (u' : Level)
          (fvs' : List Expr) (concl' : Expr),
          cvRus[i]? = some (cvRi', nIdx, u') ∧
          ConLeche.openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi'.type 0
            = some (fvs', concl') := by
      intro rs' hrest hcv
      subst hcv
      cases i with
      | zero => exact ⟨cvRi, ms.nIdx, u, fvs, concl, rfl, by simpa using hop⟩
      | succ i =>
        obtain ⟨cvRi', nIdx, u', fvs', concl', hcu, hop'⟩ :=
          checkBlockRecTys_open hrest i (by simpa using hi)
        exact ⟨cvRi', nIdx, u', fvs', concl', by simpa using hcu,
          by rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hop'⟩
    by_cases hlarge : ConLeche.blockLargeElimAllowed p nested = true
    case pos =>
      rw [if_pos hlarge] at h
      obtain ⟨rs', hrest, h⟩ := ConLeche.exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm
    case neg =>
      rw [if_neg hlarge] at h
      obtain ⟨b, _, h⟩ := ConLeche.exceptBind_ok h
      by_cases hb : b = true
      case neg => rw [if_neg hb] at h; close_throw h
      rw [if_pos hb] at h
      obtain ⟨rs', hrest, h⟩ := ConLeche.exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm

/-! ## The identification: the stored type's reading IS a Π-tower

The stream's recursor type is stored AS IS, so the reading is not
compared with a generated form (as `denoteMeta_structRecTyR` does at
`k = 1`): it is IDENTIFIED by the run's own Π-peel.  `rds` and `concl`
are therefore functions of the run, spelled here so that the regimes'
lane can state its `hTyE` at a name instead of an existential. -/

/-- The `i`-th stored recursor type's READING at `ψ` (`default` off
the list, or at a type that does not read — neither happens under the
run, `checkBlockRecK_tyPis`). -/
@[expose] def blockRecTyAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : AnnotTerm :=
  (rs[c]?.bind fun r => denoteMeta acval envC ψ 0 r.1.type).getD default

/-- The `i`-th recursor's BINDER DATA: the reading's `mI + 1` Π-entries
— the block's parameters, the `nP … rP-1` stretch, the indices and the
major. -/
@[expose] def blockRecRdsAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((stripPisAV (p.majorIdxAt c + 1) (blockRecTyAV acval envC rs ψ c)).map (·.1)).getD []

/-- The `i`-th recursor's CONCLUSION, read under its `mI + 1`
binders. -/
@[expose] def blockRecConclAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
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

/-- **The stage's tuple is the type stage's checked constant, and its
type is Π-peeled** — `checkBlockRecK_tyReads`' identification
(`checkBlockRecK_reserved`'s, `Verify/Inductives/BlockWF.lean`) at an
INDEX, carrying the peel with it. -/
theorem checkBlockRecK_tyShape {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    (∃ cv : ConstantVal,
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) envC cv = .ok r.1) ∧
    ∃ (fvs : List Expr) (concl : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt i + 1) r.1.type 0
        = some (fvs, concl) := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨-, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkBlockRecsRules_facts h
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  obtain ⟨-, r', -, hr', hcvRa, -⟩ := hallR i hil
  obtain rfl := Option.some.inj (hr.symm.trans hr')
  obtain ⟨rc2, cvRi, nIdx, u', -, hcu, hcv⟩ := hallT i hil
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have hq := hcvRa
    rw [Nat.zero_add] at hq
    exact congrArg Prod.fst (Option.some.inj (hq.symm.trans hcvRa'))
  obtain ⟨cvRi2, nIdx2, u2, fvs, concl, hcu2, hop⟩ := checkBlockRecTys_open htys i hil
  obtain rfl : cvRi2 = cvRi := by
    have := Option.some.inj (hcu2.symm.trans hcu)
    exact congrArg Prod.fst this
  rw [hr1]
  rw [Nat.zero_add] at hop
  exact ⟨⟨_, hcv⟩, fvs, concl, hop⟩

/-- **O-2, the identification**: at every `ψ`, the `i`-th stored
recursor type READS, its reading is GRADED, and it IS the Π-tower
`mkPisAV rds concl` over the run's own binder data — with the domains'
readings, the bits (`0` and at most `1`) and the conclusion's reading
at the full depth.  This is what the regimes consume: `hTyE` at
`RecTy ψ c := blockRecTyAV …`, `rds`/`concl` at the two named
spellings. -/
theorem checkBlockRecK_tyPis {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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
  obtain ⟨⟨cv, hcv⟩, fvs, concl, hop⟩ := checkBlockRecK_tyShape h hr
  obtain ⟨ta, hta, hwd⟩ := checkConstantVal_reads hμ mpC hcv ψ
  obtain rfl : blockRecTyAV mpC.base2.acval envC rs ψ i = ta := blockRecTyAV_eq hr hta
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis _ hop hta
  have hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i = pps := by
    rw [blockRecRdsAV, blockRecTyAV_eq hr hta, hst]; rfl
  have hcon : blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ i = b := by
    rw [blockRecConclAV, blockRecTyAV_eq hr hta, hst]; rfl
  refine ⟨fvs, concl, hop, hta, ?_, ?_, ?_, ?_, ?_, hwd⟩
  · rw [hrds, hcon]; exact (stripPisAV_eq_mkPis hst).1
  · rw [hrds]; exact hlen
  · rw [hrds]; exact fun pd hpd => stripPisAV_denoteMeta_bits _ hop hta hst pd hpd
  · rw [hrds]; exact fun j x hx => by simpa using hbind j x hx
  · rw [hcon]; simpa using hb

/-! ## The seam: `hmem`

`blockRecAV_facts` (`Semantics/Tower/BlockRecI.lean`) says the class's
leaf lies in `interp V ρ (RecTy c)`; `denoteMeta` is a function, so
the `ta` the seam is handed IS `RecTy c` once `RecTy c` is the stored
type's reading.  `BlockRecPre` is taken as a PREMISE, in the shape
lane RM3's `blockRecPre_of` (`Model/Inductives/BlockRecRegimes.lean`)
concludes in. -/

/-- **`hrd_of_mem`'s `hmem`, proved.**  The `i`-th stored recursor's
leaf inhabits whatever its stored type reads to, at every `ψ` and
every `ρ`.

Three premises, each in the shape its owner exports:

* `hty` — the reading, at the spelling the family premise is stated
  at (`checkBlockRecK_tyPis` gives it at
  `RecTy ψ := blockRecTyAV …`);
* `hacv` — the stage's VALUATION: the `i`-th recursor's leaf is the
  `i`-th projection of the chosen tuple (`blockRecStaged_of`'s `acv`,
  which the assembly lane picks);
* `hpre` — the family premise (lane RM3's `blockRecPre_of`). -/
theorem hmem_of_pre {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {acv : Name → (Name → Nat) → AnnotTerm} {s K : Nat}
    {RecTy : (Name → Nat) → Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    (hK : rs.length = K)
    (hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta acval envC ψ 0 r.1.type = some (RecTy ψ i))
    (hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        acv r.1.name ψ = ConLeche.Semantics.blockRecAV s K (RecTy ψ) (eqs ψ) i)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V s K (RecTy ψ) (eqs ψ) ρ) :
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
grading are the run's (`checkBlockRecK_tyReads`), the membership is
the family premise's (`hmem_of_pre`). -/
theorem hrd_of_pre {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {acv : Name → (Name → Nat) → AnnotTerm} {s K : Nat}
    {RecTy : (Name → Nat) → Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hK : rs.length = K)
    (hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some (RecTy ψ i))
    (hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        acv r.1.name ψ = ConLeche.Semantics.blockRecAV s K (RecTy ψ) (eqs ψ) i)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V s K (RecTy ψ) (eqs ψ) ρ) :
    ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) :=
  hrd_of_mem hμ mpC h (hmem_of_pre hK hty hacv hpre)

end ConLeche.Model
