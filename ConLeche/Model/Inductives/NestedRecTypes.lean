module

public import ConLeche.Model.Inductives.NestedRecRead
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Model.Inductives.BlockRecLeaf
public section

/-!
# The restored recursor types at the run (task #315, M7-2)

`NestedRecRead.lean` reads ONE restored recursor type at the
pre-annotated door; this file runs that reading over the whole tail
input (`NestedTailIn`, `NestedRecsStage.lean`): the auxiliary
recursors ARE the scratch install's generated ones
(`auxStored_rec_eq`), their types are syntactic `∀`-telescopes of
`nP + k + n + nIdx + 1` binders over the constant-free conclusion
(`mutualRecTy_stripPis`), the restore keeps the telescope
(`restoredRecTy_reading`), and the door the restore ran on inferred a
sort for every one of them (`restoreRecTys_at`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-- **The auxiliary recursor type of class `c`, syntactically**: the
read-back's recursor at `c` is the scratch install's generated one
(`auxStored_rec_eq`, at the tail's OWN formers'/constructors'/kinds'
runs), so its type is a `∀`-telescope of `nP + k + n + nIdx_c + 1`
binders, every binder carrying the elimination datum, over the
constant-free conclusion `motive_c ı⃗ t`. -/
theorem NestedTailIn.auxRecTy {c : Nat} (hc : c < b.k) :
    ∃ (a : AuxStored) (f : MutualFormerA) (cbs : List (Expr × BinderMeta)),
      stored[c]? = some a ∧ fms[c]? = some f ∧
      a.cvRa.levelParams = b.rlps ∧
      a.cvRa.type.stripPis (b.nP + (b.k + b.ctors.length + (f.nIdx + 1)))
        = some (cbs, Expr.mkAppN (.bvar (f.nIdx + b.ctors.length + b.k - c))
            (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0])) ∧
      (∀ x ∈ cbs, x.2 = (⟨Level.zeronessOf b.elimLevel⟩ : BinderMeta)) ∧
      (∀ n : Name, (Expr.mkAppN (.bvar (f.nIdx + b.ctors.length + b.k - c))
        (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0])).mentionsConst n = false) ∧
      a.cvRa.type.looseBVarsBounded 0 = true ∧ a.cvRa.type.hasFvar = false := by
  obtain ⟨hlenS, hgetS⟩ := ConLeche.auxStoredAll_get I.hstored
  obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenS]; exact hc)⟩
  obtain ⟨-, hlpsA, fms', f₀', ctorsA', sortss', kinds', hformers', hf₀', hctors', hkinds',
    hgen, -, -, hbv, hfv, -, -⟩ := ConLeche.auxStored_rec_eq I.haux I.hstored ha
  -- the runs are the tail's own
  have hfms : fms = fms' := by
    have h := Except.ok.inj (I.out.formers.symm.trans hformers')
    exact congrArg Prod.snd h
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀')
  subst hf0
  have hctA : (ctorsA, sortss) = (ctorsA', sortss') := Except.ok.inj (I.out.ctors.symm.trans hctors')
  have hcA : ctorsA = ctorsA' := congrArg Prod.fst hctA
  subst hcA
  have hkd : kinds = kinds' := Except.ok.inj (I.out.kindsRun.symm.trans hkinds')
  subst hkd
  -- the generated type's telescope
  obtain ⟨f4, cbs, hf4, hstrip, hmeta, hfree⟩ := ConLeche.mutualRecTy_stripPis hgen
  obtain ⟨f, hf⟩ : ∃ f, fms[c]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact hc)⟩
  have hfl : (ConLeche.mutualGenData b fms ctorsA kinds).1.length = b.k := by
    show (fms.map _).length = b.k
    rw [List.length_map, I.out.facts.lenFms]
  have hcl : (ConLeche.mutualGenData b fms ctorsA kinds).2.length = b.ctors.length := by
    show (List.zipWith _ (b.ctors.zip ctorsA) kinds).length = b.ctors.length
    rw [List.length_zipWith, List.length_zip, I.out.facts.lenA, I.out.facts.lenK,
      I.out.facts.lenA]
    omega
  have hnIdx : f4.nIdx = f.nIdx := by
    have h : (ConLeche.mutualGenData b fms ctorsA kinds).1[c]?
        = some ⟨f.cvTa.name, f.nIdx, f.cvTa.type⟩ := by
      show (fms.map _)[c]? = _
      rw [List.getElem?_map, hf]
      rfl
    rw [h, Option.some.injEq] at hf4
    rw [← hf4]
  rw [hfl, hcl, hnIdx] at hstrip
  rw [hnIdx, hfl, hcl] at hfree
  exact ⟨a, f, cbs, ha, hf, hlpsA, by rw [show b.nP + (b.k + b.ctors.length + (f.nIdx + 1))
      = b.nP + b.k + b.ctors.length + f.nIdx + 1 from by omega]; exact hstrip,
    hmeta, hfree, hbv, hfv⟩

/-- The restore table's parameter count is the auxiliary block's. -/
theorem NestedTailIn.tblNP : (ConLeche.restoreTbl p st).nP = b.nP := by
  exact ((ConLeche.auxBlock_fields I.hb).1).symm

/-- **One class's restored recursor type, read at the run**: the
restored constant carries the recursors' level parameters, and at
every level assignment its type reads to a Π-tower of the auxiliary's
length over the conclusion `motive_c ı⃗ t`, with the elimination
datum's bits, closed domains, graded and formed at the ONE sort the
pre-annotated door inferred for it. -/
theorem NestedTailIn.recTyRead {names : List Name} {as : List AuxStored} {out : List ConstantVal}
    (hrun : ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env))
      (ConLeche.restoreTbl p st) p.lps names as = .ok out)
    {i c : Nat} {a : AuxStored} {o : ConstantVal}
    (ha : as[i]? = some a) (ho : out[i]? = some o)
    (hc : c < b.k) (hsa : stored[c]? = some a) :
    o.levelParams = b.rlps ∧
    ∃ (u : Level) (rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.rlps, ψ₁ q = ψ₂ q) → rds ψ₁ = rds ψ₂) ∧
      ∀ ψ : Name → Nat,
        denoteMeta mp₂.base2.acval
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0 o.type
          = some (mkPisAV (rds ψ)
              (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
        (rds ψ).length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) ∧
        (∀ e ∈ rds ψ, e.1 = 0 ∧ e.2.1 = pwBit ψ (Level.zeronessOf b.elimLevel)) ∧
        DomsBelow 0 (rds ψ) ∧
        ∀ ρ : Nat → V,
          WellDenotedV V ρ (mkPisAV (rds ψ)
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
          interp V ρ (mkPisAV (rds ψ)
              (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
            ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨aa, f, cbs, hsa', hf, hlpsA, hstrip, hmeta, hfree, hbv, hfv⟩ := I.auxRecTy hc
  obtain rfl : a = aa := Option.some.inj (hsa.symm.trans hsa')
  obtain ⟨hlp, hres, hb0, hfv0, hlpd, -, sty, u, hinf, hens⟩ :=
    ConLeche.restoreRecTys_at hrun i a o ha ho
  have hfD : (fms.getD c default).nIdx = f.nIdx := by
    rw [List.getD_eq_getElem?_getD, hf]; rfl
  rw [I.henv] at hinf hens
  have hlps : o.levelParams = b.rlps := by rw [hlp, hlpsA]
  rw [hlps] at hlpd
  refine ⟨hlps, u, ?_⟩
  have hread : ∀ ψ : Name → Nat, ∃ rds : List (Nat × Nat × AnnotTerm),
      denoteMeta mp₂.base2.acval
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0 o.type
        = some (mkPisAV rds (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
      rds.length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) ∧
      (∀ e ∈ rds, e.1 = 0 ∧ e.2.1 = pwBit ψ (Level.zeronessOf b.elimLevel)) ∧
      DomsBelow 0 rds ∧
      ∀ ρ : Nat → V,
        WellDenotedV V ρ (mkPisAV rds
          (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
        interp V ρ (mkPisAV rds
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
          ∈ˢ (univ (u.eval ψ) : V) := by
    intro ψ
    rw [hfD]
    exact nestedRecTy_read_of I.hμ mp₂ I.tblNP hc hstrip hmeta (fun n' _ => hfree n') hres hb0 hfv0
      hinf hens ψ
  obtain ⟨rdsF, hspec⟩ : ∃ rdsF : (Name → Nat) → List (Nat × Nat × AnnotTerm), ∀ ψ : Name → Nat,
      denoteMeta mp₂.base2.acval
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0 o.type
        = some (mkPisAV (rdsF ψ)
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
      (rdsF ψ).length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) ∧
      (∀ e ∈ rdsF ψ, e.1 = 0 ∧ e.2.1 = pwBit ψ (Level.zeronessOf b.elimLevel)) ∧
      DomsBelow 0 (rdsF ψ) ∧
      ∀ ρ : Nat → V,
        WellDenotedV V ρ (mkPisAV (rdsF ψ)
          (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
        interp V ρ (mkPisAV (rdsF ψ)
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
          ∈ˢ (univ (u.eval ψ) : V) :=
    ⟨fun ψ => Classical.choose (hread ψ), fun ψ => Classical.choose_spec (hread ψ)⟩
  refine ⟨rdsF, fun ψ₁ ψ₂ hφ => ?_, hspec⟩
  have h1 := (hspec ψ₁).1
  have h2 := (hspec ψ₂).1
  rw [denoteMeta_params_ext mp₂.base2 hφ 0 o.type hlpd] at h1
  exact (mkPisAV_inj (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1])
    (Option.some.inj (h1.symm.trans h2))).1

/-! ## The classes' constants -/

/-- The block's member count is the classes' count. -/
theorem NestedTailIn.storedLen : stored.length = b.k :=
  (ConLeche.auxStoredAll_get I.hstored).1

/-- The restored member recursors are as many as the members. -/
theorem NestedTailIn.lenM : cvRms.length = p.k := by
  rw [(ConLeche.restoreRecTys_id I.hrm).1, List.length_take, I.storedLen, I.out.bk]
  omega

/-- The restored auxiliary recursors are as many as the pins. -/
theorem NestedTailIn.lenN : cvRns.length = pinsS.length := by
  rw [(ConLeche.restoreRecTys_id I.hrn).1, List.length_drop, I.storedLen, I.out.bk]
  omega

/-- **Class `c`'s restored recursor constant**: a member's below `k`, a
pin's above. -/
@[expose] def nestedRecCvAt (k : Nat) (cvRms cvRns : List ConstantVal) (c : Nat) : ConstantVal :=
  if c < k then cvRms.getD c default else cvRns.getD (c - k) default

/-- **Class `c`'s restored recursor type, read at the run** — `recTyRead`
at the member list below `k` and the auxiliary list above. -/
theorem NestedTailIn.classRecTy {c : Nat} (hc : c < b.k) :
    (nestedRecCvAt p.k cvRms cvRns c).levelParams = b.rlps ∧
    ∃ (u : Level) (rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.rlps, ψ₁ q = ψ₂ q) → rds ψ₁ = rds ψ₂) ∧
      ∀ ψ : Name → Nat,
        denoteMeta mp₂.base2.acval
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0
            (nestedRecCvAt p.k cvRms cvRns c).type
          = some (mkPisAV (rds ψ)
              (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
        (rds ψ).length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) ∧
        (∀ e ∈ rds ψ, e.1 = 0 ∧ e.2.1 = pwBit ψ (Level.zeronessOf b.elimLevel)) ∧
        DomsBelow 0 (rds ψ) ∧
        ∀ ρ : Nat → V,
          WellDenotedV V ρ (mkPisAV (rds ψ)
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
          interp V ρ (mkPisAV (rds ψ)
              (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
            ∈ˢ (univ (u.eval ψ) : V) := by
  have hst := I.storedLen
  obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [hst]; exact hc)⟩
  by_cases hck : c < p.k
  · have hasa : (stored.take p.k)[c]? = some a := by
      rw [List.getElem?_take_of_lt hck]; exact ha
    obtain ⟨o, ho⟩ : ∃ o, cvRms[c]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [I.lenM]; exact hck)⟩
    have hcv : nestedRecCvAt p.k cvRms cvRns c = o := by
      unfold nestedRecCvAt
      rw [if_pos hck, List.getD_eq_getElem?_getD, ho]
      rfl
    rw [hcv]
    exact I.recTyRead I.hrm hasa ho hc ha
  · obtain ⟨q, rfl⟩ : ∃ q, c = p.k + q := ⟨c - p.k, by omega⟩
    have hq : q < pinsS.length := by
      have := I.out.bk
      omega
    have hasa : (stored.drop p.k)[q]? = some a := by
      rw [List.getElem?_drop]; exact ha
    obtain ⟨o, ho⟩ : ∃ o, cvRns[q]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [I.lenN]; exact hq)⟩
    have hcv : nestedRecCvAt p.k cvRms cvRns (p.k + q) = o := by
      unfold nestedRecCvAt
      rw [if_neg hck, show p.k + q - p.k = q from by omega, List.getD_eq_getElem?_getD, ho]
      rfl
    rw [hcv]
    exact I.recTyRead I.hrn hasa ho hc ha

/-! ## The block model's bookkeeping at the run -/

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- The classes are the auxiliary block's members. -/
theorem NestedTailIn.kT : (D).kT = b.k := by
  rw [nestedBlockModel_kT, ← I.out.bk]

/-- The minors are the auxiliary block's constructors. -/
theorem NestedTailIn.nCtorsT : (D).nCtorsT PC = b.ctors.length :=
  nestedBlockModel_nCtorsT I.out.stage.ctorsLen I.out.bk
    (ConLeche.checkMutualCore_inv I.haux).2.2.1

/-- **Class `c`'s index count is its auxiliary former's** — a member's
by construction, a pin's through its group (the pin's recorded index
count is its container member's, and the copy's index telescope is the
container's instantiated at the components). -/
theorem NestedTailIn.nIdxT {c : Nat} (hc : c < b.k) :
    (D).nIdxT c = (fms.getD c default).nIdx := by
  have hkf : p.k ≤ fms.length := by rw [I.out.facts.lenFms, I.out.bk]; omega
  by_cases hck : c < p.k
  · exact nestedBlockModel_nIdxT_mem hck hkf
  · obtain ⟨q, rfl⟩ : ∃ q, c = p.k + q := ⟨c - p.k, by omega⟩
    have hq : q < pinsS.length := by have := I.out.bk; omega
    obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := I.out.stage.groups q hq
    obtain ⟨f, hf⟩ : ∃ f, fms[p.k + (q₀ + i)]? = some f :=
      ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms, I.out.bk]; omega)⟩
    have hfD : (fms.getD (p.k + (q₀ + i)) default).nIdx = f.nIdx := by
      rw [List.getD_eq_getElem?_getD, hf]; rfl
    rw [hfD]
    refine nestedBlockModel_nIdxT_pin G hi (fun ψ => ?_)
    rw [show p.k + q₀ + i = p.k + (q₀ + i) from by omega]
    exact (I.out.facts.FD _ f hf).len ψ

/-- The auxiliary block's largeness flag is the members' sort's. -/
theorem NestedTailIn.large : b.large = f₀.s.isNeverZero := by
  obtain ⟨-, -, -, -, _env₁, fms', f₀', _tq₀, _ctorsA', _sortss', _kinds', _formers4, _ctors4,
    _cvRas, _rulesOf, hformers', hf₀', -, -, hL, -, -, -, -, -, -, -, -⟩ :=
    ConLeche.checkMutualCore_inv I.haux
  have hfms : fms = fms' := by
    have h := Except.ok.inj (I.out.formers.symm.trans hformers')
    exact congrArg Prod.snd h
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀')
  subst hf0
  exact hL

omit I in
/-- The block's sort is the block model's width. -/
theorem NestedTailIn.wEq (ψ : Name → Nat) : (D).w ψ = f₀.s.eval ψ := rfl

/-! ## The readings, assembled -/

/-- **THE `k + nPins` RESTORED RECURSOR TYPES' READINGS AT THE RUN**
(DESIGN §U.25 (e) 2, first half): a sort `s` and readings
`rdsM`/`concM` with every clause of `NestedRecReadings` — the
members' and the auxiliary recursors' types read to Π-towers of the
stage's length over `mutualConcAV`, at the recursors' level
parameters, with the elimination datum's bits, closed at their depths,
stable under those parameters, graded, formed at `s` and `ℓ = 0` at a
`Prop`-valued block — GIVEN the readings' FRAMES for readings so
characterised (`ReadingFramesT`, the second half: the frame
inversion and the frame's two semantic typings). -/
theorem NestedTailIn.readings
    (hfr : ∀ (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      (∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
        denoteMeta mp₂.base2.acval
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0
            (nestedRecCvAt p.k cvRms cvRns c).type
          = some (mkPisAV (rdsM c ψ) (concM c))) →
      (∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
        (rdsM c ψ).length = (D).nP + (D).kT + (D).nCtorsT PC + (D).nIdxT c + 1) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (D).kT →
        (D).ReadingFramesT PC ψ (b.elimLevel.eval ψ) (rdsM c ψ) (concM c) c ρ) :
    ∃ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM := by
  have hkT : (D).kT = b.k := I.kT
  -- the readings, class by class
  have hcl : ∀ c : Nat, ∃ (u : Level) (rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      c < b.k →
        (nestedRecCvAt p.k cvRms cvRns c).levelParams = b.rlps ∧
        (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.rlps, ψ₁ q = ψ₂ q) → rds ψ₁ = rds ψ₂) ∧
        ∀ ψ : Name → Nat,
          denoteMeta mp₂.base2.acval
              (ConLeche.consNestedCtors ctorsR.flatten
                (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0
              (nestedRecCvAt p.k cvRms cvRns c).type
            = some (mkPisAV (rds ψ)
                (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
          (rds ψ).length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) ∧
          (∀ e ∈ rds ψ, e.1 = 0 ∧ e.2.1 = pwBit ψ (Level.zeronessOf b.elimLevel)) ∧
          DomsBelow 0 (rds ψ) ∧
          ∀ ρ : Nat → V,
            WellDenotedV V ρ (mkPisAV (rds ψ)
              (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) ∧
            interp V ρ (mkPisAV (rds ψ)
                (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
              ∈ˢ (univ (u.eval ψ) : V) := by
    intro c
    by_cases hc : c < b.k
    · obtain ⟨hlps, u, rds, hpar, hspec⟩ := I.classRecTy hc
      exact ⟨u, rds, fun _ => ⟨hlps, hpar, hspec⟩⟩
    · exact ⟨.zero, fun _ => [], fun h => absurd h hc⟩
  obtain ⟨uOf, hu⟩ := Classical.skolem.mp hcl
  obtain ⟨rdsOf, hr⟩ := Classical.skolem.mp hu
  have hkD : (D).k = p.k := rfl
  have hnPins : (D).nPins = pinsS.length := rfl
  have hread : ∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
      denoteMeta mp₂.base2.acval
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0
          (nestedRecCvAt p.k cvRms cvRns c).type
        = some (mkPisAV (rdsOf c ψ)
            (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c)) := by
    intro c ψ hc
    rw [hkT] at hc
    exact ((hr c hc).2.2 ψ).1
  have hlen : ∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
      (rdsOf c ψ).length = (D).nP + (D).kT + (D).nCtorsT PC + (D).nIdxT c + 1 := by
    intro c ψ hc
    have hc' : c < b.k := by rw [← hkT]; exact hc
    rw [nestedBlockModel_nP, hkT, I.nCtorsT, I.nIdxT hc']
    rw [((hr c hc').2.2 ψ).2.1]
    omega
  have hsort : ∀ (c : Nat) (ψ : Name → Nat) (ρ : Nat → V), c < (D).kT →
      interp V ρ (mkPisAV (rdsOf c ψ)
          (mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c))
        ∈ˢ (univ (((List.range b.k).map fun c' => (uOf c').eval ψ).foldr max 0) : V) := by
    intro c ψ ρ hc
    have hc' : c < b.k := by rw [← hkT]; exact hc
    refine univ_mono (le_foldr_max _ _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc', rfl⟩)) _ ?_
    exact (((hr c hc').2.2 ψ).2.2.2.2 ρ).2
  refine ⟨fun ψ => ((List.range b.k).map fun c => (uOf c).eval ψ).foldr max 0, rdsOf,
    fun c => mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c, ?_⟩
  refine { lenM := by rw [hkD]; exact I.lenM
           lenN := by rw [hnPins]; exact I.lenN
           readM := ?_, readN := ?_
           lpsM := ?_, lpsN := ?_
           len := hlen
           bits := ?_
           below := ?_
           params := ?_
           okTy := ?_
           tyBelow := ?_
           sort := fun c ψ ρ hc => hsort c ψ ρ hc
           wℓ := fun ψ hw => ConLeche.Model.elimLevel_zero_of_w_zero I.large ψ hw
           frames := hfr rdsOf _ hread hlen }
  · intro t ht ψ
    have ht' : t < p.k := by rw [hkD] at ht; exact ht
    have hc : t < (D).kT := by rw [hkT]; have := I.out.bk; omega
    have hcv : nestedRecCvAt p.k cvRms cvRns t = cvRms.getD t default := by
      unfold nestedRecCvAt; rw [if_pos ht']
    rw [← hcv]
    exact hread t ψ hc
  · intro q hq ψ
    have hq' : q < pinsS.length := by rw [hnPins] at hq; exact hq
    have hc : (D).k + q < (D).kT := by rw [hkT, hkD]; have := I.out.bk; omega
    have hcv : nestedRecCvAt p.k cvRms cvRns ((D).k + q) = cvRns.getD q default := by
      unfold nestedRecCvAt
      rw [hkD, if_neg (by omega), show p.k + q - p.k = q from by omega]
    rw [← hcv]
    exact hread _ ψ hc
  · intro t ht
    have ht' : t < p.k := by rw [hkD] at ht; exact ht
    have hc : t < b.k := by have := I.out.bk; omega
    have hcv : nestedRecCvAt p.k cvRms cvRns t = cvRms.getD t default := by
      unfold nestedRecCvAt; rw [if_pos ht']
    rw [← hcv]
    exact (hr t hc).1
  · intro q hq
    have hq' : q < pinsS.length := by rw [hnPins] at hq; exact hq
    have hc : p.k + q < b.k := by have := I.out.bk; omega
    have hcv : nestedRecCvAt p.k cvRms cvRns (p.k + q) = cvRns.getD q default := by
      unfold nestedRecCvAt
      rw [if_neg (by omega), show p.k + q - p.k = q from by omega]
    rw [← hcv]
    exact (hr _ hc).1
  · intro c ψ hc e he
    have hc' : c < b.k := by rw [← hkT]; exact hc
    rw [(((hr c hc').2.2 ψ).2.2.1 e he).2]
    exact (pwBit_zeronessOf ψ b.elimLevel).symm
  · intro c ψ hc
    have hc' : c < b.k := by rw [← hkT]; exact hc
    exact ((hr c hc').2.2 ψ).2.2.2.1
  · intro c ψ₁ ψ₂ hc hφ
    have hc' : c < b.k := by rw [← hkT]; exact hc
    exact (hr c hc').2.1 ψ₁ ψ₂ hφ
  · intro c ψ ρ hc
    have hc' : c < b.k := by rw [← hkT]; exact hc
    exact (((hr c hc').2.2 ψ).2.2.2.2 ρ).1
  · intro c ψ hc
    have hc' : c < b.k := by rw [← hkT]; exact hc
    exact blockRecTy_below (nP := b.nP) (k := b.k) (n := b.ctors.length)
      (nIdx := (fms.getD c default).nIdx) (mm := c) ((hr c hc').2.2 ψ).2.2.2.1
      (by have := ((hr c hc').2.2 ψ).2.1; omega)

end Run

end ConLeche.Model
