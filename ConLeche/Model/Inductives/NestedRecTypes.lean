module

public import ConLeche.Model.Inductives.NestedRecRead
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.NestedElimInv
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
    hgen, -, -, hbv, hfv⟩ := ConLeche.auxStored_rec_eq I.haux I.hstored ha
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

end Run

end ConLeche.Model
