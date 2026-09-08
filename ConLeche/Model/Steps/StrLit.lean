module

public import ConLeche.Model.Steps.CapsRows

@[expose] public section

/-!
# The `String`-literal inference row (task #161, PROJ/STR install tier)

`InferStrLitStep` (`Steps/Infer.lean`), discharged.  The v1 mirror is
`Sound/Lit.lean`'s `strLit_facts`/`sndInfLitStr`; the transposition is
shorter, and for one structural reason:

* v1 walks `henv.mem_type` at each of the seven support constants and
  then **builds the `AnnotOkV` of every one of those types by hand**
  (`hnilOk`, `hconsOk`, `hofOk`, `hOFOk` — four bespoke `AnnotOkV_pi`
  towers, each with its own domain-membership side conditions).  The P
  currency's `ConstType` residue delivers a stored type's reading
  **together with its grading**, so all four disappear: what remains is
  the walk itself.
* the fits are `TeleFit`, whose cons peels under `cons a ρ` instead of
  substituting, so the `Term.inst_eq_self_of_closed` bookkeeping that
  dominates the v1 proof is replaced by three leaf-closedness
  equations (`interp_closed` at the `acval` leaves).

**No bit positivity is used anywhere** (`NatEqsP.lean`'s finding): the
memberships ride `wellDenotedV_mkAppN_of_fit`, whose `v = 0` fibre premise
comes from the type reading's own `AnnotValid`.

The chain lemma is stated over the five head packages as *explicit
arguments*, exactly as `natLit_factsAV` (`Steps/Lit.lean`) is stated
over the two numeral heads and for the same reason: the head facts are
one `ConstType` chain, the same for every literal, and factoring them
out keeps the character induction free of the guard's inversion
plumbing.

## Why `Steps/StrLit.lean`'s `charList_facts2` is not reused

The denoteAnnot-lane chain (`charList_facts2`, `strLit_facts2`) takes its
head memberships at `piR 1 …` — the regime bit **fixed at 1**, on the
argument that `Char`/`List Char`/`String`/`Nat` are all `Type`-level.
That argument is unavailable at the P currency: `denoteMeta` reads the
*stored* bit `pwBit φ mb.pw` off the annotated binder, and nothing in
`strLitSupported` pins it.  The rows below therefore keep the bits
abstract and pay for it with `TeleFit`/`wellDenotedV_mkAppN_of_fit`,
whose `v = 0` fibre premises come from the type reading's own
`AnnotValid`.  The two chains are the same walk at two currencies;
neither subsumes the other.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The character-list chain -/

/-- **The character-list facts** — `natLit_factsAV`'s companion.  Every
`denoteMeta` character list is graded and inhabits `List Char`'s reading,
by induction on the list from the `nil`/`cons`/`Char.ofNat` head
packages and the two numeral heads. -/
theorem charList_facts {ρ : Nat → V}
    {KL KH KN KC KF Kz Ks KNat : AnnotTerm} {bN b1 b2 b3 bF : Nat}
    (hclL : ∀ σ : Nat → V, interp V σ KL = interp V ρ KL)
    (hclH : ∀ σ : Nat → V, interp V σ KH = interp V ρ KH)
    (hokKH : WellDenotedV V ρ KH) (hokKN : WellDenotedV V ρ KN)
    (hokKC : WellDenotedV V ρ KC) (hokKF : WellDenotedV V ρ KF)
    (hokKz : WellDenotedV V ρ Kz) (hokKs : WellDenotedV V ρ Ks)
    (hCharU : interp V ρ KH ∈ˢ (univ 1 : V))
    (hokTN : WellDenotedV V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AnnotTerm))
    (hmemN : interp V ρ KN ∈ˢ interp V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AnnotTerm))
    (hokTC : WellDenotedV V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AnnotTerm))
    (hmemC : interp V ρ KC ∈ˢ interp V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AnnotTerm))
    (hokTF : WellDenotedV V ρ ((.pi 0 bF KNat KH) : AnnotTerm))
    (hmemF : interp V ρ KF ∈ˢ interp V ρ
      ((.pi 0 bF KNat KH) : AnnotTerm))
    (hz : interp V ρ Kz ∈ˢ interp V ρ KNat)
    (hsucc : interp V ρ Ks
      ∈ˢ piR 1 (interp V ρ KNat) fun _ => interp V ρ KNat) :
    ∀ cs : List Char,
      WellDenotedV V ρ (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs) ∧
        interp V ρ (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs)
          ∈ˢ interp V ρ ((.app KL KH) : AnnotTerm) := by
  -- the sort domain, at the reading's own spelling
  have hCharS : interp V ρ KH ∈ˢ interp V ρ ((.sort 1) : AnnotTerm) := by
    rw [interp_sort]; exact hCharU
  -- one character element: `Char.ofNat` applied to a numeral
  have helem : ∀ c : Char,
      WellDenotedV V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm) ∧
        interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm)
          ∈ˢ interp V ρ KH := by
    intro c
    have hnat := natLit_factsAV hokKz.1 hokKs.1 hz hsucc c.toNat
    have hokNum : WellDenotedV V ρ (natLitAV Kz Ks c.toNat) :=
      ⟨hnat.1, AnnotValid_natLitAV hokKz.2 hokKs.2 c.toNat⟩
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
      [natLitAV Kz Ks c.toNat] hokTF hokKF
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokNum)
      hmemF (TeleFit.cons hnat.2 TeleFit.nil)
    refine ⟨h.1, ?_⟩
    have := h.2
    rwa [hclH (cons (interp V ρ (natLitAV Kz Ks c.toNat)) ρ)] at this
  -- the walk
  intro cs
  induction cs with
  | nil =>
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ) [KH] hokTN hokKN
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokKH)
      hmemN (TeleFit.cons hCharS TeleFit.nil)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp_app, hclL (cons (interp V ρ KH) ρ)] at h2
    rw [interp_app]
    exact h2
  | cons c cs ih =>
    obtain ⟨ihA, ihm⟩ := ih
    obtain ⟨heA, hem⟩ := helem c
    -- the three memberships, at the fit's own environments
    have hm2 : interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm)
        ∈ˢ interp V (cons (interp V ρ KH) ρ) ((.bvar 0) : AnnotTerm) := hem
    have hm3 : interp V ρ
          (charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs)
        ∈ˢ interp V
          (cons (interp V ρ ((.app KF (natLitAV Kz Ks c.toNat)) : AnnotTerm))
            (cons (interp V ρ KH) ρ))
          ((.app KL (.bvar 1)) : AnnotTerm) := by
      have hi := ihm
      rw [interp_app] at hi
      rw [interp_app, hclL _]
      exact hi
    have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
      [KH, .app KF (natLitAV Kz Ks c.toNat),
        charListAV (.app KN KH) (.app KC KH) KF Kz Ks cs]
      hokTC hokKC
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hokKH
        · exact heA
        · exact ihA)
      hmemC
      (TeleFit.cons hCharS (TeleFit.cons hm2 (TeleFit.cons hm3
        TeleFit.nil)))
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp_app, hclL _] at h2
    rw [interp_app]
    exact h2

/-! ## The chain at the environment

The five head packages, read off `ConstType` at the guard's pinned
types.  Note what is *absent*: `List`'s own membership
(`strLit_facts`' `hListMem`) and the four hand-built type gradings —
the P residue delivers a stored type's grading with its reading, so
the only environment facts consumed are the four memberships and
`Char`'s universe membership. -/

/-- **The string chain, at the environment.**  `strLit_facts`' mirror
at the validated-annotation currency. -/
theorem strLitFacts {m : EnvModel V env} (hct : ConstType m φ)
    (hval : AcvalValid m) (hnh : NatHeads m φ)
    (hg : ConLeche.strLitSupported env = true) {d : Nat} {s : String}
    {ea : AnnotTerm}
    (hea : denoteMeta m.acval env φ d (.lit (.strVal s)) = some ea)
    (ρ : Nat → V) :
    WellDenotedV V ρ ea ∧
      interp V ρ ea ∈ˢ
        interp V ρ (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    hTS, hTH, ⟨mbO, hTO⟩, ⟨mbL, hTL⟩, ⟨mbN, hTN⟩,
    ⟨mb1, mb2, mb3, hTC⟩, ⟨mbF, hTF⟩⟩ :=
    ConLeche.strLitSupported_inv hg
  obtain ⟨cvNat, capsNat, cv0, i0, j0, cv1, i1, j1, hfNat, hfZ, hfSc,
    hlpNat, hlpZ, hlpSc, hTNat, hTZ, hTSc⟩ :=
    ConLeche.natLitSupported_inv hs
  rw [denoteMeta, if_pos hg] at hea
  obtain rfl := (Option.some.inj hea).symm
  -- the two `List` level-parameter lists, at the reading's spelling
  have hlpAtN : levelParamsAt env ConLeche.listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env ConLeche.listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  -- every leaf is closed, graded and bit-valid
  have hleafC : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      interp V σ (m.acval n ψ) = interp V ρ (m.acval n ψ) := fun n ψ σ =>
    interp_closed V (by rw [m.acval_erase]; exact m.cval_closed n ψ) σ ρ
  have hleafOk : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      WellDenotedV V σ (m.acval n ψ) := fun n ψ σ =>
    ⟨m.acval_wellDenoted _ _ σ, hval _ _ σ⟩
  -- the stored types' rows, from the `const` residue
  have head : ∀ (n : Name) (ci : ConstantInfo) (us : List Level)
      (ta : AnnotTerm), env.find? n = some ci → ci.isTowerEntry = false →
      us.length = ci.toConstantVal.levelParams.length →
      denoteMeta m.acval env φ 0
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta →
      (∀ σ : Nat → V, WellDenotedV V σ ta) ∧
        ∀ σ : Nat → V,
          interp V σ (m.acval n
              (Level.substFn φ ci.toConstantVal.levelParams us))
            ∈ˢ interp V σ ta := by
    intro n ci us ta hf hnt hlen hta
    obtain ⟨ta', hta', hok, hmem⟩ := hct 0 n ci us hf hnt hlen
    obtain rfl : ta = ta' := Option.some.inj (hta.symm.trans hta')
    exact ⟨hok, hmem⟩
  -- the shared `.const` readings
  have hKL : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.listName [.zero])
      = some (m.acval ConLeche.listName
          (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) :=
    fun D => denoteMeta_const hfL (by simp [hlpL])
  have hKH : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.charName [])
      = some (m.acval ConLeche.charName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfH (by simp [hlpH]), hlpH]
  have hKNat : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.natName [])
      = some (m.acval ConLeche.natName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfNat
      (by simp [ConstantInfo.toConstantVal, hlpNat])]
    simp only [ConstantInfo.toConstantVal, hlpNat]
  have hKS : ∀ D : Nat, denoteMeta m.acval env φ D
      (.const ConLeche.stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteMeta_const (us := []) hfS (by simp [hlpS]), hlpS]
  -- `Char` is a type in `univ 1`
  have hCharU : interp V ρ
      (m.acval ConLeche.charName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have hIH : ciH.toConstantVal.type.instantiateLevelParams
        ciH.toConstantVal.levelParams []
        = Expr.sort (Level.succ Level.zero) := by
      rw [hlpH, hTH]
      simp [Expr.instantiateLevelParams, Level.subst]
    have hR : denoteMeta m.acval env φ 0
        (ciH.toConstantVal.type.instantiateLevelParams
          ciH.toConstantVal.levelParams []) = some ((.sort 1) : AnnotTerm) := by
      rw [hIH, denoteMeta_sort]
      rfl
    have h := (head _ _ _ _ hfH (ConLeche.isTowerEntry_false_of_find? hfH (fun _ _ h => by simp [ConLeche.charName] at h)) (by simp [hlpH]) hR).2 ρ
    rw [hlpH, interp_sort] at h
    exact h
  -- `List.nil`
  have hIN : ciN.toConstantVal.type.instantiateLevelParams
      ciN.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.app (.const ConLeche.listName [Level.zero]) (.bvar 0))
          ⟨Level.substPW [pN] [Level.zero] mbN.pw⟩ := by
    rw [hlpN, hTN]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRN : denoteMeta m.acval env φ 0
      (ciN.toConstantVal.type.instantiateLevelParams
        ciN.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pN] [Level.zero] mbN.pw))
          (.sort 1)
          (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (.bvar 0))) : AnnotTerm) := by
    rw [hIN, denoteMeta_forallE, denoteMeta_sort,
      show (Expr.app (.const ConLeche.listName [Level.zero]) (.bvar 0)).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteMeta_app, hKL, denoteMeta_fvar]
    rfl
  obtain ⟨hokRN, hmemRN⟩ := head _ _ _ _ hfN (ConLeche.isTowerEntry_false_of_find? hfN (fun _ _ h => by simp [ConLeche.listNilName] at h)) (by simp [hlpN]) hRN
  -- `List.cons`
  have hIC : ciC.toConstantVal.type.instantiateLevelParams
      ciC.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩)
          ⟨Level.substPW [pC] [Level.zero] mb1.pw⟩ := by
    rw [hlpC, hTC]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRC : denoteMeta m.acval env φ 0
      (ciC.toConstantVal.type.instantiateLevelParams
        ciC.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb1.pw))
          (.sort 1)
          (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb2.pw)) (.bvar 0)
            (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb3.pw))
              (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 1))
              (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 2))))) : AnnotTerm) := by
    rw [hIC, denoteMeta_forallE, denoteMeta_sort,
      show (Expr.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.forallE (.fvar 0 (Expr.sort (Level.succ Level.zero)))
            (.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩ from rfl,
      denoteMeta_forallE, denoteMeta_fvar,
      show (Expr.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩).instantiate1
          (.fvar (0 + 1) (.fvar 0 (Expr.sort (Level.succ Level.zero))))
        = Expr.forallE
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩ from rfl,
      denoteMeta_forallE, denoteMeta_app, hKL, denoteMeta_fvar,
      show (Expr.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))).instantiate1
          (.fvar (0 + 1 + 1)
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteMeta_app, hKL, denoteMeta_fvar]
    rfl
  obtain ⟨hokRC, hmemRC⟩ := head _ _ _ _ hfC (ConLeche.isTowerEntry_false_of_find? hfC (fun _ _ h => by simp [ConLeche.listConsName] at h)) (by simp [hlpC]) hRC
  -- `Char.ofNat`
  have hIF : ciF.toConstantVal.type.instantiateLevelParams
      ciF.toConstantVal.levelParams []
      = Expr.forallE (.const ConLeche.natName []) (.const ConLeche.charName [])
          ⟨Level.substPW [] [] mbF.pw⟩ := by
    rw [hlpF, hTF]
    simp [Expr.instantiateLevelParams]
  have hRF : denoteMeta m.acval env φ 0
      (ciF.toConstantVal.type.instantiateLevelParams
        ciF.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbF.pw))
          (m.acval ConLeche.natName (Level.substFn φ [] []))
          (m.acval ConLeche.charName (Level.substFn φ [] []))) : AnnotTerm) := by
    rw [hIF, denoteMeta_forallE, hKNat,
      show (Expr.const ConLeche.charName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.const ConLeche.natName []))
        = Expr.const ConLeche.charName [] from rfl, hKH]
    rfl
  obtain ⟨hokRF, hmemRF⟩ := head _ _ _ _ hfF (ConLeche.isTowerEntry_false_of_find? hfF (fun _ _ h => by simp [ConLeche.charOfNatName] at h)) (by simp [hlpF]) hRF
  -- `String.ofList`
  have hIO : ciO.toConstantVal.type.instantiateLevelParams
      ciO.toConstantVal.levelParams []
      = Expr.forallE
          (.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName []))
          (.const ConLeche.stringName [])
          ⟨Level.substPW [] [] mbO.pw⟩ := by
    rw [hlpO, hTO]
    simp [Expr.instantiateLevelParams, Level.subst]
  have hRO : denoteMeta m.acval env φ 0
      (ciO.toConstantVal.type.instantiateLevelParams
        ciO.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbO.pw))
          (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (m.acval ConLeche.charName (Level.substFn φ [] [])))
          (m.acval ConLeche.stringName
            (Level.substFn φ [] []))) : AnnotTerm) := by
    rw [hIO, denoteMeta_forallE, denoteMeta_app, hKL, hKH,
      show (Expr.const ConLeche.stringName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName [])))
        = Expr.const ConLeche.stringName [] from rfl, hKS]
    rfl
  obtain ⟨hokRO, hmemRO⟩ := head _ _ _ _ hfO (ConLeche.isTowerEntry_false_of_find? hfO (fun _ _ h => by simp [ConLeche.stringOfListName] at h)) (by simp [hlpO]) hRO
  -- the numeral heads
  obtain ⟨hz, hsucc⟩ := hnh hs ρ
  -- the chain
  obtain ⟨hclA, hclm⟩ :=
    charList_facts (V := V) (ρ := ρ)
      (KL := m.acval ConLeche.listName
        (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
      (KH := m.acval ConLeche.charName (Level.substFn φ [] []))
      (KN := m.acval ConLeche.listNilName
        (Level.substFn φ (levelParamsAt env ConLeche.listNilName) [Level.zero]))
      (KC := m.acval ConLeche.listConsName
        (Level.substFn φ (levelParamsAt env ConLeche.listConsName) [Level.zero]))
      (KF := m.acval ConLeche.charOfNatName (Level.substFn φ [] []))
      (Kz := m.acval ConLeche.natZeroName (Level.substFn φ [] []))
      (Ks := m.acval ConLeche.natSuccName (Level.substFn φ [] []))
      (KNat := m.acval ConLeche.natName (Level.substFn φ [] []))
      (fun σ => hleafC _ _ σ) (fun σ => hleafC _ _ σ)
      (hleafOk _ _ ρ) (hleafOk _ _ ρ) (hleafOk _ _ ρ) (hleafOk _ _ ρ)
      (hleafOk _ _ ρ) (hleafOk _ _ ρ) hCharU
      (hokRN ρ) (by rw [hlpAtN]; exact hmemRN ρ)
      (hokRC ρ) (by rw [hlpAtC]; exact hmemRC ρ)
      (hokRF ρ) (by
        have := hmemRF ρ
        rwa [hlpF] at this)
      hz hsucc s.toList
  -- the outer `String.ofList` application
  have h := wellDenotedV_mkAppN_of_fit (V := V) (ρ := ρ)
    [charListAV
      (.app (m.acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName) [.zero]))
        (m.acval ConLeche.charName (Level.substFn φ [] [])))
      (.app (m.acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName) [.zero]))
        (m.acval ConLeche.charName (Level.substFn φ [] [])))
      (m.acval ConLeche.charOfNatName (Level.substFn φ [] []))
      (m.acval ConLeche.natZeroName (Level.substFn φ [] []))
      (m.acval ConLeche.natSuccName (Level.substFn φ [] []))
      s.toList]
    (hokRO ρ) (hleafOk _ _ ρ)
    (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hclA)
    (by
      have := hmemRO ρ
      rwa [hlpO] at this)
    (TeleFit.cons (by rw [interp_app]; exact hclm) TeleFit.nil)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [hleafC ConLeche.stringName (Level.substFn φ [] []) _] at h2

/-! ## The row -/

/-- **`InferStrLitStep`, discharged.**  The returned type is
`.const stringName []`, whose reading the support guard pins to the
`String` leaf itself — so identifying `ta` is the `denoteMeta` `const`
clause and nothing more, exactly as at the numeral clause. -/
theorem inferStrLitStep_of_claims {m : EnvModel V env}
    (hct : ConstType m φ) (hval : AcvalValid m) (hnh : NatHeads m φ) :
    InferStrLitStep m μ φ fuel := by
  intro d s t Δa ea ta h hea hta
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody, pure,
    Except.pure] at h
  split at h
  · next hgb =>
    simp only [Except.ok.injEq] at h
    subst h
    have hg : ConLeche.strLitSupported env = true := by simpa using hgb
    obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, -,
      -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
      ConLeche.strLitSupported_inv hg
    have hta' : ta = m.acval ConLeche.stringName (Level.substFn φ [] []) := by
      have hc := denoteMeta_const (acval := m.acval) (φ := φ) (d := d)
        (us := []) hfS (by simp [hlpS])
      rw [hlpS] at hc
      rw [hc] at hta
      exact (Option.some.inj hta).symm
    subst hta'
    exact ⟨fun ρ _ => (strLitFacts hct hval hnh hg hea ρ).1,
      fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩,
      fun ρ _ => (strLitFacts hct hval hnh hg hea ρ).2⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end ConLeche.Model
