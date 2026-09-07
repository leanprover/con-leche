import Lech.SetP.Step2.CapsRowsP

/-!
# The `String`-literal inference row (task #161, PROJ/STR install tier)

`InferStrLitStepP` (`Step2/InferP.lean`), discharged.  The v1 mirror is
`Sound/Lit.lean`'s `strLit_facts`/`sndInfLitStr`; the transposition is
shorter, and for one structural reason:

* v1 walks `henv.mem_type` at each of the seven support constants and
  then **builds the `AnnotOkV` of every one of those types by hand**
  (`hnilOk`, `hconsOk`, `hofOk`, `hOFOk` — four bespoke `AnnotOkV_pi`
  towers, each with its own domain-membership side conditions).  The P
  currency's `ConstTypeP` residue delivers a stored type's reading
  **together with its grading**, so all four disappear: what remains is
  the walk itself.
* the fits are `TeleFitP`, whose cons peels under `cons a ρ` instead of
  substituting, so the `VExpr.inst_eq_self_of_closed` bookkeeping that
  dominates the v1 proof is replaced by three leaf-closedness
  equations (`interp2_closed` at the `acval` leaves).

**No bit positivity is used anywhere** (`NatEqsP.lean`'s finding): the
memberships ride `annotOkP_mkAppN_of_fit`, whose `v = 0` fibre premise
comes from the type reading's own `AnnotValidV`.

The chain lemma is stated over the five head packages as *explicit
arguments*, exactly as `natLit_facts2` (`Step2/Lit.lean`) is stated
over the two numeral heads and for the same reason: the head facts are
one `ConstTypeP` chain, the same for every literal, and factoring them
out keeps the character induction free of the guard's inversion
plumbing.

## Why `Step2/StrLit.lean`'s `charList_facts2` is not reused

The denote2-lane chain (`charList_facts2`, `strLit_facts2`) takes its
head memberships at `piR 1 …` — the regime bit **fixed at 1**, on the
argument that `Char`/`List Char`/`String`/`Nat` are all `Type`-level.
That argument is unavailable at the P currency: `denoteP` reads the
*stored* bit `pwBit φ mb.pw` off the annotated binder, and nothing in
`strLitSupported` pins it.  The rows below therefore keep the bits
abstract and pay for it with `TeleFitP`/`annotOkP_mkAppN_of_fit`,
whose `v = 0` fibre premises come from the type reading's own
`AnnotValidV`.  The two chains are the same walk at two currencies;
neither subsumes the other.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The character-list chain -/

/-- **The character-list facts** — `natLit_facts2`'s companion.  Every
`denoteP` character list is graded and inhabits `List Char`'s reading,
by induction on the list from the `nil`/`cons`/`Char.ofNat` head
packages and the two numeral heads. -/
theorem charList_factsP {ρ : Nat → V}
    {KL KH KN KC KF Kz Ks KNat : AVExpr} {bN b1 b2 b3 bF : Nat}
    (hclL : ∀ σ : Nat → V, interp2 V σ KL = interp2 V ρ KL)
    (hclH : ∀ σ : Nat → V, interp2 V σ KH = interp2 V ρ KH)
    (hokKH : AnnotOkP V ρ KH) (hokKN : AnnotOkP V ρ KN)
    (hokKC : AnnotOkP V ρ KC) (hokKF : AnnotOkP V ρ KF)
    (hokKz : AnnotOkP V ρ Kz) (hokKs : AnnotOkP V ρ Ks)
    (hCharU : interp2 V ρ KH ∈ˢ (univ 1 : V))
    (hokTN : AnnotOkP V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AVExpr))
    (hmemN : interp2 V ρ KN ∈ˢ interp2 V ρ
      ((.pi 0 bN (.sort 1) (.app KL (.bvar 0))) : AVExpr))
    (hokTC : AnnotOkP V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AVExpr))
    (hmemC : interp2 V ρ KC ∈ˢ interp2 V ρ
      ((.pi 0 b1 (.sort 1) (.pi 0 b2 (.bvar 0)
        (.pi 0 b3 (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : AVExpr))
    (hokTF : AnnotOkP V ρ ((.pi 0 bF KNat KH) : AVExpr))
    (hmemF : interp2 V ρ KF ∈ˢ interp2 V ρ
      ((.pi 0 bF KNat KH) : AVExpr))
    (hz : interp2 V ρ Kz ∈ˢ interp2 V ρ KNat)
    (hsucc : interp2 V ρ Ks
      ∈ˢ piR 1 (interp2 V ρ KNat) fun _ => interp2 V ρ KNat) :
    ∀ cs : List Char,
      AnnotOkP V ρ (charListT2 (.app KN KH) (.app KC KH) KF Kz Ks cs) ∧
        interp2 V ρ (charListT2 (.app KN KH) (.app KC KH) KF Kz Ks cs)
          ∈ˢ interp2 V ρ ((.app KL KH) : AVExpr) := by
  -- the sort domain, at the reading's own spelling
  have hCharS : interp2 V ρ KH ∈ˢ interp2 V ρ ((.sort 1) : AVExpr) := by
    rw [interp2_sort]; exact hCharU
  -- one character element: `Char.ofNat` applied to a numeral
  have helem : ∀ c : Char,
      AnnotOkP V ρ ((.app KF (natLitT2 Kz Ks c.toNat)) : AVExpr) ∧
        interp2 V ρ ((.app KF (natLitT2 Kz Ks c.toNat)) : AVExpr)
          ∈ˢ interp2 V ρ KH := by
    intro c
    have hnat := natLit_facts2 hokKz.1 hokKs.1 hz hsucc c.toNat
    have hokNum : AnnotOkP V ρ (natLitT2 Kz Ks c.toNat) :=
      ⟨hnat.1, AnnotValidV_natLitT2 hokKz.2 hokKs.2 c.toNat⟩
    have h := annotOkP_mkAppN_of_fit (V := V) (ρ := ρ)
      [natLitT2 Kz Ks c.toNat] hokTF hokKF
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokNum)
      hmemF (TeleFitP.cons hnat.2 TeleFitP.nil)
    refine ⟨h.1, ?_⟩
    have := h.2
    rwa [hclH (cons (interp2 V ρ (natLitT2 Kz Ks c.toNat)) ρ)] at this
  -- the walk
  intro cs
  induction cs with
  | nil =>
    have h := annotOkP_mkAppN_of_fit (V := V) (ρ := ρ) [KH] hokTN hokKN
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokKH)
      hmemN (TeleFitP.cons hCharS TeleFitP.nil)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp2_app, hclL (cons (interp2 V ρ KH) ρ)] at h2
    rw [interp2_app]
    exact h2
  | cons c cs ih =>
    obtain ⟨ihA, ihm⟩ := ih
    obtain ⟨heA, hem⟩ := helem c
    -- the three memberships, at the fit's own environments
    have hm2 : interp2 V ρ ((.app KF (natLitT2 Kz Ks c.toNat)) : AVExpr)
        ∈ˢ interp2 V (cons (interp2 V ρ KH) ρ) ((.bvar 0) : AVExpr) := hem
    have hm3 : interp2 V ρ
          (charListT2 (.app KN KH) (.app KC KH) KF Kz Ks cs)
        ∈ˢ interp2 V
          (cons (interp2 V ρ ((.app KF (natLitT2 Kz Ks c.toNat)) : AVExpr))
            (cons (interp2 V ρ KH) ρ))
          ((.app KL (.bvar 1)) : AVExpr) := by
      have hi := ihm
      rw [interp2_app] at hi
      rw [interp2_app, hclL _]
      exact hi
    have h := annotOkP_mkAppN_of_fit (V := V) (ρ := ρ)
      [KH, .app KF (natLitT2 Kz Ks c.toNat),
        charListT2 (.app KN KH) (.app KC KH) KF Kz Ks cs]
      hokTC hokKC
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hokKH
        · exact heA
        · exact ihA)
      hmemC
      (TeleFitP.cons hCharS (TeleFitP.cons hm2 (TeleFitP.cons hm3
        TeleFitP.nil)))
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [interp2_app, hclL _] at h2
    rw [interp2_app]
    exact h2

/-! ## The chain at the environment

The five head packages, read off `ConstTypeP` at the guard's pinned
types.  Note what is *absent*: `List`'s own membership
(`strLit_facts`' `hListMem`) and the four hand-built type gradings —
the P residue delivers a stored type's grading with its reading, so
the only environment facts consumed are the four memberships and
`Char`'s universe membership. -/

/-- **The string chain, at the environment.**  `strLit_facts`' mirror
at the validated-annotation currency. -/
theorem strLitFactsP {m : EnvS2Core V env} (hct : ConstTypeP m φ)
    (hval : AcvalValidP m) (hnh : NatHeadsP m φ)
    (hg : Lech.strLitSupported env = true) {d : Nat} {s : String}
    {ea : AVExpr}
    (hea : denoteP m.acval env φ d (.lit (.strVal s)) = some ea)
    (ρ : Nat → V) :
    AnnotOkP V ρ ea ∧
      interp2 V ρ ea ∈ˢ
        interp2 V ρ (m.acval Lech.stringName (Level.substFn φ [] [])) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    hTS, hTH, ⟨nmO, mbO, hTO⟩, ⟨nmL, mbL, hTL⟩, ⟨nmN, mbN, hTN⟩,
    ⟨nm1, nm2, nm3, mb1, mb2, mb3, hTC⟩, ⟨nmF, mbF, hTF⟩⟩ :=
    Lech.strLitSupported_inv hg
  obtain ⟨cvNat, capsNat, cv0, i0, j0, cv1, i1, j1, hfNat, hfZ, hfSc,
    hlpNat, hlpZ, hlpSc, hTNat, hTZ, hTSc⟩ :=
    Lech.natLitSupported_inv hs
  rw [denoteP, if_pos hg] at hea
  obtain rfl := (Option.some.inj hea).symm
  -- the two `List` level-parameter lists, at the reading's spelling
  have hlpAtN : levelParamsAt env Lech.listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env Lech.listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  -- every leaf is closed, graded and bit-valid
  have hleafC : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      interp2 V σ (m.acval n ψ) = interp2 V ρ (m.acval n ψ) := fun n ψ σ =>
    interp2_closed V (by rw [m.acval_erase]; exact m.cval_closed n ψ) σ ρ
  have hleafOk : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      AnnotOkP V σ (m.acval n ψ) := fun n ψ σ =>
    ⟨m.acval_ok2 _ _ σ, hval _ _ σ⟩
  -- the stored types' rows, from the `const` residue
  have head : ∀ (n : Name) (ci : ConstantInfo) (us : List Level)
      (ta : AVExpr), env.find? n = some ci → ci.isTowerEntry = false →
      us.length = ci.toConstantVal.levelParams.length →
      denoteP m.acval env φ 0
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta →
      (∀ σ : Nat → V, AnnotOkP V σ ta) ∧
        ∀ σ : Nat → V,
          interp2 V σ (m.acval n
              (Level.substFn φ ci.toConstantVal.levelParams us))
            ∈ˢ interp2 V σ ta := by
    intro n ci us ta hf hnt hlen hta
    obtain ⟨ta', hta', hok, hmem⟩ := hct 0 n ci us hf hnt hlen
    obtain rfl : ta = ta' := Option.some.inj (hta.symm.trans hta')
    exact ⟨hok, hmem⟩
  -- the shared `.const` readings
  have hKL : ∀ D : Nat, denoteP m.acval env φ D
      (.const Lech.listName [.zero])
      = some (m.acval Lech.listName
          (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) :=
    fun D => denoteP_const hfL (by simp [hlpL])
  have hKH : ∀ D : Nat, denoteP m.acval env φ D
      (.const Lech.charName [])
      = some (m.acval Lech.charName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteP_const (us := []) hfH (by simp [hlpH]), hlpH]
  have hKNat : ∀ D : Nat, denoteP m.acval env φ D
      (.const Lech.natName [])
      = some (m.acval Lech.natName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteP_const (us := []) hfNat
      (by simp [ConstantInfo.toConstantVal, hlpNat])]
    simp only [ConstantInfo.toConstantVal, hlpNat]
  have hKS : ∀ D : Nat, denoteP m.acval env φ D
      (.const Lech.stringName [])
      = some (m.acval Lech.stringName (Level.substFn φ [] [])) := by
    intro D
    rw [denoteP_const (us := []) hfS (by simp [hlpS]), hlpS]
  -- `Char` is a type in `univ 1`
  have hCharU : interp2 V ρ
      (m.acval Lech.charName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have hIH : ciH.toConstantVal.type.instantiateLevelParams
        ciH.toConstantVal.levelParams []
        = Expr.sort (Level.succ Level.zero) := by
      rw [hlpH, hTH]
      simp [Expr.instantiateLevelParams, Level.subst]
    have hR : denoteP m.acval env φ 0
        (ciH.toConstantVal.type.instantiateLevelParams
          ciH.toConstantVal.levelParams []) = some ((.sort 1) : AVExpr) := by
      rw [hIH, denoteP_sort]
      rfl
    have h := (head _ _ _ _ hfH (Lech.isTowerEntry_false_of_find? hfH (fun _ _ h => by simp [Lech.charName] at h)) (by simp [hlpH]) hR).2 ρ
    rw [hlpH, interp2_sort] at h
    exact h
  -- `List.nil`
  have hIN : ciN.toConstantVal.type.instantiateLevelParams
      ciN.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.app (.const Lech.listName [Level.zero]) (.bvar 0))
          ⟨Level.substPW [pN] [Level.zero] mbN.pw⟩ := by
    rw [hlpN, hTN]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRN : denoteP m.acval env φ 0
      (ciN.toConstantVal.type.instantiateLevelParams
        ciN.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pN] [Level.zero] mbN.pw))
          (.sort 1)
          (.app (m.acval Lech.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (.bvar 0))) : AVExpr) := by
    rw [hIN, denoteP_forallE, denoteP_sort,
      show (Expr.app (.const Lech.listName [Level.zero]) (.bvar 0)).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.app (.const Lech.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteP_app, hKL, denoteP_fvar]
    rfl
  obtain ⟨hokRN, hmemRN⟩ := head _ _ _ _ hfN (Lech.isTowerEntry_false_of_find? hfN (fun _ _ h => by simp [Lech.listNilName] at h)) (by simp [hlpN]) hRN
  -- `List.cons`
  have hIC : ciC.toConstantVal.type.instantiateLevelParams
      ciC.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.forallE (.bvar 0)
            (.forallE (.app (.const Lech.listName [Level.zero]) (.bvar 1))
              (.app (.const Lech.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩)
          ⟨Level.substPW [pC] [Level.zero] mb1.pw⟩ := by
    rw [hlpC, hTC]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRC : denoteP m.acval env φ 0
      (ciC.toConstantVal.type.instantiateLevelParams
        ciC.toConstantVal.levelParams [Level.zero])
      = some ((.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb1.pw))
          (.sort 1)
          (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb2.pw)) (.bvar 0)
            (.pi 0 (pwBit φ (Level.substPW [pC] [Level.zero] mb3.pw))
              (.app (m.acval Lech.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 1))
              (.app (m.acval Lech.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 2))))) : AVExpr) := by
    rw [hIC, denoteP_forallE, denoteP_sort,
      show (Expr.forallE (.bvar 0)
            (.forallE (.app (.const Lech.listName [Level.zero]) (.bvar 1))
              (.app (.const Lech.listName [Level.zero]) (.bvar 2))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.forallE (.fvar 0 (Expr.sort (Level.succ Level.zero)))
            (.forallE
              (.app (.const Lech.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const Lech.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩)
            ⟨Level.substPW [pC] [Level.zero] mb2.pw⟩ from rfl,
      denoteP_forallE, denoteP_fvar,
      show (Expr.forallE
              (.app (.const Lech.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const Lech.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩).instantiate1
          (.fvar (0 + 1) (.fvar 0 (Expr.sort (Level.succ Level.zero))))
        = Expr.forallE
            (.app (.const Lech.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            (.app (.const Lech.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            ⟨Level.substPW [pC] [Level.zero] mb3.pw⟩ from rfl,
      denoteP_forallE, denoteP_app, hKL, denoteP_fvar,
      show (Expr.app (.const Lech.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))).instantiate1
          (.fvar (0 + 1 + 1)
            (.app (.const Lech.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))))
        = Expr.app (.const Lech.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denoteP_app, hKL, denoteP_fvar]
    rfl
  obtain ⟨hokRC, hmemRC⟩ := head _ _ _ _ hfC (Lech.isTowerEntry_false_of_find? hfC (fun _ _ h => by simp [Lech.listConsName] at h)) (by simp [hlpC]) hRC
  -- `Char.ofNat`
  have hIF : ciF.toConstantVal.type.instantiateLevelParams
      ciF.toConstantVal.levelParams []
      = Expr.forallE (.const Lech.natName []) (.const Lech.charName [])
          ⟨Level.substPW [] [] mbF.pw⟩ := by
    rw [hlpF, hTF]
    simp [Expr.instantiateLevelParams]
  have hRF : denoteP m.acval env φ 0
      (ciF.toConstantVal.type.instantiateLevelParams
        ciF.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbF.pw))
          (m.acval Lech.natName (Level.substFn φ [] []))
          (m.acval Lech.charName (Level.substFn φ [] []))) : AVExpr) := by
    rw [hIF, denoteP_forallE, hKNat,
      show (Expr.const Lech.charName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.const Lech.natName []))
        = Expr.const Lech.charName [] from rfl, hKH]
    rfl
  obtain ⟨hokRF, hmemRF⟩ := head _ _ _ _ hfF (Lech.isTowerEntry_false_of_find? hfF (fun _ _ h => by simp [Lech.charOfNatName] at h)) (by simp [hlpF]) hRF
  -- `String.ofList`
  have hIO : ciO.toConstantVal.type.instantiateLevelParams
      ciO.toConstantVal.levelParams []
      = Expr.forallE
          (.app (.const Lech.listName [Level.zero])
            (.const Lech.charName []))
          (.const Lech.stringName [])
          ⟨Level.substPW [] [] mbO.pw⟩ := by
    rw [hlpO, hTO]
    simp [Expr.instantiateLevelParams, Level.subst]
  have hRO : denoteP m.acval env φ 0
      (ciO.toConstantVal.type.instantiateLevelParams
        ciO.toConstantVal.levelParams [])
      = some ((.pi 0 (pwBit φ (Level.substPW [] [] mbO.pw))
          (.app (m.acval Lech.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (m.acval Lech.charName (Level.substFn φ [] [])))
          (m.acval Lech.stringName
            (Level.substFn φ [] []))) : AVExpr) := by
    rw [hIO, denoteP_forallE, denoteP_app, hKL, hKH,
      show (Expr.const Lech.stringName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.app (.const Lech.listName [Level.zero])
            (.const Lech.charName [])))
        = Expr.const Lech.stringName [] from rfl, hKS]
    rfl
  obtain ⟨hokRO, hmemRO⟩ := head _ _ _ _ hfO (Lech.isTowerEntry_false_of_find? hfO (fun _ _ h => by simp [Lech.stringOfListName] at h)) (by simp [hlpO]) hRO
  -- the numeral heads
  obtain ⟨hz, hsucc⟩ := hnh hs ρ
  -- the chain
  obtain ⟨hclA, hclm⟩ :=
    charList_factsP (V := V) (ρ := ρ)
      (KL := m.acval Lech.listName
        (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
      (KH := m.acval Lech.charName (Level.substFn φ [] []))
      (KN := m.acval Lech.listNilName
        (Level.substFn φ (levelParamsAt env Lech.listNilName) [Level.zero]))
      (KC := m.acval Lech.listConsName
        (Level.substFn φ (levelParamsAt env Lech.listConsName) [Level.zero]))
      (KF := m.acval Lech.charOfNatName (Level.substFn φ [] []))
      (Kz := m.acval Lech.natZeroName (Level.substFn φ [] []))
      (Ks := m.acval Lech.natSuccName (Level.substFn φ [] []))
      (KNat := m.acval Lech.natName (Level.substFn φ [] []))
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
  have h := annotOkP_mkAppN_of_fit (V := V) (ρ := ρ)
    [charListT2
      (.app (m.acval Lech.listNilName
          (Level.substFn φ (levelParamsAt env Lech.listNilName) [.zero]))
        (m.acval Lech.charName (Level.substFn φ [] [])))
      (.app (m.acval Lech.listConsName
          (Level.substFn φ (levelParamsAt env Lech.listConsName) [.zero]))
        (m.acval Lech.charName (Level.substFn φ [] [])))
      (m.acval Lech.charOfNatName (Level.substFn φ [] []))
      (m.acval Lech.natZeroName (Level.substFn φ [] []))
      (m.acval Lech.natSuccName (Level.substFn φ [] []))
      s.toList]
    (hokRO ρ) (hleafOk _ _ ρ)
    (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hclA)
    (by
      have := hmemRO ρ
      rwa [hlpO] at this)
    (TeleFitP.cons (by rw [interp2_app]; exact hclm) TeleFitP.nil)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [hleafC Lech.stringName (Level.substFn φ [] []) _] at h2

/-! ## The row -/

/-- **`InferStrLitStepP`, discharged.**  The returned type is
`.const stringName []`, whose reading the support guard pins to the
`String` leaf itself — so identifying `ta` is the `denoteP` `const`
clause and nothing more, exactly as at the numeral clause. -/
theorem inferStrLitStepP_of_claims {m : EnvS2Core V env}
    (hct : ConstTypeP m φ) (hval : AcvalValidP m) (hnh : NatHeadsP m φ) :
    InferStrLitStepP m μ φ fuel := by
  intro d s t Δa ea ta h hea hta
  rw [Lech.inferTypeCore_succ] at h
  simp only [Lech.inferBody, pure,
    Except.pure] at h
  split at h
  · next hgb =>
    simp only [Except.ok.injEq] at h
    subst h
    have hg : Lech.strLitSupported env = true := by simpa using hgb
    obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, -,
      -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
      Lech.strLitSupported_inv hg
    have hta' : ta = m.acval Lech.stringName (Level.substFn φ [] []) := by
      have hc := denoteP_const (acval := m.acval) (φ := φ) (d := d)
        (us := []) hfS (by simp [hlpS])
      rw [hlpS] at hc
      rw [hc] at hta
      exact (Option.some.inj hta).symm
    subst hta'
    exact ⟨fun ρ _ => (strLitFactsP hct hval hnh hg hea ρ).1,
      fun ρ _ => ⟨m.acval_ok2 _ _ ρ, hval _ _ ρ⟩,
      fun ρ _ => (strLitFactsP hct hval hnh hg hea ρ).2⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end Lech.SetP
