module

-- `RedSoundKit` is the SHARED kit: `DenoteSpine`'s list algebra,
-- `denote_mkAppN(_inv)`, `denote_proj_inv`,
-- `teleFit_nil_inv` and the tower entry's reading live there
public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Semantics.Hoist
import ConLeche.Semantics.LitStep
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.WellDenotedTransport

public section

/-!
# The inference kit (task #305)

The pieces the inference rules' soundness needs:

* `wellDenoted_mkAppN_of_fit` — the fit-to-application kit the
  string chain rides (`teleFit_nil_inv`, the spine inversion and the
  entry-kind inversion come from `RedSoundKit.lean`);
* `charList_facts` and `strLitFacts` — the `String`-literal clause's
  whole content, stated over `RulesInputs`' fields
  (`ConstType`/`NatHeads`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The `WellDenoted` splitters

The consumption motive's entry into every non-leaf clause: the io
grade's premise splits hereditarily into the parts' gradings, and at
an application into the **hereditary app slot** the io claim reads.
-/

/-- The `WellDenoted` ∀-splitter, the domain a graded type. -/
theorem _root_.ConLeche.Semantics.WellDenoted.hoist_piTy {Δa : List Term} {A B : Term}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) :=
  ⟨fun ρ hρ => ⟨(Semantics.WellDenoted.hoist_pi (V := V) h).1 ρ hρ,
      (cast (WellDenoted_pi V ρ A B) (h ρ hρ)).2.1⟩,
    (Semantics.WellDenoted.hoist_pi (V := V) h).2⟩

/-! ## The fit-to-application kit -/

theorem wellDenoted_mkAppN_of_fit {ρ : Nat → V} :
    ∀ (vs : List Term) {Ta f : Term} {σ : Nat → V} {rest : V},
      WellDenoted V σ Ta → WellDenoted V ρ f →
      (∀ x ∈ vs, WellDenoted V ρ x) →
      interp V ρ f ∈ˢ interp V σ Ta →
      TeleFit V σ Ta (vs.map (interp V ρ)) rest →
      WellDenoted V ρ (Term.mkAppN f vs) ∧
        interp V ρ (Term.mkAppN f vs) ∈ˢ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f σ rest _ hf _ hmem hfit
    obtain rfl : rest = interp V σ Ta := teleFit_nil_inv hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f σ rest hokT hf hoks hmem hfit
    simp only [List.map_cons] at hfit
    cases hfit with
    | @cons _ A B _ _ _ hx hfit' =>
      have hpi := cast (WellDenoted_pi V σ A B) hokT
      have hokB : ∀ y, y ∈ˢ interp V σ A → WellDenoted V (cons y σ) B :=
        fun y hy => hpi.2.2.1 y hy
      rw [interp_pi] at hmem
      have hokx : WellDenoted V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenoted V ρ (.app f x) := by
        rw [WellDenoted_app]
        exact ⟨hf, hokx, _, interp V σ A,
          (fun y => interp V (cons y σ) B), hmem, hx, propN_eq_zero.mp,
          fun _ => hpi.2.1⟩
      have hmem' : interp V ρ (.app f x)
          ∈ˢ interp V (cons (interp V ρ x) σ) B := by
        rw [interp_app]
        exact app_mem_piV hmem hx
      -- (`mkAppN f (x :: xs) = mkAppN (.app f x) xs` is definitional)
      exact ih (hokB _ hx) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-! ## The character-list chain -/

/-- **The character-list facts** — `natLit_factsAV`'s companion.  Every
`denote` character list is graded and inhabits `List Char`'s reading,
by induction on the list from the `nil`/`cons`/`Char.ofNat` head
packages and the two numeral heads. -/
theorem charList_facts {ρ : Nat → V}
    {KL KH KN KC KF Kz Ks KNat : Term}
    (hclL : ∀ σ : Nat → V, interp V σ KL = interp V ρ KL)
    (hclH : ∀ σ : Nat → V, interp V σ KH = interp V ρ KH)
    (hokKH : WellDenoted V ρ KH) (hokKN : WellDenoted V ρ KN)
    (hokKC : WellDenoted V ρ KC) (hokKF : WellDenoted V ρ KF)
    (hokKz : WellDenoted V ρ Kz) (hokKs : WellDenoted V ρ Ks)
    (hCharU : interp V ρ KH ∈ˢ (univ 1 : V))
    (hokTN : WellDenoted V ρ
      ((.pi (.sort 1) (.app KL (.bvar 0))) : Term))
    (hmemN : interp V ρ KN ∈ˢ interp V ρ
      ((.pi (.sort 1) (.app KL (.bvar 0))) : Term))
    (hokTC : WellDenoted V ρ
      ((.pi (.sort 1) (.pi (.bvar 0)
        (.pi (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : Term))
    (hmemC : interp V ρ KC ∈ˢ interp V ρ
      ((.pi (.sort 1) (.pi (.bvar 0)
        (.pi (.app KL (.bvar 1)) (.app KL (.bvar 2))))) : Term))
    (hokTF : WellDenoted V ρ ((.pi KNat KH) : Term))
    (hmemF : interp V ρ KF ∈ˢ interp V ρ
      ((.pi KNat KH) : Term))
    (hz : interp V ρ Kz ∈ˢ interp V ρ KNat)
    (hsucc : interp V ρ Ks
      ∈ˢ piR 1 (interp V ρ KNat) fun _ => interp V ρ KNat) :
    ∀ cs : List Char,
      WellDenoted V ρ (charListT (.app KN KH) (.app KC KH) KF Kz Ks cs) ∧
        interp V ρ (charListT (.app KN KH) (.app KC KH) KF Kz Ks cs)
          ∈ˢ interp V ρ ((.app KL KH) : Term) := by
  -- the sort domain, at the reading's own spelling
  have hCharS : interp V ρ KH ∈ˢ interp V ρ ((.sort 1) : Term) := by
    rw [interp_sort]; exact hCharU
  -- one character element: `Char.ofNat` applied to a numeral
  have helem : ∀ c : Char,
      WellDenoted V ρ ((.app KF (natLitT Kz Ks c.toNat)) : Term) ∧
        interp V ρ ((.app KF (natLitT Kz Ks c.toNat)) : Term)
          ∈ˢ interp V ρ KH := by
    intro c
    have hNatTy : IsTy (interp V ρ KNat) := (cast (WellDenoted_pi V ρ KNat KH) hokTF).2.1
    have hnat := natLit_factsAV hokKz hokKs hz hsucc hNatTy c.toNat
    have hokNum : WellDenoted V ρ (natLitT Kz Ks c.toNat) := hnat.1
    have h := wellDenoted_mkAppN_of_fit (V := V) (ρ := ρ)
      [natLitT Kz Ks c.toNat] hokTF hokKF
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hokNum)
      hmemF (TeleFit.cons hnat.2 TeleFit.nil)
    refine ⟨h.1, ?_⟩
    have := h.2
    rwa [hclH (cons (interp V ρ (natLitT Kz Ks c.toNat)) ρ)] at this
  -- the walk
  intro cs
  induction cs with
  | nil =>
    have h := wellDenoted_mkAppN_of_fit (V := V) (ρ := ρ) [KH] hokTN hokKN
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
    have hm2 : interp V ρ ((.app KF (natLitT Kz Ks c.toNat)) : Term)
        ∈ˢ interp V (cons (interp V ρ KH) ρ) ((.bvar 0) : Term) := hem
    have hm3 : interp V ρ
          (charListT (.app KN KH) (.app KC KH) KF Kz Ks cs)
        ∈ˢ interp V
          (cons (interp V ρ ((.app KF (natLitT Kz Ks c.toNat)) : Term))
            (cons (interp V ρ KH) ρ))
          ((.app KL (.bvar 1)) : Term) := by
      have hi := ihm
      rw [interp_app] at hi
      rw [interp_app, hclL _]
      exact hi
    have h := wellDenoted_mkAppN_of_fit (V := V) (ρ := ρ)
      [KH, .app KF (natLitT Kz Ks c.toNat),
        charListT (.app KN KH) (.app KC KH) KF Kz Ks cs]
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
types.  Note what is *absent*: `List`'s own membership and
hand-built type gradings — the P residue delivers a stored type's grading with its reading, so
the only environment facts consumed are the four memberships and
`Char`'s universe membership. -/

/-- **The string chain, at the environment**, at the
`denote` currency. -/
theorem strLitFacts {m : EnvModel V env} (hct : ConstType m φ)
    (hnh : NatHeads m φ)
    (hg : ConLeche.strLitSupported env = true) {d : Nat} {s : String}
    {ea : Term}
    (hea : denote m.acval env φ d (.lit (.strVal s)) = some ea)
    (ρ : Nat → V) :
    WellDenoted V ρ ea ∧
      interp V ρ ea ∈ˢ
        interp V ρ (m.acval ConLeche.stringName (Level.substFn φ [] [])) ∧
      IsTy (interp V ρ (m.acval ConLeche.stringName (Level.substFn φ [] []))) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    hTS, hTH, hTO, hTL, hTN, hTC, hTF⟩ :=
    ConLeche.strLitSupported_inv hg
  obtain ⟨cvNat, capsNat, cv0, i0, j0, cv1, i1, j1, hfNat, hfZ, hfSc,
    hlpNat, hlpZ, hlpSc, hTNat, hTZ, hTSc⟩ :=
    ConLeche.natLitSupported_inv hs
  rw [denote, ite_eq_left hg] at hea
  obtain rfl := (Option.some.inj hea).symm
  -- the two `List` level-parameter lists, at the reading's spelling
  have hlpAtN : levelParamsAt env ConLeche.listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env ConLeche.listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  -- every leaf is closed and graded
  have hleafC : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      interp V σ (m.acval n ψ) = interp V ρ (m.acval n ψ) := fun n ψ σ =>
    interp_closed V (by exact m.cval_closed n ψ) σ ρ
  have hleafOk : ∀ (n : Name) (ψ : Name → Nat) (σ : Nat → V),
      WellDenoted V σ (m.acval n ψ) := fun n ψ σ =>
    (m.acval_wellDenoted _ _ σ)
  -- the stored types' rows, from the `const` residue
  have head : ∀ (n : Name) (ci : ConstantInfo) (us : List Level)
      (ta : Term), env.find? n = some ci →
      us.length = ci.toConstantVal.levelParams.length →
      denote m.acval env φ 0
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta →
      (∀ σ : Nat → V, WellDenoted V σ ta) ∧
        ∀ σ : Nat → V,
          interp V σ (m.acval n
              (Level.substFn φ ci.toConstantVal.levelParams us))
            ∈ˢ interp V σ ta := by
    intro n ci us ta hf hlen hta
    obtain ⟨ta', hta', hok, hmem⟩ := hct 0 n ci us hf hlen
    obtain rfl : ta = ta' := Option.some.inj (hta.symm.trans hta')
    exact ⟨fun σ => (hok σ).1, hmem⟩
  -- the shared `.const` readings
  have hKL : ∀ D : Nat, denote m.acval env φ D
      (.const ConLeche.listName [.zero])
      = some (m.acval ConLeche.listName
          (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) :=
    fun D => denote_const hfL (by simp [hlpL])
  have hKH : ∀ D : Nat, denote m.acval env φ D
      (.const ConLeche.charName [])
      = some (m.acval ConLeche.charName (Level.substFn φ [] [])) := by
    intro D
    rw [denote_const (us := []) hfH (by simp [hlpH]), hlpH]
  have hKNat : ∀ D : Nat, denote m.acval env φ D
      (.const ConLeche.natName [])
      = some (m.acval ConLeche.natName (Level.substFn φ [] [])) := by
    intro D
    rw [denote_const (us := []) hfNat
      (by simp [ConstantInfo.toConstantVal, hlpNat])]
    simp only [ConstantInfo.toConstantVal, hlpNat]
  have hKS : ∀ D : Nat, denote m.acval env φ D
      (.const ConLeche.stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    intro D
    rw [denote_const (us := []) hfS (by simp [hlpS]), hlpS]
  -- `Char` is a type in `univ 1`
  have hCharU : interp V ρ
      (m.acval ConLeche.charName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have hIH : ciH.toConstantVal.type.instantiateLevelParams
        ciH.toConstantVal.levelParams []
        = Expr.sort (Level.succ Level.zero) := by
      rw [hlpH, hTH]
      simp [Expr.instantiateLevelParams, Level.subst]
    have hR : denote m.acval env φ 0
        (ciH.toConstantVal.type.instantiateLevelParams
          ciH.toConstantVal.levelParams []) = some ((.sort 1) : Term) := by
      rw [hIH, denote_sort]
      rfl
    have h := (head _ _ _ _ hfH (by simp [hlpH]) hR).2 ρ
    rw [hlpH, interp_sort] at h
    exact h
  -- `String` is a type in `univ 1`
  have hStringU : interp V ρ
      (m.acval ConLeche.stringName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have hIS : ciS.toConstantVal.type.instantiateLevelParams
        ciS.toConstantVal.levelParams []
        = Expr.sort (Level.succ Level.zero) := by
      rw [hlpS, hTS]
      simp [Expr.instantiateLevelParams, Level.subst]
    have hR : denote m.acval env φ 0
        (ciS.toConstantVal.type.instantiateLevelParams
          ciS.toConstantVal.levelParams []) = some ((.sort 1) : Term) := by
      rw [hIS, denote_sort]
      rfl
    have h := (head _ _ _ _ hfS (by simp [hlpS]) hR).2 ρ
    rw [hlpS, interp_sort] at h
    exact h
  -- `List.nil`
  have hIN : ciN.toConstantVal.type.instantiateLevelParams
      ciN.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.app (.const ConLeche.listName [Level.zero]) (.bvar 0)) := by
    rw [hlpN, hTN]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRN : denote m.acval env φ 0
      (ciN.toConstantVal.type.instantiateLevelParams
        ciN.toConstantVal.levelParams [Level.zero])
      = some ((.pi (.sort 1)
          (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (.bvar 0))) : Term) := by
    rw [hIN, denote_forallE, denote_sort,
      show (Expr.app (.const ConLeche.listName [Level.zero]) (.bvar 0)).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denote_app, hKL, denote_fvar]
    rfl
  obtain ⟨hokRN, hmemRN⟩ := head _ _ _ _ hfN (by simp [hlpN]) hRN
  -- `List.cons`
  have hIC : ciC.toConstantVal.type.instantiateLevelParams
      ciC.toConstantVal.levelParams [Level.zero]
      = Expr.forallE (.sort (Level.succ Level.zero))
          (.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2)))) := by
    rw [hlpC, hTC]
    simp [Expr.instantiateLevelParams, Level.subst, Level.subst.go]
  have hRC : denote m.acval env φ 0
      (ciC.toConstantVal.type.instantiateLevelParams
        ciC.toConstantVal.levelParams [Level.zero])
      = some ((.pi (.sort 1)
          (.pi (.bvar 0)
            (.pi (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 1))
              (.app (m.acval ConLeche.listName
                (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
                (.bvar 2))))) : Term) := by
    rw [hIC, denote_forallE, denote_sort,
      show (Expr.forallE (.bvar 0)
            (.forallE (.app (.const ConLeche.listName [Level.zero]) (.bvar 1))
              (.app (.const ConLeche.listName [Level.zero]) (.bvar 2)))).instantiate1
          (.fvar 0 (Expr.sort (Level.succ Level.zero)))
        = Expr.forallE (.fvar 0 (Expr.sort (Level.succ Level.zero)))
            (.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))) from rfl,
      denote_forallE, denote_fvar,
      show (Expr.forallE
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))
              (.app (.const ConLeche.listName [Level.zero])
                (.fvar 0 (Expr.sort (Level.succ Level.zero))))).instantiate1
          (.fvar (0 + 1) (.fvar 0 (Expr.sort (Level.succ Level.zero))))
        = Expr.forallE
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero))))
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))) from rfl,
      denote_forallE, denote_app, hKL, denote_fvar,
      show (Expr.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))).instantiate1
          (.fvar (0 + 1 + 1)
            (.app (.const ConLeche.listName [Level.zero])
              (.fvar 0 (Expr.sort (Level.succ Level.zero)))))
        = Expr.app (.const ConLeche.listName [Level.zero])
            (.fvar 0 (Expr.sort (Level.succ Level.zero))) from rfl,
      denote_app, hKL, denote_fvar]
    rfl
  obtain ⟨hokRC, hmemRC⟩ := head _ _ _ _ hfC (by simp [hlpC]) hRC
  -- `Char.ofNat`
  have hIF : ciF.toConstantVal.type.instantiateLevelParams
      ciF.toConstantVal.levelParams []
      = Expr.forallE (.const ConLeche.natName []) (.const ConLeche.charName []) := by
    rw [hlpF, hTF]
    simp [Expr.instantiateLevelParams]
  have hRF : denote m.acval env φ 0
      (ciF.toConstantVal.type.instantiateLevelParams
        ciF.toConstantVal.levelParams [])
      = some ((.pi (m.acval ConLeche.natName (Level.substFn φ [] []))
          (m.acval ConLeche.charName (Level.substFn φ [] []))) : Term) := by
    rw [hIF, denote_forallE, hKNat,
      show (Expr.const ConLeche.charName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.const ConLeche.natName []))
        = Expr.const ConLeche.charName [] from rfl, hKH]
    rfl
  obtain ⟨hokRF, hmemRF⟩ := head _ _ _ _ hfF (by simp [hlpF]) hRF
  -- `String.ofList`
  have hIO : ciO.toConstantVal.type.instantiateLevelParams
      ciO.toConstantVal.levelParams []
      = Expr.forallE
          (.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName []))
          (.const ConLeche.stringName []) := by
    rw [hlpO, hTO]
    simp [Expr.instantiateLevelParams, Level.subst]
  have hRO : denote m.acval env φ 0
      (ciO.toConstantVal.type.instantiateLevelParams
        ciO.toConstantVal.levelParams [])
      = some ((.pi (.app (m.acval ConLeche.listName
            (Level.substFn φ ciL.toConstantVal.levelParams [Level.zero]))
            (m.acval ConLeche.charName (Level.substFn φ [] [])))
          (m.acval ConLeche.stringName
            (Level.substFn φ [] []))) : Term) := by
    rw [hIO, denote_forallE, denote_app, hKL, hKH,
      show (Expr.const ConLeche.stringName ([] : List Level)).instantiate1
          (.fvar 0 (Expr.app (.const ConLeche.listName [Level.zero])
            (.const ConLeche.charName [])))
        = Expr.const ConLeche.stringName [] from rfl, hKS]
    rfl
  obtain ⟨hokRO, hmemRO⟩ := head _ _ _ _ hfO (by simp [hlpO]) hRO
  -- the numeral heads
  obtain ⟨hz, hsucc, -⟩ := hnh hs ρ
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
  have h := wellDenoted_mkAppN_of_fit (V := V) (ρ := ρ)
    [charListT
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
  refine ⟨h.1, ?_, IsTy_of_mem_univ hStringU⟩
  have h2 := h.2
  rwa [hleafC ConLeche.stringName (Level.substFn φ [] []) _] at h2

/-! ## The tower-entry kit

The `.proj` rule's reading walk: the spine inversion,
the entry-kind inversion, and the fit-free residual — the checker's
`instPisAt` peel of the stored entry type reads to the syntactic peel
of its reading.  The spine relation and its algebra are
`Verify/Denote/Lemmas.lean`'s `DenoteSpine`. -/

/-- **The checker's `instPisAt` peel reads to the syntactic peel of
the type's reading** — the fit's residual (`TeleFitPA.peelPis`)
without the fit: the two
walks step in lockstep (`body.instantiate1 a` against `B.inst a`), and
the per-step content is `denote_beta`, once. -/
theorem denote_instPisAt_peel
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {ds : List Expr} {Ta : Term}
      {vs : List Term},
      Expr.instPisAt args ty = some (ds, rest) →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denote acval env φ d ty = some Ta →
      DenoteSpine acval env φ d args vs →
      ∃ restA, denote acval env φ d rest = some restA ∧
        Term.peelPis Ta vs = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest ds Ta vs hpr _ _ hty hsp
    obtain ⟨-, rfl⟩ : ds = [] ∧ rest = ty := by
      simpa [Expr.instPisAt] using hpr.symm
    cases hsp
    exact ⟨Ta, hty, rfl⟩
  | cons a as ih =>
    intro ty rest ds Ta vs hpr hwty hargs hty hsp
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body, hpr, hwty, hty => ?_
    -- the peel's own step
    simp only [Expr.instPisAt, Option.map_eq_some_iff] at hpr
    obtain ⟨⟨ds', rest'⟩, hpr', heq⟩ := hpr
    obtain ⟨-, rfl⟩ : dom :: ds' = ds ∧ rest' = rest := by
      simpa using heq
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hty
    have hbody' : denote acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denote_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    obtain ⟨restA, hrestA, hpeel⟩ := ih hpr'
      (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hbody' hsp'
    exact ⟨restA, hrestA, hpeel⟩

/-- **The checker's projection type reads as the telescope's peel**
(task #175 S1): `ProjEntry.typeAt` is the `instPisAt` peel of the body
telescope along the arguments and the subject, so its reading is the
syntactic peel of the telescope's reading along the readings. -/
theorem denote_typeAt_peel {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : Term} {d : Nat}
    (hTa : denote m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta)
    {targs : List Expr} {pe : Expr} (hlen : targs.length = entry.numParams)
    (hframes : ∀ a ∈ targs ++ [pe], Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    {vs : List Term}
    (hsp : DenoteSpine m.acval env φ d (targs ++ [pe]) vs) :
    ∃ restA, denote m.acval env φ d (entry.typeAt us targs pe) = some restA ∧
      Term.peelPis Ta vs = some restA := by
  obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
  exact denote_instPisAt_peel m.acval_closed (acval_inst_self m) (targs ++ [pe])
    (ConLeche.instPisAt_typeAt entry us hlen pe)
    (Expr.WScoped.of_not_hasFvar (towerEntry_tele_closed m.wf hfe us).1)
    hframes (hTad d) hsp

end ConLeche.Model.Rules
