module

public import ConLeche.Model.Sidecar.Shared
import ConLeche.Model.Harvest
import ConLeche.Model.Modular.Proofs
import ConLeche.Verify.Driver.Reach
import ConLeche.Model.Modular.RestrictAgree
public import ConLeche.Model.Levels
import ConLeche.Model.Inductives.RunEnv
import ConLeche.Verify.Cached.DeclNames
import ConLeche.Model.Modular.Valid

public section

/-!
# A justified axiom's step

A justified axiom `cv` of the input is installed with the renamed sidecar model's value at its
name, read at the input's level parameters: the sidecar's constant is `cv` up to those names, and
everything `cv`'s type reads is shared, where the input's model and the sidecar's agree, so the
type reads alike on both sides and the sidecar's value inhabits it (`harvestAxiomAt`).
-/

namespace ConLeche.Model.Sidecar

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify
open ConLeche.Semantics SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The sidecar's constant at the input's statement**: the renamed sidecar's constant of a
justified statement's name reads, at the input's level parameters, as the statement's type. -/
theorem justified_type {Ef : Env} {cv : ConstantVal} {cS : ConstantInfo}
    (hEf : Ef.find? cv.name = some (.axiomInfo cv)) (hn : cS.name = cv.name)
    (hs : sameCvUpToLevels cv cS.toConstantVal = true) :
    (renS Ef cS).toConstantVal.levelParams.length = cv.levelParams.length ∧
    (∀ (a : Name → (Name → Nat) → Term.Term) (S : Env), AcvalParamsAt S a → ∀ ψ,
      denote a S ψ 0 cv.type =
        denote a S (Level.substFn ψ (renS Ef cS).toConstantVal.levelParams
          (cv.levelParams.map Level.param)) 0 (renS Ef cS).toConstantVal.type) ∧
    (Refines (.axiomInfo cv) (renS Ef cS) → (renS Ef cS).toConstantVal = cv) := by
  have hren : renS Ef cS = (if cS.isStmtKind && !reservedBasisNames.contains cS.name &&
        cv.levelParams != cS.toConstantVal.levelParams &&
        levelsRenaming cS.toConstantVal.levelParams cv.levelParams
      then cS.atLps cv.levelParams else cS) := by
    unfold renS; rw [hn, hEf]; rfl
  have hself : ∀ ψ : Name → Nat, Level.substFn ψ cv.levelParams (cv.levelParams.map Level.param) = ψ :=
    fun ψ => Level.substFn_param_self ψ cv.levelParams
  unfold sameCvUpToLevels at hs
  split at hs
  · next he =>
    have hcv := ConstantVal.eq_of_beqP hs
    have hl : cv.levelParams = cS.toConstantVal.levelParams := by simpa using he
    have hr : renS Ef cS = cS := by rw [hren]; simp [hl]
    rw [hr, ← hcv]
    exact ⟨rfl, fun a S _ ψ => by rw [hself], fun _ => rfl⟩
  · next he =>
    simp only [Bool.and_eq_true] at hs
    obtain ⟨hlr, hb⟩ := hs
    obtain ⟨hlen, -, -⟩ := levelsRenaming_spec hlr
    rw [← ConLeche.Cached.ConstantVal.atLps_eq_atLpsC] at hb
    have hcv : cS.toConstantVal.atLps cv.levelParams = cv := ConstantVal.eq_of_beqP hb
    have hne : cv.levelParams ≠ cS.toConstantVal.levelParams := by simpa using he
    have hlr' : levelsRenaming cS.toConstantVal.levelParams cv.levelParams = true := by
      obtain ⟨a, b, c⟩ := levelsRenaming_spec hlr
      simp [levelsRenaming, a, b, c]
    by_cases hc : (cS.isStmtKind && !reservedBasisNames.contains cS.name) = true
    · have hr : renS Ef cS = cS.atLps cv.levelParams := by
        have hcond : (cS.isStmtKind && !reservedBasisNames.contains cS.name &&
            cv.levelParams != cS.toConstantVal.levelParams &&
            levelsRenaming cS.toConstantVal.levelParams cv.levelParams) = true := by
          rw [hc, hlr']; simp [hne]
        rw [hren, ite_eq_left hcond]
      have hcv' : (renS Ef cS).toConstantVal = cv := by rw [hr, atLps_cv, hcv]
      refine ⟨by rw [hcv'], fun a S _ ψ => ?_, fun _ => hcv'⟩
      rw [hcv', hself]
    · have hr : renS Ef cS = cS := by
        rw [hren, ite_eq_right]
        intro h
        apply hc
        simp only [Bool.and_eq_true] at h ⊢
        exact h.1.1
      rw [hr]
      refine ⟨hlen.symm, fun a S hp ψ => ?_, fun hR => ?_⟩
      · rw [← denote_instLevels hp ψ 0 _]
        rw [← hcv]
        rfl
      · rcases hR with h | ⟨h, hk⟩
        · rw [← h]; rfl
        · have := congrArg ConstantInfo.toConstantVal h
          exact this.symm.trans rfl


/-- The names a needs walk from scratch lists are all of an expression's names. -/
private theorem needs_mem {e : Expr} {n : Name} (h : n ∈ e.needs) : n ∈ (needsGo {} #[] e).2 := by
  have h0 : Driver.NeedsInv (({} : Std.HashSet Expr), (#[] : Array Name)) := fun k hk => by
    simp at hk
  exact (NeedsSt.expr_spec h0 e).2.2 n h

/-- **A justified axiom's step** (see the module docstring). -/
theorem justStep {JS : Sidecar} {Ef envS E : Env} (hJ : JS.idx = mkFEnv envS)
    (mp : EnvModelM V E) (hcov : LfpCover mp []) (hN : NatFacts E)
    (mS : EnvModelM V (renEnv Ef envS))
    (hPL : ProofLeaves V (renEnv Ef envS) mS.base2.acval)
    (hagree : ∀ x, (E.find? x).isSome = true → Shared JS Ef x →
      mp.base2.acval x = mS.base2.acval x)
    (hEF : ∀ x ci, E.find? x = some ci → Ef.find? x = some ci)
    (hEFt : ∀ x, (E.find? x).isSome = true → Ef.findTable? x = E.findTable? x)
    {pd : Declaration} {cv : ConstantVal} (hj : justifiable pd = some cv)
    (hwhy : justifyWhy JS (mkFEnv E) cv = none) (hb : basisNamesOk pd = true)
    {F : Nat} (hrun : ConstantValRun F E cv cv.type)
    (hwf₂ : EnvWF ⟨.axiomInfo cv :: E.consts, E.tables⟩)
    (hEf : Ef.find? cv.name = some (.axiomInfo cv)) :
    ∃ mp' : EnvModelM V ⟨.axiomInfo cv :: E.consts, E.tables⟩, CoverRel mp mp' ∧
      LfpCover mp' [] ∧ NatFacts ⟨.axiomInfo cv :: E.consts, E.tables⟩ ∧
      (Shared JS Ef cv.name → mp'.base2.acval cv.name = mS.base2.acval cv.name) := by
  classical
  -- the record
  have hpd : pd = .axiomDecl cv ∧ builtinAxiomName cv.name = false ∧ natOpName cv.name = false ∧
      reduceOpNames.contains cv.name = false := by
    cases pd with
    | axiomDecl c =>
      simp only [justifiable] at hj
      split at hj
      · exact nomatch hj
      · next hc =>
        obtain rfl := Option.some.inj hj
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
    | _ => simp [justifiable] at hj
  obtain ⟨rfl, hbi, hopn, hro⟩ := hpd
  have hnres : reservedBasisNames.contains cv.name = false := by
    simp only [basisNamesOk, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with h | h
    · exfalso; simp [builtinAxiomName, h] at hbi
    · simpa using h
  have hnotreduce : cv.name ∉ reduceOpNames := fun h => by
    have h' : reduceOpNames.contains cv.name = true := List.elem_iff.mpr h
    rw [h'] at hro; exact nomatch hro
  -- the justification
  obtain ⟨cS, hfS, hs, T, hT, hTn⟩ := justifyWhy_cone hwhy
  have hfE : (mkFEnv E).find? = E.find? := funext (mkFEnv_find? E)
  have hfEt : (mkFEnv E).findTable? = E.findTable? := funext (mkFEnv_findTable? E)
  rw [hfE, hfEt] at hT
  have hTsh : ∀ n, T n → Shared JS Ef n := fun n hn => ⟨T, coneClosed_lift hEF hEFt hT, hn⟩
  rw [hJ, mkFEnv_find?] at hfS
  have hnS : cS.name = cv.name := Env.find?_name hfS
  let S' := renEnv Ef envS
  let c₀ := renS Ef cS
  have hf₀ : S'.find? cv.name = some c₀ := by
    show (renEnv Ef envS).find? cv.name = _
    rw [renEnv_find, hfS]; rfl
  have hn₀ : c₀.name = cv.name := (renS_name Ef cS).trans hnS
  obtain ⟨hlen, hty, hstmt⟩ := justified_type (Ef := Ef) hEf hnS hs
  -- the shared part stored before the record
  let R := sharedPart (Shared JS Ef) E S'
  have hfS' : ∀ x, Shared JS Ef x → ∃ ci ci', Ef.find? x = some ci ∧ S'.find? x = some ci' ∧
      Refines ci ci' ∧ (reduceOpNames.contains x = true → ci' = ci) :=
    fun x hx => refines_ren hJ ((shared_closed JS Ef x hx).1)
  have hR : ∀ {x}, (R.find? x).isSome = true → Shared JS Ef x ∧ (E.find? x).isSome = true := by
    intro x h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact (sharedPart_find_some hc).2
  -- the type reads alike on both sides
  have hres : cv.type.constsResolve R = true := by
    obtain ⟨-, -, -, -, -, -, htr, -, -⟩ := hrun
    have h1 : Expr.constsAll (Shared JS Ef) cv.type :=
      constsAll_of_needs fun n hn => hTsh n (hTn n (needs_mem hn))
    have h2 := (Modular.Expr.constsResolve_iff E).mp htr
    refine (Modular.Expr.constsResolve_iff R).mpr (Modular.Expr.constsAll_mono (fun n hn => ?_)
      (Modular.Expr.constsAll_and h1 h2))
    rw [sharedPart_find_of hn.1 hn.2]
    obtain ⟨_, _, -, h3, -⟩ := hfS' n hn.1
    rw [h3]; rfl
  have hden : ∀ ψ, denote mp.base2.acval E ψ 0 cv.type = denote mS.base2.acval S' ψ 0 cv.type := by
    intro ψ
    refine denote_alike (R := R) (fun {x} hx => ?_) (fun x hx => hagree x (hR hx).2 (hR hx).1)
      (fun {x} hx => ?_) ψ 0 cv.type hres
    · obtain ⟨hsh, hEs⟩ := hR hx
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hEs
      obtain ⟨ci₀, ci', g1, g2, g3, -⟩ := hfS' x hsh
      rw [hEF x ci hci] at g1
      obtain rfl := Option.some.inj g1
      exact ⟨ci, ci', hci, g2, g3.alike⟩
    · obtain ⟨hsh, hEs⟩ := hR hx
      obtain ⟨-, -, -, -, -, ht⟩ := (shared_closed JS Ef x hsh).1
      rw [← hEFt x hEs, tableBeqP_eq ht, hJ, mkFEnv_findTable?]
      exact (renEnv_findTable Ef envS x).symm
  -- the leaf
  let A : (Name → Nat) → Term.Term := fun ψ =>
    mS.base2.acval cv.name (Level.substFn ψ c₀.toConstantVal.levelParams
      (cv.levelParams.map Level.param))
  have hmem₀ : c₀ ∈ S'.consts := Env.find?_mem hf₀
  have hmemA : ∀ (ψ : Name → Nat) (ta : Term.Term), denote mp.base2.acval E ψ 0 cv.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta := by
    intro ψ ta hta ρ
    rw [hden, hty mS.base2.acval S' mS.base2.acval_params] at hta
    have := mS.mem_type c₀ hmem₀ _ ta hta ρ
    rw [hn₀] at this
    exact this
  obtain ⟨mp', hrel, hP, hnP, hc⟩ := harvestAxiomAt (A := A) mp hopn hrun hwf₂ hnres
    (fun ψ => mS.base2.cval_closed _ _)
    (fun ψ₁ ψ₂ hag => mS.base2.acval_params cv.name c₀ hf₀ _ _
      (substFn_map_param_agree hlen hag))
    (fun ψ ρ => mS.base2.acval_wellDenoted _ _ ρ) hmemA hnotreduce
  have hnat : NatFacts (⟨.axiomInfo cv :: E.consts, E.tables⟩ : Env) := by
    refine hN.append (new := [.axiomInfo cv]) rfl fun c hc => ?_
    obtain rfl := List.mem_singleton.mp hc
    have hne : ∀ m, reservedBasisNames.contains m = true → cv.name ≠ m := fun m hm h => by
      rw [h, hm] at hnres; exact nomatch hnres
    exact ⟨hne _ (by decide), hne _ (by decide), hne _ (by decide)⟩
  refine ⟨mp', hrel, hc hcov, hnat, fun hsh => ?_⟩
  -- a shared justified name: the sidecar's statement is the input's
  obtain ⟨ci, ci', g1, g2, g3, -⟩ := hfS' cv.name hsh
  rw [hEf] at g1
  obtain rfl := Option.some.inj g1
  rw [hf₀] at g2
  obtain rfl := Option.some.inj g2
  have hcv₀ : c₀.toConstantVal = cv := hstmt g3
  have hk₀ : c₀.isStmtKind = true := by
    rcases g3 with h | ⟨-, h⟩
    · rw [← h]; rfl
    · exact h
  have hA : A = mS.base2.acval cv.name := by
    funext ψ
    show mS.base2.acval cv.name _ = _
    rw [hcv₀, Level.substFn_param_self]
  by_cases hp : SemPropType V mp.base2.acval E cv.type
  · rw [hP hp]
    refine ((hPL cv.name c₀ hf₀ hk₀).2 ?_).symm
    intro ψ Ta hTa ρ
    rw [hcv₀, ← hden] at hTa
    exact hp ψ Ta hTa ρ
  · rw [hnP hp, hA]

end ConLeche.Model.Sidecar
