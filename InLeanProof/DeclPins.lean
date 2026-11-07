module

public import InLeanProof.DeclStep
/- `ConstantInfo.name`/`levelParams`/`type` are read as projections of `toConstantVal`. -/
import all Lean.Declaration

/-!
# O6: the pinned axioms and the compiler-trust opaques (task #451, lane O6)

InLean's guards on the standard-axiom and compiler-trust families
(`InLean/CheckerC.lean`: `pinFoundInd`/`pinFoundCtor`/`pinFoundRec`,
`Pin.matchesDeclExact`) against master's (`stdAxiomOk`, `trustCompilerOk`,
`reduceElemOk`, `reduceStoredOk`, `ofReduceAxOk`): a stored entry InLean reads
of a kind and counts is master's of the same kind and counts at the
translated name (`EnvPresI`), matching the translated pin.
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-- A pin, translated. -/
@[expose] def trPin (p : InLean.Pin) : ConLeche.ConstantVal :=
  ⟨toName p.name, p.lps.map toName, trC p.type⟩

/-- **`Pin.matchesDeclExact` is master's `matchesPin`** at the translation. -/
theorem matchesPin_tr {n : Name} {lps : List Name} {ty : Expr} {c : ConLeche.Expr}
    (hc : toExprC ty = some c) {p : InLean.Pin} (hok : okC p.type = true)
    (h : p.matchesDeclExact n lps ty = true) :
    ConLeche.ConstantVal.matchesPin ⟨toName n, lps.map toName, c⟩ (trPin p) = true := by
  simp only [InLean.Pin.matchesDeclExact, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hcl⟩ := h
  have := toExpr_of_clEq (fun _ => none) hcl
  rw [show toExpr (fun _ => none) ty = some c from hc,
    show toExpr (fun _ => none) p.type = some (trC p.type) from toExprC_of_okC hok] at this
  cases this
  simp [ConLeche.ConstantVal.matchesPin, trPin]

theorem matchesPin_of_cvrel {v : Lean.ConstantVal} {ccv : ConLeche.ConstantVal}
    (hr : CVRel v ccv) {p : InLean.Pin} (hok : okC p.type = true)
    (h : p.matchesDeclExact v.name v.levelParams v.type = true) :
    ConLeche.ConstantVal.matchesPin ccv (trPin p) = true := by
  obtain ⟨n, l, t⟩ := ccv
  obtain ⟨h1, h2, h3⟩ := hr
  simp only at h1 h2
  subst h1 h2
  exact matchesPin_tr h3.2.2 hok h

theorem find_rel {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {ci : Lean.ConstantInfo} (h : fe.find? n = some ci) :
    ∃ cci, L.find? (toName n) = some cci ∧ EntryRelI fe ci cci :=
  hP.entry n ci h

/-- An inductive InLean reads is one master reads. -/
theorem pinFoundInd_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {p : InLean.Pin}
    (hok : okC p.type = true) (h : InLean.pinFoundInd fe p = true) :
    ∃ ccv caps, L.find? (toName p.name) = some (.indInfo ccv caps) ∧
      ConLeche.ConstantVal.matchesPin ccv (trPin p) = true := by
  unfold InLean.pinFoundInd at h
  split at h
  · rename_i ci v hf
    obtain ⟨cci, hc, hr⟩ := find_rel hP hf
    cases cci with
    | indInfo ccv caps => exact ⟨ccv, caps, hc, matchesPin_of_cvrel hr.1 hok h⟩
    | _ => simp [EntryRelI] at hr
  · exact nomatch h

/-- A constructor InLean reads, with its counts, is one master reads. -/
theorem pinFoundCtor_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {p : InLean.Pin}
    {nP nF : Nat} (hok : okC p.type = true) (h : InLean.pinFoundCtor fe p nP nF = true) :
    ∃ ccv, L.find? (toName p.name) = some (.ctorInfo ccv nP nF) ∧
      ConLeche.ConstantVal.matchesPin ccv (trPin p) = true := by
  unfold InLean.pinFoundCtor at h
  split at h
  · rename_i ci v hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hm⟩ := h
    obtain ⟨cci, hc, hr⟩ := find_rel hP hf
    cases cci with
    | ctorInfo ccv a b =>
      obtain ⟨hr, rfl, rfl⟩ := hr
      exact ⟨ccv, hc, matchesPin_of_cvrel hr hok hm⟩
    | _ => simp [EntryRelI] at hr
  · exact nomatch h

/-- A recursor InLean reads, with its counts, is one master reads. -/
theorem pinFoundRec_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {p : InLean.Pin}
    {mI rP : Nat} (hok : okC p.type = true) (h : InLean.pinFoundRec fe p mI rP = true) :
    ∃ ccv k rules, L.find? (toName p.name) = some (.recInfo ccv mI rP k rules) ∧
      ConLeche.ConstantVal.matchesPin ccv (trPin p) = true := by
  unfold InLean.pinFoundRec at h
  split at h
  · rename_i ci rv hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, hm⟩ := h
    obtain ⟨cci, hc, hr⟩ := find_rel hP hf
    obtain ⟨ccv, crules, rfl, hcv, -⟩ := hr
    refine ⟨ccv, rv.k, crules, ?_, matchesPin_of_cvrel hcv hok hm⟩
    rw [hc, show majorIdxOf rv = mI from h1, show rulePrefixOf rv = rP from h2]
  · exact nomatch h

end InLeanProof

namespace InLeanProof
open Lean InLean ConLeche.Cached

/-! ## The standard axioms -/

theorem pins_std :
    trPin InLean.iffPin = ConLeche.iffA.toConstantVal ∧
    trPin InLean.iffIntroPin = ConLeche.iffIntroA.toConstantVal ∧
    trPin InLean.iffRecPin = ConLeche.iffRecA.toConstantVal ∧
    trPin InLean.propextPin = ConLeche.propextA ∧
    trPin InLean.nonemptyPin = ConLeche.nonemptyA.toConstantVal ∧
    trPin InLean.nonemptyIntroPin = ConLeche.nonemptyIntroA.toConstantVal ∧
    trPin InLean.nonemptyRecPin = ConLeche.nonemptyRecA.toConstantVal ∧
    trPin InLean.choicePin = ConLeche.choiceA := by
  decide

theorem pins_std_ok :
    okC InLean.iffPin.type = true ∧ okC InLean.iffIntroPin.type = true ∧
    okC InLean.iffRecPin.type = true ∧ okC InLean.propextPin.type = true ∧
    okC InLean.nonemptyPin.type = true ∧ okC InLean.nonemptyIntroPin.type = true ∧
    okC InLean.nonemptyRecPin.type = true ∧ okC InLean.choicePin.type = true := by
  decide

theorem names_std :
    toName InLean.iffName = ConLeche.iffName ∧ toName InLean.iffIntroName = ConLeche.iffIntroName ∧
    toName InLean.iffRecName = ConLeche.iffRecName ∧ toName InLean.propextName = ConLeche.propextName ∧
    toName InLean.nonemptyName = ConLeche.nonemptyName ∧
    toName InLean.nonemptyIntroName = ConLeche.nonemptyIntroName ∧
    toName InLean.nonemptyRecName = ConLeche.nonemptyRecName ∧
    toName InLean.choiceName = ConLeche.choiceName ∧ toName InLean.eqName = ConLeche.eqName :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **InLean's standard-axiom guard is master's** at the translation. -/
theorem stdAxiomOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {lps : List Name} {ty : Expr} (hok : okC ty = true)
    (h : InLean.stdAxiomOk fe n lps ty = true) :
    ConLeche.stdAxiomOk L (trCVn n lps ty) = true := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := pins_std
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := pins_std_ok
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := names_std
  have hc : toExprC ty = some (trC ty) := toExprC_of_okC hok
  unfold InLean.stdAxiomOk at h
  unfold ConLeche.stdAxiomOk
  by_cases hp : n = InLean.propextName
  · subst hp
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hEq, hI⟩, hIi⟩, hIr⟩, hm⟩ := h
    have e1 := find_isSome_of_pres hP hEq
    obtain ⟨c2, k2, e2, hm2⟩ := pinFoundInd_tr hP o1 hI
    obtain ⟨c3, hc3, hm3⟩ := pinFoundCtor_tr hP o2 hIi
    obtain ⟨c4, k4, r4, hc4, hm4⟩ := pinFoundRec_tr hP o3 hIr
    have e5 := matchesPin_tr hc o4 hm
    rw [n9] at e1
    rw [show InLean.iffPin.name = InLean.iffName from rfl, n1] at e2
    rw [t1] at hm2
    rw [show InLean.iffIntroPin.name = InLean.iffIntroName from rfl, n2] at hc3
    rw [t2] at hm3
    rw [show InLean.iffRecPin.name = InLean.iffRecName from rfl, n3] at hc4
    rw [t3] at hm4
    rw [t4, n4] at e5
    simp only [trCVn, n4, ↓reduceIte, e1, e2, hm2, hc3, hm3, hc4, hm4, e5, Bool.and_self]
  · have hp' : (n == InLean.propextName) = false := by simpa using hp
    have tp : toName n ≠ ConLeche.propextName := by rw [← n4]; exact fun e => hp (toName_inj e)
    simp only [hp', Bool.false_eq_true, ↓reduceIte] at h
    by_cases hch : n = InLean.choiceName
    · subst hch
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hI, hIi⟩, hIr⟩, hm⟩ := h
      obtain ⟨c2, k2, e2, hm2⟩ := pinFoundInd_tr hP o5 hI
      obtain ⟨c3, hc3, hm3⟩ := pinFoundCtor_tr hP o6 hIi
      obtain ⟨c4, k4, r4, hc4, hm4⟩ := pinFoundRec_tr hP o7 hIr
      have e5 := matchesPin_tr hc o8 hm
      rw [show InLean.nonemptyPin.name = InLean.nonemptyName from rfl, n5] at e2
      rw [t5] at hm2
      rw [show InLean.nonemptyIntroPin.name = InLean.nonemptyIntroName from rfl, n6] at hc3
      rw [t6] at hm3
      rw [show InLean.nonemptyRecPin.name = InLean.nonemptyRecName from rfl, n7] at hc4
      rw [t7] at hm4
      rw [t8, n8] at e5
      simp only [trCVn, n8, show ConLeche.choiceName ≠ ConLeche.propextName by decide, ↓reduceIte,
        e2, hm2, hc3, hm3, hc4, hm4, e5, Bool.and_self]
    · have hc' : (n == InLean.choiceName) = false := by simpa using hch
      simp [hc'] at h

end InLeanProof

namespace InLeanProof
open Lean InLean ConLeche.Cached

/-! ## The compiler-trust family -/

/-- **`Nat` is the pinned basis wherever it is stored** (master's
`reduceElemOk` compares the stored entry with `natA` itself): a premise on `L`,
what P4 reads off `NatFacts`. -/
@[expose] def NatPinned (L : ConLeche.Env) : Prop :=
  (L.find? ConLeche.natName).isSome = true → L.find? ConLeche.natName = some ConLeche.natA

theorem trust_beqs :
    (InLean.reduceBoolName == InLean.reduceNatName) = false ∧
    (InLean.ofReduceBoolName == InLean.ofReduceNatName) = false := by
  constructor <;> simp only [beq_eq_false_iff_ne] <;> exact ne_of_toName (by decide)

theorem pins_trust :
    trPin InLean.truePin = ConLeche.trueCvA ∧ trPin InLean.trueIntroPin = ConLeche.trueIntroCvA ∧
    trPin InLean.trustCompilerPin = ConLeche.trustCompilerA ∧
    trPin InLean.boolPin = ConLeche.boolCvA ∧
    trPin (InLean.reduceOpPin InLean.reduceNatName) = ConLeche.reduceOpCvA ConLeche.reduceNatName ∧
    trPin (InLean.reduceOpPin InLean.reduceBoolName) = ConLeche.reduceOpCvA ConLeche.reduceBoolName ∧
    trPin (InLean.ofReducePin InLean.ofReduceNatName) = ConLeche.ofReducePinA ConLeche.ofReduceNatName ∧
    trPin (InLean.ofReducePin InLean.ofReduceBoolName) =
      ConLeche.ofReducePinA ConLeche.ofReduceBoolName := by
  simp only [InLean.reduceOpPin, InLean.ofReducePin, InLean.ofReduceOp, InLean.reduceElemTy,
    beq_self_eq_true, trust_beqs.1, trust_beqs.2, Bool.false_eq_true, ↓reduceIte]
  decide

theorem pins_trust_ok :
    okC InLean.truePin.type = true ∧ okC InLean.trueIntroPin.type = true ∧
    okC InLean.trustCompilerPin.type = true ∧ okC InLean.boolPin.type = true ∧
    okC (InLean.reduceOpPin InLean.reduceNatName).type = true ∧
    okC (InLean.reduceOpPin InLean.reduceBoolName).type = true ∧
    okC (InLean.ofReducePin InLean.ofReduceNatName).type = true ∧
    okC (InLean.ofReducePin InLean.ofReduceBoolName).type = true := by
  simp only [InLean.reduceOpPin, InLean.ofReducePin, InLean.ofReduceOp, InLean.reduceElemTy,
    beq_self_eq_true, trust_beqs.1, trust_beqs.2, Bool.false_eq_true, ↓reduceIte]
  decide

theorem names_trust :
    toName InLean.trueName = ConLeche.trueName ∧ toName InLean.trueIntroName = ConLeche.trueIntroName ∧
    toName InLean.trustCompilerName = ConLeche.trustCompilerName ∧
    toName InLean.boolName = ConLeche.boolName ∧ toName InLean.natName = ConLeche.natName ∧
    toName InLean.reduceNatName = ConLeche.reduceNatName ∧
    toName InLean.reduceBoolName = ConLeche.reduceBoolName ∧
    toName InLean.ofReduceNatName = ConLeche.ofReduceNatName ∧
    toName InLean.ofReduceBoolName = ConLeche.ofReduceBoolName :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`Lean.trustCompiler`'s guard is master's.** -/
theorem trustCompilerOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {lps : List Name} {ty : Expr} (hok : okC ty = true)
    (h : InLean.trustCompilerOk fe n lps ty = true) :
    ConLeche.trustCompilerOk L (trCVn n lps ty) = true := by
  obtain ⟨t1, t2, t3, -⟩ := pins_trust
  obtain ⟨o1, o2, o3, -⟩ := pins_trust_ok
  obtain ⟨n1, n2, -⟩ := names_trust
  unfold InLean.trustCompilerOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hI, hIi⟩, hm⟩ := h
  obtain ⟨c2, k2, e2, hm2⟩ := pinFoundInd_tr hP o1 hI
  obtain ⟨c3, hc3, hm3⟩ := pinFoundCtor_tr hP o2 hIi
  have e5 := matchesPin_tr (toExprC_of_okC hok) o3 hm
  rw [show InLean.truePin.name = InLean.trueName from rfl, n1] at e2
  rw [t1] at hm2
  rw [show InLean.trueIntroPin.name = InLean.trueIntroName from rfl, n2] at hc3
  rw [t2] at hm3
  rw [t3] at e5
  unfold ConLeche.trustCompilerOk
  simp only [trCVn, e2, hm2, hc3, hm3, e5, Bool.and_self]

/-- **The element inductive's guard is master's**, `Nat` through `NatPinned`. -/
theorem reduceElemOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (hnat : NatPinned L) {c : Name} (h : InLean.reduceElemOk fe c = true) :
    ConLeche.reduceElemOk L (toName c) = true := by
  obtain ⟨-, -, -, t4, -⟩ := pins_trust
  obtain ⟨-, -, -, o4, -⟩ := pins_trust_ok
  obtain ⟨-, -, -, n4, n5, n6, -⟩ := names_trust
  unfold InLean.reduceElemOk at h
  unfold ConLeche.reduceElemOk
  by_cases hc : c = InLean.reduceNatName
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    have e := find_isSome_of_pres hP (n := InLean.natName) (by
      simp only [natLitStoredF, Bool.and_eq_true] at h; exact h.1.1.1)
    rw [n5] at e
    simp [n6, hnat e]
  · have hc' : (c == InLean.reduceNatName) = false := by simpa using hc
    have tc : toName c ≠ ConLeche.reduceNatName := by rw [← n6]; exact fun e => hc (toName_inj e)
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨c2, k2, e2, hm2⟩ := pinFoundInd_tr hP o4 h
    rw [show InLean.boolPin.name = InLean.boolName from rfl, n4] at e2
    rw [t4] at hm2
    simp only [tc, ↓reduceIte, e2, hm2]

/-- **A reduce operation's stored-entry guard is master's** (InLean stores an
opaque, con-leche an axiom). -/
theorem reduceStoredOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {c : Name}
    (hc : c = InLean.reduceNatName ∨ c = InLean.reduceBoolName)
    (h : InLean.reduceStoredOk fe c = true) :
    ConLeche.reduceStoredOk L (toName c) = true := by
  obtain ⟨-, -, -, -, t5, t6, -⟩ := pins_trust
  obtain ⟨-, -, -, -, o5, o6, -⟩ := pins_trust_ok
  obtain ⟨-, -, -, -, -, n6, n7, -⟩ := names_trust
  have hpin : trPin (InLean.reduceOpPin c) = ConLeche.reduceOpCvA (toName c) ∧
      okC (InLean.reduceOpPin c).type = true := by
    rcases hc with rfl | rfl
    · rw [n6]; exact ⟨t5, o5⟩
    · rw [n7]; exact ⟨t6, o6⟩
  unfold InLean.reduceStoredOk at h
  unfold ConLeche.reduceStoredOk
  split at h
  · rename_i ci v hf
    obtain ⟨cci, hcc, hr⟩ := find_rel hP hf
    cases cci with
    | axiomInfo ccv =>
      rw [hcc, ← hpin.1]
      exact matchesPin_of_cvrel hr hpin.2 h
    | _ => simp [EntryRelI] at hr
  · rename_i ci v hf
    obtain ⟨cci, hcc, hr⟩ := find_rel hP hf
    cases cci with
    | axiomInfo ccv =>
      rw [hcc, ← hpin.1]
      exact matchesPin_of_cvrel hr hpin.2 h
    | _ => simp [EntryRelI] at hr
  · exact nomatch h

theorem ofReduceOp_tr (n : Name) : toName (InLean.ofReduceOp n) = ConLeche.ofReduceOp (toName n) := by
  obtain ⟨-, -, -, -, -, n6, n7, n8, -⟩ := names_trust
  unfold InLean.ofReduceOp ConLeche.ofReduceOp
  by_cases h : n = InLean.ofReduceNatName
  · subst h; simp [n6, n8]
  · have h' : (n == InLean.ofReduceNatName) = false := by simpa using h
    have t : toName n ≠ ConLeche.ofReduceNatName := by rw [← n8]; exact fun e => h (toName_inj e)
    simp [h', t, n7]

theorem ofReduceOp_cases (n : Name) :
    InLean.ofReduceOp n = InLean.reduceNatName ∨ InLean.ofReduceOp n = InLean.reduceBoolName := by
  unfold InLean.ofReduceOp; split <;> simp

/-- **The `ofReduce*` axioms' guard is master's.** -/
theorem ofReduceAxOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (hnat : NatPinned L) {n : Name} {lps : List Name} {ty : Expr} (hok : okC ty = true)
    (hn : n = InLean.ofReduceNatName ∨ n = InLean.ofReduceBoolName)
    (h : InLean.ofReduceAxOk fe n lps ty = true) :
    ConLeche.ofReduceAxOk L (trCVn n lps ty) = true := by
  obtain ⟨-, -, -, -, -, -, t7, t8⟩ := pins_trust
  obtain ⟨-, -, -, -, -, -, o7, o8⟩ := pins_trust_ok
  obtain ⟨-, -, -, -, -, -, -, n8, n9⟩ := names_trust
  have hpin : trPin (InLean.ofReducePin n) = ConLeche.ofReducePinA (toName n) ∧
      okC (InLean.ofReducePin n).type = true := by
    rcases hn with rfl | rfl
    · rw [n8]; exact ⟨t7, o7⟩
    · rw [n9]; exact ⟨t8, o8⟩
  unfold InLean.ofReduceAxOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hEq, hE⟩, hS⟩, hm⟩ := h
  have e1 := find_isSome_of_pres hP hEq
  rw [show toName InLean.eqName = ConLeche.eqName from rfl] at e1
  have e2 := reduceElemOk_tr hP hnat hE
  have e3 := reduceStoredOk_tr hP (ofReduceOp_cases n) hS
  have e4 := matchesPin_tr (toExprC_of_okC hok) hpin.2 hm
  rw [hpin.1] at e4
  rw [ofReduceOp_tr] at e2 e3
  unfold ConLeche.ofReduceAxOk
  simp only [trCVn, e1, e2, e3, e4, Bool.and_self]

end InLeanProof

namespace InLeanProof
open Lean InLean ConLeche.Cached

/-! ## The pinned axioms' arm -/

/-- **An axiom other than `sorryAx` and `Quot.sound`** (`checkAxiomC`: the
standard axioms, `Lean.trustCompiler`, the `ofReduce*` pair; any other declines
at con-leche's policy). -/
theorem checkAxiomC_pinned_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hnat : NatPinned L)
    {pins : List ConLeche.NatOpPinSet} {v : AxiomVal} {a : InLean.Added} {s₀ s' : InLean.CState}
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false)
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hsafe : v.isUnsafe = false)
    (hq : v.name ≠ InLean.quotSoundName) (hso : v.name ≠ InLean.sorryAxName)
    (h : InLean.checkAxiomC .verified InLeanProof.theoremConfig fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.axiomInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.axiomInfo v] = some d ∧ StepRuns pins L d := by
  obtain ⟨c1, c2, -, -, c5, c6, c7, -, -, -⟩ := cl_axNames
  have hfe : ({ fe with safety := .safe } : InLean.FEnv) = fe := by cases fe; simp_all
  have bq : (v.name == InLean.quotSoundName) = false := by simpa using hq
  have bs : (v.name == InLean.sorryAxName) = false := by simpa using hso
  unfold InLean.checkAxiomC at h
  simp only [bq, Bool.false_eq_true, ↓reduceIte, hsafe] at h
  rw [hfe, hfc] at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok, -, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  -- what InLean accepted on
  have key : (InLean.stdAxiomOk fe v.name v.levelParams v.type = true ∨
      (v.name = InLean.trustCompilerName ∧
        InLean.trustCompilerOk fe v.name v.levelParams v.type = true) ∨
      ((v.name = InLean.ofReduceNatName ∨ v.name = InLean.ofReduceBoolName) ∧
        InLean.ofReduceAxOk fe v.name v.levelParams v.type = true)) ∧
      ({ consts := #[.axiomInfo v] } : InLean.Added) = a ∧ s₁ = s' := by
    split at h
    · exact ⟨.inl ‹_›, pureI_ok h⟩
    split at h
    · rename_i ht
      split at h
      · exact ⟨.inr (.inl ⟨by simpa using ht, ‹_›⟩), pureI_ok h⟩
      · exact (throw_bindI_ok h).elim
    split at h
    · rename_i ho
      split at h
      · exact ⟨.inr (.inr ⟨by simpa [Bool.or_eq_true] using ho, ‹_›⟩), pureI_ok h⟩
      · exact (throw_bindI_ok h).elim
    split at h
    · exact (throw_bindI_ok h).elim
    split at h
    · rename_i hh
      simp [bs, show theoremConfig.coreAxioms = false from rfl] at hh
    · exact (throwI_ok h).elim
  obtain ⟨key, hres⟩ := key
  have hres : a = { consts := #[.axiomInfo v] } ∧ s' = s₁ := ⟨hres.1.symm, hres.2.symm⟩
  obtain ⟨rfl, rfl⟩ := hres
  refine ⟨hs₁, ht₁, rfl, rfl, .axiomDecl (trCVn v.name v.levelParams v.type),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok],
    ⟨.axiomInfo (trCVn v.name v.levelParams v.type) :: L.consts, L.tables⟩, ?_⟩
  have tq : toName v.name ≠ ConLeche.quotSoundName := by
    rw [← c2]; exact fun e => hq (toName_inj e)
  unfold ConLeche.checkDecl
  simp only [trCVn, tq, ↓reduceIte] at hRC ⊢
  refine Runs.bind hRC ?_
  by_cases hm : ConLeche.stdAxiomOk L ⟨toName v.name, v.levelParams.map toName, trC v.type⟩ = true
  · simp only [hm, ↓reduceIte]
    exact Runs.pure _
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rcases key with k | ⟨hn, k⟩ | ⟨hn, k⟩
    · have := stdAxiomOk_tr hJ.pres hok k
      simp only [trCVn] at this
      rw [hm] at this; exact nomatch this
    · have := trustCompilerOk_tr hJ.pres hok k
      simp only [trCVn, hn, c5] at this
      simp only [hn, c5, ↓reduceIte, this]
      exact Runs.pure _
    · have := ofReduceAxOk_tr hJ.pres hnat hok hn k
      simp only [trCVn] at this
      have tt : toName v.name ≠ ConLeche.trustCompilerName := by
        rcases hn with hn | hn <;> rw [hn] <;> decide
      have to : toName v.name = ConLeche.ofReduceNatName ∨ toName v.name = ConLeche.ofReduceBoolName := by
        rcases hn with hn | hn <;> rw [hn] <;> simp [c6, c7]
      simp only [tt, to, ↓reduceIte, this]
      exact Runs.pure _

end InLeanProof
