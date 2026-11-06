module

public import ConLeche.Model.DeclsRun
public import ConLeche.Modular
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.PinRen

public section

/-!
# A module's own records, installed on its context's model

The step of the modular theorem (`ConLeche/Modular.lean`): a module's own records, accepted from
its context one after another by the fold's step (`DeclsRun`), carry a covered model of the
context to one of the module's own environment that keeps every context leaf, and whose leaf at
every name the module flags as a proof (`FlagsOk`) is the canonical proof `.prf`.  Each step is a
pure `checkDecl` run (`checkDeclStepC_run`), and `declStep_agrees` installs it.  A flagged
definition or opaque record passed the theorem record's check (`ProofDecl`), and a flagged axiom
record's type is inferred to be a proposition, so either type is one the checker finds to be a
proposition (`PropTypeRun`), which is where its install gives it the canonical proof
(`DeclProofLeaf`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Cached ConLeche.Semantics ConLeche.Modular ConLeche.Model
open ConLeche.Term (Term)

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet}

/-- A name stored, or pushed, is stored after a push. -/
theorem find?_pushDelta_isSome {E : Env} {L : List ConstantInfo} {Q : List ProjTable} {n : Name}
    (h : (E.find? n).isSome = true ∨ n ∈ L.map (·.name)) :
    ((E.pushDelta L Q).find? n).isSome = true := by
  unfold Env.find? Env.pushDelta at *
  simp only [List.find?_isSome, List.mem_append, List.mem_reverse, beq_iff_eq] at h ⊢
  rcases h with ⟨c, hc, he⟩ | h
  · exact ⟨c, .inr hc, he⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨c, .inl hc, rfl⟩

/-- **A flagged proof's record is a proof**: a theorem, a definition or opaque record whose type
the theorem record's check finds to be a proposition, at a name with no fast path, or an axiom
record whose type is one.  Its one name gets the canonical proof from its install
(`DeclProofLeaf`). -/
theorem proofDecl_leaf {E : Env} (henv : EnvWF E) {d : Declaration}
    (hpd : ProofDecl .verified pins E d) {acval : Name → (Name → Nat) → Term}
    (h : DeclProofLeaf E d acval) :
    ∀ n ∈ declNames d, acval n = fun _ => .prf := by
  -- the theorem record's check, as a run: its type is a proposition
  have hthm : ∀ {cv : ConstantVal} {v : Expr} {r : FEnv × CState},
      checkDeclStepC .verified pins (mkFEnv E) (.thmDecl cv v) {} = .ok r →
      natOpName cv.name = false ∧ PropTypeRun E cv.type := by
    intro cv v r hr
    obtain ⟨-, -, F, hF⟩ := checkDeclStepC_run henv CSOKF.empty hr
    have hrun : DeclThmRun F E cv v _ := checkDeclRun_ofEnvFactsK hF
    obtain ⟨hopn, type', value', hcv, ⟨stype, u, h1, h2, h3⟩, -, -⟩ := hrun
    have hann : type' = cv.type := hcv.2.2.2.2.2.1
    subst hann
    exact ⟨hopn, F, stype, u, h1, h2, h3⟩
  cases d with
  | thmDecl cv v =>
    intro n hn
    obtain rfl : n = cv.name := List.mem_singleton.mp hn
    exact h
  | defnDecl cv v hint =>
    intro n hn
    obtain rfl : n = cv.name := List.mem_singleton.mp hn
    obtain ⟨r, hr⟩ := hpd
    obtain ⟨hop, hprop⟩ := hthm hr
    exact h ⟨hop, hprop⟩
  | opaqueDecl cv v =>
    intro n hn
    obtain rfl : n = cv.name := List.mem_singleton.mp hn
    obtain ⟨hred, r, hr⟩ := hpd
    exact h ⟨hred, (hthm hr).2⟩
  | axiomDecl cv =>
    -- the name it stores, if any: `Quot.sound`'s pin at its name, no name for `sorryAx`
    intro n hn
    simp only [declNames, declConstants] at hn
    by_cases hq : cv.name = quotSoundName
    · simp only [hq, ↓reduceIte, List.map_cons, List.map_nil, List.mem_singleton] at hn
      have hn' : n = cv.name := by rw [hn, hq]; exact ConLeche.Verify.atLps_name _ _
      subst hn'
      exact h ⟨by rw [hq]; decide, hpd⟩
    · by_cases hs : cv.name = sorryAxName
      · have hsq : sorryAxName ≠ quotSoundName := by decide
        simp [hs, hsq] at hn
      · simp only [hq, hs, ↓reduceIte, List.map_cons, List.map_nil, List.mem_singleton] at hn
        subst hn
        exact h ⟨hs, hpd⟩
  | quotDecl _ _ => exact hpd.elim
  | indDecl _ _ => exact hpd.elim

/-- **A module's own records, installed on its context's model** (see the module docstring): a
covered carrier at the context, with the η-family closure and the `Nat` facts, carries to one at
the own environment that keeps every context leaf, and whose leaf at every flagged name a record
installs is the canonical proof. -/
theorem declsRun_flags {proofs : Name → Bool} :
    ∀ {ds : List Declaration} {p q : Nat × FEnv}, DeclsRun .verified pins ds p q →
    ∀ {E : Env}, p.2 = mkFEnv E → FlagsOk .verified pins proofs E ds →
    ∀ mp : EnvModelM V E, LfpCover mp [] → FamilyRan mp → EtaFamiliesClosed E → NatFacts E →
    ∃ mp' : EnvModelM V q.2.env,
      (∀ n, (E.find? n).isSome = true → mp'.base2.acval n = mp.base2.acval n) ∧
      LfpCover mp' [] ∧ FamilyRan mp' ∧ EtaFamiliesClosed q.2.env ∧ NatFacts q.2.env ∧
      ∀ d ∈ ds, ∀ n ∈ declNames d, proofs n = true → mp'.base2.acval n = fun _ => .prf := by
  intro ds p q hrun
  induction hrun with
  | nil p =>
    intro E hp _ mp hcov hS hE hN
    rw [hp]
    exact ⟨mp, fun _ _ => rfl, hcov, hS, hE, hN, fun _ h => nomatch h⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    intro E hp hfl mp hcov hS hE hN
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hp] at hstepC
    have henv : EnvWF E := mp.base2.wf
    obtain ⟨-, hcanon, F, hF⟩ := checkDeclStepC_run henv CSOKF.empty hstepC
    obtain ⟨⟨mp₁, hleaf₁, hcov₁, hS₁, hPL⟩, hE₁, hN₁⟩ :=
      declStep_agrees mp hcov hS hE hN (checkDeclRun_ofEnvFactsK hF)
    have hfe₁ : fe₁.env = streamEnv [pd] E := by
      have h₁ := checkDeclStepC_pushes (pins := pins) .verified (mkFEnv E) pd {} fe₁ s₁ hstepC
      simp only at h₁
      rw [h₁, pushDelta_env]
      rfl
    cases hfl with
    | cons hflag hrest =>
    rw [← hfe₁] at hrest
    obtain ⟨mp', hleaf', hcov', hS', hE', hN', hfl'⟩ :=
      ih (E := fe₁.env) hcanon hrest mp₁ hcov₁ hS₁ hE₁ hN₁
    have hst : ∀ n, (E.find? n).isSome = true ∨ n ∈ declNames pd →
        (fe₁.env.find? n).isSome = true := fun n h => by
      rw [hfe₁]; exact find?_pushDelta_isSome h
    refine ⟨mp', fun n hn => (hleaf' n (hst n (.inl hn))).trans (hleaf₁ n hn), hcov', hS', hE',
      hN', fun d hd n hn hp => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [hleaf' n (hst n (.inr hn))]
      exact proofDecl_leaf henv (hflag n hn hp) hPL n hn
    · exact hfl' d hd n hn hp

end ConLeche.Model.Modular
