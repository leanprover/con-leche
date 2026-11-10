module

import ConLeche.Model.DeclsRun
public import ConLeche.Model.Modular.Proofs
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.PinRen

public section

/-!
# A module's own records, installed on its context's model

The step of the modular theorem (`ConLeche/Modular.lean`): a module's own records, accepted from
its context one after another by the fold's step (`DeclsRun`), carry a covered model of the
context to one of the module's own environment that keeps every context leaf and every proof's
leaf the canonical proof (`ProofLeaves`).  Each step is a pure `checkDecl` run
(`checkDeclStepC_run`), and `declStep_agrees` installs it: an earlier name keeps its leaf and its
type's reading, a new theorem's type reads as a truth value (the theorem record's check,
`new_thm_prop`), and a new theorem, or definition, opaque constant or axiom whose type reads so,
gets the canonical proof (`DeclProofLeaf`, `new_proof_leaf`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Cached ConLeche.Semantics ConLeche.Modular ConLeche.Model
open ConLeche.Term (Term)

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}

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

/-- A new constant at the front of an environment is the one a lookup of a fresh name finds. -/
theorem find?_cons_fresh {c ci : ConstantInfo} {env : Env} {n : Name}
    (h : (⟨c :: env.consts, env.tables⟩ : Env).find? n = some ci) (hnew : env.find? n = none) :
    ci = c ∧ c.name = n := by
  unfold Env.find? at h hnew
  rw [List.find?_cons] at h
  split at h
  · next heq =>
    obtain rfl := Option.some.inj h
    exact ⟨rfl, by simpa using heq⟩
  · rw [hnew] at h
    exact nomatch h

/-- **A new theorem's type reads as a truth value**: the theorem record's check finds it a
proposition before the record, and it reads the same after it. -/
theorem new_thm_prop {F : Nat} {env env₂ : Env} {d : Declaration}
    (hrun : DeclRun F (ConLeche.Semantics.DeclIndRunDispatchK F env) env d env₂) {fe : FEnv}
    (hch : PushChain env fe) (he : fe.env = env₂)
    (hmem : ∀ c ∈ env₂.consts, c ∉ env.consts → c ∈ declConstants d)
    (mp : EnvModelM V env) {a' : Name → (Name → Nat) → Term}
    (hleaf : ∀ n, (env.find? n).isSome = true → a' n = mp.base2.acval n) {n : Name}
    {cv : ConstantVal} (hf : env₂.find? n = some (.thmInfo cv)) (hnew : env.find? n = none) :
    SemPropType V a' env₂ cv.type := by
  subst he
  have hname := ConLeche.Env.find?_name hf
  have hmem_ci : ConstantInfo.thmInfo cv ∈ declConstants d := by
    refine hmem _ (ConLeche.Env.find?_mem hf) fun h => ?_
    have : (env.find? (ConstantInfo.thmInfo cv).name).isSome = true := by
      unfold Env.find?; rw [List.find?_isSome]; exact ⟨_, h, by simp⟩
    rw [hname, hnew] at this; exact nomatch this
  obtain ⟨v, rfl⟩ := thm_of_record hmem_ci
  obtain ⟨-, -, type', value', hcv, hprop, -, henv2⟩ := hrun
  rw [henv2] at hf
  obtain ⟨h, -⟩ := find?_cons_fresh hf hnew
  rw [show cv.type = type' from congrArg (·.type) (ConstantInfo.thmInfo.inj h)]
  obtain ⟨-, -, hlbt, hitf, hann, -, htr, -, -⟩ := hcv
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  refine SemPropType.of_denote (fun ψ => pushChain_denote_old hch hleaf htr ψ)
    (semPropType_of_run mp (Expr.WScoped.of_not_hasFvar htf') hbt' (fun l hl => ?_)
      (Expr.fvarLeaves_eq_nil_of_not_hasFvar htf') ⟨F, hprop⟩)
  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
  exact absurd hl List.not_mem_nil

/-- **A new proof's leaf is the canonical proof**: a stored constant a record adds, a theorem or
of a type that reads as a truth value, gets it from its install. -/
theorem new_proof_leaf {F : Nat} {env env₂ : Env} {d : Declaration}
    (hrun : DeclRun F (ConLeche.Semantics.DeclIndRunDispatchK F env) env d env₂) {fe : FEnv}
    (hch : PushChain env fe) (he : fe.env = env₂)
    (hmem : ∀ c ∈ env₂.consts, c ∉ env.consts → c ∈ declConstants d)
    {a a' : Name → (Name → Nat) → Term}
    (hleaf : ∀ n, (env.find? n).isSome = true → a' n = a n)
    (hpl : DeclProofLeaf V a env d a') {n : Name} {ci : ConstantInfo}
    (hf : env₂.find? n = some ci) (hnew : env.find? n = none) (hk : ci.isStmtKind = true)
    (hqs : n ≠ quotSoundName)
    (hc : SemPropType V a' env₂ ci.toConstantVal.type) :
    a' n = fun _ => .prf := by
  subst he
  -- the constant is the record's
  have hname := ConLeche.Env.find?_name hf
  have hmem_ci : ci ∈ declConstants d := by
    refine hmem ci (ConLeche.Env.find?_mem hf) fun h => ?_
    have : (env.find? ci.name).isSome = true := by
      unfold Env.find?; rw [List.find?_isSome]; exact ⟨ci, h, by simp⟩
    rw [hname, hnew] at this; exact nomatch this
  have hrec := stmt_of_record hmem_ci hk (by rw [hname]; exact hqs)
  -- a type resolving before the record reads the same after it
  have hsem : ∀ {ty : Expr}, ty.constsResolve env = true →
      SemPropType V a' fe.env ty → SemPropType V a env ty := fun hr hs =>
    SemPropType.of_denote (fun ψ => (pushChain_denote_old hch hleaf hr ψ).symm) hs
  obtain ⟨-, hrun⟩ := hrun
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.1
    exact hpl _ hmem_ci hk (.inr (hsem htr hc))
  | thmDecl cv v =>
    obtain ⟨-, type', value', hcv, -, -, henv2⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    exact hpl _ hmem_ci hk (.inl ⟨_, rfl⟩)
  | opaqueDecl cv v =>
    obtain ⟨-, type', value', hcv, -, henv2, -⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.1
    exact hpl _ hmem_ci hk (.inr (hsem htr hc))
  | axiomDecl cv =>
    rcases hrun with ⟨hq, -, -, -, henv2⟩ | ⟨-, type', -, hcv, hbr⟩
    · rw [henv2] at hf
      obtain ⟨-, hname⟩ := find?_cons_fresh hf hnew
      rw [show (quotAt .sound cv).name = (quotPin .sound).name from
        ConLeche.Verify.atLps_name _ _] at hname
      exact absurd hname.symm (by rw [show (quotPin .sound).name = quotSoundName from rfl]; exact hqs)
    · have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.1
      have hax : fe.env = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ ∨
          fe.env = env := by
        rcases hbr with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, -, -, -, -, h⟩
        · exact .inl h
        · exact .inl h
        · exact .inl h
        · exact .inr h
      rcases hax with h | h
      · rw [h] at hf
        obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
        exact hpl _ hmem_ci hk (.inr (hsem htr hc))
      · rw [h, hnew] at hf; exact nomatch hf
  | quotDecl k cv =>
    rcases hrec with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  | indDecl block nP =>
    rcases hrec with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, h, -⟩ <;> cases h

/-- **A module's own records, installed on its context's model** (see the module docstring): a
covered carrier at the context, with the `Nat` facts and every proof's leaf
the canonical proof, carries to one at the own environment that keeps every context leaf. -/
theorem declsRun_proofs :
    ∀ {ds : List Declaration} {p q : Nat × FEnv}, DeclsRun .verified pins maxNatSize ds p q →
    ∀ {E : Env}, p.2 = mkFEnv E →
    ∀ mp : EnvModelM V E, LfpCover mp [] → NatFacts E →
      ProofLeaves V E mp.base2.acval →
    ∃ mp' : EnvModelM V q.2.env,
      (∀ n, (E.find? n).isSome = true → mp'.base2.acval n = mp.base2.acval n) ∧
      LfpCover mp' [] ∧ NatFacts q.2.env ∧
      ProofLeaves V q.2.env mp'.base2.acval := by
  intro ds p q hrun
  induction hrun with
  | nil p =>
    intro E hp mp hcov hN hPL
    rw [hp]
    exact ⟨mp, fun _ _ => rfl, hcov, hN, hPL⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    intro E hp mp hcov hN hPL
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hp] at hstepC
    have henv : EnvWF E := mp.base2.wf
    obtain ⟨-, hcanon, F, hF⟩ := checkDeclStepC_run henv (CSOKF.fresh _) hstepC
    have hrunD := checkDeclRun_ofEnvFactsK hF
    obtain ⟨⟨mp₁, hleaf₁, hcov₁, hPL₁⟩, hN₁⟩ := declStep_agrees mp hcov hN hrunD
    have hch : PushChain E fe₁ :=
      checkDeclStepC_push (pins := pins) .verified (PushChain.refl E) pd { maxNatSize := maxNatSize } fe₁ s₁
        hstepC
    -- every proof's leaf, after the record
    have hPLn : ProofLeaves V fe₁.env mp₁.base2.acval := by
      intro n ci hf hk
      by_cases hold : (E.find? n).isSome = true
      · have hf' : E.find? n = some ci := (pushChain_find_old hch hold) ▸ hf
        have hr : ci.toConstantVal.type.constsResolve E = true :=
          (henv.consts ci (ConLeche.Env.find?_mem hf')).2.2.1
        obtain ⟨h1, h2⟩ := hPL n ci hf' hk
        refine ⟨fun ht => SemPropType.of_denote
          (fun ψ => pushChain_denote_old hch hleaf₁ hr ψ) (h1 ht), fun h => ?_⟩
        rw [hleaf₁ n hold]
        exact h2 (SemPropType.of_denote (fun ψ => (pushChain_denote_old hch hleaf₁ hr ψ).symm) h)
      · have hnew : E.find? n = none := by
          cases h : E.find? n with
          | none => rfl
          | some _ => rw [h] at hold; exact absurd rfl hold
        have hfe₁ : fe₁.env = streamEnv [pd] E := by
          have h₁ := checkDeclStepC_pushes (pins := pins) .verified (mkFEnv E) pd { maxNatSize := maxNatSize } fe₁
            s₁ hstepC
          simp only at h₁
          rw [h₁, pushDelta_env]
          rfl
        have hmem : ∀ c ∈ fe₁.env.consts, c ∉ E.consts → c ∈ declConstants pd := by
          intro c hc hnc
          rw [hfe₁] at hc
          simp only [streamEnv, List.foldl, Env.pushDelta, List.mem_append, List.mem_reverse] at hc
          exact hc.resolve_right hnc
        refine ⟨fun ⟨cv, h⟩ => ?_, fun hc => ?_⟩
        · subst h
          exact new_thm_prop hrunD hch rfl hmem mp hleaf₁ hf hnew
        by_cases hqs : n = quotSoundName
        · subst hqs; exact quotSound_leaf mp₁ hf
        exact new_proof_leaf hrunD hch rfl hmem hleaf₁ hPL₁ hf hnew hk hqs hc
    obtain ⟨mp', hleaf', hcov', hN', hPL'⟩ :=
      ih (E := fe₁.env) hcanon mp₁ hcov₁ hN₁ hPLn
    have hst : ∀ n, (E.find? n).isSome = true → (fe₁.env.find? n).isSome = true := fun n h => by
      rw [pushChain_find_old hch h]; exact h
    exact ⟨mp', fun n hn => (hleaf' n (hst n hn)).trans (hleaf₁ n hn), hcov', hN', hPL'⟩

end ConLeche.Model.Modular
