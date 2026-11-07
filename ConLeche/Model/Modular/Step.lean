module

public import ConLeche.Model.DeclsRun
public import ConLeche.Model.Modular.Proofs
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.PinRen

public section

/-!
# A module's own records, installed on its context's model

The step of the modular theorem (`ConLeche/Modular.lean`): a module's own records, accepted from
its context one after another by the fold's step (`DeclsRun`), carry a covered model of the
context to one of the module's own environment that keeps every context leaf and every proof's
leaf the canonical proof (`ProofLeaves`).  Each step is a pure `checkDecl` run
(`checkDeclStepC_run`), and `declStep_agrees` installs it: an earlier name keeps its leaf and its
type's reading, and a new theorem, or definition, opaque constant or axiom whose type reads as a
truth value, gets the canonical proof (`DeclProofLeaf`, `new_proof_leaf`).
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

/-- **A new proof's leaf is the canonical proof**: a stored constant a record adds, a theorem or
of a type that reads as a truth value at a name with no pinned leaf, gets it from its install. -/
theorem new_proof_leaf {F : Nat} {env env₂ : Env} {d : Declaration}
    (hrun : DeclRun F (ConLeche.Semantics.DeclIndRunDispatchK F env) env d env₂) {fe : FEnv}
    (hch : PushChain env fe) (he : fe.env = env₂)
    (hmem : ∀ c ∈ env₂.consts, c ∉ env.consts → c ∈ declConstants d)
    {a a' : Name → (Name → Nat) → Term}
    (hleaf : ∀ n, (env.find? n).isSome = true → a' n = a n)
    (hpl : DeclProofLeaf V a env d a') {n : Name} {ci : ConstantInfo}
    (hf : env₂.find? n = some ci) (hnew : env.find? n = none) (hk : ci.isStmtKind = true)
    (hpin : pinnedLeafName n = false)
    (hc : (∃ cv, ci = .thmInfo cv) ∨ SemPropType V a' env₂ ci.toConstantVal.type) :
    a' n = fun _ => .prf := by
  obtain ⟨hop, hred, hqs, hsy⟩ := pinnedLeafName_false hpin
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
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.2.1
    have hann : type' = cv.type := hcv.2.2.2.2.2.1
    rcases hc with ⟨_, h⟩ | hc
    · exact nomatch h
    · exact hpl ⟨hop, hann ▸ hsem htr hc⟩
  | thmDecl cv v =>
    obtain ⟨-, type', value', hcv, -, -, henv2⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    exact hpl
  | opaqueDecl cv v =>
    obtain ⟨-, type', value', hcv, -, henv2, -⟩ := hrun
    rw [henv2] at hf
    obtain ⟨rfl, rfl⟩ := find?_cons_fresh hf hnew
    have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.2.1
    have hann : type' = cv.type := hcv.2.2.2.2.2.1
    rcases hc with ⟨_, h⟩ | hc
    · exact nomatch h
    · exact hpl ⟨hred, hann ▸ hsem htr hc⟩
  | axiomDecl cv =>
    rcases hrun with ⟨hq, -, -, -, henv2⟩ | ⟨type', -, hcv, hbr⟩
    · rw [henv2] at hf
      obtain ⟨-, hname⟩ := find?_cons_fresh hf hnew
      rw [show (quotAt .sound cv).name = (quotPin .sound).name from
        ConLeche.Verify.atLps_name _ _] at hname
      exact absurd hname.symm (by rw [show (quotPin .sound).name = quotSoundName from rfl]; exact hqs)
    · have htr : type'.constsResolve env = true := hcv.2.2.2.2.2.2.2.1
      have hann : type' = cv.type := hcv.2.2.2.2.2.1
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
        rcases hc with ⟨_, h⟩ | hc
        · exact nomatch h
        · exact hpl ⟨hsy, hann ▸ hsem htr hc⟩
      · rw [h, hnew] at hf; exact nomatch hf
  | quotDecl k cv =>
    rcases hrec with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  | indDecl block nP =>
    rcases hrec with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, h, -⟩ <;> cases h

/-- **A module's own records, installed on its context's model** (see the module docstring): a
covered carrier at the context, with the η-family closure, the `Nat` facts and every proof's leaf
the canonical proof, carries to one at the own environment that keeps every context leaf. -/
theorem declsRun_proofs :
    ∀ {ds : List Declaration} {p q : Nat × FEnv}, DeclsRun .verified pins ds p q →
    ∀ {E : Env}, p.2 = mkFEnv E →
    ∀ mp : EnvModelM V E, LfpCover mp [] → EtaFamiliesClosed E → NatFacts E →
      ProofLeaves V E mp.base2.acval →
    ∃ mp' : EnvModelM V q.2.env,
      (∀ n, (E.find? n).isSome = true → mp'.base2.acval n = mp.base2.acval n) ∧
      LfpCover mp' [] ∧ EtaFamiliesClosed q.2.env ∧ NatFacts q.2.env ∧
      ProofLeaves V q.2.env mp'.base2.acval := by
  intro ds p q hrun
  induction hrun with
  | nil p =>
    intro E hp mp hcov hE hN hPL
    rw [hp]
    exact ⟨mp, fun _ _ => rfl, hcov, hE, hN, hPL⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    intro E hp mp hcov hE hN hPL
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hp] at hstepC
    have henv : EnvWF E := mp.base2.wf
    obtain ⟨-, hcanon, F, hF⟩ := checkDeclStepC_run henv CSOKF.empty hstepC
    have hrunD := checkDeclRun_ofEnvFactsK hF
    obtain ⟨⟨mp₁, hleaf₁, hcov₁, hPL₁⟩, hE₁, hN₁⟩ := declStep_agrees mp hcov hE hN hrunD
    have hch : PushChain E fe₁ :=
      checkDeclStepC_push (pins := pins) .verified (PushChain.refl E) pd {} fe₁ s₁ hstepC
    -- every proof's leaf, after the record
    have hPLn : ProofLeaves V fe₁.env mp₁.base2.acval := by
      intro n ci hf hk hpin hc
      by_cases hold : (E.find? n).isSome = true
      · have hf' : E.find? n = some ci := (pushChain_find_old hch hold) ▸ hf
        rw [hleaf₁ n hold]
        refine hPL n ci hf' hk hpin ?_
        rcases hc with h | h
        · exact .inl h
        · have hr : ci.toConstantVal.type.constsResolve E = true :=
            (henv.consts ci (ConLeche.Env.find?_mem hf')).2.2.1
          exact .inr (SemPropType.of_denote
            (fun ψ => (pushChain_denote_old hch hleaf₁ hr ψ).symm) h)
      · have hnew : E.find? n = none := by
          cases h : E.find? n with
          | none => rfl
          | some _ => rw [h] at hold; exact absurd rfl hold
        have hfe₁ : fe₁.env = streamEnv [pd] E := by
          have h₁ := checkDeclStepC_pushes (pins := pins) .verified (mkFEnv E) pd {} fe₁ s₁ hstepC
          simp only at h₁
          rw [h₁, pushDelta_env]
          rfl
        refine new_proof_leaf hrunD hch rfl (fun c hc hnc => ?_) hleaf₁ hPL₁ hf hnew hk hpin hc
        rw [hfe₁] at hc
        simp only [streamEnv, List.foldl, Env.pushDelta, List.mem_append, List.mem_reverse] at hc
        exact hc.resolve_right hnc
    obtain ⟨mp', hleaf', hcov', hE', hN', hPL'⟩ :=
      ih (E := fe₁.env) hcanon mp₁ hcov₁ hE₁ hN₁ hPLn
    have hst : ∀ n, (E.find? n).isSome = true → (fe₁.env.find? n).isSome = true := fun n h => by
      rw [pushChain_find_old hch h]; exact h
    exact ⟨mp', fun n hn => (hleaf' n (hst n hn)).trans (hleaf₁ n hn), hcov', hE', hN', hPL'⟩

end ConLeche.Model.Modular
