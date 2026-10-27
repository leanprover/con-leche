module

public import ConLeche.Model.InstallRun
public import ConLeche.Modular
import ConLeche.Verify.CheckerSplit
import ConLeche.Semantics.DeclEta
import ConLeche.Semantics.Bridge.Sound

public section

/-!
# A module's declarations, installed on its context's model

The middle step of the modular theorem (`ConLeche/Modular.lean`): a
module's declarations accepted from its context (`AcceptedFrom`), one
step at a time, carry a covered model of the context to one of the
module's own environment that keeps every context leaf (`Agrees`), and
whose leaf at every constant the module flags as a proof is the
canonical proof.  Each step is the fold's own install and record check
at the canonical index of the environment so far; it is a `checkDecl`
run (`installStepC_model`), and `declStep_agrees` installs it.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Cached ConLeche.Semantics ConLeche.Modular ConLeche.Model
open ConLeche.Verify

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {pins : List NatOpPinSet}

/-- **One accepted step is a `checkDecl` run**, onto a name-unique
environment the canonical index chains to. -/
theorem acceptStep_checkDecl (hμ : μ.isVerified = true) {E : Env} {d : Declaration}
    {i : Nat} {fe : FEnv} {pend : Array PendingCheck}
    (hm : EnvModelOk V μ E) (hnd : NodupNames E)
    (hstep : installDeclStep μ pins (i, mkFEnv E, #[]) d = .ok (i + 1, fe, pend))
    (hrec : ∀ pc ∈ pend.toList, ∃ s, checkPending μ fe pc {} = .ok ((), s)) :
    NodupNames fe.env ∧ PushChain E fe ∧
      ∃ F, checkDecl μ (fueledOps μ F) pins E d = .ok fe.env := by
  have hrun : InstallRun μ pins [d] (i, mkFEnv E, #[]) (i + 1, fe, pend) :=
    .cons hstep (.nil _)
  obtain ⟨hch, -⟩ := installRun_trace μ hrun (PushChain.refl E)
  have hnd' : NodupNames fe.env := hch.2.2.1 hnd
  obtain ⟨fe₁, pend₁, s₁, hq, hstepC⟩ := installDeclStep_ok hstep
  simp only [Prod.mk.injEq] at hq
  obtain ⟨-, rfl, rfl⟩ := hq
  obtain ⟨hpush₁, -⟩ :=
    installStepC_push μ i (PushChain.self (fe := mkFEnv E) rfl) #[] d {} (fe, pend) s₁ hstepC
  obtain ⟨-, -, F, hF⟩ :=
    installStepC_model (V := V) (q := (i + 1, fe, pend)) (new₁ := []) hμ rfl hpush₁.canon hm
      CSOKF.empty hstepC (PushChain.self hpush₁.canon) (by simp) hnd' hrec
  exact ⟨hnd', hch, F, hF⟩

/-- **A theorem check passes, so the type is a proposition**: the
flag's check (`ProofDecl`'s `checkPending` with the theorem kind, at
the environment's canonical index) is a `PropTypeRun`. -/
theorem propTypeRun_of_thmCheck (hμ : μ.isVerified = true) {E : Env} (mp : EnvModelM V μ E)
    (hnd : NodupNames E) {cv : ConstantVal} {v : Expr} (hwty : Expr.WScoped 0 cv.type)
    {s : CState}
    (h : checkPending μ (mkFEnv E) ⟨⟨.thm, cv, v⟩, 0, (mkFEnv E).visibleBelow⟩ {} = .ok ((), s)) :
    PropTypeRun μ E cv.type := by
  have hvis : (mkFEnv E).visibleBelow = E.consts.length := mkFEnv_visibleBelow E
  have hfind : ∀ n, ((mkFEnv E).restrictTo (mkFEnv E).visibleBelow).find? n = E.find? n := by
    rw [hvis]
    exact restrictTo_find?_of_extends (new := []) rfl hnd rfl
  have htab : ∀ T, ((mkFEnv E).restrictTo (mkFEnv E).visibleBelow).findTable? T
      = E.findTable? T := by
    rw [hvis]
    exact restrictTo_findTable?_of_extends (new := []) (newQ := []) rfl hnd rfl rfl
      (fun _ h => nomatch h)
  obtain ⟨-, F, hC⟩ := checkPending_run (CheckMode.vc hμ) mp.base2.wf
    (pc := ⟨⟨.thm, cv, v⟩, 0, (mkFEnv E).visibleBelow⟩) hfind htab hwty
    (fun h => absurd rfl h) CSOKF.empty h
  obtain ⟨stype, u, hst, hsort, hthm, -⟩ := checkValueGroup_inv hC
  exact ⟨F, stype, u, hst, hsort, hthm rfl⟩

/-- **A module's declarations, installed on its context's model**: a
covered carrier at the context, with the η-family closure and unique
names, carries to one at the own environment that agrees with it and
whose leaf at every flagged name the declarations store is the
canonical proof. -/
theorem acceptedFrom_model (hμ : μ.isVerified = true) {proofs : Name → Bool} :
    ∀ {E : Env} {ds : List Declaration} {E' : Env}, AcceptedFrom μ pins proofs E ds E' →
    ∀ mp : EnvModelM V μ E, LfpCover mp [] → EtaFamiliesClosed E → NodupNames E →
    ∃ mp' : EnvModelM V μ E', Agrees mp mp' ∧ LfpCover mp' [] ∧ EtaFamiliesClosed E' ∧
      NodupNames E' ∧
      ∀ n, proofs n = true → E.find? n = none → (E'.find? n).isSome = true →
        mp'.base2.acval n = fun _ => .prf := by
  intro E ds E' h
  induction h with
  | nil E =>
    intro mp hcov hE hnd
    exact ⟨mp, Agrees.refl mp, hcov, hE, hnd, fun n _ h1 h2 => by rw [h1] at h2; exact nomatch h2⟩
  | @cons E E' d ds i fe pend hstep hrec hflag rest ih =>
    intro mp hcov hE hnd
    obtain ⟨hnd₁, -, F, hF⟩ := acceptStep_checkDecl (V := V) hμ ⟨⟨mp, hcov⟩, hE⟩ hnd hstep hrec
    have hrunD := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hF
    obtain ⟨mp₁, hag₁, hcov₁, hleaf₁⟩ := declStep_agrees hμ mp hcov hE hrunD
    have hE₁ : EtaFamiliesClosed fe.env := ConLeche.Semantics.declEtaStepRun
      (fun h' => ConLeche.Semantics.declIndRunDispatchKEtaClosed hE h') hE hrunD
    obtain ⟨mp', hag', hcov', hE', hnd', hfl'⟩ := ih mp₁ hcov₁ hE₁ hnd₁
    refine ⟨mp', hag₁.trans hag', hcov', hE', hnd', fun n hp hn hs => ?_⟩
    cases hn₁ : fe.env.find? n with
    | none => exact hfl' n hp hn₁ hs
    | some ci =>
      have hs₁ : (fe.env.find? n).isSome = true := by rw [hn₁]; rfl
      rw [(hag' n hs₁).2]
      have hpd := hflag n hp hn hs₁
      -- the step's one new name is the declaration's own
      have hnew : ∀ c₀ : ConstantInfo, fe.env = ⟨c₀ :: E.consts, E.tables⟩ → n = c₀.name := by
        intro c₀ he
        rw [he, ConLeche.Env.find?_cons] at hn₁
        split at hn₁
        · next h => exact h.symm
        · rw [hn] at hn₁; exact nomatch hn₁
      cases d with
      | thmDecl cv v =>
        obtain ⟨type', value', -, -, -, henv2⟩ := hrunD
        rw [hnew _ henv2]
        exact hleaf₁
      | defnDecl cv v hint =>
        obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hrunD
        rw [hnew _ henv2]
        obtain ⟨hpin, s, hck⟩ := hpd
        have hwty : Expr.WScoped 0 cv.type := Expr.WScoped.of_not_hasFvar hcv.2.2.2.2.1
        refine hleaf₁ ⟨?_, propTypeRun_of_thmCheck hμ mp hnd hwty hck⟩
        cases h1 : ConLeche.natOpNames.contains cv.name <;>
          cases h2 : ConLeche.natDivModNames.contains cv.name <;> simp
        all_goals exact absurd (by simp [pinnedNames, List.contains_iff_mem.mp ‹_›]) hpin
      | opaqueDecl cv v =>
        obtain ⟨type', value', hcv, -, henv2, -⟩ := hrunD
        rw [hnew _ henv2]
        obtain ⟨hpin, s, hck⟩ := hpd
        have hwty : Expr.WScoped 0 cv.type := Expr.WScoped.of_not_hasFvar hcv.2.2.2.2.1
        refine hleaf₁ ⟨?_, propTypeRun_of_thmCheck hμ mp hnd hwty hck⟩
        cases h1 : ConLeche.reduceOpNames.contains cv.name
        · rfl
        · exact absurd (by simp [pinnedNames, List.contains_iff_mem.mp h1]) hpin
      | axiomDecl _ => exact hpd.elim
      | basisDecl _ => exact hpd.elim
      | quotDecl _ _ => exact hpd.elim
      | indDecl _ _ => exact hpd.elim

end ConLeche.Model.Modular
