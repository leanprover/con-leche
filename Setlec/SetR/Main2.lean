import Setlec.SetR.Main
import Setlec.SetR.Interp2.Keys2Bundle

/-!
# The fourteen's conditional swap — the same results over `EnvS2U`

`Setlec/SetR/Main.lean`'s fourteen conclude over `EnvS`.  This file
states their `EnvS2U` counterparts, conditional on the install step
the interp2 tier does not yet have.

**Three things, recorded rather than assumed.**

1. **v1's fourteen are untouched and stay hypothesis-free.**  Nothing
   here edits `Main.lean`; every theorem below is a new name ending in
   `R2`, and the `_R` forms keep their unconditional proofs.  Where a
   swapped form needs an `EnvS` fact it reads it off `EnvS2U.base` —
   *containment*, not re-proof.
2. **Mode-generic.**  Seal 10 withdrew `μ.verified`, so this is a
   swap and not a swap-plus-restriction.  `DeclStep2All` quantifies
   over `μ` exactly as v1's `declStepS` does, and no statement below
   carries a mode premise.
3. **`Nonempty` is not an obstacle** (seal 36's R6): it eliminates
   into `Prop`, so `Nonempty (EnvS2U V env')` is the fold's carrier
   in exactly the way `Nonempty (EnvS V env')` is v1's.

## What the conditional is, and what it is not

The single hypothesis is `DeclStep2All` — the interp2 counterpart of
`Install/Step.lean`'s `declStepS`, at the same `DeclR` currency.  It
is **not** item 1's bundle, and pretending otherwise would be the
honesty rule's own failure mode:

* item 1 (`Keys2Bundle.lean`) closes **three** of the five inputs
  `declStepS` consumes — `ReducePin2`, `MemberBlock2`, `DeclStep2` at
  a fresh axiom.  `DeclBasisS`/`DeclIndS` have no interp2 counterpart
  at all, and `DivModPinS` has one only as a draft (`DivModV2`);
* item 1's `MemberBlock2` lands at a constant already stored in the
  *prefix*, while `declStep2_of_axiom` needs it at the **new** name in
  the extension — the install-tier half seal 40 measured.  So the two
  do not chain, and `DeclStep2Residues.newMember` stays a residue.

`DeclStep2All` is therefore the honest name for "the interp2
dispatch, once it exists", and item 1 is the record of how far its
axiom kind has got.  **It is not inhabited in this tree**, and neither
is `CheckStep2E` behind it; per seals 39 and 50 both discharge at
junction closure, and until then every statement below says "if the
install lane lands, the fourteen swap" and nothing stronger.

## What the swap actually buys, per theorem

* The four `checkDecls*_sound_R2` and `checkDecl_sound_R2` conclude a
  **strictly stronger** carrier than their `_R` originals: the
  annotated valuation and its five laws, on top of the collapse-lane
  invariant.  This is where the swap has content.
* The eight `no_proof_of_Empty*_R2` conclude `False`, which v1 already
  proves **unconditionally**.  Their content is the *route*, not the
  fact: they show that the interp2 tier reaches the same corollaries
  through its own fold.  Said out loud because a conditional theorem
  with an already-unconditional conclusion is worth exactly that much
  and no more.
* `no_constant_of_Empty_R2` is the tier's own statement of the
  emptiness fact, and its proof is `no_constant_of_Empty_R` at
  `m.base`: the `Empty` content is the collapse lane's, and the swap
  does not re-derive it over `interp2`.  There is no `empty_pinned`
  counterpart at the annotated tier, so a genuinely interp2-side
  proof is not available and is not claimed.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory EStore Expr
open Setlec.SetR.Interp2 (EnvS2U)

universe w
variable {V : Type w} [SetTheory V]

/-! ## The one hypothesis -/

/-- **The interp2 counterpart of `declStepS`.**  A checked
declaration of any kind extends the annotated invariant, at the same
`DeclR` currency v1's dispatch uses.

*Provenance*: `Install/Step.lean`'s `declStepS`, with `EnvS` replaced
by `EnvS2U`.  Its five inputs there are `DivModPinS`, `ReducePinS`,
`StdAxiomKeyS`, `DeclBasisS`, `DeclIndS`; item 1's bundle closes the
interp2 forms of the second and third (and of the axiom-kind
construction itself), and the other two have no interp2 counterpart
yet.

*Discharges*: with the interp2 install lane, at junction closure.
**Not inhabited in this tree.**

*Not `rfl`*: the conclusion is `Nonempty` of a nine-field structure at
an arbitrary extended environment.

**No mode premise.**  `μ` is the checker mode the run was made in,
quantified exactly as in `declStepS`. -/
def DeclStep2All (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {d : Declaration} (m : EnvS2U V env),
    EtaFamiliesClosed env →
    DeclR μ F m.base.cval env d env₂ →
    Nonempty (EnvS2U V env₂)

/-- The annotated fold's carrier — `EnvSOk` one tier up.  The eta
side invariant is V-free and is **not** re-proved here: it comes from
v1's own dispatch, run alongside at `m.base`. -/
def EnvS2UOk (V : Type w) [SetTheory V] (env : Env) : Prop :=
  Nonempty (EnvS2U V env) ∧ EtaFamiliesClosed env

/-- The empty environment carries the annotated invariant. -/
theorem EnvS2UOk.empty (V : Type w) [SetTheory V] :
    EnvS2UOk V Env.empty :=
  ⟨⟨EnvS2U.empty V⟩, EtaFamiliesClosed.empty⟩

/-! ## The swap, theorem by theorem -/

/-- **`no_constant_of_Empty_R`, over `EnvS2U`.**  The emptiness
content is the collapse lane's, read off `base`; what the swap
changes is the carrier the hypothesis names. -/
theorem no_constant_of_Empty_R2 {env : Env} (m : EnvS2U V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_constant_of_Empty_R m.base c hc hty

/-- **`checkDecl_sound_R`, over `EnvS2U`.**  One checked declaration
extends the annotated invariant. -/
theorem checkDecl_sound_R2 {μ : CheckMode} (hstep : DeclStep2All V μ)
    {F : Nat} {env env₂ : Env} {d : Declaration} (m : EnvS2U V env)
    (hE : EtaFamiliesClosed env)
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    EnvS2UOk V env₂ :=
  ⟨hstep m hE (checkDeclR_sound m.base hE h),
    (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
      (declIndS memberKeyS) m.base hE
      (checkDeclR_sound m.base hE h)).2⟩

/-- The pure checker's fold, over `EnvS2U`. -/
theorem foldlM_R2 {μ : CheckMode} {F : Nat}
    (hstep : DeclStep2All V μ) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      EnvS2UOk V env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      exact foldlM_R2 hstep ds env1
        (checkDecl_sound_R2 hstep m hE hd) h

/-- **The acceptance theorem, over `EnvS2U`.**  `checkDecls_sound_R`
with the annotated carrier. -/
theorem checkDecls_sound_R2 {μ : CheckMode} {F : Nat}
    (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    Nonempty (EnvS2U V env') :=
  (foldlM_R2 hstep ds Env.empty (EnvS2UOk.empty V) h).1

/-- **No proof of `Empty`**, through the annotated fold. -/
theorem no_proof_of_Empty_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} {F : Nat} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- The cached-executable fold, over `EnvS2U`. -/
theorem foldlM_RC2 {μ : CheckMode} (hstep : DeclStep2All V μ) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl μ (cachedOps μ)) env = .ok env' →
      EnvS2UOk V env'
  | [], env, env', hm, h => by
    have h' : (Except.ok env : CheckM Env) = Except.ok env' := h
    cases h'
    exact hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (cachedOps μ) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge m.base.wf hd
      exact foldlM_RC2 hstep ds env1
        (checkDecl_sound_R2 hstep m hE hF) h

/-- **The cached executable's acceptance theorem, over `EnvS2U`.** -/
theorem checkDeclsC_sound_R2 {μ : CheckMode}
    (hstep : DeclStep2All V μ) {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env') :
    Nonempty (EnvS2U V env') :=
  (foldlM_RC2 hstep ds Env.empty (EnvS2UOk.empty V) h).1

/-- **No proof of `Empty`** — cached executable, annotated fold. -/
theorem no_proof_of_Empty_C_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsC_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- The shared-state executable's fold, over `EnvS2U`. -/
theorem foldlM_RS2 {μ : CheckMode} (hstep : DeclStep2All V μ) :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      EnvS2UOk V fe.env →
      ds.foldlM (checkDeclSharedF μ) fe = .ok fe' →
      EnvS2UOk V fe'.env
  | [], fe, fe', _, hm, h => by
    have h' : (Except.ok fe : CheckM FEnv) = Except.ok fe' := h
    cases h'
    exact hm
  | d :: ds, fe, fe', hfe, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDeclSharedF μ fe d with
    | error e => rw [hd] at h; exact nomatch h
    | ok fe1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      rw [hfe] at hd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.base.wf hd
      exact foldlM_RS2 hstep ds fe1 hfe1
        (checkDecl_sound_R2 hstep m hE hF) h

/-- **The shared-state executable's acceptance theorem, over
`EnvS2U`.** -/
theorem checkDeclsS_sound_R2 {μ : CheckMode}
    (hstep : DeclStep2All V μ) {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env') :
    Nonempty (EnvS2U V env') := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF μ) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    exact (foldlM_RS2 hstep ds (mkFEnv Env.empty) rfl
      (EnvS2UOk.empty V) hf).1

/-- **No proof of `Empty`** — shared-state executable, annotated
fold. -/
theorem no_proof_of_Empty_S_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsS_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- The parsed-index executable's fold, over `EnvS2U`. -/
theorem foldSP_R2 {μ : CheckMode} (hstep : DeclStep2All V μ)
    {st0 : EStore} (hwfst : st0.WF) :
    ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv} {s₀ s' : IState},
      fe = mkFEnv fe.env →
      EnvS2UOk V fe.env →
      ISOKF s₀ → Ext st0 s₀.store →
      (pds.foldlM (checkDeclSPStep μ
        (st0.nodes.size + st0.nodes.size)) fe) s₀ = .ok (fe', s') →
      EnvS2UOk V fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact hm
  | pd :: pds, fe, fe', s₀, s', hfe, hm, hres, hext0, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepP, h⟩ := bindI_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd0⟩ := denoteDeclP_total hwfst
      (checkDeclSPStep_inRange hstepP)
    have hd : denoteDeclP s₀.store pd = some d :=
      denoteDeclP_mono hwfst hext0 hd0
    rw [hfe] at hstepP
    obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
      checkDeclSPStep_run m.base.wf hres hd hstepP
    exact foldSP_R2 hstep hwfst pds fe₁ hfe₁
      (checkDecl_sound_R2 hstep m hE hF) hres₁
      (hext0.trans hext₁) h

/-- **The parsed-index executable's acceptance theorem, over
`EnvS2U`.** -/
theorem checkDeclsSP_sound_R2 {μ : CheckMode}
    (hstep : DeclStep2All V μ)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env') :
    Nonempty (EnvS2U V env') := by
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind] at h
  cases hf : (pds.foldlM (checkDeclSPStep μ
      (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)).run' { store := st.raw } with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (pds.foldlM (checkDeclSPStep μ
        (st.raw.nodes.size + st.raw.nodes.size))
        (mkFEnv Env.empty)) { store := st.raw } with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨feO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact (foldSP_R2 hstep hwf pds (mkFEnv Env.empty) rfl
        (EnvS2UOk.empty V) (ISOKF.fresh hwf) (Ext.refl _) hrun).1

/-- **No proof of `Empty`** — parsed-index executable, annotated
fold. -/
theorem no_proof_of_Empty_SP_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSP_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- Annotating the `Empty` leaf returns it unchanged.  Factored out
of the four input-level folds, where `Main.lean` inlines it; the
statement is v1's, verbatim. -/
theorem annotate_empty_const_eq {μ : CheckMode} {env : Env} {F : Nat}
    {type : Expr}
    (h : annotateCore μ env F 0 (.const emptyName []) = .ok type) :
    Expr.const emptyName [] = type := by
  cases F with
  | zero =>
    rw [annotateCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ F' =>
    rw [annotateCore_succ] at h
    simpa [annotateBody, pure, Except.pure] using h

/-! ## The input-level four

Their conclusion is `False`, which v1 proves unconditionally, so what
these add is the route and not the fact.  Stated anyway, because the
route is what the swap is about: the fold that carries them is the
annotated one throughout. -/

/-- The pure checker's input-level fold, over `EnvS2U`. -/
theorem foldlM_no_Empty_R2 {μ : CheckMode} {F : Nat}
    (hstep : DeclStep2All V μ)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type :=
        annotate_empty_const_eq hann
      obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d) hstep m hE hdd).1
      exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_R2 (value := value) (hint := hint)
        hstep hty ds env1
        (checkDecl_sound_R2 (d := d) hstep m hE hdd) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — annotated
fold. -/
theorem no_proof_of_Empty_input_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} {F : Nat} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_R2 hstep hty ds Env.empty (EnvS2UOk.empty V) h hd

/-- The cached executable's input-level fold, over `EnvS2U`. -/
theorem foldlM_no_Empty_RC2 {μ : CheckMode}
    (hstep : DeclStep2All V μ)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl μ (cachedOps μ)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl μ (cachedOps μ) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨F, hF⟩ := checkDecl_bridge m.base.wf hdd
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type :=
        annotate_empty_const_eq hann
      obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d) hstep m hE hF).1
      exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_RC2 (value := value) (hint := hint)
        hstep hty ds env1
        (checkDecl_sound_R2 (d := d) hstep m hE hF) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — cached
executable, annotated fold. -/
theorem no_proof_of_Empty_input_C_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_RC2 hstep hty ds Env.empty (EnvS2UOk.empty V) h hd

/-- The shared-state executable's input-level fold, over `EnvS2U`. -/
theorem foldlM_no_Empty_RS2 {μ : CheckMode}
    (hstep : DeclStep2All V μ)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      EnvS2UOk V fe.env →
      ds.foldlM (checkDeclSharedF μ) fe = .ok fe' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, fe, fe', hfe, hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDeclSharedF μ fe d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok fe1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    rw [hfe] at hdd
    obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.base.wf hdd
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type :=
        annotate_empty_const_eq hann
      obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d) hstep m hE hF).1
      exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_RS2 (value := value) (hint := hint)
        hstep hty ds fe1 hfe1
        (checkDecl_sound_R2 (d := d) hstep m hE hF) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — shared-state
executable, annotated fold. -/
theorem no_proof_of_Empty_input_S_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF μ) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    exact foldlM_no_Empty_RS2 hstep hty ds (mkFEnv Env.empty) rfl
      (EnvS2UOk.empty V) hf hd

/-- **No accepted input stream declares a proof of `Empty`** — the
parsed-index executable at the stream level, annotated fold. -/
theorem no_proof_of_Empty_input_SP_R2 (V : Type w) [SetTheory V]
    {μ : CheckMode} (hstep : DeclStep2All V μ)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) :
    False := by
  replace hty : st.raw.denote cvp.type
      = some (.const emptyName []) := hty
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind, StateT.run'] at h
  cases hrun : (pds.foldlM (checkDeclSPStep μ
      (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)) { store := st.raw } with
  | error e => rw [hrun] at h; exact nomatch h
  | ok pr =>
    clear h
    obtain ⟨feO, sO⟩ := pr
    suffices hgen : ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv}
        {s₀ s' : IState},
        fe = mkFEnv fe.env →
        EnvS2UOk V fe.env →
        ISOKF s₀ → Ext st.raw s₀.store →
        (pds.foldlM (checkDeclSPStep μ
          (st.raw.nodes.size + st.raw.nodes.size)) fe) s₀
          = .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
      exact hgen pds (mkFEnv Env.empty) rfl (EnvS2UOk.empty V)
        (ISOKF.fresh hwf) (Ext.refl _) hrun hd
    clear hrun hd
    intro pds
    induction pds with
    | nil =>
      intro fe fe' s₀ s' _ _ _ _ _ hd
      rcases hd with ⟨_, hd⟩ | hd <;> cases hd
    | cons pd pds ih =>
      intro fe fe' s₀ s' hfe hm hres hext0 h hd
      rw [List.foldlM_cons] at h
      obtain ⟨fe₁, s₁, hstepP, h⟩ := bindI_ok h
      obtain ⟨⟨m⟩, hE⟩ := hm
      obtain ⟨d, hd0⟩ := denoteDeclP_total hwf
        (checkDeclSPStep_inRange hstepP)
      have hden : denoteDeclP s₀.store pd = some d :=
        denoteDeclP_mono hwf hext0 hd0
      rw [hfe] at hstepP
      obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
        checkDeclSPStep_run m.base.wf hres hden hstepP
      by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
          pd = DeclP.thmDecl cvp value
      · have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                hint) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve := by
          rcases hdis with ⟨hint, rfl⟩ | rfl
          · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
              Option.map_eq_some_iff] at hd0
            obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
            rw [hty] at hty'
            cases hty'
            exact ⟨ve, .inl ⟨hint, rfl⟩⟩
          · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
              Option.map_eq_some_iff] at hd0
            obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
            rw [hty] at hty'
            cases hty'
            exact ⟨ve, .inr rfl⟩
        obtain ⟨ve, hdd⟩ := hdd
        have hfin : ((d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                (.regular 0) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve) ∨
            (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                hint)) →
            False := by
          intro hcase
          have hstores : ∃ type, annotateCore μ fe.env F 0
                (.const emptyName []) = .ok type ∧
              ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
                ⟨cvp.name, cvp.levelParams, type⟩ := by
            rcases hcase with hdis' | ⟨hint, hdis'⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ :=
                checkDecl_stores hF hdis'
              exact ⟨type, hann, c, hc, hcv⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF
                (Or.inl hdis')
              exact ⟨type, hann, c, hc, hcv⟩
          obtain ⟨type, hann, c, hc, hcv⟩ := hstores
          obtain rfl : Expr.const emptyName [] = type :=
            annotate_empty_const_eq hann
          obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d)
            hstep m hE hF).1
          exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
        rcases hdd with ⟨hint, rfl⟩ | rfl
        · exact hfin (.inr ⟨hint, rfl⟩)
        · exact hfin (.inl (.inr rfl))
      · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
            DeclP.thmDecl cvp value ∈ pds := by
          rcases hd with ⟨hint, hdm2⟩ | hdm2
          · rcases List.mem_cons.mp hdm2 with heq | hmem
            · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
            · exact .inl ⟨hint, hmem⟩
          · rcases List.mem_cons.mp hdm2 with heq | hmem
            · exact absurd (.inr heq.symm) hdis
            · exact .inr hmem
        exact ih fe₁ hfe₁
          (checkDecl_sound_R2 (d := d) hstep m hE hF)
          hres₁ (hext0.trans hext₁) h hd'

/-! ## The three sweeps

**1. Smallest fuel.**  No statement here asserts a `denote2` success;
the annotated existence facts all sit inside `EnvS2U`'s fields, whose
uniqueness form was frozen at seal 36 precisely so that none of them
is a conclusion.

**2. Vacuity — the honest reading.**  Every theorem here is
conditional on `DeclStep2All`, which **nothing in this tree
inhabits**, and behind which sits `CheckStep2E`, which nothing
inhabits either.  So none of these statements is usable today, and
saying so is the point: the sequencing seal 39 adopted is *conditional
now, unconditional at junction closure*, and this file is what
"conditional now" looks like when written down.

Two consequences worth separating:

* the five carrier-strengthening results
  (`checkDecl_sound_R2`, the four `checkDecls*_sound_R2`) would say
  something new the moment `DeclStep2All` lands;
* the eight `no_proof_of_Empty*_R2` would not — v1 already proves
  their conclusions unconditionally.  They are a route check.

**3. Tombstones.**  A file added, none edited; `Main.lean`'s fourteen
are byte-identical and still hypothesis-free. -/

end Setlec.SetR
