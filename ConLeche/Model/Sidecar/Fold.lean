module

public import ConLeche.Model.Sidecar.Justified
public import ConLeche.Model.DeclsRun
import ConLeche.Verify.Cached.JustifyBridge
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Model.Modular.Valid
import ConLeche.Model.Inductives.BlockRunFacts
import ConLeche.Semantics.DeclWF
import ConLeche.Semantics.Bridge.DeclRun

public section

/-!
# The input's fold, with a sidecar

The input's accepted fold with the sidecar `JS` carries a covered model whose leaves on every
shared name (`Shared`) are the renamed sidecar model's: a record whose names are shared takes
the sidecar's leaves (`sharedStep`), a justified axiom the sidecar's value (`justStep`), any other
record its own step (`declStep_agrees`).  A record has all its names shared or none: its names
are each other's mates (`recordMates`), and the justification's cone follows a name's mates.
-/

namespace ConLeche.Model.Sidecar

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify
open ConLeche.Semantics

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}

/-- **Every stored constant's laws read stored names.** -/
@[expose] def ScopedE (E : Env) : Prop :=
  ∀ n ci, E.find? n = some ci → EntryScopedP (fun d => (E.find? d).isSome = true) E n ci

/-! ## Records -/

/-- A record other than an inductive block installs at most one constant. -/
theorem declConstants_single {pd : Declaration} (hk : ∀ block nP, pd ≠ .indDecl block nP)
    {c c' : ConstantInfo} (hc : c ∈ declConstants pd) (hc' : c' ∈ declConstants pd) : c = c' := by
  cases pd with
  | indDecl block nP => exact absurd rfl (hk block nP)
  | axiomDecl cv =>
    simp only [declConstants] at hc hc'
    by_cases h1 : cv.name = quotSoundName
    · simp only [h1, ↓reduceIte, List.mem_singleton] at hc hc'; rw [hc, hc']
    · by_cases h2 : cv.name = sorryAxName
      · simp only [h2, ↓reduceIte] at hc; exact absurd hc List.not_mem_nil
      · simp only [h1, h2, ↓reduceIte, List.mem_singleton] at hc hc'; rw [hc, hc']
  | _ =>
    simp only [declConstants, List.mem_singleton] at hc hc'
    rw [hc, hc']

/-- **A record's names are each other's mates**, where the sidecar's mates hold its blocks. -/
theorem record_mates {JS : Sidecar} {pd : Declaration}
    (hmat : ∀ block nP, pd = .indDecl block nP → ∀ b ∈ block, ∀ b' ∈ block,
      b'.name ∈ JS.mates.getD b.name #[])
    {c c' : ConstantInfo} (hc : c ∈ declConstants pd) (hc' : c' ∈ declConstants pd) :
    c = c' ∨ c'.name ∈ JS.mates.getD c.name #[] := by
  by_cases hk : ∃ block nP, pd = .indDecl block nP
  · right
    obtain ⟨block, nP, rfl⟩ := hk
    simp only [declConstants] at hc hc'
    split at hc
    · next p hp =>
      rw [hp] at hc'
      obtain ⟨b, hb, hbn⟩ := blockConstants_names_mem hp c.name (List.mem_map_of_mem hc)
      obtain ⟨b', hb', hbn'⟩ := blockConstants_names_mem hp c'.name (List.mem_map_of_mem hc')
      rw [← hbn, ← hbn']
      exact hmat block nP rfl b hb b' hb'
    · exact absurd hc List.not_mem_nil
  · exact .inl (declConstants_single (fun b n h => hk ⟨b, n, h⟩) hc hc')

/-- **A record's names are all shared or none.** -/
theorem record_shared {JS : Sidecar} {Ef : Env} {pd : Declaration}
    (hmat : ∀ block nP, pd = .indDecl block nP → ∀ b ∈ block, ∀ b' ∈ block,
      b'.name ∈ JS.mates.getD b.name #[])
    (hst : ∀ c ∈ declConstants pd, Ef.find? c.name = some c)
    {c c' : ConstantInfo} (hc : c ∈ declConstants pd) (hc' : c' ∈ declConstants pd)
    (hs : Shared JS Ef c.name) : Shared JS Ef c'.name := by
  rcases record_mates hmat hc hc' with rfl | hm
  · exact hs
  · exact (shared_closed JS Ef c.name hs).2 c (hst c hc) c'.name
      (entryNeeds_mates JS.mates Ef.findTable? (by rw [cv_name_eq]; exact hm))

/-- A stream's former's constructors are stored. -/
theorem stream_ctors {L : List Declaration} {d : Name} {cv : ConstantVal} {caps : IndCaps}
    (hnd : NodupNames (streamEnv L)) (h : (streamEnv L).find? d = some (.indInfo cv caps)) :
    ∀ x ∈ caps.ctors, ((streamEnv L).find? x).isSome = true := by
  intro x hx
  obtain ⟨e, he, hci, -⟩ := streamEnv_find?_some h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (declConstants_ctors hci x hx)
  rw [streamEnv_find?_of_mem hnd he hc]; rfl

/-! ## The fold -/

/-- **The input's fold, with the sidecar** (see the module docstring). -/
theorem sideFold {JS : Sidecar} {envS Ef : Env} (hJ : JS.idx = mkFEnv envS)
    (mS : EnvModelM V (renEnv Ef envS)) (hcovS : LfpCover mS []) (hNS : NatFacts (renEnv Ef envS))
    (hPLS : ProofLeaves V (renEnv Ef envS) mS.base2.acval)
    (htS : ∀ t ∈ envS.tables, envS.findTable? t.structName = some t ∧
      ∃ cv caps, envS.find? t.structName = some (.indInfo cv caps))
    (hsc : ∀ {pd : Declaration} {p q : Nat × FEnv},
      declStep .verified pins maxNatSize (some JS) p pd = .ok q →
      p.2 = mkFEnv p.2.env → EnvWF p.2.env → ScopedE p.2.env → ScopedE q.2.env) :
    ∀ {ds : List Declaration} {p q : Nat × FEnv},
      DeclsRun .verified pins maxNatSize (some JS) ds p q → q.2.env = Ef →
      (∀ pd ∈ ds, ∀ block nP, pd = .indDecl block nP → ∀ b ∈ block, ∀ b' ∈ block,
        b'.name ∈ JS.mates.getD b.name #[]) →
      ∀ {L : List Declaration} {E : Env}, E = streamEnv L → p.2 = mkFEnv E → NodupNames E →
      ScopedE E → ∀ mp : EnvModelM V E, LfpCover mp [] → NatFacts E →
      (∀ x, (E.find? x).isSome = true → Shared JS Ef x → mp.base2.acval x = mS.base2.acval x) →
      ∃ mq : EnvModelM V Ef, LfpCover mq [] := by
  intro ds p q hrun
  induction hrun with
  | nil p =>
    intro hq _ L E _ hp _ _ mp hcov _ _
    rw [hp] at hq
    subst hq
    exact ⟨mp, hcov⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hq hmat L E hL hp hnd hscE mp hcov hN hagree
    obtain ⟨fe₁, s₁, rfl, hC⟩ := declStep_ok hstep
    have hpE : p.2.env = E := by rw [hp]; rfl
    have hscE₁ : ScopedE fe₁.env :=
      hsc hstep (by rw [hp]; rfl) (hpE ▸ mp.base2.wf) (hpE ▸ hscE)
    rw [hp] at hC
    have hch1 : PushChain E fe₁ :=
      checkRecordC_push .verified (some JS) (PushChain.refl E) pd _ fe₁ s₁ hC
    have hchR : PushChain fe₁.env q.2 := declsRun_chain .verified rest (PushChain.self hch1.1)
    have hfe₁ : fe₁.env = streamEnv (L ++ [pd]) := by
      have h₁ := checkRecordC_pushes (pins := pins) .verified (some JS) (mkFEnv E) pd _ fe₁ s₁ hC
      simp only at h₁
      rw [h₁, pushDelta_env, ← streamEnv_append, hL]
      rfl
    have hnd₁ : NodupNames fe₁.env := hch1.2.2.1 hnd
    have hwf₁ : EnvWF fe₁.env :=
      declsRun_envWF (DeclsRun.cons hstep (.nil _)) (by rw [hp]; rfl) (hpE ▸ mp.base2.wf)
    have hEF : ∀ x ci, fe₁.env.find? x = some ci → Ef.find? x = some ci := by
      intro x ci h
      rw [← hq, pushChain_find_old hchR (by rw [h]; rfl), h]
    have hEFt : ∀ x, (fe₁.env.find? x).isSome = true → Ef.findTable? x = fe₁.env.findTable? x :=
      fun x h => by rw [← hq]; exact pushChain_table_old hchR h
    have hEE₁ : ∀ x ci, E.find? x = some ci → fe₁.env.find? x = some ci := fun x ci h => by
      rw [pushChain_find_old hch1 (by rw [h]; rfl), h]
    have hEE₁t : ∀ x, (E.find? x).isSome = true → fe₁.env.findTable? x = E.findTable? x :=
      fun x h => pushChain_table_old hch1 h
    -- the new names are the record's
    have hnew : ∀ x, (fe₁.env.find? x).isSome = true → (E.find? x).isSome = false →
        ∃ c ∈ declConstants pd, c.name = x := by
      intro x hx hxo
      have h₁ := checkRecordC_pushes (pins := pins) .verified (some JS) (mkFEnv E) pd _ fe₁ s₁ hC
      simp only at h₁
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      have hm := Env.find?_mem hc
      rw [h₁, pushDelta_env] at hm
      simp only [Env.pushDelta, List.mem_append, List.mem_reverse] at hm
      rcases hm with hm | hm
      · exact ⟨c, hm, Env.find?_name hc⟩
      · exfalso
        have : (E.find? c.name).isSome = true := find?_isSome_of_mem' hm
        rw [Env.find?_name hc] at this
        rw [this] at hxo; exact nomatch hxo
    have hmat₁ := hmat pd List.mem_cons_self
    have hmatR : ∀ pd ∈ ds, _ := fun pd' h => hmat pd' (List.mem_cons_of_mem _ h)
    have hst : ∀ c ∈ declConstants pd, Ef.find? c.name = some c := by
      intro c hc
      have : fe₁.env.find? c.name = some c := by
        rw [hfe₁]
        exact streamEnv_find?_of_mem (hfe₁ ▸ hnd₁) (List.mem_append_right _ List.mem_cons_self) hc
      exact hEF _ _ this
    cases hj : justifiable pd with
    | some cv =>
      obtain ⟨-, hfe, hwhy, hb, F, hrunV⟩ :=
        checkRecordC_justified_run (pins := pins) mp.base2.wf hj (CSOKF.fresh _) hC
      have hwf₂ : EnvWF ⟨.axiomInfo cv :: E.consts, E.tables⟩ := by
        have := hwf₁; rwa [hfe] at this
      have hEf : Ef.find? cv.name = some (.axiomInfo cv) := by
        refine hEF _ _ ?_
        rw [hfe]
        show (ConstantInfo.axiomInfo cv :: E.consts).find? (·.name == cv.name) = _
        simp only [List.find?_cons]
        have : (ConstantInfo.axiomInfo cv).name = cv.name := rfl
        simp [this]
      obtain ⟨mp', hrel, hcov', hN', hleaf⟩ := justStep hJ mp hcov hN mS hPLS hagree
        (fun x ci h => hEF x ci (hEE₁ x ci h))
        (fun x h => (hEFt x (by rw [pushChain_find_old hch1 h]; exact h)).trans (hEE₁t x h))
        hj hwhy hb hrunV hwf₂ hEf
      have hE₁ : fe₁.env = ⟨.axiomInfo cv :: E.consts, E.tables⟩ := by rw [hfe]; rfl
      refine ih hq hmatR (L := L ++ [pd]) (hE₁ ▸ hfe₁) hfe (hE₁ ▸ hnd₁)
        (hE₁ ▸ hscE₁) mp' hcov' hN' fun x hx hsx => ?_
      by_cases hxo : (E.find? x).isSome = true
      · rw [hrel.leaf x hxo]; exact hagree x hxo hsx
      · have hx' : (fe₁.env.find? x).isSome = true := hE₁ ▸ hx
        obtain ⟨c, hc, hcn⟩ := hnew x hx' (by simpa using hxo)
        rw [(justifiable_constants hj).1, List.mem_singleton] at hc
        subst hc
        have hx : cv.name = x := hcn
        subst hx
        exact hleaf hsx
    | none =>
      rw [checkRecordC_own .verified (some JS) (mkFEnv E) hj] at hC
      obtain ⟨-, hcanon, F, hF⟩ := checkDeclStepC_run mp.base2.wf (CSOKF.fresh _) hC
      have hrunD := checkDeclRun_ofEnvFactsK hF
      obtain ⟨⟨mReg, hleafReg, hcovReg, -⟩, hNReg⟩ := declStep_agrees mp hcov hN hrunD
      have hrec : (fe₁.env.find? = (streamEnv (L ++ [pd])).find?) := by rw [hfe₁]
      by_cases hsh : ∃ c ∈ declConstants pd, Shared JS Ef c.name
      · obtain ⟨c, hc, hsc⟩ := hsh
        have hall : ∀ x, (fe₁.env.find? x).isSome = true → (E.find? x).isSome = false →
            Shared JS Ef x := by
          intro x hx hxo
          obtain ⟨c', hc', rfl⟩ := hnew x hx hxo
          exact record_shared hmat₁ hst hc hc' hsc
        have htE : ∀ t ∈ E.tables, E.findTable? t.structName = some t ∧
            ∃ cv caps, E.find? t.structName = some (.indInfo cv caps) := by
          subst hL; exact fun t ht => stream_tables_mem hnd ht
        have hnd₁' : NodupNames (streamEnv (L ++ [pd])) := by rw [← hfe₁]; exact hnd₁
        have htC : ∀ t ∈ fe₁.env.tables, fe₁.env.findTable? t.structName = some t ∧
            ∃ cv caps, fe₁.env.find? t.structName = some (.indInfo cv caps) := by
          rw [hfe₁]; exact fun t ht => stream_tables_mem hnd₁' ht
        obtain ⟨mp', hcov', hN', hold', hnew'⟩ := sharedStep (C := fe₁.env) hJ mp hcov hN mS hcovS
          hNS hagree hEE₁ hEE₁t hEF hEFt hall hnd₁ hscE hscE₁
          (fun d cv caps h x hx => by subst hL; exact stream_ctors hnd h x hx)
          (fun d cv caps h x hx => by rw [hfe₁] at h ⊢; exact stream_ctors hnd₁' h x hx)
          htC htE htS
        refine ih hq hmatR (L := L ++ [pd]) hfe₁ hcanon hnd₁ hscE₁ mp' hcov' hN' fun x hx hsx => ?_
        by_cases hxo : (E.find? x).isSome = true
        · rw [hold' x hxo]; exact hagree x hxo hsx
        · exact hnew' x hx (by simpa using hxo)
      · refine ih hq hmatR (L := L ++ [pd]) hfe₁ hcanon hnd₁ hscE₁ mReg hcovReg hNReg
          fun x hx hsx => ?_
        by_cases hxo : (E.find? x).isSome = true
        · rw [hleafReg x hxo]; exact hagree x hxo hsx
        · obtain ⟨c, hc, rfl⟩ := hnew x hx (by simpa using hxo)
          exact absurd ⟨c, hc, hsx⟩ hsh

end ConLeche.Model.Sidecar
