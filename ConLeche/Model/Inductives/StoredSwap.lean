module

import ConLeche.Verify.Denote.EnvExt
import ConLeche.Verify.Denote
import ConLeche.Model.Swap
public import ConLeche.Model.IndPinGrade
public import ConLeche.Verify.Extend.RecsTy
public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Verify.Inductives.StoredRecsInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockCover

public section

/-!
# The stored recursors installed, P tier (task #431)

The block install generates its recursors and installs the STORED ones
— the records' types and right-hand sides — once they agree with the
generated ones (`storedRecsCheck`).  The generated install carries the
P invariant (`genRecStage`); `EnvModelM.swapTyP` carries it to the
stored install with the same leaf valuation (the swap changes no name,
no level parameter, no kind, so `denote` and every guard agree), given
the stored types' facts and the ι contract at the stored recursors;
`blockRecStagedAt_stored` is the stage's form.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 3200000 in
/-- **The stored recursors' swap, P tier** (task #431): an invariant
of the generated install transports to the install carrying the STORED
recursors (other types, other right-hand sides, the same names, level
parameters and kinds), with the *same* leaf valuation.  As the rule-list
swap (`EnvModelM.swapP`), plus the stored types' three facts (`htyS`). -/
theorem EnvModelM.swapTyP {μ : CheckMode} {env₀ env₃ : Env}
    (mp : EnvModelM V μ env₀)
    (hsw : ConLeche.SwapTyList env₀.consts env₃.consts)
    (htab : env₃.tables = env₀.tables)
    -- the four syntactic environment facts at the swapped
    -- environment: taking them rather than rebuilding them keeps this
    -- file free of the rule facts
    (hwf₃ : EnvWF env₃) (hctors₃ : ConLeche.RecCtorsStored env₃)
    (hbp₃ : BasisPinnedTT env₃ mp.base2.acval)
    (hproj₃ : ProjOkT env₃)
    (hrecP : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval →
      ∀ φ : Name → Nat, RecRules m₃ φ)
    -- the stored types' facts, at every constant not stored before
    (htyS : ∀ c ∈ env₃.consts, c ∉ env₀.consts →
      (∀ ψ : Name → Nat, ∃ ta : Term,
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp.base2.acval env₃ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, interp V ρ (mp.base2.acval c.name ψ) ∈ˢ interp V ρ ta)) :
    ∃ mp₃ : EnvModelM V μ env₃, mp₃.base2.acval = mp.base2.acval ∧
      mp₃.base2.acval = mp.base2.acval := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapTyList.congrEnv hsw htab
  have hcorr := ConLeche.swapTy_find?_corrEnv hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env₀ ψ d e
        = denote mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denote_swap hcg ψ d e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  -- a pinned `Nat`-operation type: the stored `Bool` entry keeps its
  -- constant value (a swap changes a recursor's rules only)
  have hpinUp : ∀ {c : Name} {ty : Expr}, ConLeche.natOpTyPinned env₀ c ty = true →
      ConLeche.natOpTyPinned env₃ c ty = true := fun h =>
    ConLeche.Verify.natOpTyPinned_of_find (fun ci hf => by
      rcases hcorr ConLeche.boolName with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -, -,
          hname, hres⟩
      · exact ⟨ci, by rw [heq]; exact hf, rfl⟩
      · rw [hname] at hres
        exact absurd hres (by decide)) h
  refine ⟨{ base2 :=
              { wf := hwf₃
                acval := mp.base2.acval
                cval_closed := fun n ψ => mp.base2.cval_closed n ψ
                basis_pinned := hbp₃
                proj_ok := hproj₃
                rec_ctors := hctors₃
                acval_params := by
                  intro n ci hf ψ₁ ψ₂ hp
                  rcases hcorr n with heq |
                    ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -, hlp, -⟩
                  · exact mp.base2.acval_params n ci
                      (by rw [← heq]; exact hf) ψ₁ ψ₂ hp
                  · rw [h₃] at hf
                    obtain rfl := Option.some.inj hf
                    exact mp.base2.acval_params n _ h₀ ψ₁ ψ₂
                      (by simpa [ConstantInfo.toConstantVal, hlp] using hp)
                acval_wellDenoted := mp.base2.acval_wellDenoted }
            type_reads := ?_
            type_wellDenotedTy := ?_
            mem_type := ?_
            defn_reads := ?_
            nat_heads := ?_
            nat_ops := ?_
            div_mod := ?_
            eq_law := ?_
            caps_ok := ?_
            rec_rules := hrecP _ rfl
            reduce_ops := ?_
            tower_ok := ?_
            -- the formers are never swapped, and keep their readings
            ind_strict := fun I cv caps hf ψ ab n hread =>
              mp.ind_strict I cv caps
                ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
                ψ ab n (by rw [hde]; exact hread)
            -- the recorded lfp clauses: the swap touches recursors only,
            -- and keeps every leaf
            lfpBlocks := mp.lfpBlocks
            lfp_ok := mp.lfp_ok_transport
              (fun n ci hf hnr => (hsame n ci hnr).mpr hf)
              (fun _ _ _ _ => rfl)
              (fun _ _ _ _ ψ _ hta => by rw [← denote_swap hcg ψ 0]; exact hta)
              (fun _ _ _ _ _ ψ _ hta => by rw [← denote_swap hcg ψ 0]; exact hta)
              (fun _ _ _ _ _ _ ψ _ _ hta => by rw [← denote_swap hcg ψ _]; exact hta) },
          rfl, rfl⟩
  · -- `type_reads`
    intro c hc ψ
    by_cases h₀ : c ∈ env₀.consts
    · obtain ⟨ta, hta⟩ := mp.type_reads c h₀ ψ
      exact ⟨ta, by rw [← hde]; exact hta⟩
    · exact (htyS c hc h₀).1 ψ
  · -- `type_wellDenotedTy`
    intro c hc ψ ta hta ρ
    by_cases h₀ : c ∈ env₀.consts
    · rw [← hde] at hta
      exact mp.type_wellDenotedTy c h₀ ψ ta hta ρ
    · exact (htyS c hc h₀).2.1 ψ ta hta ρ
  · -- `mem_type`
    intro c hc ψ ta hta ρ
    by_cases h₀ : c ∈ env₀.consts
    · rw [← hde] at hta
      exact mp.mem_type c h₀ ψ ta hta ρ
    · exact (htyS c hc h₀).2.2 ψ ta hta ρ
  · -- `defn_reads`
    intro ψ cv value hmem
    have hmem₀ : ∃ hint : ConLeche.ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env₀.consts := by
      obtain ⟨hint, hd⟩ := hmem
      obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapTy_mem_corr hsw _ hd
      rcases hpair with rfl | ⟨cv2, cv2', mI, rP, rules, rules', rfl, heq, -⟩
      · exact ⟨hint, hc₀⟩
      · exact nomatch heq
    rw [← hde]
    exact mp.defn_reads ψ cv value hmem₀
  · -- `nat_heads`
    intro φ hsup ρ
    exact mp.nat_heads φ (hcg.natEq ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.nat_ops φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL,
      by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, hlaw⟩
  · -- `eq_law`: `Eq` is stored as an `indInfo`, so it is never swapped
    intro hf
    exact mp.eq_law
      ((hsame eqName eqA
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- `caps_ok`
    obtain ⟨he, hu⟩ := mp.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        ConLeche.EtaFamilyStored env₃ T caps →
        ConLeche.EtaFamilyStored env₀ T caps := by
      intro T caps hst
      obtain ⟨h1, ⟨cvC, cnP, cnF, hC⟩, h3⟩ := hst
      exact ⟨h1, ⟨cvC, cnP, cnF, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hC⟩, h3⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw, hcoh⟩ :=
        he T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres (hfam T caps hfamS) φ' us hus
      refine ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw,
        hcoh.transport (fun cvC nPc nFc hf₂ => (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf₂)
        (fun cvC nPc nFc TCa _ hTCa => by rw [← hde]; exact hTCa) rfl
        (fun _ _ _ => rfl)⟩
    · intro T cvT caps hf hcap hres φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
        hu T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres φ' us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw⟩
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
      hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩
  · -- `tower_ok` (task #175 wiring W5): a table entry, a former and a
    -- constructor are never recursors, so every lookup the law reads
    -- is unchanged by the swap, and the readings are `hde`
    intro φ T i entry hf
    have hfP : env₀.findProj? T i = some entry := by
      rw [hcg.projEq]; exact hf
    obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, hO5, cvC, hfC, hlpsC,
      hlaw, hetaL⟩ := mp.tower_ok φ T i entry hfP
    refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hlpsT⟩,
      hO5, cvC, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfC, hlpsC,
      fun us hus => ?_, ?_⟩
    · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
      exact ⟨⟨Ta, by rw [← hde]; exact hTa, hA⟩,
        ⟨TCa, by rw [← hde]; exact hTCa, hB⟩⟩
    · -- (C) the η law (task #175 W4c): the former's lookup is unchanged
      -- by the swap, and the reading is `hde`
      intro cvT' capsT' hfT' us hus
      obtain ⟨TVa, hTVa, hok, hlaw', hcoh⟩ := hetaL cvT' capsT' ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hfT') us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hok, hlaw', fun he =>
        (hcoh he).transport (fun cvC nPc nFc hf₂ => (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf₂)
        (fun cvC nPc nFc TCa _ hTCa => by rw [← hde]; exact hTCa) rfl
        (fun _ _ _ => rfl)⟩

/-! ## The stage -/

/-- The generated and the stored install, entry by entry: the same
recursors but for their types and right-hand sides. -/
theorem swapTyList_storedOut {f : Name → Option ConstantInfo} {q : ConLeche.BlockShape} :
    ∀ {m : Nat} {recs : List ConLeche.RecShape}
      {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env₀ env₃ : Env},
      out.length = recs.length →
      (∀ g ∈ out, ConLeche.reservedRecName g.1.name = false) →
      ConLeche.SwapTyList env₀.consts env₃.consts → env₃.tables = env₀.tables →
      ConLeche.SwapTyList (ConLeche.consBlockRecsT f q m out env₀).consts
        (ConLeche.consBlockRecsT f q m (ConLeche.storedOut recs out) env₃).consts
  | _, [], [], _, _, _, _, h, _ => h
  | _, [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | m, rc :: recs, g :: out, env₀, env₃, hl, hres, h, ht => by
    simp only [ConLeche.storedOut, List.zipWith_cons_cons, ConLeche.consBlockRecsT]
    refine swapTyList_storedOut (m := m + 1) (recs := recs) (out := out)
      (env₀ := ⟨_ :: env₀.consts, env₀.tables⟩) (env₃ := ⟨_ :: env₃.consts, env₃.tables⟩)
      (by simpa using hl) (fun g' hg' => hres g' (List.mem_cons_of_mem _ hg'))
      (ConLeche.SwapTyList.cons (Or.inr ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl,
        hres g List.mem_cons_self⟩) h) ht

/-- A lookup off the new recursors' names is the environment's. -/
theorem find?_consBlockRecsT_of_not_mem {f : Name → Option ConstantInfo}
    {q : ConLeche.BlockShape} {n : Name} :
    ∀ {m : Nat} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env : Env},
      (∀ t ∈ out, t.1.name ≠ n) →
      (ConLeche.consBlockRecsT f q m out env).find? n = env.find? n
  | _, [], _, _ => rfl
  | m, t :: out, env, h => by
    simp only [ConLeche.consBlockRecsT]
    rw [find?_consBlockRecsT_of_not_mem (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')),
      ConLeche.Env.find?_cons]
    exact ite_eq_right_iff.mpr fun he => absurd he (h t List.mem_cons_self)

/-- **The semantic content of the stored check** (task #431), at the
stored install `envS` over the generated install `envG` (the same leaf
valuation): the stored types read, are graded types and hold the
recursors' leaves (from `recTyCheck`: the stored type checked, its
domains and residue definitionally the generated ones', `paramFrames`);
the ι contract at the stored recursors (`RecRuleLaw` carried from the
generated rules: fits at the stored type are fits at the generated one,
the stored right-hand sides read as the generated ones — `ruleAgree`'s
two defeq claims); and the syntactic facts at `envS` (its well-formedness —
`storedRecs_recsWF` at the generated stage's run —, the rules'
constructors, the pinned basis, the tables: unchanged by the swap).

**#431 cont.: OPEN** — the one proof obligation left on the branch;
its statement is the stage's need, its proof the plan of DESIGN #431 §3. -/
theorem storedSwap_sem {μ : CheckMode} (hμ : μ.isVerified = true) {envC : Env}
    {f : Name → Option ConstantInfo} {q : ConLeche.BlockShape} {recs : List ConLeche.RecShape}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {F : Nat}
    (mpG : EnvModelM V μ (ConLeche.consBlockRecsT f q 0 out envC))
    (hS : ConLeche.storedRecsCheck id (ConLeche.fueledOps μ F) .plain
      (ConLeche.mkFEnv (ConLeche.consBlockRecsT f q 0 out envC)) recs out = .ok ()) :
    EnvWF (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC) ∧
    ConLeche.RecCtorsStored (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC) ∧
    BasisPinnedTT (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)
      mpG.base2.acval ∧
    ProjOkT (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC) ∧
    (∀ (m₃ : EnvModel V (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)),
      m₃.acval = mpG.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ) ∧
    (∀ c ∈ (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC).consts,
      c ∉ (ConLeche.consBlockRecsT f q 0 out envC).consts →
      (∀ ψ : Name → Nat, ∃ ta : Term,
        denote mpG.base2.acval (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)
          ψ 0 c.toConstantVal.type = some ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mpG.base2.acval (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)
          ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mpG.base2.acval (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)
          ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, interp V ρ (mpG.base2.acval c.name ψ) ∈ˢ interp V ρ ta)) := by
  sorry

/-- **The recursors' stage, at the STORED recursors** (task #431): the
generated install's stage facts carried to the install of the stored
recursors. -/
theorem blockRecStagedAt_stored {μ : CheckMode} (hμ : μ.isVerified = true) {envC : Env}
    {mpC : EnvModelM V μ envC} {f : Name → Option ConstantInfo} {q : ConLeche.BlockShape}
    {recs : List ConLeche.RecShape} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)}
    {F : Nat}
    (hG : BlockRecStagedAt μ envC (ConLeche.consBlockRecsT f q 0 out envC) mpC)
    (hlen : out.length = recs.length)
    (hfr : ∀ g ∈ out, envC.find? g.1.name = none)
    (hnres : ∀ g ∈ out, ConLeche.reservedRecName g.1.name = false)
    (hS : ConLeche.storedRecsCheck id (ConLeche.fueledOps μ F) .plain
      (ConLeche.mkFEnv (ConLeche.consBlockRecsT f q 0 out envC)) recs out = .ok ()) :
    BlockRecStagedAt μ envC (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC)
      mpC := by
  obtain ⟨mpG, hag, -, hden⟩ := hG
  have hsw := swapTyList_storedOut (f := f) (q := q) (m := 0) (env₀ := envC) (env₃ := envC)
    hlen hnres (ConLeche.SwapTyList.of_eq _) rfl
  have htab : (ConLeche.consBlockRecsT f q 0 (ConLeche.storedOut recs out) envC).tables
      = (ConLeche.consBlockRecsT f q 0 out envC).tables := by
    rw [consBlockRecsT_tables 0, consBlockRecsT_tables 0]
  obtain ⟨hwfS, hctors, hbp, hproj, hrecP, htyS⟩ := storedSwap_sem hμ mpG hS
  obtain ⟨mpS, hac, -⟩ := EnvModelM.swapTyP mpG hsw htab hwfS hctors hbp hproj hrecP htyS
  have hcg := ConLeche.SwapTyList.congrEnv hsw htab
  have hnm : ∀ n, (envC.find? n).isSome = true → ∀ t ∈ ConLeche.storedOut recs out,
      t.1.name ≠ n := by
    intro n hn t ht he
    obtain ⟨g, hg, hgn, -⟩ := ConLeche.mem_storedOut ht
    rw [hgn] at he
    rw [← he, hfr g hg] at hn
    exact nomatch hn
  refine ⟨mpS, fun n hn => by rw [hac]; exact hag n hn, fun n c hc => ?_, fun ψ dd e hcb => ?_⟩
  · rw [find?_consBlockRecsT_of_not_mem (hnm n (by rw [hc]; rfl))]
    exact hc
  · rw [hac, ← denote_swap hcg ψ dd e]
    exact hden ψ dd e hcb

end ConLeche.Model
