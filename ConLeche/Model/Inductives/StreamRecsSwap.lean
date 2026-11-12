module

import ConLeche.Verify.Denote
import ConLeche.Model.Swap
public import ConLeche.Verify.Extend.RecsTy
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Verify.Inductives.StreamRecsInv
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.StreamRecsSem
import ConLeche.Model.Levels

public section

/-!
# The stream's recursors, P tier

A block generates its recursors and installs the stream's — the records' types and right-hand
sides — once they agree with the generated ones (`streamRecsCheck`).  The environment holding the
generated ones carries the P invariant (`genRecStage`); `EnvModelM.swapTyP` carries it to the one
holding the stream's with the same leaf valuation (the swap changes no name, no level parameter, no
kind, so `denote` and every guard agree), given the records' types' facts and the ι contract at
them; `blockRecStagedAt_stored` is the stage's form.
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
theorem EnvModelM.swapTyP {env₀ env₃ : Env}
    (mp : EnvModelM V env₀)
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
    ∃ mp₃ : EnvModelM V env₃, mp₃.base2.acval = mp.base2.acval ∧
      mp₃.base2.acval = mp.base2.acval := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapTyList.congrEnv hsw htab
  have hcorr := ConLeche.swapTy_find?_corrEnv hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env₀ ψ d e
        = denote mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denote_swap hcg ψ d e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  -- a pinned `Nat`-operation type: the stored `Bool` entry keeps its
  -- constant value (a swap changes a recursor's rules only)
  have hpinUp : ∀ {c : Name} {ty : Expr}, ConLeche.natOpTyPinned env₀ c ty = true →
      ConLeche.natOpTyPinned env₃ c ty = true := fun h =>
    ConLeche.Verify.natOpTyPinned_of_find (fun ci hf => by
      rcases hcorr ConLeche.boolName with heq | ⟨cv, cv', mI, rP, isK, rules, rules', h₀, h₃, -, -,
          hname, hres⟩
      · exact ⟨ci, by rw [heq]; exact hf, rfl⟩
      · rw [hname] at hres
        exact absurd hres (by decide)) h
  have hsomeOp : ∀ n, (env₃.find? n).isSome = true → (env₀.find? n).isSome = true := by
    intro n hn
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, isK, rules, rules', h₀, h₃, -⟩
    · rw [← heq]; exact hn
    · rw [h₀]; rfl
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
                    ⟨cv, cv', mI, rP, isK, rules, rules', h₀, h₃, -, hlp, -⟩
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
            op_defn := mp.op_defn.of_same hsomeOp
              (fun n cv v hh hf => (hsame _ _ (fun _ _ _ _ _ he => ConstantInfo.noConfusion he)).mpr hf)
            rec_rules := hrecP _ rfl
            reduce_ops := ?_
            tower_ok := ?_
            -- the recorded lfp clauses: the swap touches recursors only,
            -- and keeps every leaf
            lfpBlocks := mp.lfpBlocks
            lfp_ok := mp.lfp_ok_transport
              (fun n ci hf hnr => (hsame n ci hnr).mpr hf)
              (fun _ _ _ _ => rfl)
              (fun ψ d _ _ _ hta => by rw [← denote_swap hcg ψ d]; exact hta)
              (fun _ => ConstsBound.of_isSome fun n h => by rw [← hcg.isSomeEq]; exact h) },
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
      rcases hpair with rfl | ⟨cv2, cv2', mI, rP, isK, rules, rules', rfl, heq, -⟩
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
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL,
      by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hpin, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hpinUp hpin, hlaw⟩
  · -- `eq_law`: `Eq` is stored as an `indInfo`, so it is never swapped
    intro ci p hf hp
    exact mp.eq_law ci p ((hsame eqName ci
      (eqCopy_not_rec (hbp₃ eqName ci hf (by decide)).1)).mp hf) hp
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
      hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩
  · -- `tower_ok` (task #175 wiring W5): a table entry, a former and a
    -- constructor are never recursors, so every lookup the law reads
    -- is unchanged by the swap, and the readings are `hde`
    intro φ
    refine ⟨fun T tbl hf => ?_, fun T i entry hf => ?_⟩
    · -- the table's η law (task #175 W4c): the former's lookup is
      -- unchanged by the swap, and the reading is `hde`
      have hfT0 : env₀.findTable? T = some tbl := by
        rw [hcg.tableEq]; exact hf
      obtain ⟨⟨cvT, capsT, hfT, hlpsT⟩, hetaL⟩ := (mp.tower_ok φ).table T tbl hfT0
      refine ⟨⟨cvT, capsT, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hlpsT⟩, ?_⟩
      intro cvT' capsT' hfT' us hus
      obtain ⟨hlaw', hcoh⟩ := hetaL cvT' capsT' ((hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hfT') us hus
      exact ⟨hlaw', fun he =>
        (hcoh he).transport (fun cvC nPc nFc iT hf₂ => (hsame _ _
          (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf₂)
        (fun cvC nPc nFc iT TCa _ hTCa => by rw [← hde]; exact hTCa) rfl
        (fun _ _ _ => rfl)⟩
    have hfP : env₀.findProj? T i = some entry := by
      rw [hcg.projEq]; exact hf
    obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, cvC, iT, hfC, hlpsC,
      hlaw⟩ := (mp.tower_ok φ).entry T i entry hfP
    refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hlpsT⟩,
      cvC, iT, (hsame _ _
        (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfC, hlpsC,
      fun us hus => ?_⟩
    obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
    exact ⟨⟨Ta, by rw [← hde]; exact hTa, fun ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ hg =>
        hA ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ (hg.imp_left (TowerGuardAt.mono
          (by rw [hsn, (hsame _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hfT])
          (fun _ _ _ _ h => by rw [← hde]; exact h) fun _ h => by rw [← hde]; exact h))⟩,
      ⟨TCa, by rw [← hde]; exact hTCa, hB⟩⟩

/-! ## The stage -/

/-- The generated recursors and the stream's, entry by entry: the same
recursors but for their types and right-hand sides. -/
theorem swapTyList_streamRecs {q : ConLeche.BlockShape} :
    ∀ {m : Nat} {recs : List ConLeche.RecShape}
      {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env₀ env₃ : Env},
      out.length = recs.length →
      (∀ g ∈ out, ConLeche.reservedRecName g.1.name = false) →
      ConLeche.SwapTyList env₀.consts env₃.consts → env₃.tables = env₀.tables →
      ConLeche.SwapTyList (ConLeche.consBlockRecsT q m out env₀).consts
        (ConLeche.consBlockRecsT q m (ConLeche.streamRecs recs out) env₃).consts
  | _, [], [], _, _, _, _, h, _ => h
  | _, [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | m, rc :: recs, g :: out, env₀, env₃, hl, hres, h, ht => by
    simp only [ConLeche.streamRecs, List.zipWith_cons_cons, ConLeche.consBlockRecsT]
    refine swapTyList_streamRecs (m := m + 1) (recs := recs) (out := out)
      (env₀ := ⟨_ :: env₀.consts, env₀.tables⟩) (env₃ := ⟨_ :: env₃.consts, env₃.tables⟩)
      (by simpa using hl) (fun g' hg' => hres g' (List.mem_cons_of_mem _ hg'))
      (ConLeche.SwapTyList.cons (Or.inr ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl,
        hres g List.mem_cons_self⟩) h) ht

/-- A lookup off the new recursors' names is the environment's. -/
theorem find?_consBlockRecsT_of_not_mem {q : ConLeche.BlockShape} {n : Name} :
    ∀ {m : Nat} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env : Env},
      (∀ t ∈ out, t.1.name ≠ n) →
      (ConLeche.consBlockRecsT q m out env).find? n = env.find? n
  | _, [], _, _ => rfl
  | m, t :: out, env, h => by
    simp only [ConLeche.consBlockRecsT]
    rw [find?_consBlockRecsT_of_not_mem (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')),
      ConLeche.Env.find?_cons]
    exact ite_eq_right_iff.mpr fun he => absurd he (h t List.mem_cons_self)

/-- **The semantic content of the stored check** (task #431), at the
stored install `envS` over the generated install `envG` (the same leaf
valuation): the syntactic facts at `envS` other than its
well-formedness (the rules' constructors, the pinned basis, the tables:
unchanged by the swap, `StreamCorr`), the ι contract at the stored
recursors (`recRuleLaw_stored`: fits at the stored type are fits at the
generated one, `storedTy_sem`; the stored right-hand sides read as the
generated ones, `storedRhs_sem`), and the stored types' readings,
gradings and the recursors' leaves in them. -/
theorem storedSwap_sem {envC : Env}
    {q : ConLeche.BlockShape}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {F : Nat}
    (mpG : EnvModelM V (ConLeche.consBlockRecsT q 0 out envC))
    (hlen : out.length = q.recs.length)
    (hnres : ∀ g ∈ out, ConLeche.reservedRecName g.1.name = false)
    -- the reserved names' check (`basisNamesOk`), at the generated recursors
    (hresB : ∀ g ∈ out, ConLeche.reservedBasisNames.contains g.1.name = false)
    (hS : ConLeche.streamRecsCheck (ConLeche.fueledOps .verified F)
      (ConLeche.mkFEnv (ConLeche.consBlockRecsT q 0 out envC)) q.recs out = .ok ()) :
    ConLeche.RecCtorsStored (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC) ∧
    BasisPinnedTT (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
      mpG.base2.acval ∧
    ProjOkT (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC) ∧
    (∀ (m₃ : EnvModel V (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)),
      m₃.acval = mpG.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ) ∧
    (∀ c ∈ (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).consts,
      c ∉ (ConLeche.consBlockRecsT q 0 out envC).consts →
      (∀ ψ : Name → Nat, ∃ ta : Term,
        denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
          ψ 0 c.toConstantVal.type = some ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
          ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
          ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, interp V ρ (mpG.base2.acval c.name ψ) ∈ˢ interp V ρ ta)) := by
  have hsw := swapTyList_streamRecs (q := q) (m := 0) (env₀ := envC) (env₃ := envC)
    hlen hnres (ConLeche.SwapTyList.of_eq _) rfl
  have htab : (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).tables
      = (ConLeche.consBlockRecsT q 0 out envC).tables := by
    rw [consBlockRecsT_tables 0, consBlockRecsT_tables 0]
  have hcg := ConLeche.SwapTyList.congrEnv hsw htab
  have hcorr := ConLeche.swapTy_find?_corrEnv hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
        ψ d e = denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 out envC) ψ d e :=
    fun ψ d e => (denote_swap hcg ψ d e).symm
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      (ConLeche.consBlockRecsT q 0 out envC).find? n = some ci →
      (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).find? n = some ci :=
    fun n ci hnr h => hcg.findUp n ci h hnr
  have hctor : ∀ (c : Name) (cvj : ConstantVal) (cnP cnF : Nat) (iT : Name),
      (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).find? c
        = some (.ctorInfo cvj cnP cnF iT) →
      (ConLeche.consBlockRecsT q 0 out envC).find? c = some (.ctorInfo cvj cnP cnF iT) :=
    fun c cvj cnP cnF iT h => hcg.findDown c _ h (fun _ _ _ _ _ h => ConstantInfo.noConfusion h)
  have hfam : ∀ cvj : ConstantVal,
      ctorTypeFamily
          (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).find? cvj
        = ctorTypeFamily (ConLeche.consBlockRecsT q 0 out envC).find? cvj := by
    intro cvj
    unfold ctorTypeFamily ConLeche.ctorFamily
    cases h : cvj.type.piResult.getAppFn with
    | const T _ =>
      dsimp only
      rcases hcorr T with heq | ⟨cv, cv', mI, rP, isK, rules, rules', h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
    | _ => rfl
  obtain ⟨-, hallS⟩ := ConLeche.streamRecsCheck_inv hS
  let Q : Nat → ConLeche.RecShape → ConstantVal × ConLeche.TargetMajor × List Expr → Prop :=
    fun j rc g => q.recs[j]? = some rc ∧ out[j]? = some g ∧
      ConLeche.streamRecCheck (ConLeche.fueledOps .verified F)
        (ConLeche.mkFEnv (ConLeche.consBlockRecsT q 0 out envC)) rc g = .ok ()
  have hC : ConLeche.StreamCorr q Q
      (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
      (ConLeche.consBlockRecsT q 0 out envC) :=
    ConLeche.StreamCorr.consBlockRecsT (m := 0) hlen
      (fun i rc g hr hg => by
        simp only [Nat.zero_add]; exact ⟨hr, hg, hallS i rc g hr hg⟩)
      (ConLeche.StreamCorr.refl q Q envC)
  -- a stored position's facts
  have hposQ : ∀ {j rc g}, Q j rc g →
      q.majorIdxAt j = rc.mI ∧ (rc.rules.map (·.rhs)).length = g.2.2.length ∧
      (rc.cvR.type = g.1.type ∨ ConLeche.recTyCheck (ConLeche.fueledOps .verified F)
        (ConLeche.mkFEnv (ConLeche.consBlockRecsT q 0 out envC)) g.1.name g.1.levelParams
        (rc.mI + 1) rc.cvR.type g.1.type = .ok ()) ∧
      ConLeche.streamRulesCheck (ConLeche.fueledOps .verified F)
        (ConLeche.mkFEnv (ConLeche.consBlockRecsT q 0 out envC)) g.1.name g.1.levelParams
        rc.rules g.2.2 = .ok () := by
    intro j rc g hQ
    obtain ⟨hrc, -, hck⟩ := hQ
    obtain ⟨-, -, hcmp⟩ := ConLeche.streamRecCheck_inv hck
    obtain ⟨hty, hrules⟩ := ConLeche.streamRecCompare_inv hcmp
    refine ⟨by simp only [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some], by rw [List.length_map]; exact (ConLeche.streamRulesCheck_inv hrules).1,
      hty, hrules⟩
  -- a generated entry's facts
  have hgen : ∀ {j g}, ConLeche.recEntryG q j g ∈ (ConLeche.consBlockRecsT q 0 out envC).consts →
      g.1.type.looseBVarsBounded 0 = true ∧
      (∀ ψ : Name → Nat, ∃ TG, denote mpG.base2.acval (ConLeche.consBlockRecsT q 0 out envC)
        ψ 0 g.1.type = some TG) ∧
      (∀ (ψ : Name → Nat) (TG : Term), denote mpG.base2.acval
        (ConLeche.consBlockRecsT q 0 out envC) ψ 0 g.1.type = some TG →
        ∀ ρ : Nat → V, WellDenotedTy V ρ TG) ∧
      (∀ (ψ : Name → Nat) (TG : Term), denote mpG.base2.acval
        (ConLeche.consBlockRecsT q 0 out envC) ψ 0 g.1.type = some TG →
        ∀ ρ : Nat → V, interp V ρ (mpG.base2.acval g.1.name ψ) ∈ˢ interp V ρ TG) ∧
      ∀ r ∈ ConLeche.generatedRules (q.rulePrefixAt j) g.2.1 g.2.2,
        r.rhs.looseBVarsBounded 0 = true :=
    fun hm => ⟨(mpG.base2.wf.consts _ hm).2.2.2.1, mpG.type_reads _ hm,
      mpG.type_wellDenotedTy _ hm, mpG.mem_type _ hm,
      fun r hr => ((mpG.base2.wf.consts _ hm).2.2.2.2.2 _ _ _ _ _ rfl r hr).2.2.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `RecCtorsStored`
    intro n cv mI rP isK rules hf r hr
    rcases hC.1 n _ hf with hG | ⟨j, rc, g, hQ, -, hG, hci⟩
    · obtain ⟨cvj, cnP, cnF, iT, hfc⟩ := mpG.base2.rec_ctors n cv mI rP isK rules hG r hr
      exact ⟨cvj, cnP, cnF, iT, hkeep _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h) hfc⟩
    · obtain ⟨e1, e2, e3, e5, e4⟩ := ConstantInfo.recInfo.inj hci
      subst e1 e2 e3 e5 e4
      obtain ⟨-, hl, -, -⟩ := hposQ hQ
      obtain ⟨i, rG, hrG, -, -, hreq⟩ := ConLeche.streamRule_corr hl hr
      obtain ⟨cvj, cnP, cnF, iT, hfc⟩ := mpG.base2.rec_ctors n g.1 _ _ _ _ hG rG hrG
      have hc : r.ctor = rG.ctor := by rw [hreq]
      rw [hc]
      exact ⟨cvj, cnP, cnF, iT, hkeep _ _ (fun _ _ _ _ _ h => ConstantInfo.noConfusion h) hfc⟩
  · -- `BasisPinnedTT`: a stored recursor is never reserved
    intro n ci hf hres
    rcases hC.1 n ci hf with hG | ⟨j, rc, g, ⟨-, hg, -⟩, hn, -, -⟩
    · have hp := mpG.base2.basis_pinned n ci hG hres
      exact ⟨hp.1, hp.2.1.mono hctor, hp.2.2⟩
    · have := hresB g (List.mem_of_getElem? hg)
      rw [hn, hres] at this
      exact nomatch this
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf
    exact ConLeche.TableHead.mono hkeep (mpG.base2.proj_ok n tbl ((hcg.tableEq n).trans hf))
  · -- `RecRules`
    intro m₃ hac φ n cv mI rP isK rules hf rl hrl
    rcases hC.1 n _ hf with hG | ⟨j, rc, g, hQ, -, hG, hci⟩
    · have h := mpG.rec_rules φ n cv mI rP isK rules hG rl hrl
      exact recRuleLaw_stored (mG := mpG.base2) (mS := m₃) hac hde hctor hfam (T := cv.type)
        (e := rl.rhs) (fun us _ TS hTS => ⟨TS, hTS, fun ρ xs rest _ hfit => ⟨rest, hfit⟩⟩)
        (fun us hus RaG hRaG => by
          obtain ⟨Ra, hRa, hw, -⟩ := h.2.1 us hus
          obtain rfl := Option.some.inj (hRa.symm.trans hRaG)
          exact ⟨Ra, hRa, fun ρ => ⟨hw ρ, rfl⟩⟩) h
    · obtain ⟨e1, e2, e3, e5, e4⟩ := ConstantInfo.recInfo.inj hci
      subst e1 e2 e3 e5 e4
      obtain ⟨hmI, hl, hty, hrules⟩ := hposQ hQ
      obtain ⟨i, rG, hrG, hiS, hiG, hreq⟩ := ConLeche.streamRule_corr hl hrl
      have hmG := ConLeche.Env.find?_mem hG
      obtain ⟨hGb, hGr, hGw, -, hgb⟩ := hgen hmG
      have h := mpG.rec_rules φ n g.1 _ _ _ _ hG rG hrG
      have hp := mpG.base2.acval_params
      rw [hreq]
      refine recRuleLaw_stored (mG := mpG.base2) (mS := m₃) hac hde hctor hfam ?_ ?_ h
      · intro us hus TS hTS
        rcases hty with htyE | htyC
        · rw [htyE] at hTS
          exact ⟨TS, hTS, fun ρ xs rest _ hfit => ⟨rest, hfit⟩⟩
        · rw [denote_instLevels hp] at hTS ⊢
          obtain ⟨TS', TG, hTS', hTG, -, hEq⟩ := storedTy_sem mpG htyC hGb hGr hGw
            (Level.substFn φ g.1.levelParams us)
          obtain rfl := Option.some.inj (hTS.symm.trans hTS')
          refine ⟨TG, hTG, fun ρ xs rest hxl hfit => TEqAt.fit hfit (hEq ρ) ?_⟩
          rw [← hmI]; exact hxl
      · intro us hus RaG hRaG
        obtain ⟨r0, hr0, hr0e⟩ : ∃ r0, rc.rules[i]? = some r0 ∧ r0.rhs = rl.rhs := by
          rw [List.getElem?_map] at hiS
          cases h0 : rc.rules[i]? with
          | none => rw [h0] at hiS; exact nomatch hiS
          | some r0 => rw [h0] at hiS; exact ⟨r0, rfl, Option.some.inj hiS⟩
        rcases (ConLeche.streamRulesCheck_inv hrules).2 i r0 rG.rhs hr0 hiG with heq | hag
        · rw [← hr0e, heq]
          obtain ⟨Ra, hRa, hw, -⟩ := h.2.1 us hus
          obtain rfl := Option.some.inj (hRa.symm.trans hRaG)
          exact ⟨Ra, hRa, fun ρ => ⟨hw ρ, rfl⟩⟩
        · rw [← hr0e, denote_instLevels hp]
          rw [denote_instLevels hp] at hRaG
          exact storedRhs_sem mpG hag (hgb rG hrG) _ hRaG
  · -- the stored types' facts
    intro c hc hnot
    rcases hC.2 c hc with h | ⟨j, rc, g, hQ, rfl, hmG⟩
    · exact absurd h hnot
    obtain ⟨-, -, hty, -⟩ := hposQ hQ
    obtain ⟨hGb, hGr, hGw, hGm, -⟩ := hgen hmG
    have key : ∀ ψ : Name → Nat, ∃ TS, denote mpG.base2.acval
        (ConLeche.consBlockRecsT q 0 out envC) ψ 0 rc.cvR.type = some TS ∧
        (∀ ρ : Nat → V, WellDenotedTy V ρ TS) ∧
        ∀ ρ : Nat → V, interp V ρ (mpG.base2.acval g.1.name ψ) ∈ˢ interp V ρ TS := by
      intro ψ
      rcases hty with htyE | htyC
      · rw [htyE]
        obtain ⟨TG, hTG⟩ := hGr ψ
        exact ⟨TG, hTG, hGw ψ TG hTG, hGm ψ TG hTG⟩
      · obtain ⟨TS, TG, hTS, hTG, hw, hEq⟩ := storedTy_sem mpG htyC hGb hGr hGw ψ
        exact ⟨TS, hTS, hw, fun ρ => by rw [(hEq ρ).interp_eq]; exact hGm ψ TG hTG ρ⟩
    refine ⟨fun ψ => ?_, fun ψ ta hta ρ => ?_, fun ψ ta hta ρ => ?_⟩
    · obtain ⟨TS, hTS, -, -⟩ := key ψ
      exact ⟨TS, by rw [hde]; exact hTS⟩
    · obtain ⟨TS, hTS, hw, -⟩ := key ψ
      rw [hde] at hta
      obtain rfl := Option.some.inj (hta.symm.trans hTS)
      exact hw ρ
    · obtain ⟨TS, hTS, -, hm⟩ := key ψ
      rw [hde] at hta
      obtain rfl := Option.some.inj (hta.symm.trans hTS)
      exact hm ρ

/-- **The recursors' stage, at the STORED recursors** (task #431): the
generated install's stage facts carried to the install of the stored
recursors. -/
theorem blockRecStagedAt_stored {envC : Env}
    {mpC : EnvModelM V envC} {q : ConLeche.BlockShape}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {F : Nat}
    (hG : BlockRecStagedAt envC (ConLeche.consBlockRecsT q 0 out envC) mpC)
    (hlen : out.length = q.recs.length)
    (hfr : ∀ g ∈ out, envC.find? g.1.name = none)
    (hnres : ∀ g ∈ out, ConLeche.reservedRecName g.1.name = false)
    -- the reserved names' check (`basisNamesOk`), at the generated recursors
    (hresB : ∀ g ∈ out, ConLeche.reservedBasisNames.contains g.1.name = false)
    (hS : ConLeche.streamRecsCheck (ConLeche.fueledOps .verified F)
      (ConLeche.mkFEnv (ConLeche.consBlockRecsT q 0 out envC)) q.recs out = .ok ())
    (hwfS : EnvWF (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)) :
    BlockRecStagedAt envC (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC)
      mpC := by
  obtain ⟨mpG, hag, -, hden⟩ := hG
  have hsw := swapTyList_streamRecs (q := q) (m := 0) (env₀ := envC) (env₃ := envC)
    hlen hnres (ConLeche.SwapTyList.of_eq _) rfl
  have htab : (ConLeche.consBlockRecsT q 0 (ConLeche.streamRecs q.recs out) envC).tables
      = (ConLeche.consBlockRecsT q 0 out envC).tables := by
    rw [consBlockRecsT_tables 0, consBlockRecsT_tables 0]
  obtain ⟨hctors, hbp, hproj, hrecP, htyS⟩ := storedSwap_sem mpG hlen hnres hresB hS
  obtain ⟨mpS, hac, -⟩ := EnvModelM.swapTyP mpG hsw htab hwfS hctors hbp hproj hrecP htyS
  have hcg := ConLeche.SwapTyList.congrEnv hsw htab
  have hnm : ∀ n, (envC.find? n).isSome = true → ∀ t ∈ ConLeche.streamRecs q.recs out,
      t.1.name ≠ n := by
    intro n hn t ht he
    obtain ⟨g, hg, hgn, -⟩ := ConLeche.mem_streamRecs ht
    rw [hgn] at he
    rw [← he, hfr g hg] at hn
    exact nomatch hn
  refine ⟨mpS, fun n hn => by rw [hac]; exact hag n hn, fun n c hc => ?_, fun ψ dd e hcb => ?_⟩
  · rw [find?_consBlockRecsT_of_not_mem (hnm n (by rw [hc]; rfl))]
    exact hc
  · rw [hac, ← denote_swap hcg ψ dd e]
    exact hden ψ dd e hcb

end ConLeche.Model
