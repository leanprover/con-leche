module

public import InLeanProof.PassRecs6

/-!
# O7-recursors: the recursor stage composed (task #451, lane O7-recursors, round 6)

* `targetRecPins_not_sorryAx`: every recursor name the pins accept is a
  member's `T.rec` or the block's `T.rec_i`, so none is `sorryAx`.
* `genRecCheckI_run`: InLean's `genRecCheck` (the twin of `genRecCheckC`)
  against master's at `fueledOpsM .verified`, from the
  earlier rounds' pieces in the stage's order.
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## The recursor names are not `sorryAx` -/

theorem str_rec_ne_sorryAx (n : Lean.Name) : n.str "rec" ≠ InLean.sorryAxName := by
  intro h; unfold InLean.sorryAxName at h; injection h with _ h2; simp at h2

theorem str_recI_ne_sorryAx (n : Lean.Name) (i : Nat) :
    n.str (toString "rec_" ++ toString (i + 1)) ≠ InLean.sorryAxName := by
  intro h; unfold InLean.sorryAxName at h; injection h with _ h2
  rw [show toString "rec_" = "rec_" from rfl] at h2
  have := congrArg (fun s : String => s.toList.head?) h2
  simp at this

/-- **No recursor the pins accept is named `sorryAx`**: a member's own
recursor is `T.rec` (`blockRecNameSetOk`), an auxiliary one `T.rec_i`. -/
theorem targetRecPins_not_sorryAx {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s₀ s' : InLean.CState} {u : Unit} (h : InLean.targetRecPins p block s₀ = .ok (u, s')) :
    ∀ rc ∈ p.recs, rc.cvR.name ≠ InLean.sorryAxName := by
  unfold InLean.targetRecPins at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok (u, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : InLean.blockRecLpsOk p <;> simp only [g1] at h
  · exact absurd h hth
  cases g2 : InLean.blockRecNamesUnreserved p <;> simp only [g2, ↓reduceIte] at h
  · exact absurd h hth
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g3
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g4
  intro rc hrc
  by_cases ht : rc.tgt < p.k
  · simp only [InLean.blockRecNameSetOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
      List.mem_map, List.mem_filter] at g3
    obtain ⟨ms, -, hn⟩ := g3.2 _ ⟨rc, ⟨hrc, by simpa using ht⟩, rfl⟩
    rw [← hn]; exact str_rec_ne_sorryAx _
  · simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_map,
      List.mem_filter, List.mem_range] at g4
    obtain ⟨i, -, hn⟩ := g4.2 _ ⟨rc, ⟨hrc, by simpa using ht⟩, rfl⟩
    rw [← hn]; exact str_recI_ne_sorryAx _ _

/-! ## The stage -/

theorem genCVs_okC : ∀ {xs : List Lean.ConstantVal} {rcs : List InLean.RecShape}, GenCVs xs rcs →
    ∀ x ∈ xs, okC x.type = true
  | _, _, .nil => fun _ h => by cases h
  | _, _, .cons hx hxs => fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx.2.1
    · exact genCVs_okC hxs y hy

theorem genCVs_closed : ∀ {xs : List Lean.ConstantVal} {rcs : List InLean.RecShape}, GenCVs xs rcs →
    ∀ x ∈ xs, okC x.type = true ∧ (trC x.type).looseBVarsBounded 0 = true
  | _, _, .nil => fun _ h => by cases h
  | _, _, .cons hx hxs => fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx.2
    · exact genCVs_closed hxs y hy

theorem mem_nfs_nil {v Ms : List InLean.TargetMajor}
    (h : v.map (fun M => { M with nfs := [] }) = Ms) {M : InLean.TargetMajor} (hM : M ∈ v) :
    { M with nfs := [] } ∈ Ms := h ▸ List.mem_map_of_mem hM

theorem okSL_of_okC (s : InLean.CState) {l : List Lean.Expr} (h : ∀ e ∈ l, okC e = true) :
    OkSL s l = true := by
  simp only [OkSL, List.all_eq_true]; exact fun e he => OkS_of_okC s (h e he)

/-- **The generated recursor stage** (`genRecCheck`): InLean's (with the
flushes of `genRecCheckC`) answers master's at `(fueledOpsM
.verified)` on the readings.  The steps in order: the pins, the stream's
recursor types, the guards, the classes' normal forms (`ClassOk` of their
output), their constructors, the minors' guard, the former types; the
prefix's marker-freeness from the first recursor type, the prefix, the
recursor types; the rule-less recursors' environment (`jobEnvI_ruleEnv`,
the `sorryAx` clause from the pins), the flush, the rules, the flush.  The
generator's record is master's `g0` component by component (`trCG` and the
mono lemmas).  Of every output it also gives its name fresh in `fe` and
`sorryAx` only under `coreAxioms` (it is a generated constant's), and the
stream's recursor names distinct (the pins), what the generated family's
push needs (`jobEnvI_genRecs`). -/
theorem genRecCheckI_run (hC : CheckConstantValFSimI) (hRF : ReducedFormerSimI)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {p : InLean.BlockShape} {nestedBit : Bool} {params : List Lean.Expr}
    {tbl : List InLean.NestCtorNf} {rd : InLean.ClassRead} {Ms : List InLean.TargetMajor}
    {block : List Lean.ConstantInfo} {s₀ s' : InLean.CState}
    {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
    (hs : CSOKI .verified false L s₀)
    (hrecs : ∀ rc ∈ p.recs, okC rc.cvR.type = true ∧ (trC rc.cvR.type).looseBVarsBounded 0 = true)
    (hfo : ∀ cv ∈ p.formers, okC cv.type = true ∧ (trC cv.type).looseBVarsBounded 0 = true)
    (htb : ∀ e ∈ tbl, OkNf s₀ e ∧ (TrS s₀ e.ty).looseBVarsBounded 0 = true)
    (hMs : ∀ M ∈ Ms, OkTM s₀ M ∧ FrameOk (TrSL s₀ M.pfvs) (TrSL s₀ (p.formers.map (·.type))) ∧
      (∀ a ∈ M.ds, (TrS s₀ a).looseBVarsBounded 0 = true) ∧
      (∀ c ∈ M.ctors, okC c.1.type = true ∧ (trC c.1.type).looseBVarsBounded 0 = true) ∧
      ∀ t, M.member = some t → t < p.formers.length)
    (hpar : FvsOk s₀ params) (hpl : params.length = p.nP)
    (hsl : ∀ sl ∈ rd.slots, OkSlot s₀ sl) (hrc : ∀ c ∈ rd.recCls, c < Ms.length)
    (hmc : ∀ s < rd.slots.length, ∀ k, rd.slots.getD s default = .motive k →
      ((List.range s).filter fun s' =>
        match rd.slots.getD s' default with | .motive _ => true | _ => false).length < Ms.length)
    (h : InLean.genRecCheck .verified fe p nestedBit params tbl rd Ms block s₀ =
      .ok (out, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      (∀ o ∈ out, okC o.1.type = true ∧ (trC o.1.type).looseBVarsBounded 0 = true ∧
        (∀ r ∈ o.2.2, okC r = true ∧ (trC r).looseBVarsBounded 0 = true) ∧ OkTMN s' o.2.1 ∧
        fe.env.find? o.1.name = none ∧ (o.1.name = InLean.sorryAxName → fe.coreAxioms = true)) ∧
      (p.recs.map (·.cvR.name)).Nodup ∧
      Runs (ConLeche.genRecCheck (ConLeche.fueledOpsM .verified)
        (ConLeche.mkFEnv L) (trShape p) nestedBit (TrSL s₀ params) (tbl.map (trNf s₀))
        (trCR s₀ rd) (Ms.map (trTM s₀)) (block.map trCI)) (out.map (trOut s')) := by
  unfold InLean.genRecCheck at h
  obtain ⟨u, s₁, h1, h⟩ := bind_run h
  obtain ⟨cvRis, s₂, h2, h⟩ := bind_run h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM _} {s : InLean.CState},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s = .ok (out, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  dsimp only at h
  split at h
  rotate_left
  · exact absurd h hth
  rename_i hk
  split at h
  · exact absurd h hth
  rename_i hle
  obtain ⟨Ms₁, s₃, h3, h⟩ := bind_run h
  obtain ⟨ctors, s₄, h4, h⟩ := bind_run h
  split at h
  rotate_left
  · exact absurd h hth
  rename_i hmin
  obtain ⟨formerTysC, s₅, h5, hA⟩ := bind_run h
  obtain ⟨pre?, s₆, h6, hB⟩ := bind_run hA
  obtain ⟨pre, s₆', h6', hC'⟩ := bind_run hB
  obtain ⟨hpre, hs₆⟩ := unwrapOrI_run h6'
  subst hs₆ hpre
  obtain ⟨cvGs, s₇, h7, hD⟩ := bind_run hC'
  obtain ⟨u, s₈, h8, hE⟩ := bind_run hD
  obtain ⟨out', s₉, h9, hF⟩ := bind_run hE
  obtain ⟨u, s₁₀, h10, hG⟩ := bind_run hF
  obtain ⟨rfl, rfl⟩ := pure_run hG
  clear h hA hB hC' hD hE hF hG h6'
  have hO := hJ.ops
  -- the pins
  obtain ⟨hs₁, hR1⟩ := targetRecPinsI_run h1
  subst s₁
  have hnd := targetRecPins_nodup h1
  have hnsa := targetRecPins_not_sorryAx h1
  have hne := recs_ne_nil_of_pins h1 hk
  -- the stream's recursor types
  obtain ⟨hs₂, ht₂, hcv, hR2⟩ := classStreamRecsI_run hC hJ p.recs hs (fun rc h => (hrecs rc h).1) h2
  subst hcv
  -- the formers' types: closed readings, at every state
  have hfoC : ∀ e ∈ p.formers.map (·.type), okC e = true := by
    intro e he; obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 he; exact (hfo cv hcv).1
  have hftOk : ∀ s, OkSL s (p.formers.map (·.type)) = true := fun s => okSL_of_okC s hfoC
  have hftTr : ∀ s, TrSL s (p.formers.map (·.type)) = (p.formers.map (·.type)).map trC :=
    fun s => TrSL_of_okC s hfoC
  have hfrF : ∀ s, ∀ t ∈ TrSL s (p.formers.map (·.type)),
      ConLeche.Expr.WScoped 0 t ∧ t.looseBVarsBounded 0 = true := by
    intro s t ht
    rw [hftTr] at ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 he
    exact ⟨trC_wscoped 0 _, (hfo cv hcv).2⟩
  -- the classes' normal forms
  obtain ⟨hs₃, ht₃, hMs₁, hmap₁, hR3⟩ := classesNfsI_run hO Ms hs₂ (hftOk s₂)
    (fun e he => (OkNf.mono ht₂ (htb e he).1).1)
    (fun M hM => ⟨(OkTM.mono ht₂ (hMs M hM).1).1, by
      rw [TrSL_of_tabLe ht₂ (hMs M hM).1.2.2.1, hftTr, ← hftTr s₀]; exact (hMs M hM).2.1⟩) h3
  have hsub := classesNfs_sub Ms h3
  have hlen₁ : Ms₁.length = Ms.length := by rw [← hmap₁, List.length_map]
  have hcl₃ : ∀ M ∈ Ms₁, ClassOk s₃ M := by
    intro M hM
    obtain ⟨-, -, hds, hct, -⟩ := hMs _ (mem_nfs_nil hmap₁ hM)
    obtain ⟨-, hdsO, -, -⟩ := (hMs _ (mem_nfs_nil hmap₁ hM)).1
    refine ⟨hMs₁ M hM, fun e he => ?_, fun a ha => ?_, fun c hc => (hct c hc).1⟩
    · have he' := htb e (hsub M hM e he)
      rw [TrS_of_tabLe (ht₂.trans ht₃) he'.1.2.2]; exact he'.2
    · have hdsO' : OkSL s₀ M.ds = true := hdsO
      simp only [OkSL, List.all_eq_true] at hdsO'
      rw [TrS_of_tabLe (ht₂.trans ht₃) (hdsO' a ha)]; exact hds a ha
  have hfr₃ : ∀ t, FrameOk (TrSL s₃ (Ms₁.getD t default).pfvs) (TrSL s₃ (p.formers.map (·.type))) := by
    intro t
    refine getD_of_all (P := fun (M : InLean.TargetMajor) => FrameOk (TrSL s₃ M.pfvs) (TrSL s₃ (p.formers.map (·.type))))
      (fun M hM => ?_) ⟨fun _ h => (List.not_mem_nil h).elim, hfrF s₃⟩ t
    have hF := (hMs _ (mem_nfs_nil hmap₁ hM)).2.1
    have hpf : OkSL s₀ M.pfvs = true := (hMs _ (mem_nfs_nil hmap₁ hM)).1.2.2.1
    rw [TrSL_of_tabLe (ht₂.trans ht₃) hpf, hftTr, ← hftTr s₀]; exact hF
  -- the classes' constructors
  obtain ⟨hs₄, ht₄, hxss, hR4⟩ := classesCtorsI_run (sr := s₀) hO Ms₁ 0 hs₃ (hftOk s₃)
    (fun t => getD_of_all hcl₃ (classOk_default s₃) t) hfr₃ hcl₃
    (fun M hM c hc => ((hMs _ (mem_nfs_nil hmap₁ hM)).2.2.2.1 c hc).2) h4
  -- the classes' former types
  obtain ⟨hs₅, ht₅, hfC, hlenC, hfCl, hR5⟩ := classFormerTysI_run hJ hRF hfo Ms₁ hs₄
    (fun M hM => ⟨(OkTMN.mono ht₄ (hcl₃ M hM).1).1, (hMs _ (mem_nfs_nil hmap₁ hM)).2.2.2.2⟩) h5
  have ht₃₅ := ht₄.trans ht₅
  have ht₀₅ := ht₂.trans (ht₃.trans ht₃₅)
  -- the generator's record before the prefix
  have hg0 : CGOk s₅ ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, []⟩ :=
    ⟨(hpar.mono ht₀₅).1.okSL, fun M hM => (OkTMN.mono ht₃₅ (hcl₃ M hM).1).1, hfC,
      fun sl hsl' => OkSlot.mono ht₀₅ (hsl sl hsl'),
      fun xs hxs x hx => (OkCC.mono ht₅ (hxss xs hxs x hx).1).1, rfl⟩
  have hcl₅ : ∀ c, ClassOk s₅ (Ms₁.getD c default) :=
    fun c => getD_of_all (fun M hM => (hcl₃ M hM).mono ht₃₅) (classOk_default _) c
  have hct₅ : ∀ xs ∈ ctors, ∀ x ∈ xs, CtorLbb s₅ x :=
    fun xs hxs x hx => CtorLbb.mono ht₅ (hxss xs hxs x hx).1 (hxss xs hxs x hx).2
  have hel : okLv (InLean.structElimLevel p.elim p.large) = true := by
    unfold InLean.structElimLevel; cases p.large <;> rfl
  -- the prefix's marker-freeness, from the first recursor type
  obtain ⟨rc₀, rcs₀, hrr⟩ := List.exists_cons_of_ne_nil hne
  have hem : ∀ b ∈ pre, emvarS b = false := by
    have h7' := h7
    rw [hrr] at h7'
    exact classRecTysOk_pre_emvar h7'
  obtain ⟨hs₆, ht₆, hP⟩ := prefixBindersI_run hs₅ hg0 hcl₅ hfCl hel
    (by intro s hs k hk; show _ < formerTysC.length; rw [hlenC, hlen₁]; exact hmc s hs k hk) hct₅ (hpar.mono ht₀₅).1 h6
  obtain ⟨hpreO, hpreC⟩ := hP pre rfl hem
  -- the recursor types
  obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, htrG0⟩ := CGOk.mono ht₆ hg0
  have hg6 : CGOk s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, pre⟩ := ⟨g1, g2, g3, g4, g5, hpreO⟩
  have hfC' := hfC
  simp only [OkSL, List.all_eq_true] at hfC'
  have hcG : ∀ c ∈ rd.recCls, GenCls s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, pre⟩ c := by
    intro c hc
    have hcl : c < formerTysC.length := by rw [hlenC, hlen₁]; exact hrc c hc
    have hmem : formerTysC.getD c default ∈ formerTysC := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl, Option.getD_some]
      exact List.getElem_mem hcl
    refine ⟨(hcl₅ c).mono ht₆, ?_, hcl⟩
    show (TrS s₆' (formerTysC.getD c default)).looseBVarsBounded 0 = true
    rw [TrS_of_tabLe ht₆ (hfC' _ hmem)]
    exact hfCl _ hmem
  obtain ⟨hs₇, ht₇, hgen, hR7⟩ := classRecTysOkI_run (k := p.k) hJ p.recs (p.recs.map fun rc => rc.cvR) rd.recCls hs₆ hg6
    (fun cv hcv => by
      obtain ⟨rc, hrc', rfl⟩ := List.mem_map.1 hcv; exact hrecs rc hrc') hcG h7
  obtain ⟨hle₇, hfr₇, hnm₇⟩ := classRecTysOk_facts p.recs _ rd.recCls h7
  -- the rule-less recursors' environment
  have hnd' : (cvGs.map (·.name)).Nodup := by
    rw [hnm₇]; exact List.Pairwise.of_map toName (fun a b h he => h (he ▸ rfl)) ((namesNodup_iff _).1 hnd)
  have hso : ∀ x ∈ cvGs, x.name = InLean.sorryAxName → fe.coreAxioms = true := by
    intro x hx hxn
    have hm : x.name ∈ p.recs.map (·.cvR.name) := hnm₇ ▸ List.mem_map_of_mem hx
    obtain ⟨rc, hrc', he⟩ := List.mem_map.1 hm
    exact absurd (he.trans hxn) (hnsa rc hrc')
  have hJR := jobEnvI_ruleEnv hJ (Ms := Ms₁) (recCls := rd.recCls) s₆' hle₇ hfr₇ hnd' hso
    (genCVs_okC hgen) hR7
  -- the flush, the rules, the flush
  have e8 : s₈ = s₇.flushed := ((Prod.mk.inj (Except.ok.inj ((flushI_run s₇).symm.trans h8))).2).symm
  subst e8
  have e10 : s₁₀ = s₉.flushed :=
    ((Prod.mk.inj (Except.ok.inj ((flushI_run s₉).symm.trans h10))).2).symm
  subst e10
  have ht₆₈ := ht₇.trans (TabLe.flushed (s := s₇))
  have hg8 := (CGOk.mono ht₆₈ hg6).1
  have hct8 : ∀ xs ∈ ctors, ∀ x ∈ xs, RuleCtorOk s₇.flushed x := by
    intro xs hxs x hx
    have ht' := ht₅.trans (ht₆.trans ht₆₈)
    have hl := CtorLbb.mono ht' (hxss xs hxs x hx).1 (hxss xs hxs x hx).2
    exact ⟨(OkCC.mono ht' (hxss xs hxs x hx).1).1, hl.1, hl.2⟩
  unfold InLean.classFeROvl at h9
  obtain ⟨hs₉, ht₉, hout, hR9⟩ := classRecsRulesOkI_run (feT := fe) hJ.pres hJR
    (recOfM := ConLeche.classRecOf rd.recCls (cvGs.map trCV)) (fun t => classRecOf_tr _ _ t) hpl
    cvGs rd.recCls (fun m e L' => flushI_csoki hs₇.residue m e L') hg8 hct8 h9
  have ht₉' := ht₉.trans (TabLe.flushed (s := s₉))
  refine ⟨flushI_csoki (hs₉ .verified false L).residue _ _ _,
    ht₂.trans (ht₃.trans (ht₃₅.trans (ht₆.trans (ht₆₈.trans ht₉')))), fun o ho => ?_,
    List.Pairwise.of_map toName (fun a b h he => h (he ▸ rfl)) ((namesNodup_iff _).1 hnd), ?_⟩
  · obtain ⟨hcv, hr, c, hc⟩ := hout o ho
    refine ⟨(genCVs_closed hgen _ hcv).1, (genCVs_closed hgen _ hcv).2, hr, ?_, hfr₇ _ hcv,
      hso _ hcv⟩
    rw [hc]
    exact (OkTMN.mono ht₉' (getD_of_all hg8.2.1 (okTMN_default _) c)).1
  -- master's side, step by step
  have hfM : ∀ s, (trShape p).formers.map (·.type) = TrSL s (p.formers.map (·.type)) := by
    intro s; rw [hftTr, trShape_formers, List.map_map, List.map_map]; rfl
  have hMs₀ : ∀ M ∈ Ms, OkTM s₀ M := fun M hM => (hMs M hM).1
  rw [← hfM, map_trNf_mono ht₂ (fun e he => (htb e he).1),
    List.map_congr_left (fun M hM => (OkTM.mono ht₂ (hMs₀ M hM)).2)] at hR3
  rw [← hfM] at hR4
  have hMs₁₃ : ∀ M ∈ Ms₁, OkTMN s₃ M := fun M hM => (hcl₃ M hM).1
  rw [map_trTM_mono ht₄ hMs₁₃, ← trShape_formers] at hR5
  have hG0 : trCG s₅ ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, []⟩ =
      ⟨(trShape p).nP, TrSL s₀ params, Ms₁.map (trTM s₃), TrSL s₅ formerTysC, (trCR s₀ rd).slots,
        ctors.map (fun x => x.map (trCC s₄)), ConLeche.structElimLevel (trShape p).elim (trShape p).large,
        []⟩ := by
    unfold trCG
    rw [show (trShape p).elim = toName p.elim from rfl, show (trShape p).large = p.large from rfl,
      structElimLevel_tr, (hpar.mono ht₀₅).2, map_trTM_mono ht₃₅ hMs₁₃,
      List.map_congr_left fun xs hxs => map_trCC_mono ht₅ (fun x hx => (hxss xs hxs x hx).1)]
    simp only [trCR, TrSL]
    congr 1
    exact List.map_congr_left fun sl hsl' => trSlot_mono ht₀₅ (hsl sl hsl')
  rw [hG0] at hpreC
  have hG6 : trCG s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, pre⟩ =
      ⟨(trShape p).nP, TrSL s₀ params, Ms₁.map (trTM s₃), TrSL s₅ formerTysC, (trCR s₀ rd).slots,
        ctors.map (fun x => x.map (trCC s₄)), ConLeche.structElimLevel (trShape p).elim (trShape p).large,
        TrSL s₆' pre⟩ := by
    have h' : trCG s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
        InLean.structElimLevel p.elim p.large, pre⟩ =
        { trCG s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
          InLean.structElimLevel p.elim p.large, []⟩ with pre := TrSL s₆' pre } := rfl
    rw [h', htrG0, hG0]
  have hG8 : trCG s₇.flushed ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, pre⟩ =
      trCG s₆' ⟨p.nP, params, Ms₁, formerTysC, rd.slots, ctors,
      InLean.structElimLevel p.elim p.large, pre⟩ := (CGOk.mono ht₆₈ hg6).2
  rw [hG6] at hR7
  rw [hG8, hG6, map_trTM_mono (ht₄.trans (ht₅.trans ht₆)) hMs₁₃, ← classFeR_mkFEnv] at hR9
  have hout' : out'.map (trOut s₉.flushed) = out'.map (trOut s₇.flushed) := by
    refine List.map_congr_left fun o ho => ?_
    obtain ⟨-, hr, c, hc⟩ := hout o ho
    have hM : OkTMN s₇.flushed o.2.1 := by rw [hc]; exact getD_of_all hg8.2.1 (okTMN_default _) c
    simp only [trOut, TrSL_of_okC _ fun r h => (hr r h).1, (OkTMN.mono ht₉' hM).2]
  rw [hout']
  unfold ConLeche.genRecCheck
  dsimp only
  refine Runs.bind hR1 (Runs.bind hR2 ?_)
  rw [ite_eq_left (by rw [trShape_k]; exact hk), ite_eq_right (by
    rw [any_member_trTM, blockLargeElimAllowed_tr]; exact hle)]
  refine Runs.bind hR3 (Runs.bind hR4 ?_)
  rw [ite_eq_left (by rw [minors_trCR, ctorsSum_tr]; exact hmin)]
  refine Runs.bind (runs_mapM hR5) ?_
  rw [hpreC]
  refine Runs.bind (Runs.pure _) ?_
  rw [trShape_k]
  exact Runs.bind hR7 hR9

end InLeanProof
