module

public import InLeanProof.PassRecs4
public import InLeanProof.DeclStep

/-!
# O7-recursors: the recursor types checked (task #451, lane O7-recursors)

The recursor stage (`genRecCheck`) against master's, continued bottom-up from
`PassRecs4`:

* `classConstOk` against master's: the `EO.inRange` guard gives the term's
  range and its marker-freeness (`classConstOk_emvar`, read before the
  generator's statement is used), a reading without free variables is a
  closed one (`okC_of_OkS`); InLean's monadic `allLevelParamsDefined` and
  `constsResolveF` read the term alone at a term without free variables;
  master's resolution guard comes from the inference (`constsResolve_of_infer`).
* `classRecTyCheck`, `classRecTyOk`, `classRecTysOk`: the generated type
  (`classGenRecTyI_run`) checked and compared with the stream's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## The annotations of a term without free variables -/

theorem withAnnotations_noFVar {e : Lean.Expr} (h : e.hasFVar = false) (s : InLean.CState) :
    InLean.withAnnotations e s = .ok ([e], s) := by
  unfold InLean.withAnnotations
  simp [h]
  rfl

theorem allLevelParamsDefined_noFVar {lps : List Lean.Name} {e : Lean.Expr}
    (h : e.hasFVar = false) {s s' : InLean.CState} {b : Bool}
    (hr : InLean.allLevelParamsDefined lps e s = .ok (b, s')) :
    s' = s ∧ b = (!e.hasLevelParam || (EO.levelParams e).all lps.contains) := by
  unfold InLean.allLevelParamsDefined at hr
  obtain ⟨a, s₁, h1, h2⟩ := bindI_ok hr
  rw [withAnnotations_noFVar h] at h1
  cases h1
  obtain ⟨rfl, rfl⟩ := pureI_ok h2
  simp

theorem constsResolveF_state {fe : InLean.FEnv} {e : Lean.Expr} {s s' : InLean.CState} {b : Bool}
    (hr : InLean.constsResolveF fe e s = .ok (b, s')) : s' = s :=
  constsResolveF_noSt fe e s b s' hr

/-! ## A generated constant -/

/-- **A generated constant accepted is marker-free** (the `EO.inRange` guard). -/
theorem classConstOk_emvar {ops : InLean.CheckerOps} {fe : InLean.FEnv} {cv : Lean.ConstantVal}
    {s₀ s' : InLean.CState} (h : InLean.classConstOk ops fe cv s₀ = .ok ((), s')) :
    Expr.RangeOk cv.type ∧ emvarS cv.type = false := by
  unfold InLean.classConstOk at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok ((), s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : (fe.env.find? cv.name).isSome <;> simp only [g1, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g2 : InLean.litShapeOk cv.name cv.levelParams cv.type <;> simp only [g2, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g3 : InLean.namesNodup cv.levelParams <;> simp only [g3, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g4 : cv.type.hasLooseBVars <;> simp only [g4, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g5 : cv.type.hasFVar <;> simp only [g5, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g6 : EO.inRange cv.type <;> simp only [g6, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  exact RangeOk_of_inRange g6

/-- **A generated constant, checked** (`classConstOk`, `checkConstantValC_sim`'s
twin): at a term with a reading, accepted at the job's operations, master's
`classConstOk` runs on the translated constant at the job's environment. -/
theorem classConstOkI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {cv : Lean.ConstantVal} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hok : OkS s₀ cv.type = true)
    (h : InLean.classConstOk (sharedOpsC .verified fe) fe cv s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC cv.type = true ∧
      (trC cv.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.classConstOk (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) (trCV cv))
        () := by
  unfold InLean.classConstOk at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok ((), s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : (fe.env.find? cv.name).isSome <;> simp only [g1, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g2 : InLean.litShapeOk cv.name cv.levelParams cv.type <;> simp only [g2, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g3 : InLean.namesNodup cv.levelParams <;> simp only [g3, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g4 : cv.type.hasLooseBVars <;> simp only [g4, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g5 : cv.type.hasFVar <;> simp only [g5, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  cases g6 : EO.inRange cv.type <;> simp only [g6, Bool.false_eq_true, ↓reduceIte] at h <;>
    try exact absurd h hth
  have hr := RangeOk_of_OkS hok
  obtain ⟨hokc, hTr⟩ := okC_of_OkS hok (by rw [← hasFVar_TrS _ hok]; exact g5)
  have hlbb := lbb_trC_of_range hr hokc g4
  obtain ⟨l, s₁, hl, h⟩ := bindI_ok h
  obtain ⟨hs1, rfl⟩ := allLevelParamsDefined_noFVar g5 hl
  rw [hs1] at h
  cases gl : (!cv.type.hasLevelParam || (EO.levelParams cv.type).all cv.levelParams.contains) <;>
    simp only [gl, Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  have hlp : (trC cv.type).allLevelParamsDefined (cv.levelParams.map toName) = true :=
    allLevelParamsDefined_of_guard hr fun hh => by simpa [hh] using gl
  obtain ⟨c, s₁, hc, h⟩ := bindI_ok h
  rw [constsResolveF_state hc] at h
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  obtain ⟨v, s₂, hI, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hokv, hRI, hwv, hcv⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₀) (d := 0)
    (i := cv.type) hs hok (by rw [hTr]; exact trC_wscoped 0 _) (by rw [hTr]; exact hlbb))
    v s₂ hI
  obtain ⟨u, s₃, hS, h⟩ := bindI_ok h
  obtain ⟨hs₃, ht₃, -, hRS⟩ := tripleI_iff_run.1 (hJ.ops.sort (s₀ := s₂) (d := 0) (i := v) hs₂ hokv
    hwv hcv) u s₃ hS
  obtain ⟨-, rfl⟩ := pureI_ok h
  refine ⟨hs₃, ht₂.trans ht₃, hokc, hlbb, ?_⟩
  rw [hTr] at hRI
  have g1' : (L.find? (toName cv.name)).isSome = false := by
    rw [hJ.pres.none cv.name (FEnv_find_none (by simpa using g1))]; rfl
  have g2' := litShapeOk_tr hokc g2
  have g3' : ConLeche.Name.nodup (cv.levelParams.map toName) = true := by rw [nodup_tr]; exact g3
  obtain ⟨F, hF⟩ := runs_atF hRI
  have g6' : (trC cv.type).constsResolve L = true := constsResolve_of_infer (trC_hasFvar _) hF
  unfold ConLeche.classConstOk
  simp only [trCV, ConLeche.mkFEnv_find?, ConLeche.mkFEnv_env, ConLeche.constsResolveF_eq, g1',
    g2', g3', hlbb, trC_hasFvar, hlp, g6', Bool.false_eq_true, ↓reduceIte]
  exact Runs.bind hRI (Runs.bind hRS (Runs.pure _))

/-- **A generated recursor type, checked and compared** (`classRecTyCheck`):
the stream's checked type `cvRi` closed, the generated one with a reading. -/
theorem classRecTyCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {cvRi cvG : Lean.ConstantVal} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hokR : okC cvRi.type = true)
    (hlbbR : (trC cvRi.type).looseBVarsBounded 0 = true) (hok : OkS s₀ cvG.type = true)
    (h : InLean.classRecTyCheck (sharedOpsC .verified fe) fe cvRi cvG s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC cvG.type = true ∧
      (trC cvG.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.classRecTyCheck (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (trCV cvRi) (trCV cvG)) () := by
  unfold InLean.classRecTyCheck at h
  obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hokc, hlbb, hR1⟩ := classConstOkI_run hJ hs hok h1
  obtain ⟨b, s₂, h2, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₁) (d := 0) (i := cvRi.type)
    (j := cvG.type) hs₁ (OkS_of_okC _ hokR) (OkS_of_okC _ hokc)
    (by rw [TrS_of_okC _ hokR]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokc]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokR]; exact hlbbR) (by rw [TrS_of_okC _ hokc]; exact hlbb)) b s₂ h2
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact (throwI_ok h).elim
  simp only [↓reduceIte] at h
  obtain ⟨-, rfl⟩ := pureI_ok h
  refine ⟨hs₂, ht₁.trans ht₂, hokc, hlbb, ?_⟩
  rw [TrS_of_okC _ hokR, TrS_of_okC _ hokc] at hRD
  unfold ConLeche.classRecTyCheck
  refine Runs.bind hR1 (Runs.bind (by rw [ConLeche.mkFEnv_env]; exact hRD) ?_)
  exact Runs.pure _

/-- A generated recursor type accepted by `classRecTyCheck` is marker-free. -/
theorem classRecTyCheck_emvar {ops : InLean.CheckerOps} {fe : InLean.FEnv}
    {cvRi cvG : Lean.ConstantVal} {s₀ s' : InLean.CState}
    (h : InLean.classRecTyCheck ops fe cvRi cvG s₀ = .ok ((), s')) : emvarS cvG.type = false := by
  unfold InLean.classRecTyCheck at h
  obtain ⟨_, _, h1, -⟩ := bindI_ok h
  exact (classConstOk_emvar h1).2

/-- **One recursor's generated type, checked** (`classRecTyOk`): the record's
guards read, the generated type (`classGenRecTyI_run`) read where the check
found it marker-free, then checked and compared (`classRecTyCheckI_run`).
The stored constant is the record's with the generated type. -/
theorem classRecTyOkI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {g : InLean.ClassGen} {k c : Nat} {rc : InLean.RecShape} {cvRi : Lean.ConstantVal}
    {s₀ s' : InLean.CState} {v : Lean.ConstantVal}
    (hs : CSOKI .verified false L s₀) (hokR : okC cvRi.type = true)
    (hlbbR : (trC cvRi.type).looseBVarsBounded 0 = true) (hg : CGOk s₀ g)
    (hM : ClassOk s₀ (g.cls.getD c default))
    (hftc : (TrS s₀ (g.formerTys.getD c default)).looseBVarsBounded 0 = true)
    (hc : c < g.formerTys.length)
    (h : InLean.classRecTyOk (sharedOpsC .verified fe) fe g k rc cvRi c s₀ = .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ v = { rc.cvR with type := v.type } ∧
      okC v.type = true ∧ (trC v.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.classRecTyOk (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (trCG s₀ g) k (trRec rc) (trCV cvRi) c) (trCV v) := by
  unfold InLean.classRecTyOk at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Lean.ConstantVal},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok (v, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : (rc.tgt == (g.cls.getD c default).member.getD k) <;>
    simp only [g1, Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  cases g2 : (rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + (g.cls.getD c default).nIdx) <;>
    simp only [g2, Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  obtain ⟨r, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hgen⟩ := classGenRecTyI_run hs hM (okS_getD hg.2.2.1 hc) hftc hc hg.2.2.2.2.2 h1
  obtain ⟨gty, s₂, h2, hA⟩ := bindI_ok h
  obtain ⟨hr, rfl⟩ := unwrapOr_run h2
  obtain ⟨_, s₃, h3, hB⟩ := bindI_ok hA
  obtain ⟨rfl, rfl⟩ := pureI_ok hB
  have hem := classRecTyCheck_emvar h3
  obtain ⟨hok, hmas⟩ := hgen gty hr hem
  obtain ⟨hs₃, ht₃, hokc, hlbb, hR3⟩ := classRecTyCheckI_run hJ hs₁ hokR hlbbR hok h3
  refine ⟨hs₃, ht₁.trans ht₃, rfl, hokc, hlbb, ?_⟩
  rw [TrS_of_okC _ hokc] at hmas
  have hmem : (trCG s₀ g).cls.getD c default = trTM s₀ (g.cls.getD c default) := by
    simp only [trCG, getD_map_trTM]
  unfold ConLeche.classRecTyOk
  have hsl : (trCG s₀ g).slots.length = g.slots.length := by simp [trCG]
  have hnP : (trCG s₀ g).nP = g.nP := rfl
  simp only [hmem, trTM, trRec, g1, hsl, hnP, g2, ↓reduceIte, hmas]
  exact Runs.bind (Runs.pure _) (Runs.bind hR3 (Runs.pure _))

/-- What `classRecTysOk` gives back, per recursor record. -/
@[expose] def GenCV (x : Lean.ConstantVal) (rc : InLean.RecShape) : Prop :=
  x = { rc.cvR with type := x.type } ∧ okC x.type = true ∧ (trC x.type).looseBVarsBounded 0 = true

/-- `GenCV`, pairwise. -/
inductive GenCVs : List Lean.ConstantVal → List InLean.RecShape → Prop
  | nil : GenCVs [] []
  | cons {x : Lean.ConstantVal} {rc : InLean.RecShape} {xs : List Lean.ConstantVal}
      {rcs : List InLean.RecShape} : GenCV x rc → GenCVs xs rcs → GenCVs (x :: xs) (rc :: rcs)

/-- What `classRecTysOk` needs of a recursor's class. -/
@[expose] def GenCls (s : InLean.CState) (g : InLean.ClassGen) (c : Nat) : Prop :=
  ClassOk s (g.cls.getD c default) ∧
    (TrS s (g.formerTys.getD c default)).looseBVarsBounded 0 = true ∧ c < g.formerTys.length

theorem GenCls.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {g : InLean.ClassGen} {c : Nat}
    (hg : CGOk s₀ g) (hc : GenCls s₀ g c) : GenCls s₁ g c := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨ClassOk.mono h h1, ?_, h3⟩
  rw [TrS_of_tabLe h (okS_getD hg.2.2.1 h3)]
  exact h2

/-- **Every recursor's generated type, checked** (`classRecTysOk`). -/
theorem classRecTysOkI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {g : InLean.ClassGen} {k : Nat} :
    ∀ (rcs : List InLean.RecShape) (cvs : List Lean.ConstantVal) (cs : List Nat)
      {s₀ s' : InLean.CState} {v : List Lean.ConstantVal},
      CSOKI .verified false L s₀ → CGOk s₀ g →
      (∀ cvRi ∈ cvs, okC cvRi.type = true ∧ (trC cvRi.type).looseBVarsBounded 0 = true) →
      (∀ c ∈ cs, GenCls s₀ g c) →
      InLean.classRecTysOk (sharedOpsC .verified fe) fe g k rcs cvs cs s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ GenCVs v rcs ∧
        Runs (ConLeche.classRecTysOk (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
          (trCG s₀ g) k (rcs.map trRec) (cvs.map trCV) cs) (v.map trCV)
  | [], cvs, cs, s₀, s', v, hs, _, _, _, h => by
    unfold InLean.classRecTysOk at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    refine ⟨hs, TabLe.refl _, .nil, ?_⟩
    unfold ConLeche.classRecTysOk
    exact Runs.pure _
  | rc :: rcs, cvRi :: cvs, c :: cs, s₀, s', v, hs, hg, hcv, hcs, h => by
    unfold InLean.classRecTysOk at h
    obtain ⟨x, s₁, h1, hA⟩ := bindI_ok h
    obtain ⟨hcvR, hlbbR⟩ := hcv cvRi List.mem_cons_self
    obtain ⟨hM, hftc, hc⟩ := hcs c List.mem_cons_self
    obtain ⟨hs₁, ht₁, hx, hokx, hlbbx, hR1⟩ := classRecTyOkI_run hJ hs hcvR hlbbR hg hM hftc hc h1
    obtain ⟨xs, s₂, h2, hB⟩ := bindI_ok hA
    obtain ⟨hg₁, htr⟩ := CGOk.mono ht₁ hg
    obtain ⟨hs₂, ht₂, hxs, hR2⟩ := classRecTysOkI_run hJ rcs cvs cs hs₁ hg₁
      (fun r hr => hcv r (List.mem_cons_of_mem _ hr))
      (fun d hd => GenCls.mono ht₁ hg (hcs d (List.mem_cons_of_mem _ hd))) h2
    obtain ⟨rfl, rfl⟩ := pureI_ok hB
    refine ⟨hs₂, ht₁.trans ht₂, .cons ⟨hx, hokx, hlbbx⟩ hxs, ?_⟩
    rw [htr] at hR2
    simp only [List.map_cons]
    unfold ConLeche.classRecTysOk
    exact Runs.bind hR1 (Runs.bind hR2 (Runs.pure _))
  | _ :: _, [], _, s₀, s', v, _, _, _, _, h => by
    unfold InLean.classRecTysOk at h; exact (throwI_ok h).elim
  | _ :: _, _ :: _, [], s₀, s', v, _, _, _, _, h => by
    unfold InLean.classRecTysOk at h; exact (throwI_ok h).elim

/-! ## InLean's resolution test, read as master's -/

/-- The constants `EO.usedConstants` picks. -/
@[expose] def ucPick : Lean.Expr → Option Lean.Name
  | .const n _ => some n
  | _ => none

theorem ucPick_compound : ∀ x, EO.isCompound x = true → ucPick x = none := by
  intro x hx; cases x <;> first | rfl | simp [EO.isCompound] at hx

theorem ucDedup_spec : ∀ (l : List Lean.Name) (s : Std.HashSet Lean.Name) (acc : Array Lean.Name),
    (∀ x, s.contains x = true → x ∈ acc) →
    (∀ n ∈ acc, n ∈ (l.foldl (fun (s, acc) n =>
        if s.contains n then (s, acc) else (s.insert n, acc.push n)) (s, acc)).2) ∧
      ∀ n ∈ l, n ∈ (l.foldl (fun (s, acc) n =>
        if s.contains n then (s, acc) else (s.insert n, acc.push n)) (s, acc)).2
  | [], _, _, _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | a :: l, s, acc, hinv => by
    simp only [List.foldl_cons]
    by_cases ha : s.contains a = true
    · simp only [ha, ↓reduceIte]
      obtain ⟨h1, h2⟩ := ucDedup_spec l s acc hinv
      refine ⟨h1, fun n hn => ?_⟩
      rcases List.mem_cons.1 hn with rfl | hn
      · exact h1 _ (hinv _ ha)
      · exact h2 n hn
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      have hinv' : ∀ x, (s.insert a).contains x = true → x ∈ acc.push a := by
        intro x hx
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true_iff.1 hx with hx | hx
        · rw [show x = a from (eq_of_beq hx).symm]; exact Array.mem_push_self
        · exact Array.mem_push_of_mem _ (hinv x hx)
      obtain ⟨h1, h2⟩ := ucDedup_spec l (s.insert a) (acc.push a) hinv'
      refine ⟨fun n hn => h1 n (Array.mem_push_of_mem _ hn), fun n hn => ?_⟩
      rcases List.mem_cons.1 hn with rfl | hn
      · exact h1 _ Array.mem_push_self
      · exact h2 n hn

/-- **Completeness of `EO.usedConstants`**: every constant the walk reaches is listed. -/
theorem usedConstants_complete {e : Lean.Expr} {n : Lean.Name}
    (h : OccS (fun _ => false) ucPick n e) : n ∈ EO.usedConstants e := by
  unfold EO.usedConstants
  have hc := collect_complete ucPick_compound e h
  dsimp only
  rw [← Array.foldl_toList]
  exact (ucDedup_spec _ {} #[] (fun x hx => by simp at hx)).2 n (Array.mem_toList_iff.2 hc)

/-- The nodes InLean's resolution test refuses. -/
@[expose] def crBad (fe : InLean.FEnv) : Lean.Expr → Bool
  | .proj s _ _ => (fe.find? s).isNone
  | .lit (.natVal _) => !natLitStoredF fe
  | .lit (.strVal _) => !strLitStoredF fe
  | _ => false

theorem find_isSome_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Lean.Name}
    (h : (fe.find? n).isSome = true) : (L.find? (toName n)).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨cci, hL, -⟩ := hP.entry n ci hci
  rw [hL]; rfl

/-- **InLean's resolution test is master's**, on a closed reading. -/
theorem constsResolve_of_test {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) :
    ∀ {e : Lean.Expr}, okC e = true →
      (∀ n, OccS (fun _ => false) ucPick n e → (fe.find? n).isSome = true) →
      ∀ k, anySpec (fun x _ => if crBad fe x then some true else none) e k = false →
      (trC e).constsResolve L = true := by
  intro e
  induction e with
  | bvar | sort => intros; rfl
  | fvar => intro h; simp [okC, okE] at h
  | mvar => intro h; simp [okC, okE] at h
  | const n us =>
    intro _ hc _ _
    exact find_isSome_tr hP (hc n ⟨rfl, rfl⟩)
  | lit l =>
    intro _ _ k ha
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := cl_litNames
    cases l with
    | natVal =>
      simp only [anySpec, crBad] at ha
      cases hs : natLitStoredF fe
      · simp [hs] at ha
      simp only [natLitStoredF, Bool.and_eq_true] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      simp only [trC, trE, toLit, ConLeche.Expr.constsResolve, ← c1, ← c2, ← c3,
        find_isSome_tr hP h1, find_isSome_tr hP h2, find_isSome_tr hP h3, Bool.and_self]
    | strVal =>
      simp only [anySpec, crBad] at ha
      cases hs : strLitStoredF fe
      · simp [hs] at ha
      simp only [strLitStoredF, natLitStoredF, Bool.and_eq_true] at hs
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hs
      simp only [trC, trE, toLit, ConLeche.Expr.constsResolve, ← c1, ← c2, ← c3, ← c4, ← c5,
        ← c6, ← c7, ← c8, ← c9, ← c10, find_isSome_tr hP h1, find_isSome_tr hP h2,
        find_isSome_tr hP h3, find_isSome_tr hP h4, find_isSome_tr hP h5, find_isSome_tr hP h6,
        find_isSome_tr hP h7, find_isSome_tr hP h8, find_isSome_tr hP h9, find_isSome_tr hP h10,
        Bool.and_self]
  | app f a ihf iha =>
    intro hok hc k ha
    simp only [okC, okE, Bool.and_eq_true] at hok
    simp only [anySpec, crBad, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trC, trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) k ha.1,
      iha hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) k ha.2⟩
  | lam _ t b _ iht ihb =>
    intro hok hc k ha
    simp only [okC, okE, Bool.and_eq_true] at hok
    simp only [anySpec, crBad, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trC, trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) k ha.1,
      ihb hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) (k + 1) ha.2⟩
  | forallE _ t b _ iht ihb =>
    intro hok hc k ha
    simp only [okC, okE, Bool.and_eq_true] at hok
    simp only [anySpec, crBad, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trC, trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) k ha.1,
      ihb hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) (k + 1) ha.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro hok hc k ha
    simp only [okC, okE, Bool.and_eq_true] at hok
    simp only [anySpec, crBad, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trC, trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨iht hok.1.1 (fun n h => hc n ⟨rfl, .inl h⟩) k ha.1.1,
      ihv hok.1.2 (fun n h => hc n ⟨rfl, .inr (.inl h)⟩) k ha.1.2⟩,
      ihb hok.2 (fun n h => hc n ⟨rfl, .inr (.inr h)⟩) (k + 1) ha.2⟩
  | mdata _ x ih =>
    intro hok hc k ha
    simp only [okC, okE] at hok
    simp only [anySpec, crBad, Bool.false_eq_true, ↓reduceIte, Option.getD_none] at ha
    exact ih hok (fun n h => hc n ⟨rfl, h⟩) k ha
  | proj s i x ih =>
    intro hok hc k ha
    simp only [okC, okE] at hok
    simp only [anySpec, crBad] at ha
    cases hs : (fe.find? s).isNone
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, Option.getD_none] at ha
      simp only [trC, trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
      refine ⟨find_isSome_tr hP (by simpa using hs), ?_⟩
      exact ih hok (fun n h => hc n ⟨rfl, h⟩) k ha
    · simp [hs] at ha

/-- **InLean's resolution test on a term without free variables** (a walker's
`resolve`, `constsResolveF`): accepted, master's resolution holds of the
closed reading at a related environment. -/
theorem constsResolveF_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {e : Lean.Expr} (hok : okC e = true) {s s' : InLean.CState}
    (h : InLean.constsResolveF fe e s = .ok (true, s')) : (trC e).constsResolve L = true := by
  have hf : e.hasFVar = false := by
    rw [Expr.hasFVar_eq (RangeOk_of_okE hok)]; exact fvarS_of_okC hok
  unfold InLean.constsResolveF at h
  obtain ⟨a, s₁, h1, h2⟩ := bindI_ok h
  rw [withAnnotations_noFVar hf] at h1
  cases h1
  obtain ⟨hb, -⟩ := pureI_ok h2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true'] at hb
  refine constsResolve_of_test hP hok (fun n hn => ?_) 0 ?_
  · exact Array.all_eq_true_iff_forall_mem.1 hb.1 n (usedConstants_complete hn)
  · have := hb.2
    simp only [EO.any, anyNode_fresh] at this
    rw [← this]
    congr 1

end InLeanProof
