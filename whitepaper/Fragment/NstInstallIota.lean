module

public import Fragment.NstInstallInd

@[expose] public section

/-!
# Installing an inductive block, part 2: the ι law of the generated
rules

The third `EnvModel` law for the recursor: every generated rule's ι
equation holds on values (`RecRuleLaw`, `EnvModel.lean`), its
right-hand side is well-denoted and its application chain along the
rule's arguments is well-formed (`rec_rule_law`).

The proof reads both sides.  The **left-hand side** is the recursor's
set applied to the parameters, the motive, the minors, the indices and
the major; the major, being the constructor's set applied to the
parameters and the fields, is the constructor value at the fields
(`ctor_app`, by β over the constructor's context — or, at a
proposition, the point).  The three comparisons of `Red.iota` put the
constructor's parameters at the recursor's, its levels at the
recursor's and the index values at the constructor's index expressions
read under the fields, so the left-hand side is the semantic recursor
at the constructor value (`rec_app_mem`, by β over the recursor's
context), which the recursion equation of the model's recursor makes
the minor at the fields and the inductive hypotheses' values
(`recSem_eq`, `IndSem.lean`).  The **right-hand side** is β over the
rule's context (`fits_ruleCtx`) of the minor applied to the fields and
the generated inductive-hypothesis terms, and each of those terms is
a recursor call whose spine fits the recursor's context, hence reads
as the semantic inductive hypothesis (`recCall_ok`, `ihVal_ok`).  The
same spine fit gives the terms' invariant, and the minor's typing
gives the application chain (`Reader₂.minorOk`).
-/

namespace Fragment.IndSpec.Nst
open Fragment.NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

/-! ## Two syntactic facts -/

omit [IndLib V] [LevelOracle] in
theorem Expr.instL_mkAppN (ps : List Name) (ls : List Level) (f : Expr) (args : List Expr) :
    (Expr.mkAppN f args).instL ps ls = Expr.mkAppN (f.instL ps ls) (args.map (·.instL ps ls)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp [ih]

omit [IndLib V] [LevelOracle] in
theorem Expr.map_instL_varsAt (ps : List Name) (ls : List Level) (o n : Nat) :
    (Expr.varsAt o n).map (·.instL ps ls) = Expr.varsAt o n := by
  simp [Expr.varsAt, List.map_map, Function.comp]

omit [LevelOracle] in
theorem Expr.wd_of_mem_varsAt {M : Name → List Nat → V} {φ : Name → Nat} {ρ : Nat → V}
    {o n : Nat} {a : Expr} (h : a ∈ Expr.varsAt o n) : WellDenoted M φ ρ a := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  simp

/-! ## Levels: the recursor's parameters and the block's -/

omit [IndLib V] [LevelOracle] in
/-- Substituting one more parameter in front does not change the
others' substitutes. -/
theorem Level.substVal_cons_of_ne (φ : Name → Nat) {p n : Name} (h : n ≠ p) (ps : List Name)
    (l : Level) (ls : List Level) :
    Level.substVal φ (p :: ps) (l :: ls) n = Level.substVal φ ps ls n := by
  have : (n == p) = false := by simpa using h
  simp [Level.substVal, Level.lookupLevel, List.lookup_cons, this]

omit [LevelOracle] in
/-- The domains of a lifted telescope are well-denoted exactly when
the telescope's are at its own frame (`FitsVals_liftCtx_atCtx` and
`WellDenoted_atCtx`, entry by entry). -/
theorem CtxWD_liftCtx_atCtx (M : Name → List Nat → V) (φ : Name → Nat) {nF k l o : Nat}
    {ihs fs os ps : List V} (ρ : Nat → V)
    (hi : ihs.length = l) (hf : fs.length = nF) (ho : os.length = o) (hk : k ≤ nF) :
    ∀ (Γ : List Expr),
      CtxWD M φ (consList ihs (consList fs (consList os (consList ps ρ))))
          (Expr.liftCtx (fun t T => Expr.atCtx nF k l o t T) Γ) ↔
        CtxWD M φ (consList (fs.drop (nF - k)) (consList ps ρ)) Γ
  | [] => Iff.rfl
  | A :: Γ => by
    simp only [Expr.liftCtx_cons, CtxWD_cons]
    rw [CtxWD_liftCtx_atCtx M φ ρ hi hf ho hk Γ]
    refine and_congr Iff.rfl ⟨fun h vs hvs => ?_, fun h vs hvs => ?_⟩
    · have hl := FitsVals_length M φ hvs
      have := h vs ((FitsVals_liftCtx_atCtx M φ ρ Γ vs hi hf ho hk).mpr hvs)
      rwa [WellDenoted_atCtx M φ ρ A hl hi hf ho hk] at this
    · rw [FitsVals_liftCtx_atCtx M φ ρ Γ vs hi hf ho hk] at hvs
      have hl := FitsVals_length M φ hvs
      rw [WellDenoted_atCtx M φ ρ A hl hi hf ho hk]
      exact h vs hvs

namespace IndSpec

variable {env : Env} {S : IndSpec}

omit [IndLib V] [LevelOracle] in
theorem recLparams_nodup (hS : S.Scoped env) : S.recLparams.Nodup := by
  unfold recLparams
  cases hl : S.large
  · simpa using hS.2.2.2.2.2.1
  · simpa using List.nodup_cons.mpr ⟨hS.2.2.2.2.1 hl, hS.2.2.2.2.2.1⟩

omit [IndLib V] [LevelOracle] in
/-- The recursor's level list instantiated: the block's parameters
read as the recursor's last levels. -/
theorem lparams_map_substVal_rec (hS : S.Scoped env) (φ : Name → Nat) {us : List Level}
    (hus : us.length = S.recLparams.length) :
    S.lparams.map (Level.substVal φ S.recLparams us)
      = (us.drop (us.length - S.lparams.length)).map (Level.eval φ) := by
  unfold recLparams at hus ⊢
  cases hl : S.large
  · simp only [hl, Bool.false_eq_true, if_false] at hus ⊢
    rw [hus, Nat.sub_self, List.drop_zero]
    exact map_substVal_eq φ hS.2.2.2.2.2.1 hus
  · simp only [hl, if_true] at hus ⊢
    cases us with
    | nil => simp at hus
    | cons u us' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hus
      rw [show (u :: us').length - S.lparams.length = 0 + 1 by simp [hus], List.drop_succ_cons,
        List.drop_zero, ← map_substVal_eq φ hS.2.2.2.2.2.1 hus]
      exact List.map_congr_left fun n hn =>
        Level.substVal_cons_of_ne φ (fun h => hS.2.2.2.2.1 hl (by rw [← h]; exact hn)) _ _ _

omit [IndLib V] [LevelOracle] in
/-- The recursor's own levels, instantiated and evaluated, are the
concrete levels. -/
theorem recLvls_map_eval (hS : S.Scoped env) (φ : Name → Nat) {us : List Level}
    (hus : us.length = S.recLparams.length) :
    S.recLvls.map (Level.eval (Level.substVal φ S.recLparams us)) = us.map (Level.eval φ) := by
  simp only [recLvls, List.map_map]
  exact map_substVal_eq φ (recLparams_nodup hS) hus

omit [IndLib V] [LevelOracle] in
/-- **The level comparison of `Red.iota`, semantically**: when the
constructor's levels evaluate as the recursor's last ones, the block's
valuation is the same whether read through the constructor's
instantiation or the recursor's. -/
theorem block_valuation_eq (hS : S.Scoped env) (φ : Name → Nat) {us usj : List Level}
    (hus : us.length = S.recLparams.length) (husj : usj.length = S.lparams.length)
    (hlv : usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ)) :
    S.lparams.map (Level.substVal φ S.lparams usj)
      = S.lparams.map (Level.substVal φ S.recLparams us) := by
  rw [map_substVal_eq φ hS.2.2.2.2.2.1 husj, lparams_map_substVal_rec hS φ hus, hlv, husj]

variable (hpl : S.nest = none) (hs : Env.Scoped env) (m : EnvModel V env) (hok : S.Ok env)
include hpl hs m hok

/-! ## The recursor's set applied -/

/-- The recursor's set at concrete levels, as the abstraction over its
context read in the final model at the instantiated valuation
(`recSet_mem`'s first step, separately). -/
theorem recSet_eq (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) :
    S.M₃ m.M S.recName (us.map (Level.eval φ)) =
      lamCtx (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (S.q.holds (Level.substVal φ S.recLparams us)) ρ S.recCtx fun ρ' =>
          S.recSem m.M (S.lparams.map (Level.substVal φ S.recLparams us))
            (S.q.holds (Level.substVal φ S.recLparams us))
            (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
            (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0) := by
  have hS := hok.scoped
  have hagr := recAgree_of (S := S) φ hus
  have hval : ∀ n ∈ S.lparams, valOf S.recLparams (us.map (Level.eval φ)) n
      = Level.substVal φ S.recLparams us n :=
    fun n hn => recVal_agree φ hus n (S.lparams_sub_recLparams hn)
  have hls := block_levels_eq (S := S) φ hus
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.recLparams us)
  have R₂ := reader₂ hpl hok m.M (Level.substVal φ S.recLparams us) hval
  have hwdC : ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps →
      CtxWD (S.M₃ m.M) (Level.substVal φ S.recLparams us) (consList ps ρ) (S.fieldCtx c.fields) :=
    fun c hc ps hps hp => (R₃.R.idxFit_of_wd hS hc (wd_ctorType hpl hs m hok hc _ ρ) hps hp).1
  have hagree := R₂.agree_recCtx hS R₃ hagr hok.freshI (hok.noCont hpl) base ρ hwdC
  have e : S.M₃ m.M S.recName (us.map (Level.eval φ)) = S.recSet m.M (us.map (Level.eval φ)) := by
    simp [M₃]
  rw [e]
  show lamCtx (S.M₂ m.M) (valOf S.recLparams (us.map (Level.eval φ)))
      (S.q.holds (valOf S.recLparams (us.map (Level.eval φ)))) base S.recCtx
      (fun ρ' => S.recSem m.M (S.lparams.map (valOf S.recLparams (us.map (Level.eval φ))))
        (S.q.holds (valOf S.recLparams (us.map (Level.eval φ))))
        (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)) = _
  rw [hls, hagr.q_holds]
  exact lamCtx_congr₂ hagree fun vs hvs => by
    obtain ⟨t, is, mins, m', ps, rfl, hi, hmins, hps⟩ := S.fits_recCtx_split hvs
    rw [recF_read S m.M _ _ hi hmins hps, recF_read S m.M _ _ hi hmins hps]

/-- **The recursor's set applied to a fitting spine**: the spine fits
the recursor's context, the value lies in the motive at the indices
and the major (the recursor's typing), the application chain is
well-formed, and in the graph regime the value is the semantic
recursor at the major (β over the recursor's context). -/
theorem rec_app_mem (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {ps : List V} {m' : V} {mins is : List V} {t : V}
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hmins : mins.length = S.n)
    (hmn : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      S.minorsCtx mins)
    (his : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps)
      S.indices is)
    (ht : t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps is) :
    FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ S.recCtx
      (t :: is ++ mins ++ [m'] ++ ps) ∧
    appList (S.M₃ m.M S.recName (us.map (Level.eval φ)))
        (ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ++ [t])
      ∈ˢ appList m' (is.reverse ++ [t]) ∧
    SpineOk (S.M₃ m.M S.recName (us.map (Level.eval φ)))
      (ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ++ [t]) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      appList (S.M₃ m.M S.recName (us.map (Level.eval φ)))
          (ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ++ [t])
        = S.recSem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) false ps m' mins is t) := by
  have hS := hok.scoped
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.recLparams us)
  have hi : is.length = S.nI := by have := FitsVals_length m.M _ his; simpa [nI] using this
  have hfit : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ S.recCtx
      (t :: is ++ mins ++ [m'] ++ ps) :=
    (R₃.R.fits_recCtx_iff hS hi hmins hps).mpr ⟨hp, hm, hmn, his, ht⟩
  have hrev : ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ++ [t]
      = (t :: is ++ mins ++ [m'] ++ ps).reverse := by
    simp [List.reverse_append]
  have e : S.M₃ m.M S.recName (us.map (Level.eval φ)) = S.recSet m.M (us.map (Level.eval φ)) := by
    simp [M₃]
  have hf := recSet_mem hpl hs m hok φ ρ hus
  rw [recType_eq, interp_mkPis] at hf
  have hG : S.q.holds (Level.substVal φ S.recLparams us) = true →
      ∀ ws, FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ S.recCtx ws →
        interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) (consList ws ρ)
          (Expr.mkAppN (.bvar (1 + S.nI + S.n)) (Expr.varsAt 1 S.nI ++ [.bvar 0])) ∈ˢ
          (univ 0 : V) := by
    intro hq ws hws
    obtain ⟨t', is', mins', m'', ps', rfl, hi', hmins', hps'⟩ := S.fits_recCtx_split hws
    obtain ⟨hp', hm', -, his', ht'⟩ := (R₃.R.fits_recCtx_iff hS hi' hmins' hps').mp hws
    rw [read_recBody S _ _ hi' hmins']
    have hz := S.q_holds (Level.substVal φ S.recLparams us)
    rw [hq, Bool.true_eq, beq_iff_eq] at hz
    rw [← hz]
    exact R₃.R.motiveOk_of_mem hS hps' hp' hm' is' his' t' ht'
  refine ⟨hfit, ?_, ?_, ?_⟩
  · rw [hrev, e]
    have := appList_mem_of_piCtx _ _ hf hfit
    rwa [read_recBody S _ _ hi hmins] at this
  · rw [hrev, e]
    exact spineOk_of_piCtx _ _ hf hfit hG
  · intro hq
    rw [hrev, recSet_eq hpl hs m hok φ ρ hus, hq, appList_lamCtx_false hfit,
      recF_read S m.M _ _ hi hmins hps]

/-! ## The major: the constructor's set applied -/

/-- **The constructor's set applied to fitting values** is the
constructor value at the fields, and the values fit semantically: the
parameters the parameter context, the fields the constructor's fields.
-/
theorem ctor_app (φ : Name → Nat) (ρ : Nat → V) {usj : List Level}
    (husj : usj.length = S.lparams.length) {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c)
    {ps fs : List V} (hps : ps.length = S.nP) (hf : fs.length = c.fields.length)
    (hfit : TeleFitV (S.M₃ m.M) (Level.substVal φ S.lparams usj) ρ (S.ctorType c)
      (ps.reverse ++ fs.reverse)) :
    FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.lparams usj))) base S.params ps ∧
    S.FitsFields m.M (S.lparams.map (Level.substVal φ S.lparams usj))
      (S.bound m.M (S.lparams.map (Level.substVal φ S.lparams usj)))
      (S.Mem m.M (S.lparams.map (Level.substVal φ S.lparams usj))) ps c.fields fs ∧
    appList (S.M₃ m.M c.name (usj.map (Level.eval φ))) (ps.reverse ++ fs.reverse)
      = S.ctorVal (S.lparams.map (Level.substVal φ S.lparams usj)) j fs := by
  have hS := hok.scoped
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.lparams usj)
  unfold ctorType at hfit
  rw [← List.reverse_append, TeleFitV_mkPis _ _ _ (by simp [hf, hps, length_fieldCtx, nP, Nat.add_comm]),
    List.reverse_reverse, FitsVals_append _ _ (by rw [hf, length_fieldCtx])] at hfit
  obtain ⟨hpF, hfF⟩ := hfit
  have hp := (R₃.R.fits_params hS).mp hpF
  have hidx := R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm _ ρ) hps hp
  have hff := (R₃.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp hidx.1).1.mp hfF
  refine ⟨hp, hff, ?_⟩
  rw [R₃.ctor j c hc, ← lparams_map_substVal hok φ husj]
  have R₁ := S.reader₁ (M := m.M) (φ := Level.substVal φ S.lparams usj) hok.freshI
    (S.contGood_of_plain hpl _ _)
  have hfit₁ : FitsVals (S.M₁ m.M) (S.ψ (S.lparams.map (Level.substVal φ S.lparams usj))) base
      (S.fieldCtx c.fields ++ S.params) (fs ++ ps) :=
    (FitsVals_append _ _ (by rw [hf, S.length_fieldCtx])).mpr
      ⟨(R₁.fits_params hS).mpr hp,
       R₁.fits_fieldCtx_of_idx hS (hS.2.2.2.1 c hcm).1 (ρ := base) hps hp hff (hidx.2 fs hff).2.1⟩
  unfold ctorSet
  rw [← List.reverse_append]
  cases hz : S.z (S.lparams.map (Level.substVal φ S.lparams usj))
  · rw [appList_lamCtx_false hfit₁, consList_append, readEnv_consList hf]
  · rw [appList_lamCtx _ _ hfit₁ (G := fun _ => truthVal True)
      (fun ws _ => by simp [ctorVal, hz]; exact pt_mem_truthVal trivial)
      (fun _ _ _ => truthVal_mem_univ_zero _), consList_append, readEnv_consList hf]

/-! ## The rule's context -/

/-- **Values fitting a rule's context**: the parameters fit, the
motive is in its type, the minors fit theirs, and the fields fit the
constructor's fields semantically — and conversely. -/
theorem fits_ruleCtx (φr : Name → Nat) (ρ : Nat → V) {c : CtorSpec} (hcm : c ∈ S.ctors)
    {fs mins : List V} {m' : V} {ps : List V}
    (hf : fs.length = c.fields.length) (hmins : mins.length = S.n) (hps : ps.length = S.nP) :
    FitsVals (S.M₃ m.M) φr ρ (S.ruleCtx c) (fs ++ mins ++ [m'] ++ ps) ↔
      FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps ∧
      m' ∈ˢ interp (S.M₃ m.M) φr (consList ps ρ) S.motiveTy ∧
      FitsVals (S.M₃ m.M) φr (cons m' (consList ps ρ)) S.minorsCtx mins ∧
      S.FitsFields m.M (S.lparams.map φr) (S.bound m.M (S.lparams.map φr))
        (S.Mem m.M (S.lparams.map φr)) ps c.fields fs := by
  have hS := hok.scoped
  have R₃ := reader₃ hpl hok m.M φr
  have hosl : (mins ++ [m']).length = S.n + 1 := by simp [hmins]
  have e2 : consList mins (cons m' (consList ps ρ)) = consList (mins ++ [m']) (consList ps ρ) := by
    simp [consList_append]
  unfold ruleCtx
  rw [FitsVals_append _ _ (by simp [hf, hmins, length_fieldCtxAt, length_minorsCtx]),
    FitsVals_append _ _ (by simp [hf, hmins, length_fieldCtxAt, length_minorsCtx]),
    FitsVals_append _ _ (by simp [hf, length_fieldCtxAt]), FitsVals_cons]
  simp only [FitsVals_nil_nil, true_and, consList_cons, consList_nil]
  rw [R₃.R.fits_params hS, e2]
  unfold fieldCtxAt
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hosl]
  constructor
  · rintro ⟨hp, hm, hmn, hfF⟩
    exact ⟨hp, hm, hmn, (R₃.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp
      (R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm φr ρ) hps hp).1).1.mp hfF⟩
  · rintro ⟨hp, hm, hmn, hfF⟩
    exact ⟨hp, hm, hmn, (R₃.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp
      (R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm φr ρ) hps hp).1).1.mpr hfF⟩

/-! ## The inductive hypotheses' terms -/

/-- A field's domain is well-denoted at fitting earlier fields. -/
theorem wd_fieldDom (φr : Name → Nat) (ρ : Nat → V) {c : CtorSpec} (hcm : c ∈ S.ctors)
    {ps fs : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps)
    (hfit : S.FitsFields m.M (S.lparams.map φr) (S.bound m.M (S.lparams.map φr))
      (S.Mem m.M (S.lparams.map φr)) ps c.fields fs)
    {k : Nat} {f : Field} (hkf : c.fields[c.fields.length - 1 - k]? = some f)
    (hk : k < c.fields.length) :
    WellDenoted (S.M₃ m.M) φr (consList (earlier fs k) (consList ps ρ)) (S.fieldDom k f) := by
  have hS := hok.scoped
  have R₃ := reader₃ hpl hok m.M φr
  have hidx := R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm φr ρ) hps hp
  have hf := S.FitsFields_length m.M _ hfit
  have hfF := (hidx.2 fs hfit).1
  have hA : (S.fieldCtx c.fields)[c.fields.length - 1 - k]? = some (S.fieldDom k f) := by
    rw [fieldCtx_getElem?, hkf]
    simp only [Option.map_some, Option.some.injEq]
    congr 1
    omega
  have hdrop := FitsVals_drop (S.M₃ m.M) φr (c.fields.length - k) hfF
  rw [show c.fields.length - k = c.fields.length - 1 - k + 1 by omega] at hdrop
  have := CtxWD_getElem? (S.M₃ m.M) φr hidx.1 hA _ hdrop
  rwa [show fs.drop (c.fields.length - 1 - k + 1) = earlier fs k by
    unfold earlier; rw [hf]; congr 1; omega] at this

/-- **A recursor call in a rule**, at the parameters, the motive and
the minors, index expressions `es` lifted into the rule's frame (`mt`
binders of a reflexive field's telescope below the fields) and a last
argument denoting `t`: well-denoted; a member of the motive at the
index values and `t`; and, in the graph regime, the semantic recursor
at `t`.  Everything comes from the spine fitting the recursor's
context (`rec_app_mem`). -/
theorem recCall_ok (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {c : CtorSpec}
    {k mt : Nat} (hk : k ≤ c.fields.length) {es : List Expr}
    (hsc : ∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k + mt) e)
    {ys fs mins : List V} {m' : V} {ps : List V} (hy : ys.length = mt)
    (hf : fs.length = c.fields.length) (hmins : mins.length = S.n) (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hmn : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      S.minorsCtx mins)
    {last : Expr} {t : V}
    (hlast : interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))) last = t)
    (hwdl : WellDenoted (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))) last)
    (hwdes : ∀ e ∈ es, WellDenoted (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList (earlier fs k) (consList ps ρ))) e)
    (his : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps)
      S.indices (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
        (consList ys (consList (earlier fs k) (envP ps))) es))
    (ht : t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps
      (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
        (consList ys (consList (earlier fs k) (envP ps))) es)) :
    WellDenoted (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
      (Expr.mkAppN (.const S.recName S.recLvls)
        (Expr.varsAt (mt + c.fields.length + S.n + 1) S.nP ++ [.bvar (mt + c.fields.length + S.n)] ++
          Expr.varsAt (mt + c.fields.length) S.n ++
          es.map (Expr.atCtx c.fields.length k 0 (S.n + 1) mt) ++ [last])) ∧
    appList (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))
        (mt + c.fields.length + S.n))
      ((es.map fun e => interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
        (Expr.atCtx c.fields.length k 0 (S.n + 1) mt e)) ++
        [interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
          (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))) last])
      = appList m' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t]) ∧
    interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
      (Expr.mkAppN (.const S.recName S.recLvls)
        (Expr.varsAt (mt + c.fields.length + S.n + 1) S.nP ++ [.bvar (mt + c.fields.length + S.n)] ++
          Expr.varsAt (mt + c.fields.length) S.n ++
          es.map (Expr.atCtx c.fields.length k 0 (S.n + 1) mt) ++ [last]))
      ∈ˢ appList m' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t]) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
        (Expr.mkAppN (.const S.recName S.recLvls)
          (Expr.varsAt (mt + c.fields.length + S.n + 1) S.nP ++ [.bvar (mt + c.fields.length + S.n)] ++
            Expr.varsAt (mt + c.fields.length) S.n ++
            es.map (Expr.atCtx c.fields.length k 0 (S.n + 1) mt) ++ [last]))
        = S.recSem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) false ps m' mins
            (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
              (consList ys (consList (earlier fs k) (envP ps))) es) t) := by
  have hS := hok.scoped
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.recLparams us)
  have hosl : (mins ++ [m']).length = S.n + 1 := by simp [hmins]
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  -- the head
  have hhead : interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
      (.const S.recName S.recLvls) = S.M₃ m.M S.recName (us.map (Level.eval φ)) := by
    rw [interp_const, recLvls_map_eval hS φ hus]
  -- the motive's slot and the parameter and minor slots
  have hmot : consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))
      (mt + c.fields.length + S.n) = m' := by
    rw [show consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))
        = consList (ys ++ fs ++ mins) (cons m' (consList ps ρ)) by simp [consList_append],
      show mt + c.fields.length + S.n = 0 + (ys ++ fs ++ mins).length by simp [hy, hf, hmins]; omega,
      consList_ge]
    rfl
  have hparams : readEnv S.nP (shiftE (mt + c.fields.length + S.n + 1) 0
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))) = ps := by
    rw [show consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))
        = consList (ys ++ fs ++ (mins ++ [m'])) (consList ps ρ) by simp [consList_append],
      shiftE_consList' (by simp [hy, hf, hmins]; omega), readEnv_consList hps]
  have hminors : readEnv S.n (shiftE (mt + c.fields.length) 0
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))) = mins := by
    rw [show consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))
        = consList (ys ++ fs) (consList (mins ++ [m']) (consList ps ρ)) by simp [consList_append],
      shiftE_consList' (by simp [hy, hf]), consList_append, readEnv_consList hmins]
  -- the index expressions
  have hes : es.map (fun e => interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
      (Expr.atCtx c.fields.length k 0 (S.n + 1) mt e))
      = (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse := by
    unfold idxVals
    rw [List.reverse_reverse]
    apply List.map_congr_left
    intro e he
    have h1 := interp_atCtx (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ e (ys := ys) (ihs := []) (l := 0)
      (fs := fs) (os := mins ++ [m']) (ps := ps) hy rfl hf hosl hk
    simp only [consList_nil] at h1
    rw [h1, hkd, ← consList_append ys (earlier fs k) (consList ps ρ),
      ← consList_append ys (earlier fs k) (envP ps)]
    refine R₃.R.read (hsc e he) ?_
    simp only [List.length_append, hy, earlier, List.length_drop, hf, hps]
    omega
  have hargs : (Expr.varsAt (mt + c.fields.length + S.n + 1) S.nP ++ [Expr.bvar (mt + c.fields.length + S.n)] ++
        Expr.varsAt (mt + c.fields.length) S.n ++
        es.map (Expr.atCtx c.fields.length k 0 (S.n + 1) mt) ++ [last]).map
        (interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
          (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ)))))
      = ps.reverse ++ [m'] ++ mins.reverse ++
        (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t] := by
    simp only [List.map_append, List.map_singleton, List.map_map, interp_varsAt, interp_bvar]
    rw [hparams, hminors, hmot, hlast, ← hes]
    rfl
  have key := rec_app_mem hpl hs m hok φ ρ hus hps hp hm hmins hmn his ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
    · intro a ha
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with ((((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl)
      · exact Expr.wd_of_mem_varsAt ha
      · simp
      · exact Expr.wd_of_mem_varsAt ha
      · have h := WellDenoted_atCtx (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ e (ys := ys)
          (ihs := []) (l := 0) (fs := fs) (os := mins ++ [m']) (ps := ps) hy rfl hf hosl hk
        simp only [consList_nil] at h
        rw [h, hkd]
        exact hwdes e he
      · exact hwdl
    · rw [hhead, hargs]
      exact key.2.2.1
  · rw [hes, hmot, hlast]
  · rw [interp_mkAppN_appList, hhead, hargs]
    exact key.2.1
  · intro hq
    rw [interp_mkAppN_appList, hhead, hargs]
    exact key.2.2.2 hq

/-- **An inductive hypothesis' term, read**: well-denoted, a member
of the hypothesis' set (`IhTyped`), and in the graph regime the
semantic inductive hypothesis — a recursor call at the field, through
its telescope at a reflexive field (`Reader.lamCtx_liftCtx_atCtx`). -/
theorem ihVal_ok (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {c : CtorSpec} (hcm : c ∈ S.ctors)
    {kf : Nat × Field} (hkf : kf ∈ c.recFields)
    {fs mins : List V} {m' : V} {ps : List V}
    (hf : fs.length = c.fields.length) (hmins : mins.length = S.n) (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hmn : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      S.minorsCtx mins)
    (hfit : S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us))
      (S.bound m.M (S.lparams.map (Level.substVal φ S.recLparams us)))
      (S.Mem m.M (S.lparams.map (Level.substVal φ S.recLparams us))) ps c.fields fs) :
    WellDenoted (S.M₃ m.M) (Level.substVal φ S.recLparams us)
      (consList fs (consList (mins ++ [m']) (consList ps ρ))) (S.ihVal c.fields.length kf.1 kf.2) ∧
    S.IhTyped m.M (S.lparams.map (Level.substVal φ S.recLparams us))
      (S.q.holds (Level.substVal φ S.recLparams us)) ps m' pt fs kf
      (interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (consList fs (consList (mins ++ [m']) (consList ps ρ))) (S.ihVal c.fields.length kf.1 kf.2)) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (consList fs (consList (mins ++ [m']) (consList ps ρ))) (S.ihVal c.fields.length kf.1 kf.2)
      = S.ihSem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) false ps m' mins fs kf) := by
  have hS := hok.scoped
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.recLparams us)
  obtain ⟨k, f⟩ := kf
  obtain ⟨hkf', hk, hrec⟩ := mem_recFields hkf
  dsimp only at hkf' hk hrec ⊢
  have hosl : (mins ++ [m']).length = S.n + 1 := by simp [hmins]
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  have hsc := (hS.2.2.2.1 c hcm).1 _ f hkf'
  rw [show c.fields.length - 1 - (c.fields.length - 1 - k) = k by omega] at hsc
  have hget := S.FitsFields_get m.M _ hfit hkf' hk
  have hwdD := wd_fieldDom hpl hs m hok _ ρ hcm hps hp hfit hkf' hk
  have hidx := (R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm _ ρ) hps hp).2 fs hfit
  have hfv : consList fs (consList (mins ++ [m']) (consList ps ρ)) (c.fields.length - 1 - k)
      = fieldVal fs k := by
    rw [consList_getD (by omega)]
    unfold fieldVal
    rw [hf]
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container => exact (S.noCont_absurd (hok.noCont hpl) hcm hkf').elim
  | reflexive tele es =>
    have hmt : tele.length = tele.length := rfl
    -- the field's domain: a product over the telescope
    simp only [fieldDom] at hwdD
    rw [WellDenoted_mkPis] at hwdD
    obtain ⟨hwdT, hwdB⟩ := hwdD
    simp only [fieldSet] at hget
    -- fitting the telescope, in the final model and the block's
    have hagree := R₃.R.agree_tele hsc.1 (vs := earlier fs k) (ps := ps) (ρ := ρ)
      (by simp [earlier, hf]; omega) hps
    have hfitT : ∀ ys, FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us)
        (consList fs (consList (mins ++ [m']) (consList ps ρ)))
        (Expr.liftCtx (fun t T => Expr.atCtx c.fields.length k 0 (S.n + 1) t T) tele) ys ↔
        FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us)))
          (consList (earlier fs k) (envP ps)) tele ys := by
      intro ys
      have h := FitsVals_liftCtx_atCtx (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ tele ys
        (ihs := []) (l := 0) (fs := fs) (os := mins ++ [m']) (ps := ps) rfl hf hosl (Nat.le_of_lt hk)
      simp only [consList_nil] at h
      rw [h, hkd]
      exact FitsVals_congr₂ hagree
    -- the call under the telescope
    have hcall := fun ys (hys : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us)))
        (consList (earlier fs k) (envP ps)) tele ys) =>
        have hlen := FitsVals_length m.M _ hys
        have hys' : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams us)
            (consList (earlier fs k) (consList ps ρ)) tele ys := (FitsVals_congr₂ hagree).mpr hys
        have hmem := appList_mem_of_piCtx m.M _ hget hys
        have hspine := spineOk_of_piCtx m.M _ hget hys fun hz _ _ => by
          simp only [hz, fibreR, if_true]; exact truthVal_mem_univ_zero _
        have hlastV : interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
            (consList ys (consList fs (consList (mins ++ [m']) (consList ps ρ))))
            (Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k)) (Expr.varsAt 0 tele.length))
            = appList (fieldVal fs k) ys.reverse := by
          rw [interp_mkAppN_appList, interp_bvar, interp_varsAt, shiftE_zero_zero,
            readEnv_consList hlen,
            show tele.length + c.fields.length - 1 - k = (c.fields.length - 1 - k) + ys.length by
              rw [hlen]; omega,
            consList_ge, hfv]
        recCall_ok hpl hs m hok φ ρ hus (c := c) (mt := tele.length) (Nat.le_of_lt hk) (es := es)
          (fun e he => hsc.2.2 e he) (ys := ys) hlen hf hmins hps hp hm hmn
          (last := Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k))
            (Expr.varsAt 0 tele.length))
          (t := appList (fieldVal fs k) ys.reverse) hlastV
          (WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) (fun a ha => Expr.wd_of_mem_varsAt ha)
            (by rw [interp_bvar, interp_varsAt, shiftE_zero_zero, readEnv_consList hlen,
              show tele.length + c.fields.length - 1 - k = (c.fields.length - 1 - k) + ys.length by
                rw [hlen]; omega,
              consList_ge, hfv]; exact hspine))
          (fun e he => (WellDenoted_mkAppN' _ _ (hwdB ys hys').1).2 e (List.mem_append_right _ he))
          (hidx.2.1 k _ hkf' hk ys hys) hmem
    -- the abstraction over the lifted telescope
    have hl := R₃.R.lamCtx_liftCtx_atCtx (ihsE := []) (l := 0) (fs := fs) (os := mins ++ [m']) (ps := ps)
      (ρ := ρ) rfl hf hosl (Nat.le_of_lt hk) hps (S.q.holds (Level.substVal φ S.recLparams us)) tele
      hsc.1
    simp only [consList_nil] at hl
    refine ⟨?_, ?_, ?_⟩
    · -- the invariant
      simp only [ihVal]
      refine WellDenoted_mkLams_sem _ _ ?_ ?_ ?_
        (G := fun ρ₁ => appList (ρ₁ (tele.length + c.fields.length + S.n))
          ((es.map fun e => interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ₁
            (Expr.atCtx c.fields.length k 0 (S.n + 1) tele.length e)) ++
            [interp (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ₁
              (Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k))
                (Expr.varsAt 0 tele.length))]))
      · have h := CtxWD_liftCtx_atCtx (S.M₃ m.M) (Level.substVal φ S.recLparams us) ρ
          (ihs := []) (l := 0) (fs := fs) (os := mins ++ [m']) (ps := ps) rfl hf hosl (Nat.le_of_lt hk) tele
        simp only [consList_nil] at h
        rw [h, hkd]
        exact hwdT
      · intro ys hys
        have h := hcall ys ((hfitT ys).mp hys)
        refine ⟨h.1, ?_⟩
        rw [h.2.1]
        exact h.2.2.1
      · intro hq ys hys
        have h := hcall ys ((hfitT ys).mp hys)
        rw [h.2.1]
        have hz := S.q_holds (Level.substVal φ S.recLparams us)
        rw [hq, Bool.true_eq, beq_iff_eq] at hz
        rw [← hz]
        exact R₃.R.motiveOk_of_mem hS hps hp hm _ (hidx.2.1 k _ hkf' hk ys ((hfitT ys).mp hys)) _
          (appList_mem_of_piCtx m.M _ hget ((hfitT ys).mp hys))
    · -- the hypothesis' set
      dsimp only [IhTyped, ihVal]
      rw [interp_mkLams, hl, hkd]
      refine lamCtx_mem_piCtx m.M _ (fun ys hys => ?_) fun hq ys hys => ?_
      · have hlen := FitsVals_length m.M _ hys
        rw [readEnv_consList hlen]
        exact (hcall ys hys).2.2.1
      · have hlen := FitsVals_length m.M _ hys
        rw [readEnv_consList hlen]
        have hz := S.q_holds (Level.substVal φ S.recLparams us)
        rw [hq, Bool.true_eq, beq_iff_eq] at hz
        rw [← hz]
        exact R₃.R.motiveOk_of_mem hS hps hp hm _ (hidx.2.1 k _ hkf' hk ys hys) _
          (appList_mem_of_piCtx m.M _ hget hys)
    · -- the graph regime
      intro hq
      dsimp only [ihSem, ihVal]
      rw [interp_mkLams, hl, hkd, hq]
      refine lamCtx_congr m.M _ fun ys hys => ?_
      have hlen := FitsVals_length m.M _ hys
      rw [readEnv_consList hlen]
      exact (hcall ys hys).2.2.2 hq

/-! ## The ι law -/

omit [LevelOracle] hpl hs hok in
/-- Any list fitting a rule's context splits as the fields, the
minors, the motive and the parameters. -/
theorem fits_ruleCtx_split (φr : Name → Nat) {ρ : Nat → V} {c : CtorSpec} {vs : List V}
    (h : FitsVals (S.M₃ m.M) φr ρ (S.ruleCtx c) vs) :
    ∃ (fs mins : List V) (m' : V) (ps : List V),
      vs = fs ++ mins ++ [m'] ++ ps ∧ fs.length = c.fields.length ∧ mins.length = S.n ∧
        ps.length = S.nP := by
  have hl := FitsVals_length _ _ h
  rw [length_ruleCtx] at hl
  obtain ⟨m', ps, hmp⟩ : ∃ m' ps, (vs.drop c.fields.length).drop S.n = m' :: ps := by
    cases hd : (vs.drop c.fields.length).drop S.n with
    | nil =>
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil, hl] at this
      omega
    | cons m' ps => exact ⟨m', ps, rfl⟩
  have hps : ps.length = S.nP := by
    have := congrArg List.length hmp
    simp only [List.length_drop, List.length_cons, hl] at this
    omega
  refine ⟨vs.take c.fields.length, (vs.drop c.fields.length).take S.n, m', ps, ?_, ?_, ?_, hps⟩
  · rw [List.append_assoc, List.append_assoc, List.singleton_append, ← hmp, List.take_append_drop,
      List.take_append_drop]
  · simp only [List.length_take, hl]; omega
  · simp only [List.length_take, List.length_drop, hl]; omega

/-- **The ι law of a generated rule** (`RecRuleLaw`, `EnvModel.lean`)
for the recursor's constant and the constructor's, at the recursor's
`nP` parameters, `nP + 1 + n` arguments before the indices and the
major at `nP + 1 + n + nI`. -/
theorem rec_rule_law {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) :
    RecRuleLaw (S.M₃ m.M) S.recName S.recInfo S.nP (S.nP + 1 + S.n) (S.nP + 1 + S.n + S.nI)
      ⟨c.name, c.fields.length, S.ruleRhs c j, none⟩ (S.ctorInfo c) := by
  intro φ ρ us usj xs ys hus husj hxs hys hfitR hfitC hlv hpar hidx
  have hS := hok.scoped
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
  have hnf : c.fields.length = c.fields.length := rfl
  simp only [recInfo, ctorInfo] at hus husj hfitR hfitC hlv hidx ⊢
  rw [TeleFitV_instL] at hfitR hfitC
  have R₃ := reader₃ hpl hok m.M (Level.substVal φ S.recLparams us)
  have hLj : S.lparams.map (Level.substVal φ S.lparams usj)
      = S.lparams.map (Level.substVal φ S.recLparams us) :=
    block_valuation_eq hS φ hus husj hlv
  -- the recursor's spine, split
  obtain ⟨m', rest, hd⟩ : ∃ m' rest, xs.drop S.nP = m' :: rest := by
    cases hd : xs.drop S.nP with
    | nil =>
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil, hxs] at this
      omega
    | cons m' rest => exact ⟨m', rest, rfl⟩
  have hrest : rest.length = S.n + S.nI := by
    have := congrArg List.length hd
    simp only [List.length_drop, List.length_cons, hxs] at this
    omega
  obtain ⟨ps, mins, is, hxs', hps, hmins, hi⟩ : ∃ ps mins is,
      xs = ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ∧ ps.length = S.nP ∧
        mins.length = S.n ∧ is.length = S.nI :=
    ⟨(xs.take S.nP).reverse, (rest.take S.n).reverse, (rest.drop S.n).reverse,
      by
        rw [List.reverse_reverse, List.reverse_reverse, List.reverse_reverse, List.append_assoc,
          List.append_assoc, List.take_append_drop, List.singleton_append, ← hd,
          List.take_append_drop],
      by simp only [List.length_reverse, List.length_take, hxs]; omega,
      by simp only [List.length_reverse, List.length_take, hrest]; omega,
      by simp only [List.length_reverse, List.length_drop, hrest]; omega⟩
  subst hxs'
  have hfitR' := hfitR
  rw [recType_eq, TeleFitV_mkPis _ _ _ (by
      simp only [List.length_append, List.length_singleton, hxs, length_recCtx]; omega),
    show (ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse ++
        [appList (S.M₃ m.M c.name (usj.map (Level.eval φ))) ys]).reverse
      = appList (S.M₃ m.M c.name (usj.map (Level.eval φ))) ys :: is ++ mins ++ [m'] ++ ps by
      simp [List.reverse_append]] at hfitR'
  obtain ⟨hp, hm, hmn, his, ht⟩ := (R₃.R.fits_recCtx_iff hS hi hmins hps).mp hfitR'
  -- the constructor's spine, split
  obtain ⟨ps₂, fs, hys₂, hps₂, hf⟩ : ∃ ps₂ fs, ys = ps₂.reverse ++ fs.reverse ∧
      ps₂.length = S.nP ∧ fs.length = c.fields.length :=
    ⟨(ys.take S.nP).reverse, (ys.drop S.nP).reverse, by simp,
      by rw [List.length_reverse, List.length_take, hys]; omega,
      by rw [List.length_reverse, List.length_drop, hys, Nat.add_sub_cancel_left]⟩
  subst hys₂
  have hle₁ : S.nP ≤ (ps.reverse ++ [m'] ++ mins.reverse).length := by
    simp only [List.length_append, List.length_reverse, List.length_singleton, hps]; omega
  have hle₂ : S.nP ≤ (ps.reverse ++ [m']).length := by
    simp only [List.length_append, List.length_reverse, List.length_singleton, hps]; omega
  have hle₃ : ps.reverse.length ≤ S.nP := Nat.le_of_eq (by rw [List.length_reverse, hps])
  have hle₃' : S.nP ≤ ps.reverse.length := Nat.le_of_eq (by rw [List.length_reverse, hps])
  have hle₄ : ps₂.reverse.length ≤ S.nP := Nat.le_of_eq (by rw [List.length_reverse, hps₂])
  have hle₄' : S.nP ≤ ps₂.reverse.length := Nat.le_of_eq (by rw [List.length_reverse, hps₂])
  have htake₁ : (ps₂.reverse ++ fs.reverse).take S.nP = ps₂.reverse := by
    rw [List.take_append_of_le_length hle₄', List.take_of_length_le hle₄]
  have htake₂ : (ps.reverse ++ [m'] ++ mins.reverse ++ is.reverse).take S.nP = ps.reverse := by
    rw [List.take_append_of_le_length hle₁, List.take_append_of_le_length hle₂,
      List.take_append_of_le_length hle₃', List.take_of_length_le hle₃]
  rw [htake₁, htake₂, List.reverse_inj] at hpar
  subst ps₂
  -- the major is the constructor value at the fields
  obtain ⟨-, hfitF, hmajor⟩ := ctor_app hpl hs m hok φ ρ husj hc hps hf hfitC
  rw [hLj] at hfitF hmajor
  -- the index comparison: the indices are the constructor's index values
  have hisv : is = S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
      (consList fs (envP ps)) c.idx := by
    have hB := hidx ((S.famAt c.fields.length c.idx).instL S.lparams usj) (consList (fs ++ ps) ρ)
      S.name (S.lvls.map (Level.subst S.lparams usj))
      ((Expr.varsAt c.fields.length S.nP).map (·.instL S.lparams usj))
      (c.idx.map (·.instL S.lparams usj))
      (by
        rw [piBodyV_instL, ctorType,
          piBodyV_mkPis _ (by simp [hf, hps, length_fieldCtx, nP, Nat.add_comm])]
        simp [List.reverse_append])
      (by simp [famAt, Expr.instL_mkAppN])
      (by simp [Expr.varsAt, nP])
    rw [List.drop_left' (by simp [hps, hmins]; omega)] at hB
    have hlen : ((c.idx.map (·.instL S.lparams usj)).map (interp (S.M₃ m.M) φ (consList (fs ++ ps) ρ))).length
        = is.reverse.length := by
      simp [hi, (hS.2.2.2.1 c hcm).2.2.1]
    have := List.map_eq_of_zip id hlen hB
    simp only [List.map_id, List.map_map, Function.comp_def, id_eq, interp_instL, consList_append] at this
    rw [← List.reverse_reverse is, ← this,
      (reader₃ hpl hok m.M (Level.substVal φ S.lparams usj)).R.idxVals_eq
        (hS.2.2.2.1 c hcm).2.2.2 (by simp [hf, hps]; omega), hLj]
  subst hisv
  rw [hmajor] at ht ⊢
  -- the left-hand side: the semantic recursor at the constructor value
  have key := rec_app_mem hpl hs m hok φ ρ hus hps hp hm hmins hmn his ht
  -- the right-hand side's context and spine
  have hfitRule := (fits_ruleCtx hpl hs m hok _ ρ hcm hf hmins hps).mpr ⟨hp, hm, hmn, hfitF⟩
  have hspineR : (ps.reverse ++ [m'] ++ mins.reverse ++
        (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList fs (envP ps)) c.idx).reverse).take (S.nP + 1 + S.n) ++
        (ps.reverse ++ fs.reverse).drop S.nP
      = (fs ++ mins ++ [m'] ++ ps).reverse := by
    rw [List.take_left' (by simp [hps, hmins]; omega), List.drop_left' (by simp [hps])]
    simp [List.reverse_append]
  have henv : consList (fs ++ mins ++ [m'] ++ ps) ρ
      = consList fs (consList (mins ++ [m']) (consList ps ρ)) := by
    simp [consList_append]
  -- the minor's slot in a rule's environment
  have hminor : ∀ (fs' mins' : List V) (m'' : V) (ps' : List V), fs'.length = c.fields.length →
      mins'.length = S.n →
      consList fs' (consList (mins' ++ [m'']) (consList ps' ρ)) (c.fields.length + S.n - 1 - j)
        = S.minorAt mins' j := by
    intro fs' mins' m'' ps' hf' hmins'
    rw [show c.fields.length + S.n - 1 - j = (S.n - 1 - j) + fs'.length by rw [hf']; omega,
      consList_ge, consList_append, consList_getD (by omega)]
    rfl
  -- the rule's body, read at fitting values
  have hbody : ∀ (fs' mins' : List V) (m'' : V) (ps' : List V), fs'.length = c.fields.length →
      mins'.length = S.n →
      interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (mins' ++ [m'']) (consList ps' ρ)))
          (Expr.mkAppN (.bvar (c.fields.length + S.n - 1 - j))
            (Expr.varsAt 0 c.fields.length ++
              c.recFields.map fun kf => S.ihVal c.fields.length kf.1 kf.2))
        = appList (S.minorAt mins' j) (fs'.reverse ++ c.recFields.map fun kf =>
            interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
              (consList fs' (consList (mins' ++ [m'']) (consList ps' ρ)))
              (S.ihVal c.fields.length kf.1 kf.2)) := by
    intro fs' mins' m'' ps' hf' hmins'
    rw [interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map, interp_varsAt,
      shiftE_zero_zero, readEnv_consList hf', hminor fs' mins' m'' ps' hf' hmins']
    rfl
  -- the rule's type, read: the motive at the constructor's index values and value
  have hty : ∀ (fs' mins' : List V) (m'' : V) (ps' : List V), fs'.length = c.fields.length →
      mins'.length = S.n → ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us))
        (S.bound m.M (S.lparams.map (Level.substVal φ S.recLparams us)))
        (S.Mem m.M (S.lparams.map (Level.substVal φ S.recLparams us))) ps' c.fields fs' →
      interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (mins' ++ [m'']) (consList ps' ρ))) (S.ruleBodyTy c)
        = appList m'' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
            (consList fs' (envP ps')) c.idx).reverse ++
            [S.ctorVal (S.lparams.map (Level.substVal φ S.recLparams us)) j fs']) := by
    intro fs' mins' m'' ps' hf' hmins' hps' hp' hfitF'
    have hidx' := (R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm _ ρ) hps' hp').2 fs' hfitF'
    have h := R₃.read_concl hS hok.freshI hc (ihsE := []) (nIh := 0) (o := S.n + 1) (os := mins' ++ [m''])
      (ρ := ρ) rfl hf' (by simp [hmins']) (Nat.succ_pos _) hps' hp' hfitF' hidx'.2.1
    have hg : (mins' ++ [m'']).getD S.n pt = m'' := by rw [← hmins']; exact getD_append_length _
    rw [consList_nil, show 0 + c.fields.length + (S.n + 1) - 1 = c.fields.length + S.n by omega,
      show 0 + c.fields.length + (S.n + 1) = c.fields.length + S.n + 1 by omega,
      Nat.add_sub_cancel, hg] at h
    exact h
  -- the rule's right-hand side is well-denoted and in the rule's type
  have hT := wd_ruleType hpl hs m hok hcm (Level.substVal φ S.recLparams us) ρ
  unfold ruleType at hT
  have hrhs := mkLams_ok _ _ hT (b := Expr.mkAppN (.bvar (c.fields.length + S.n - 1 - j))
      (Expr.varsAt 0 c.fields.length ++ c.recFields.map fun kf => S.ihVal c.fields.length kf.1 kf.2))
    fun vs hvs => by
      obtain ⟨fs', mins', m'', ps', rfl, hf', hmins', hps'⟩ := fits_ruleCtx_split m _ hvs
      obtain ⟨hp', hm', hmn', hfitF'⟩ := (fits_ruleCtx hpl hs m hok _ ρ hcm hf' hmins' hps').mp hvs
      rw [show consList (fs' ++ mins' ++ [m''] ++ ps') ρ
          = consList fs' (consList (mins' ++ [m'']) (consList ps' ρ)) by simp [consList_append]]
      have hih := fun kf (hkf : kf ∈ c.recFields) =>
        ihVal_ok hpl hs m hok φ ρ hus hcm hkf hf' hmins' hps' hp' hm' hmn' hfitF'
      have hmin := minorOk_of_fits hpl hs m hok _ ρ hps' hp' hm' hmins' hmn' j c hc fs' hfitF'
        (c.recFields.map fun kf => interp (S.M₃ m.M) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (mins' ++ [m'']) (consList ps' ρ)))
          (S.ihVal c.fields.length kf.1 kf.2))
        (ListRel.map fun kf hkf => (hih kf hkf).2.1)
      refine ⟨?_, ?_⟩
      · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
        · intro a ha
          simp only [List.mem_append, List.mem_map] at ha
          rcases ha with ha | ⟨kf, hkf, rfl⟩
          · exact Expr.wd_of_mem_varsAt ha
          · exact (hih kf hkf).1
        · rw [interp_bvar, List.map_append, List.map_map, interp_varsAt, shiftE_zero_zero,
            readEnv_consList hf', hminor fs' mins' m'' ps' hf' hmins']
          exact hmin.2
      · rw [hbody fs' mins' m'' ps' hf' hmins', hty fs' mins' m'' ps' hf' hmins' hps' hp' hfitF']
        exact hmin.1
  refine ⟨?_, ?_, ?_⟩
  · -- the equation
    rw [hspineR, interp_instL]
    cases hq : S.q.holds (Level.substVal φ S.recLparams us)
    · rw [key.2.2.2 hq, S.recSem_eq m.M _ false (hok.noCont hpl)
        (fun hz => uniq_of hpl hs m hok _ hz (large_of_q_false hq) hz) hp hc hfitF m' mins]
      unfold ruleRhs
      rw [interp_mkLams, hq, appList_lamCtx_false hfitRule, henv, hbody fs mins m' ps hf hmins]
      congr 2
      exact List.map_congr_left fun kf hkf =>
        ((ihVal_ok hpl hs m hok φ ρ hus hcm hkf hf hmins hps hp hm hmn hfitF).2.2 hq).symm
    · rw [recSet_eq hpl hs m hok φ ρ hus, hq, lamCtx_true_eq_pt _ _ (by simp [recCtx]), appList_pt]
      unfold ruleRhs
      rw [interp_mkLams, hq, lamCtx_true_eq_pt _ _ (by simp [ruleCtx]), appList_pt]
  · -- the invariant
    rw [WellDenoted_instL]
    exact hrhs.1
  · -- the application chain
    rw [hspineR, interp_instL]
    refine spineOk_of_teleFitV _ _ hT hrhs.2 ?_
    rw [TeleFitV_mkPis _ _ _ (by
        rw [List.length_reverse, length_ruleCtx]
        simp only [List.length_append, List.length_singleton, hf, hmins, hps]),
      List.reverse_reverse]
    exact hfitRule

end IndSpec

end Fragment.IndSpec.Nst
