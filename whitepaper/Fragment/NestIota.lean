module

public import Fragment.InstallNest

@[expose] public section

/-!
# Installing a nested block, part 2: the two recursors' type laws and
the ι laws of their rules

The twin of `InstallInd.lean`'s recursor half and of `InstallIota.lean`
for a nested block: the sets of `T.rec` and `T.rec_1` (`recSetN`,
`rec1Set`, `NestRead.lean`) are in the recursors' types
(`type_ok_recN`, `type_ok_rec1`), every rule of `T.rec` satisfies its
ι law (`rec_rule_lawN`), and every rule of `T.rec_1` satisfies both the
plain and the nested form of its ι law (`rec_rule_law1`,
`rec_rule_law1N`).

The proofs follow the plain ones line by line.  Both recursors' sets
are abstractions over their contexts read in the model with the
former and the constructors at the recursor's own valuation; the two
readings of every entry agree (`agree_recCtxN`, `agree_rec1Ctx` — the
class's minors read through the container's constructor applied,
`classCtorApp_read`, which no reader changes), so the sets are the
abstractions in the final model (`recSetN_eq`, `rec1Set_eq`), whose
typing is the semantic recursors' (`recSemN_mem`, `NestRec.lean`) above
a proposition, or the motives' inhabitation at one.  A rule's
left-hand side is the semantic recursor at the constructor value
(`rec_app_memN`, `rec1_app_mem`), which the recursion equations
(`recSemN_eq`, `rec1Sem_eq`) make the minor at the fields and the
inductive hypotheses' values; its right-hand side is β over the rule's
context of the minor at the fields and the hypothesis terms, each a
recursor call reading as the semantic hypothesis (`recCall_okN`,
`rec1Call_ok`, `ihValN_ok`).

For a `T.rec_1` rule the major is the container's constructor
applied, and sits in the class; the class's inversion (`ClassLaws.inv`)
pins its fields, and the constructor's value, a tagged tuple, pins
which constructor and which fields (`rule1_core`).

**A proposition with a small eliminator.**  There the class's laws
are not available (`classLaws` needs `z = false`, and inversion is
false there: every member is the point).  The typing of the recursors
is then the inhabitation of the motives, by the same interleaved
induction with the class's minors read at the point
(`motives_inhabited_prop`, `minorOkK_of_fits_prop`), through the
regime-free translations between the container's own field fit and
the translated constructor's (`FitsFields_classFields_of_KS`,
`KS_FitsFields_of_classFields`); the nested law's application chain is
the point's (`spineOk_pt_of_mem`).

**What is left out.**  The plain law of a `T.rec_1` rule drops the
RECURSOR's parameter count from the constructor's spine; when the
container has more parameters than the block the dropped list is not
the fields, and the law is not provable from its hypotheses —
`rec_rule_law1` assumes `N.nPK ≤ S.nP`.
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

omit [LevelOracle] in
/-- A context lifted entry-wise by `liftN o` over `o` extras is
well-denoted exactly when the context is, below the extras. -/
theorem CtxWD_liftCtx_liftN (M : Name → List Nat → V) (φ : Name → Nat) {o : Nat}
    {os ps : List V} (ρ : Nat → V) (ho : os.length = o) :
    ∀ (Γ : List Expr),
      CtxWD M φ (consList os (consList ps ρ)) (Expr.liftCtx (fun k A => A.liftN o k) Γ) ↔
        CtxWD M φ (consList ps ρ) Γ
  | [] => Iff.rfl
  | A :: Γ => by
    simp only [Expr.liftCtx_cons, CtxWD_cons]
    rw [CtxWD_liftCtx_liftN M φ ρ ho Γ]
    refine and_congr Iff.rfl ⟨fun h vs hvs => ?_, fun h vs hvs => ?_⟩
    · have hl := FitsVals_length M φ hvs
      have := h vs ((FitsVals_liftCtx_liftN M φ ρ Γ vs ho).mpr hvs)
      rw [← hl, WellDenoted_liftN, shiftE_consList_mid rfl ho] at this
      exact this
    · rw [FitsVals_liftCtx_liftN M φ ρ Γ vs ho] at hvs
      have hl := FitsVals_length M φ hvs
      rw [← hl, WellDenoted_liftN, shiftE_consList_mid rfl ho]
      exact h vs hvs

namespace IndSpec

variable {env : Env} {S : IndSpec} {N : NestInfo}

/-! ## The two recursors' bodies and environments, read -/

omit [LevelOracle] in
theorem recTypeN_eq : S.recTypeN N = Expr.mkPis S.q (S.recCtxN N)
    (Expr.mkAppN (.bvar (S.nI + S.oN N)) (Expr.varsAt 1 S.nI ++ [.bvar 0])) := rfl

omit [LevelOracle] in
theorem rec1Type_eq : S.rec1Type N = Expr.mkPis S.q (S.rec1Ctx N)
    (Expr.mkAppN (.bvar (S.oN N - 1)) [.bvar 0]) := rfl

omit [LevelOracle] in
/-- `T.rec`'s body, read at values of its context. -/
theorem recFN_read (S : IndSpec) (M' : Name → List Nat → V) (ls : List Nat) (N : NestInfo)
    (q : Bool) {t : V} {is minsK mins : List V} {m1 m : V} {ps : List V}
    (hi : is.length = S.nI) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP) (X : Nat → V) :
    S.recSemN M' ls N q
        (readEnv S.nP (shiftE (1 + S.nI + S.oN N) 0 (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X)))
        ⟨consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X (S.nI + S.oN N),
          consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X (S.nI + S.oN N - 1),
          readEnv S.n (shiftE (1 + S.nI + N.nK) 0 (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X)),
          readEnv N.nK (shiftE (1 + S.nI) 0 (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X))⟩
        (readEnv S.nI (shiftE 1 0 (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X)))
        (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X 0)
      = S.recSemN M' ls N q ps ⟨m, m1, mins, minsK⟩ is t := by
  have e : consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X
      = consList (t :: is) (consList minsK (consList mins (consList [m1, m] (consList ps X)))) := by
    simp [consList_append]
  have hs1 : ∀ Y : Nat → V, shiftE 1 0 (consList (t :: is) Y) = consList is Y :=
    fun Y => shiftE_consList' (vs := [t]) rfl (consList is Y)
  have hs2 : ∀ Y : Nat → V, shiftE (1 + S.nI) 0 (consList (t :: is) Y) = Y :=
    fun Y => shiftE_consList' (by simp [hi]; omega) Y
  have hs3 : ∀ Y : Nat → V, shiftE (1 + S.nI + N.nK) 0 (consList (t :: is) (consList minsK Y)) = Y := by
    intro Y
    rw [← consList_append]
    exact shiftE_consList' (by simp [hi, hminsK]; omega) Y
  have hs4 : ∀ Y : Nat → V, shiftE (1 + S.nI + S.oN N) 0
      (consList (t :: is) (consList minsK (consList mins (consList [m1, m] Y)))) = Y := by
    intro Y
    rw [← consList_append, ← consList_append, ← consList_append]
    exact shiftE_consList' (by simp [hi, hminsK, hmins, oN]; omega) Y
  have hm1 : consList (t :: is) (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.nI + S.oN N - 1) = m1 := by
    rw [← consList_append, ← consList_append,
      show S.nI + S.oN N - 1 = 0 + (t :: is ++ minsK ++ mins).length by
        simp [hi, hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  have hm : consList (t :: is) (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.nI + S.oN N) = m := by
    rw [← consList_append, ← consList_append,
      show S.nI + S.oN N = 1 + (t :: is ++ minsK ++ mins).length by
        simp [hi, hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  simp only [e]
  rw [hs1, hs2, hs3, hs4, hm, hm1, readEnv_consList hi, readEnv_consList hminsK,
    readEnv_consList hmins, readEnv_consList hps]
  rfl

omit [LevelOracle] in
/-- `T.rec_1`'s body, read at values of its context. -/
theorem rec1F_read (S : IndSpec) (M' : Name → List Nat → V) (ls : List Nat) (N : NestInfo)
    (q : Bool) {t : V} {minsK mins : List V} {m1 m : V} {ps : List V}
    (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n) (hps : ps.length = S.nP) (X : Nat → V) :
    S.rec1Sem M' ls N q
        (readEnv S.nP (shiftE (1 + S.oN N) 0 (consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X)))
        ⟨consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X (S.oN N),
          consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X (S.oN N - 1),
          readEnv S.n (shiftE (1 + N.nK) 0 (consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X)),
          readEnv N.nK (shiftE 1 0 (consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X))⟩
        (consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X 0)
      = S.rec1Sem M' ls N q ps ⟨m, m1, mins, minsK⟩ t := by
  have e : consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X
      = consList [t] (consList minsK (consList mins (consList [m1, m] (consList ps X)))) := by
    simp [consList_append]
  have hs1 : ∀ Y : Nat → V, shiftE 1 0 (consList [t] Y) = Y :=
    fun Y => shiftE_consList' (vs := [t]) rfl Y
  have hs3 : ∀ Y : Nat → V, shiftE (1 + N.nK) 0 (consList [t] (consList minsK Y)) = Y := by
    intro Y
    rw [← consList_append]
    exact shiftE_consList' (by simp [hminsK]; omega) Y
  have hs4 : ∀ Y : Nat → V, shiftE (1 + S.oN N) 0
      (consList [t] (consList minsK (consList mins (consList [m1, m] Y)))) = Y := by
    intro Y
    rw [← consList_append, ← consList_append, ← consList_append]
    exact shiftE_consList' (by simp [hminsK, hmins, oN]; omega) Y
  have hm1 : consList [t] (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.oN N - 1) = m1 := by
    rw [← consList_append, ← consList_append,
      show S.oN N - 1 = 0 + ([t] ++ minsK ++ mins).length by simp [hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  have hm : consList [t] (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.oN N) = m := by
    rw [← consList_append, ← consList_append,
      show S.oN N = 1 + ([t] ++ minsK ++ mins).length by simp [hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  simp only [e]
  rw [hs1, hs3, hs4, hm, hm1, readEnv_consList hminsK, readEnv_consList hmins, readEnv_consList hps]
  rfl

omit [LevelOracle] in
/-- `T.rec`'s type's body `motive indices major`, read at values of its
context. -/
theorem read_recBodyN (S : IndSpec) (M' : Name → List Nat → V) (φ' : Name → Nat) (N : NestInfo)
    {t : V} {is minsK mins : List V} {m1 m : V} {ps : List V}
    (hi : is.length = S.nI) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n) (X : Nat → V) :
    interp M' φ' (consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X)
        (Expr.mkAppN (.bvar (S.nI + S.oN N)) (Expr.varsAt 1 S.nI ++ [.bvar 0]))
      = appList m (is.reverse ++ [t]) := by
  have e : consList (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) X
      = consList (t :: is) (consList minsK (consList mins (consList [m1, m] (consList ps X)))) := by
    simp [consList_append]
  have hs1 : ∀ Y : Nat → V, shiftE 1 0 (consList (t :: is) Y) = consList is Y :=
    fun Y => shiftE_consList' (vs := [t]) rfl (consList is Y)
  have hm : consList (t :: is) (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.nI + S.oN N) = m := by
    rw [← consList_append, ← consList_append,
      show S.nI + S.oN N = 1 + (t :: is ++ minsK ++ mins).length by
        simp [hi, hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  rw [interp_mkAppN_appList, interp_bvar, List.map_append, interp_varsAt, List.map_singleton,
    interp_bvar, e, hm, hs1, readEnv_consList hi]
  rfl

omit [LevelOracle] in
/-- `T.rec_1`'s type's body `motive_1 major`, read at values of its
context. -/
theorem read_rec1Body (S : IndSpec) (M' : Name → List Nat → V) (φ' : Name → Nat) (N : NestInfo)
    {t : V} {minsK mins : List V} {m1 m : V} {ps : List V}
    (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n) (X : Nat → V) :
    interp M' φ' (consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X)
        (Expr.mkAppN (.bvar (S.oN N - 1)) [.bvar 0])
      = appList m1 [t] := by
  have e : consList (t :: minsK ++ mins ++ [m1, m] ++ ps) X
      = consList [t] (consList minsK (consList mins (consList [m1, m] (consList ps X)))) := by
    simp [consList_append]
  have hm1 : consList [t] (consList minsK (consList mins (consList [m1, m] (consList ps X))))
      (S.oN N - 1) = m1 := by
    rw [← consList_append, ← consList_append,
      show S.oN N - 1 = 0 + ([t] ++ minsK ++ mins).length by simp [hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  rw [interp_mkAppN_appList, interp_bvar, List.map_singleton, interp_bvar, e, hm1]
  rfl

/-! ## A context of one entry per constructor: its entries are well-denoted -/

variable {M : Name → List Nat → V} {φ : Name → Nat} {M' : Name → List Nat → V} {φ' : Name → Nat}

omit [LevelOracle] in
/-- **The entries of a well-denoted context of one entry per
constructor** are well-denoted under the values before them. -/
theorem wd_ctxFrom (T : CtorSpec → Nat → Expr) :
    ∀ (cs : List CtorSpec) (j : Nat) (E : Nat → V) (minsI : List V),
      CtxWD M' φ' E (ctxFrom T cs j) → FitsVals M' φ' E (ctxFrom T cs j) minsI →
      ∀ i c, cs[i]? = some c →
        WellDenoted M' φ' (consList (minsI.drop (cs.length - i)) E) (T c (j + i))
  | [], _, _, _, _, _, i, _, h => by simp at h
  | c :: cs, j, E, minsI, hwd, hfit, i, c', hc' => by
    have hlen := FitsVals_length M' φ' hfit
    simp only [ctxFrom, List.length_append, length_ctxFrom, List.length_singleton] at hlen
    obtain ⟨minsI', v, rfl⟩ : ∃ minsI' v, minsI = minsI' ++ [v] := by
      rcases List.eq_nil_or_concat minsI with h | ⟨l, v, h⟩
      · subst h; simp at hlen
      · exact ⟨l, v, by simpa [List.concat_eq_append] using h⟩
    have hl' : minsI'.length = (ctxFrom T cs (j + 1)).length := by
      rw [length_ctxFrom]; simp at hlen; omega
    obtain ⟨h1, h2⟩ := (FitsVals_append M' φ' hl').mp hfit
    have hl'' : minsI'.length = cs.length := by rw [hl', length_ctxFrom]
    simp only [ctxFrom] at hwd
    obtain ⟨hwd1, hwd2⟩ := CtxWD_append' hwd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
      subst hc'
      have hd : (minsI' ++ [v]).drop ((c :: cs).length - 0) = [] := by
        simp [hl'']
      rw [hd, consList_nil, Nat.add_zero]
      rw [CtxWD_cons] at hwd1
      simpa using hwd1.2 [] trivial
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc'
      have hi : i < cs.length := (List.getElem?_eq_some_iff.mp hc').1
      have ih := wd_ctxFrom T cs (j + 1) (cons v E) minsI' (by simpa using hwd2 [v] h1) h2 i c' hc'
      rw [show (c :: cs).length - (i + 1) = cs.length - i by simp only [List.length_cons]; omega,
        List.drop_append_of_le_length (by omega), consList_append,
        show j + (i + 1) = j + 1 + i by omega]
      exact ih

omit [LevelOracle] in
/-- **A context of one entry per constructor agrees between two
readers**, once each entry does under values fitting the entries
after it (well-denoted in the second reader). -/
theorem agree_ctxFrom {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat} (T : CtorSpec → Nat → Expr)
    (P : CtorSpec → Nat → Prop) (os ps : List V) (ρ₁ ρ₂ : Nat → V)
    (hT : ∀ (c : CtorSpec) (j' : Nat), P c j' → ∀ (minsE : List V), minsE.length = j' →
      WellDenoted M₂ φ₂ (consList minsE (consList os (consList ps ρ₂))) (T c j') →
      interp M₁ φ₁ (consList minsE (consList os (consList ps ρ₁))) (T c j')
        = interp M₂ φ₂ (consList minsE (consList os (consList ps ρ₂))) (T c j')) :
    ∀ (cs : List CtorSpec) (j : Nat), (∀ i c, cs[i]? = some c → P c (j + i)) →
      ∀ {minsE : List V}, minsE.length = j →
      CtxWD M₂ φ₂ (consList minsE (consList os (consList ps ρ₂))) (ctxFrom T cs j) →
      CtxAgree M₁ M₂ φ₁ φ₂ (consList minsE (consList os (consList ps ρ₁)))
        (consList minsE (consList os (consList ps ρ₂))) (ctxFrom T cs j)
  | [], _, _, _, _, _ => fun i A hA => by simp [ctxFrom] at hA
  | c :: cs, j, hcs, minsE, hminsE, hwd => by
    have hc : P c j := by simpa using hcs 0 c rfl
    simp only [ctxFrom] at hwd ⊢
    obtain ⟨hwd1, hwd2⟩ := CtxWD_append' hwd
    rw [CtxWD_cons] at hwd1
    have hA : CtxAgree M₁ M₂ φ₁ φ₂ (consList minsE (consList os (consList ps ρ₁)))
        (consList minsE (consList os (consList ps ρ₂))) [T c j] := by
      intro i A hA vs hvs
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
        subst hA
        cases vs with
        | nil =>
          simp only [consList_nil]
          exact hT c j hc minsE hminsE (by simpa using hwd1.2 [] trivial)
        | cons _ _ => exact absurd (FitsVals_length M₁ φ₁ hvs) (by simp)
      | succ i => simp at hA
    refine CtxAgree_append hA fun ws hws => ?_
    obtain ⟨v, rfl⟩ : ∃ v, ws = [v] := by
      have hl := FitsVals_length M₁ φ₁ hws
      cases ws with
      | nil => simp at hl
      | cons a t => cases t with
        | nil => exact ⟨a, rfl⟩
        | cons _ _ => simp at hl
    have hws₂ := (FitsVals_congr₂ hA).mp hws
    have := agree_ctxFrom T P os ps ρ₁ ρ₂ hT cs (j + 1)
      (fun i c' hc' => by
        have := hcs (i + 1) c' (by simpa using hc')
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (minsE := v :: minsE) (by simp [hminsE]) (by simpa using hwd2 [v] hws₂)
    simpa using this

/-! ## The class's minors' conclusion, in any reader -/

omit [LevelOracle] in
/-- **The container's constructor applied to the class's arguments and
fields, read in any reader**: the container's constructor's set in
the model applied to the class's arguments and the fields — the
reader does not enter (the constructor is a stored constant). -/
theorem Reader.classCtorApp_read (hS : S.Scoped env) (R : S.Reader (env := env) M φ (S.Fam M) M' φ')
    (hN : S.nest = some N) {c : CtorSpec} (hcst : (env.find? c.name).isSome) {o nIh : Nat}
    {ihsE fs os ps : List V} {ρ : Nat → V} (hi : ihsE.length = nIh)
    (hfl : fs.length = (S.classCtor N c).fields.length) (ho : os.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps)) :
    interp M' φ' (consList ihsE (consList fs (consList os (consList ps ρ))))
        (Expr.mkAppN (.const c.name N.lsK)
          (S.classArgs N (nIh + (S.classCtor N c).fields.length + o) ++
            Expr.varsAt nIh (S.classCtor N c).fields.length))
      = appList (M c.name (S.lsK (S.lparams.map φ) N))
          (S.classArgsV M (S.lparams.map φ) N ps
            (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) ++ fs.reverse) := by
  have henv : consList ihsE (consList fs (consList os (consList ps ρ)))
      = consList (ihsE ++ fs ++ os) (consList ps ρ) := consList_three _ _ _ _
  have hlen3 : (ihsE ++ fs ++ os).length = nIh + (S.classCtor N c).fields.length + o := by
    simp [hi, hfl, ho]; omega
  rw [interp_mkAppN_appList, interp_const, ← R.agree _ hcst, R.lsK_eq hS hN,
    List.map_append, interp_varsAt, shiftE_consList' hi, readEnv_consList hfl, henv,
    Reader.classArgs_read S N hS R hN hlen3 hps hp hidx]

/-! ## The nested recursors' contexts agree between two readers -/

omit [LevelOracle] in
/-- The lifted field context of any scoped constructor agrees between
two readers, once well-denoted in the second. -/
theorem Reader.agree_fieldCtxAt' (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ (S.Fam M) M₁ φ₁) (R₂ : S.Reader (env := env) M φ (S.Fam M) M₂ φ₂)
    {c : CtorSpec} (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {o : Nat} {os₁ os₂ ps : List V} {ρ₁ ρ₂ : Nat → V}
    (ho₁ : os₁.length = o) (ho₂ : os₂.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    CtxAgree M₁ M₂ φ₁ φ₂ (consList os₁ (consList ps ρ₁)) (consList os₂ (consList ps ρ₂))
      (S.fieldCtxAt c o) := by
  have hag := R₁.agree_fieldCtx hS R₂ (ρ₁ := ρ₁) (ρ₂ := ρ₂) hps hp hsc hwd
  intro i A hA vs hvs
  unfold fieldCtxAt at hA hvs
  rw [Expr.liftCtx_getElem?, S.length_fieldCtx] at hA
  simp only [Option.map_eq_some_iff] at hA
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  have hl := FitsVals_length M₁ φ₁ hvs
  have hi : i < (S.fieldCtx c.fields).length := (List.getElem?_eq_some_iff.mp hA₀).1
  have hvl : vs.length = c.fields.length - 1 - i := by
    rw [hl, List.length_drop, Expr.length_liftCtx, S.length_fieldCtx]; omega
  rw [Expr.liftCtx_drop, FitsVals_liftCtx_liftN M₁ φ₁ _ _ _ ho₁] at hvs
  rw [← hvl, interp_liftCtx_liftN_entry M₁ φ₁ ρ₁ _ ho₁, interp_liftCtx_liftN_entry M₂ φ₂ ρ₂ _ ho₂]
  exact hag i A₀ hA₀ vs hvs

omit [LevelOracle] in
/-- The inductive hypotheses' context of any scoped constructor agrees
between two readers. -/
theorem Reader.agree_ihCtxAux' {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ (S.Fam M) M₁ φ₁) (R₂ : S.Reader (env := env) M φ (S.Fam M) M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {o : Nat} {fs os ps : List V}
    {ρ₁ ρ₂ : Nat → V} (hf : fs.length = c.fields.length) (ho : os.length = o) (hpos : 0 < o)
    (ho2 : (∃ i : Nat, c.fields[i]? = some Field.container) → 2 ≤ o) (hps : ps.length = S.nP) :
    ∀ (L : List (Nat × Field)), (∀ kf ∈ L, kf ∈ c.recFields) → ∀ {l : Nat} {ihsE : List V},
      ihsE.length = l →
      CtxAgree M₁ M₂ φ₁ φ₂ (consList ihsE (consList fs (consList os (consList ps ρ₁))))
        (consList ihsE (consList fs (consList os (consList ps ρ₂)))) (S.ihCtxAux c.fields.length o L l)
  | [], _, _, _, _ => fun i A hA => by simp [ihCtxAux] at hA
  | kf :: rest, hL, l, ihsE, hi => by
    simp only [ihCtxAux]
    refine CtxAgree_append ?_ fun ws hws => ?_
    · intro i A hA vs hvs
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
        subst hA
        cases vs with
        | nil =>
          simp only [consList_nil]
          have ho2' : kf.2 = .container → 2 ≤ o := fun hcont =>
            ho2 ⟨_, by rw [← hcont]; exact (mem_recFields (hL kf List.mem_cons_self)).1⟩
          rw [Reader.read_ihTy' S R₁ hsc (hL kf List.mem_cons_self) hi hf ho hpos ho2' hps,
            Reader.read_ihTy' S R₂ hsc (hL kf List.mem_cons_self) hi hf ho hpos ho2' hps, hq.q_holds]
        | cons _ _ => exact absurd (FitsVals_length M₁ φ₁ hvs) (by simp)
      | succ i => simp at hA
    · obtain ⟨ih, rfl⟩ : ∃ ih, ws = [ih] := by
        have hl := FitsVals_length M₁ φ₁ hws
        cases ws with
        | nil => simp at hl
        | cons a t => cases t with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hl
      have := R₁.agree_ihCtxAux' R₂ hq hsc (ρ₁ := ρ₁) (ρ₂ := ρ₂) hf ho hpos ho2 hps rest
        (fun kf' h => hL kf' (List.mem_cons_of_mem kf h)) (l := l + 1) (ihsE := ih :: ihsE)
        (by simp [hi])
      simpa using this

omit [LevelOracle] in
/-- **A block minor's type in a nested block reads alike in two
readers** (the readers agreeing on the elimination level), once the
constructor's fields are well-denoted in the second. -/
theorem Reader₂.agree_minorTyN (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hfresh : env.find? S.name = none)
    {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) {minsE : List V} {m1 m : V} {ps : List V}
    {ρ₁ ρ₂ : Nat → V} (hminsE : minsE.length = j) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    interp M₁ φ₁ (consList minsE (consList [m1, m] (consList ps ρ₁))) (S.minorTyN c j)
      = interp M₂ φ₂ (consList minsE (consList [m1, m] (consList ps ρ₂))) (S.minorTyN c j) := by
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hos : (minsE ++ [m1, m]).length = 2 + j := by simp [hminsE]; omega
  have henv : ∀ ρ : Nat → V, consList minsE (consList [m1, m] (consList ps ρ))
      = consList (minsE ++ [m1, m]) (consList ps ρ) := by
    intro ρ; rw [consList_append]
  have hgetm : (minsE ++ [m1, m]).getD (2 + j - 1) pt = m := by
    rw [show 2 + j - 1 = minsE.length + 1 by omega]; exact (getD_append_two _ _).2
  unfold minorTyN
  rw [interp_mkPis, interp_mkPis, hq.q_holds, henv, henv]
  have hagF := R₁.R.agree_fieldCtxAt hS R₂.R hcm (ρ₁ := ρ₁) (ρ₂ := ρ₂) hos hos hps hp hwd
  have hfits : ∀ fs, FitsVals M₁ φ₁ (consList (minsE ++ [m1, m]) (consList ps ρ₁))
      (S.fieldCtxAt c (2 + j)) fs →
      fs.length = c.fields.length ∧
      S.FitsFields M (S.lparams.map φ) (S.Fam M (S.lparams.map φ) ps) ps c.fields fs ∧
      (∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
        IdxFitAt S M φ ps (earlier fs k) f) := by
    intro fs hfs
    have hfs₂ := (FitsVals_congr₂ hagF).mp hfs
    unfold fieldCtxAt at hfs₂
    rw [FitsVals_liftCtx_liftN M₂ φ₂ _ _ _ hos] at hfs₂
    have hiff := R₂.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp hwd (vs := fs)
    have hfit := hiff.1.mp hfs₂
    exact ⟨S.FitsFields_length M _ hfit, hfit, hiff.2 hfit⟩
  refine piCtx_congr₂ ?_ fun vs hvs => ?_
  · refine CtxAgree_append hagF fun fs hfs => ?_
    obtain ⟨hf, -, -⟩ := hfits fs hfs
    rw [ihCtxAt_eq]
    exact R₁.R.agree_ihCtxAux' R₂.R hq (hS.2.2.2.1 c hcm).1 hf hos (by omega) (fun _ => by omega) hps
      c.recFields (fun _ h => h) (ihsE := []) rfl
  · obtain ⟨ihsR, fs, rfl, hl₁⟩ : ∃ ihsR fs, vs = ihsR ++ fs ∧ ihsR.length = (S.ihCtxAt c (2 + j)).length := by
      have hl := FitsVals_length M₁ φ₁ hvs
      refine ⟨vs.take (S.ihCtxAt c (2 + j)).length, vs.drop (S.ihCtxAt c (2 + j)).length,
        (List.take_append_drop _ _).symm, ?_⟩
      simp at hl; simp [hl]
    obtain ⟨hwsF, -⟩ := (FitsVals_append M₁ φ₁ hl₁).mp hvs
    obtain ⟨hf, hfit, hidx⟩ := hfits fs hwsF
    have hi : ihsR.length = c.recFields.length := by rw [hl₁, ihCtxAt_eq, length_ihCtxAux]
    rw [consList_append ihsR fs (consList (minsE ++ [m1, m]) (consList ps ρ₁)),
      consList_append ihsR fs (consList (minsE ++ [m1, m]) (consList ps ρ₂)),
      R₁.read_concl hS hfresh hc (ihsE := ihsR) (os := minsE ++ [m1, m]) hi hf hos (by omega) hps hp hfit hidx,
      R₂.read_concl hS hfresh hc (ihsE := ihsR) (os := minsE ++ [m1, m]) hi hf hos (by omega) hps hp hfit hidx]

omit [LevelOracle] in
/-- **A class minor's type reads alike in two readers**, once the
translated constructor's fields are well-denoted in the second: the
conclusion is the container's constructor applied, which no reader
changes. -/
theorem Reader₂.agree_minorTyK (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) (hcst : (env.find? c.name).isSome)
    {minsE mins : List V} {m1 m : V} {ps : List V} {ρ₁ ρ₂ : Nat → V}
    (hminsE : minsE.length = j) (hmins : mins.length = S.n) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx (S.classCtor N c).fields)) :
    interp M₁ φ₁ (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ₁))) (S.minorTyK N c j)
      = interp M₂ φ₂ (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ₂))) (S.minorTyK N c j) := by
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hsc := S.classCtor_fieldScoped N hS hN hKS hcm
  have hos : (minsE ++ mins ++ [m1, m]).length = 2 + S.n + j := by simp [hminsE, hmins]; omega
  have henv : ∀ ρ : Nat → V, consList minsE (consList (mins ++ [m1, m]) (consList ps ρ))
      = consList (minsE ++ mins ++ [m1, m]) (consList ps ρ) := by
    intro ρ; simp [consList_append]
  have hgetm1 : (minsE ++ mins ++ [m1, m]).getD (2 + S.n + j - 2) pt = m1 := by
    rw [show 2 + S.n + j - 2 = (minsE ++ mins).length by simp [hminsE, hmins]; omega]
    exact (getD_append_two _ _).1
  unfold minorTyK
  rw [interp_mkPis, interp_mkPis, hq.q_holds, henv, henv]
  have hagF := R₁.R.agree_fieldCtxAt' hS R₂.R hsc (ρ₁ := ρ₁) (ρ₂ := ρ₂) hos hos hps hp hwd
  have hfits : ∀ fs, FitsVals M₁ φ₁ (consList (minsE ++ mins ++ [m1, m]) (consList ps ρ₁))
      (S.fieldCtxAt (S.classCtor N c) (2 + S.n + j)) fs → fs.length = (S.classCtor N c).fields.length := by
    intro fs hfs
    have hl := FitsVals_length M₁ φ₁ hfs
    rw [hl]; unfold fieldCtxAt; rw [Expr.length_liftCtx, S.length_fieldCtx]
  refine piCtx_congr₂ ?_ fun vs hvs => ?_
  · refine CtxAgree_append hagF fun fs hfs => ?_
    have hf := hfits fs hfs
    rw [ihCtxAt_eq]
    exact R₁.R.agree_ihCtxAux' R₂.R hq hsc hf hos (by omega) (fun _ => by omega) hps
      (S.classCtor N c).recFields (fun _ h => h) (ihsE := []) rfl
  · obtain ⟨ihsR, fs, rfl, hl₁⟩ : ∃ ihsR fs, vs = ihsR ++ fs ∧
        ihsR.length = (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length := by
      have hl := FitsVals_length M₁ φ₁ hvs
      refine ⟨vs.take (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
        vs.drop (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
        (List.take_append_drop _ _).symm, ?_⟩
      simp at hl; simp [hl]
    obtain ⟨hwsF, -⟩ := (FitsVals_append M₁ φ₁ hl₁).mp hvs
    have hf := hfits fs hwsF
    have hi : ihsR.length = (S.classCtor N c).recFields.length := by
      rw [hl₁, ihCtxAt_eq, length_ihCtxAux]
    have hbv : ∀ ρ : Nat → V,
        consList ihsR (consList fs (consList (minsE ++ mins ++ [m1, m]) (consList ps ρ)))
          ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length + (2 + S.n + j) - 2)
        = m1 := by
      intro ρ
      rw [show (S.classCtor N c).recFields.length + (S.classCtor N c).fields.length + (2 + S.n + j) - 2
          = ((2 + S.n + j - 2) + (S.classCtor N c).fields.length) + (S.classCtor N c).recFields.length by
          omega,
        ← hi, consList_ge, ← hf, consList_ge, consList_getD (by omega), hgetm1]
    rw [consList_append ihsR fs (consList (minsE ++ mins ++ [m1, m]) (consList ps ρ₁)),
      consList_append ihsR fs (consList (minsE ++ mins ++ [m1, m]) (consList ps ρ₂)),
      interp_mkAppN_appList, interp_mkAppN_appList, interp_bvar, interp_bvar, List.map_singleton,
      List.map_singleton, hbv, hbv,
      Reader.classCtorApp_read hS R₁.R hN hcst (o := 2 + S.n + j) hi hf hos hps hp hidx,
      Reader.classCtorApp_read hS R₂.R hN hcst (o := 2 + S.n + j) hi hf hos hps hp hidx]

omit [LevelOracle] in
/-- A class minor's well-denotedness gives the well-denotedness of the
translated constructor's field context, below the extras. -/
theorem wdFieldCtx_of_minorTyK {c : CtorSpec} {j : Nat} {os ps : List V} {ρ : Nat → V}
    (ho : os.length = 2 + S.n + j)
    (hwd : WellDenoted M' φ' (consList os (consList ps ρ)) (S.minorTyK N c j)) :
    CtxWD M' φ' (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields) := by
  unfold minorTyK at hwd
  rw [WellDenoted_mkPis] at hwd
  have := (CtxWD_append' hwd.1).1
  unfold fieldCtxAt at this
  exact (CtxWD_liftCtx_liftN M' φ' ρ ho _).mp this

omit [LevelOracle] in
/-- **The extras' context agrees between two readers**: the two
motives read as the motive spaces, the block's minors and the class's
minors as the products over their fields and hypotheses. -/
theorem Reader₂.agree_extrasN (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    (hfresh : env.find? S.name = none)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    {ps : List V} {ρ₁ ρ₂ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hwdC : ∀ c ∈ S.ctors, CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields))
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.extrasN N)) :
    CtxAgree M₁ M₂ φ₁ φ₂ (consList ps ρ₁) (consList ps ρ₂) (S.extrasN N) := by
  unfold extrasN at hwd ⊢
  obtain ⟨-, hwdM⟩ := CtxWD_append' hwd
  -- the two motives
  have hmot : CtxAgree M₁ M₂ φ₁ φ₂ (consList ps ρ₁) (consList ps ρ₂) [S.motiveTy1 N, S.motiveTy] := by
    refine CtxAgree.of_cons (CtxAgree.of_cons (fun i A hA => by simp at hA) fun vs hvs => ?_)
      fun vs hvs => ?_
    · obtain rfl : vs = [] := by
        have := FitsVals_length M₁ φ₁ hvs; simpa using this
      simp only [consList_nil]
      rw [R₁.R.read_motiveTy hS hps hp, R₂.R.read_motiveTy hS hps hp, hq]
    · obtain ⟨m, rfl⟩ : ∃ m, vs = [m] := by
        have hl := FitsVals_length M₁ φ₁ hvs
        cases vs with
        | nil => simp at hl
        | cons a t => cases t with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hl
      simp only [consList_cons, consList_nil]
      rw [Reader.read_motiveTy1 S N hS R₁.R hN hps hp hidx,
        Reader.read_motiveTy1 S N hS R₂.R hN hps hp hidx, hq]
  refine CtxAgree_append hmot fun ms hms => ?_
  obtain ⟨m1, m, rfl⟩ : ∃ m1 m, ms = [m1, m] := by
    have hl := FitsVals_length M₁ φ₁ hms
    match ms, hl with
    | [m1, m], _ => exact ⟨m1, m, rfl⟩
  have hms₂ := (FitsVals_congr₂ hmot).mp hms
  have hwdM' := hwdM [m1, m] hms₂
  obtain ⟨hwdN, hwdK⟩ := CtxWD_append' hwdM'
  -- the block's minors
  have hminN : CtxAgree M₁ M₂ φ₁ φ₂ (consList [m1, m] (consList ps ρ₁))
      (consList [m1, m] (consList ps ρ₂)) S.minorsCtxN := by
    rw [minorsCtxN_eq]
    have := agree_ctxFrom (M₁ := M₁) (M₂ := M₂) (φ₁ := φ₁) (φ₂ := φ₂) S.minorTyN
      (fun c j' => S.ctors[j']? = some c) [m1, m] ps ρ₁ ρ₂
      (fun c j' hc minsE hminsE _ =>
        R₁.agree_minorTyN hS R₂ hq hfresh hc hminsE hps hp (hwdC c (List.mem_of_getElem? hc)))
      S.ctors 0 (fun i c hc => by simpa using hc) (minsE := []) rfl
      (by rw [← minorsCtxN_eq]; exact hwdN)
    simpa using this
  refine CtxAgree_append hminN fun mins hmins => ?_
  have hmn : mins.length = S.n := by
    have := FitsVals_length M₁ φ₁ hmins; rwa [length_minorsCtxN] at this
  have hmins₂ := (FitsVals_congr₂ hminN).mp hmins
  have hwdK' := hwdK mins hmins₂
  rw [minorsCtxK_eq] at hwdK' ⊢
  have henv : ∀ ρ : Nat → V, consList mins (consList [m1, m] (consList ps ρ))
      = consList (mins ++ [m1, m]) (consList ps ρ) := by
    intro ρ; rw [consList_append]
  rw [henv] at hwdK'
  rw [henv, henv]
  have := agree_ctxFrom (M₁ := M₁) (M₂ := M₂) (φ₁ := φ₁) (φ₂ := φ₂) (S.minorTyK N)
    (fun c j' => N.K.ctors[j']? = some c) (mins ++ [m1, m]) ps ρ₁ ρ₂
    (fun c j' hc minsE hminsE hwdE => by
      have hos : (minsE ++ mins ++ [m1, m]).length = 2 + S.n + j' := by simp [hminsE, hmn]; omega
      have hwdF := wdFieldCtx_of_minorTyK (M' := M₂) (φ' := φ₂) (ps := ps) (ρ := ρ₂) hos
        (by rw [consList_append, consList_append]; rw [consList_append] at hwdE; exact hwdE)
      exact R₁.agree_minorTyK hS R₂ hq hN hKS hc (hcst j' c hc) hminsE hmn hps hp hidx hwdF)
    N.K.ctors 0 (fun i c hc => by simpa using hc) (minsE := []) rfl hwdK'
  simpa using this

omit [LevelOracle] in
/-- Any list fitting the extras' context splits as the class's minors,
the block's minors and the two motives. -/
theorem fits_extrasN_split {ρ : Nat → V} {vs : List V} (h : FitsVals M' φ' ρ (S.extrasN N) vs) :
    ∃ (minsK mins : List V) (m1 m : V),
      vs = minsK ++ mins ++ [m1, m] ∧ minsK.length = N.nK ∧ mins.length = S.n := by
  have hl := FitsVals_length M' φ' h
  rw [length_extrasN] at hl
  simp only [oN] at hl
  obtain ⟨minsK, r₂, rfl, hminsK⟩ := exists_split (l := vs) (a := N.nK) (by omega)
  obtain ⟨mins, r₃, rfl, hmins⟩ := exists_split (l := r₂) (a := S.n) (by simp at hl; omega)
  obtain ⟨m1, m, rfl⟩ : ∃ m1 m, r₃ = [m1, m] := by
    match r₃, (by simp at hl; omega : r₃.length = 2) with
    | [m1, m], _ => exact ⟨m1, m, rfl⟩
  exact ⟨minsK, mins, m1, m, by simp, hminsK, hmins⟩

omit [LevelOracle] in
/-- **`T.rec`'s context agrees between two readers** — the sets of its
parts read alike (the parameters, the extras, the indices, the
major). -/
theorem Reader₂.agree_recCtxN (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    (hfresh : env.find? S.name = none)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    (ρ₁ ρ₂ : Nat → V)
    (hidx : ∀ ps, FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices (S.memberIdx M (S.lparams.map φ) N ps))
    (hwdC : ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields))
    (hwd : CtxWD M₂ φ₂ ρ₂ (S.recCtxN N)) :
    CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ (S.recCtxN N) := by
  unfold recCtxN at hwd ⊢
  have hagP := R₁.R.agree_params₂ hS R₂.R ρ₁ ρ₂
  obtain ⟨-, hwd₁⟩ := CtxWD_append' hwd
  refine CtxAgree_append hagP fun ps hps₁ => ?_
  have hp := (R₁.R.fits_params hS).mp hps₁
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hps₁; simpa [nP] using this
  have hps₂ := (FitsVals_congr₂ hagP).mp hps₁
  obtain ⟨hwdE, -⟩ := CtxWD_append' (hwd₁ ps hps₂)
  have hagE := R₁.agree_extrasN hS R₂ hq hN hKS hfresh hcst (ρ₁ := ρ₁) hps hp (hidx ps hp)
    (fun c hc => hwdC c hc ps hps hp) hwdE
  refine CtxAgree_append hagE fun ex hex => ?_
  obtain ⟨minsK, mins, m1, m, rfl, hminsK, hmins⟩ := fits_extrasN_split hex
  have hos : (minsK ++ mins ++ [m1, m]).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  refine CtxAgree.of_cons ?_ fun is his => ?_
  · intro i A hA vs hvs
    unfold indicesAt at hA hvs
    rw [Expr.liftCtx_getElem?] at hA
    simp only [Option.map_eq_some_iff] at hA
    obtain ⟨A₀, hA₀, rfl⟩ := hA
    have hl := FitsVals_length M₁ φ₁ hvs
    have hi : i < S.indices.length := (List.getElem?_eq_some_iff.mp hA₀).1
    have hvl : vs.length = S.indices.length - 1 - i := by
      rw [hl, List.length_drop, Expr.length_liftCtx]; omega
    rw [← hvl, interp_liftCtx_liftN_entry M₁ φ₁ ρ₁ _ hos, interp_liftCtx_liftN_entry M₂ φ₂ ρ₂ _ hos]
    exact R₁.R.read₂ R₂.R (hS.2.1 i A₀ hA₀) (by simp only [hvl, hps, nI]; omega)
  · unfold indicesAt at his
    rw [FitsVals_liftCtx_liftN M₁ φ₁ _ _ _ hos, R₁.R.fits_indices hS hps] at his
    rw [R₁.R.read_famVars hS hos hps hp his, R₂.R.read_famVars hS hos hps hp his]

omit [LevelOracle] in
/-- **`T.rec_1`'s context agrees between two readers.** -/
theorem Reader₂.agree_rec1Ctx (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    (hfresh : env.find? S.name = none)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    (ρ₁ ρ₂ : Nat → V)
    (hidx : ∀ ps, FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices (S.memberIdx M (S.lparams.map φ) N ps))
    (hwdC : ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields))
    (hwd : CtxWD M₂ φ₂ ρ₂ (S.rec1Ctx N)) :
    CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ (S.rec1Ctx N) := by
  unfold rec1Ctx at hwd ⊢
  have hagP := R₁.R.agree_params₂ hS R₂.R ρ₁ ρ₂
  obtain ⟨-, hwd₁⟩ := CtxWD_append' hwd
  refine CtxAgree_append hagP fun ps hps₁ => ?_
  have hp := (R₁.R.fits_params hS).mp hps₁
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hps₁; simpa [nP] using this
  have hps₂ := (FitsVals_congr₂ hagP).mp hps₁
  have hwdE := (hwd₁ ps hps₂).1
  have hagE := R₁.agree_extrasN hS R₂ hq hN hKS hfresh hcst (ρ₁ := ρ₁) hps hp (hidx ps hp)
    (fun c hc => hwdC c hc ps hps hp) hwdE
  refine CtxAgree.of_cons hagE fun ex hex => ?_
  obtain ⟨minsK, mins, m1, m, rfl, hminsK, hmins⟩ := fits_extrasN_split hex
  have hos : (minsK ++ mins ++ [m1, m]).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  rw [R₁.R.classTy_fit hS hN hos hps hp (hidx ps hp), R₂.R.classTy_fit hS hN hos hps hp (hidx ps hp)]

omit [LevelOracle] in
/-- The translated constructors' field contexts are well-denoted at
fitting parameters, from the extras' context being well-denoted and
values fitting it: each class minor is well-denoted there, and its
binders are the translated fields. -/
theorem wdFieldCtxK {ps : List V} {m1 m : V} {mins minsK : List V} {ρ : Nat → V}
    (hwdE : CtxWD M' φ' (consList ps ρ) (S.extrasN N))
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hm : m ∈ˢ interp M' φ' (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp M' φ' (cons m (consList ps ρ)) (S.motiveTy1 N))
    (hmn : FitsVals M' φ' (consList [m1, m] (consList ps ρ)) S.minorsCtxN mins)
    (hmnK : FitsVals M' φ' (consList (mins ++ [m1, m]) (consList ps ρ)) (S.minorsCtxK N) minsK) :
    ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c →
      CtxWD M' φ' (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields) := by
  intro j c hc
  have hj : j < N.K.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  unfold extrasN at hwdE
  obtain ⟨-, hwdM⟩ := CtxWD_append' hwdE
  have hfitM : FitsVals M' φ' (consList ps ρ) [S.motiveTy1 N, S.motiveTy] [m1, m] := by
    simp only [FitsVals_cons, FitsVals_nil_nil, true_and, consList_cons, consList_nil]
    exact ⟨hm, hm1⟩
  obtain ⟨-, hwdK⟩ := CtxWD_append' (hwdM [m1, m] hfitM)
  have hwdK' := hwdK mins hmn
  rw [consList_append] at hmnK
  rw [minorsCtxK_eq] at hwdK' hmnK
  have hwdj := wd_ctxFrom (S.minorTyK N) N.K.ctors 0 _ minsK hwdK' hmnK j c hc
  rw [Nat.zero_add] at hwdj
  have hl : (minsK.drop (N.K.ctors.length - j)).length = j := by simp [hminsK, NestInfo.nK]; omega
  have hos : (minsK.drop (N.K.ctors.length - j) ++ mins ++ [m1, m]).length = 2 + S.n + j := by
    rw [List.length_append, List.length_append, hl, hmins, List.length_cons, List.length_cons,
      List.length_nil]
    omega
  refine wdFieldCtx_of_minorTyK (M' := M') (φ' := φ') (ps := ps) (ρ := ρ) hos ?_
  rw [consList_append, consList_append]
  exact hwdj

omit [LevelOracle] in
/-- The extras' context is well-denoted at fitting parameters, from
`T.rec`'s context being so. -/
theorem wd_extrasN_of_recCtxN {ρ : Nat → V} (hwd : CtxWD M' φ' ρ (S.recCtxN N)) {ps : List V}
    (hp : FitsVals M' φ' ρ S.params ps) : CtxWD M' φ' (consList ps ρ) (S.extrasN N) := by
  unfold recCtxN at hwd
  exact (CtxWD_append' ((CtxWD_append' hwd).2 ps hp)).1

omit [LevelOracle] in
/-- … and from `T.rec_1`'s. -/
theorem wd_extrasN_of_rec1Ctx {ρ : Nat → V} (hwd : CtxWD M' φ' ρ (S.rec1Ctx N)) {ps : List V}
    (hp : FitsVals M' φ' ρ S.params ps) : CtxWD M' φ' (consList ps ρ) (S.extrasN N) := by
  unfold rec1Ctx at hwd
  exact ((CtxWD_append' hwd).2 ps hp).1

/-! ## A proposition with a small eliminator: the class, read at the point

At a proposition every member of the family and of the class is the
point, so the class's laws (`ClassLaws`, whose inversion names the
tagged tuple) are not available; the typing of the two recursors is
the inhabitation of the motives, by the same interleaved induction,
with the class's minors read at the point. -/

omit [LevelOracle] in
/-- **The container's own fit gives the block-sense fit of the
translated constructor**: the member field's value is in the member
set (inside the fibre), a container field's in the class at the fibre
(the container's family grows with the member set, `Fam_psK_mono`),
an ordinary field's in its domain. -/
theorem FitsFields_classFields_of_KS {M : Name → List Nat → V} {ls : List Nat}
    (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env) (hN : S.nest = some N)
    {c : CtorSpec} (hcm : c ∈ N.K.ctors) {X : V} {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hX : X ∈ˢ (univ (S.u₀ ls) : V))
    (hXF : X ⊆ˢ S.Fam M ls ps (S.memberIdx M ls N ps)) {W : List V → V}
    (hW : ∀ y, y ∈ˢ W [] → y ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) []) :
    ∀ {fields : List Field} {n : Nat}, c.fields.drop n = fields → ∀ {fs : List V},
      N.KS.FitsFields M (S.lsK ls N) W (S.psK M ls N ps X) fields fs →
      S.FitsFields M ls (S.Fam M ls ps) ps (S.classFields N fields) fs
  | [], _, _, [], _ => trivial
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
  | f :: rest, n, hd, v :: vs, ⟨h1, h2⟩ => by
    have hd' : c.fields.drop (n + 1) = rest := by rw [← List.drop_drop, hd]; rfl
    have ih := FitsFields_classFields_of_KS hf hlen hlsK hKS hN hcm hp hX hXF hW hd' h1
    have hl : vs.length = rest.length := N.KS.FitsFields_length M _ h1
    have hpf := positive_field N hf.positive hcm hd (i := 0) rfl
    have hpN : N.p < N.nPK := hf.positive.2.1
    simp only [classFields_cons, FitsFields]
    refine ⟨ih, ?_⟩
    cases f with
    | ordinary A =>
      rcases hpf with hA | ⟨hu, -⟩
      · -- the member field
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hA
        subst hA
        simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, fieldSet, piCtx_nil]
        simp only [fieldSet, interp_bvar] at h2
        rw [S.read_memberVar M ls N hlen hpN hl] at h2
        rw [S.idxVals_liftN M ls ps hl]
        exact hXF v h2
      · simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hu
        have e := S.classFieldSet_eq_ordinary M ls N hf hlen hlsK hKS hcm hd (i := 0) rfl X (fun _ => True)
          ps W (fs := vs) (by simpa using hl)
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at e
        rw [← e] at h2
        rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)] at h2 ⊢
        exact h2
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hpf
      simp only [classField]
      rw [S.fieldSet_container M ls hN, S.classSet_eq_Fam hf hp (S.Fam_mem_univ M ls _ _)]
      simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil] at h2
      exact S.Fam_psK_mono hf hp hXF (S.Fam_mem_univ M ls _ _) [] v (hW v h2)
    | container => exact hpf.elim

omit [LevelOracle] in
/-- **The block-sense fit of the translated constructor gives the
container's own fit** at the fibre. -/
theorem KS_FitsFields_of_classFields {M : Name → List Nat → V} {ls : List Nat}
    (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env) (hN : S.nest = some N)
    {c : CtorSpec} (hcm : c ∈ N.K.ctors) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) :
    ∀ {fields : List Field} {n : Nat}, c.fields.drop n = fields → ∀ {fs : List V},
      S.FitsFields M ls (S.Fam M ls ps) ps (S.classFields N fields) fs →
      N.KS.FitsFields M (S.lsK ls N)
        (N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps))))
        (S.psK M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps))) fields fs
  | [], _, _, [], _ => trivial
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
  | f :: rest, n, hd, v :: vs, h => by
    simp only [classFields_cons, FitsFields] at h
    obtain ⟨h1, h2⟩ := h
    have hd' : c.fields.drop (n + 1) = rest := by rw [← List.drop_drop, hd]; rfl
    have ih := KS_FitsFields_of_classFields hf hlen hlsK hKS hN hcm hp hd' h1
    have hl : vs.length = rest.length := (S.FitsFields_length M ls h1).trans (S.length_classFields N rest)
    have hpf := positive_field N hf.positive hcm hd (i := 0) rfl
    have hpN : N.p < N.nPK := hf.positive.2.1
    refine ⟨ih, ?_⟩
    cases f with
    | ordinary A =>
      rcases hpf with hA | ⟨hu, -⟩
      · -- the member field
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hA
        subst hA
        simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, fieldSet, piCtx_nil] at h2
        rw [S.idxVals_liftN M ls ps hl] at h2
        simp only [fieldSet, interp_bvar]
        rw [S.read_memberVar M ls N hlen hpN hl]
        exact h2
      · simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hu
        have e := S.classFieldSet_eq_ordinary M ls N hf hlen hlsK hKS hcm hd (i := 0) rfl
          (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
          (N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps))))
          (fs := vs) (by simpa using hl)
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at e
        rw [← e]
        rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)] at h2 ⊢
        exact h2
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hpf
      simp only [classField] at h2
      rw [S.fieldSet_container M ls hN, S.classSet_eq_Fam hf hp (S.Fam_mem_univ M ls _ _)] at h2
      simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil]
      exact h2
    | container => exact hpf.elim

omit [LevelOracle] in
/-- At a proposition the point is in the class as soon as some
constructor of the container can be fitted. -/
theorem pt_mem_classAt {M : Name → List Nat → V} {ls : List Nat}
    (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env) (hN : S.nest = some N)
    (hz : S.z ls = true) {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {fs : List V}
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps (S.classCtor N c).fields fs) :
    pt ∈ˢ S.classAt M ls N ps := by
  have hcm := List.mem_of_getElem? hc
  have hzK : N.KS.z (S.lsK ls N) = true := by rw [hf.z_eq]; exact hz
  have hfitK := KS_FitsFields_of_classFields hf hlen hlsK hKS hN hcm hp
    (List.drop_zero (l := c.fields)) (by simpa [classCtor] using hfit)
  have hF := S.Fam_mem_univ M ls ps (S.memberIdx M ls N ps)
  have hmem := N.KS.ctorVal_mem_Fam M (S.lsK ls N) hf.noRecDep (hf.domsBoundedK hp hF)
    (hf.contOkK _) hc hfitK
  rw [S.KS_idxVals hf hcm] at hmem
  simp only [ctorVal, hzK, if_true] at hmem
  unfold classAt
  rw [S.classSet_eq_Fam hf hp hF]
  exact hmem

omit [LevelOracle] in
/-- A constructor's set at a proposition is the point. -/
theorem KS_ctorSet_eq_pt (M : Name → List Nat → V) (ls' : List Nat) {j : Nat} {c : CtorSpec}
    (hzK : N.KS.z ls' = true) : N.KS.ctorSet M ls' j c = pt := by
  unfold ctorSet
  cases h : N.KS.fieldCtx c.fields ++ N.KS.params with
  | nil => simp [lamCtx, ctorVal, hzK]
  | cons A Γ => rw [hzK]; exact lamCtx_true_eq_pt _ _ (List.cons_ne_nil A Γ) _ _

omit [LevelOracle] in
/-- **The class's minors' typing at a proposition**: the class minor
at fields fitting the translated constructor (in the block's sense)
and typed hypotheses lies in the class's motive at the point — the
minor's conclusion reads as the container's constructor applied, the
point at a proposition. -/
theorem Reader₂.minorOkK_of_fits_prop (hS : S.Scoped env) (R₂ : S.Reader₂ (env := env) M φ M' φ')
    (hN : S.nest = some N) (hnf : S.NestFacts M (S.lparams.map φ) N) (hKS : N.KS.Scoped env)
    (hctor : ∀ j c, N.K.ctors[j]? = some c → ∀ ls', M c.name ls' = N.KS.ctorSet M ls' j c)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    (hz : S.z (S.lparams.map φ) = true)
    {ps : List V} {ρ : Nat → V} {m1 m : V} {mins minsK : List V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hwdC : ∀ c ∈ N.K.ctors, CtxWD M' φ' (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields))
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hmot1 : ∀ t, t ∈ˢ S.classAt M (S.lparams.map φ) N ps →
        appList m1 [t] ∈ˢ (univ (Level.eval φ' S.ℓ) : V))
    (hmnK : FitsVals M' φ' (consList (mins ++ [m1, m]) (consList ps ρ)) (S.minorsCtxK N) minsK) :
    ∀ j c, N.K.ctors[j]? = some c →
      ∀ fs, S.FitsFields M (S.lparams.map φ) (S.Fam M (S.lparams.map φ) ps) ps (S.classCtor N c).fields fs →
        ∀ ihs, ListRel (S.IhTypedN M (S.lparams.map φ) (S.q.holds φ') ps ⟨m, m1, mins, minsK⟩ fs)
            (S.classCtor N c).recFields ihs →
          appList (minorKAt N minsK j) (fs.reverse ++ ihs) ∈ˢ appList m1 [pt] ∧
          SpineOk (minorKAt N minsK j) (fs.reverse ++ ihs) := by
  intro j c hc fs hfit ihs hihs
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hj : j < N.nK := (List.getElem?_eq_some_iff.mp hc).1
  have R := R₂.R
  have hNS := hS.2.2.2.2.2.2 N hN
  have hsc := S.classCtor_fieldScoped N hS hN hKS hcm
  have hzK : N.KS.z (S.lsK (S.lparams.map φ) N) = true := by rw [hnf.z_eq]; exact hz
  -- the minor, from its context
  obtain ⟨minsE, hminsE, hmem⟩ : ∃ minsE : List V, minsE.length = j ∧
      minorKAt N minsK j ∈ˢ interp M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
        (S.minorTyK N c j) := by
    refine ⟨minsK.drop (N.nK - j), by simp [hminsK]; omega, ?_⟩
    rw [minorsCtxK_eq] at hmnK
    have := fits_ctxFrom (S.minorTyK N) N.K.ctors 0 _ minsK hmnK j c hc
    rw [Nat.zero_add] at this
    exact this
  have henv : consList minsE (consList (mins ++ [m1, m]) (consList ps ρ))
      = consList (minsE ++ mins ++ [m1, m]) (consList ps ρ) := by
    simp [consList_append]
  have hos : (minsE ++ mins ++ [m1, m]).length = 2 + S.n + j := by simp [hminsE, hmins]; omega
  have hgetm : (minsE ++ mins ++ [m1, m]).getD (2 + S.n + j - 1) pt = m := by
    rw [show 2 + S.n + j - 1 = (minsE ++ mins).length + 1 by simp [hminsE, hmins]; omega]
    exact (getD_append_two _ _).2
  have hgetm1 : (minsE ++ mins ++ [m1, m]).getD (2 + S.n + j - 2) pt = m1 := by
    rw [show 2 + S.n + j - 2 = (minsE ++ mins).length by simp [hminsE, hmins]; omega]
    exact (getD_append_two _ _).1
  -- fitting the field context in the reader is fitting the translated constructor
  have hfieldsF : ∀ fs', FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
      (S.fieldCtxAt (S.classCtor N c) (2 + S.n + j)) fs' ↔
      S.FitsFields M (S.lparams.map φ) (S.Fam M (S.lparams.map φ) ps) ps (S.classCtor N c).fields fs' := by
    intro fs'
    unfold fieldCtxAt
    rw [henv, FitsVals_liftCtx_liftN M' φ' _ _ _ hos]
    exact (R.fits_fieldCtx hS hsc hps hp (hwdC c hcm)).1
  -- the conclusion's value: the class's motive at the point
  have hconcl : ∀ fs' ihsR, fs'.length = (S.classCtor N c).fields.length →
      ihsR.length = (S.classCtor N c).recFields.length →
      interp M' φ' (consList ihsR (consList fs' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))))
          (Expr.mkAppN (.bvar ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
              (2 + S.n + j) - 2))
            [Expr.mkAppN (.const c.name N.lsK)
              (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
                  (2 + S.n + j)) ++
                Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length)])
        = appList m1 [pt] := by
    intro fs' ihsR hf' hi'
    rw [interp_mkAppN_appList, interp_bvar, List.map_singleton, henv,
      Reader.classCtorApp_read hS R hN (hcst j c hc) (o := 2 + S.n + j) hi' hf' hos hps hp hidx,
      hctor j c hc, KS_ctorSet_eq_pt M _ hzK, appList_pt]
    rw [show (S.classCtor N c).recFields.length + (S.classCtor N c).fields.length + (2 + S.n + j) - 2
        = ((2 + S.n + j - 2) + (S.classCtor N c).fields.length) + (S.classCtor N c).recFields.length by
        omega,
      ← hi', consList_ge, ← hf', consList_ge, consList_getD (by omega), hgetm1]
  -- the minor's type, read
  unfold minorTyK at hmem
  rw [interp_mkPis] at hmem
  have hlenI : ihs.reverse.length = (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length := by
    rw [List.length_reverse, ihCtxAt_eq, length_ihCtxAux, ListRel.length' hihs]
  have hf := S.FitsFields_length M _ hfit
  have hfitAll : FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
      (S.ihCtxAt (S.classCtor N c) (2 + S.n + j) ++ S.fieldCtxAt (S.classCtor N c) (2 + S.n + j))
      (ihs.reverse ++ fs) := by
    refine (FitsVals_append M' φ' hlenI).mpr ⟨(hfieldsF fs).mpr hfit, ?_⟩
    rw [ihCtxAt_eq, henv]
    exact (Reader.fits_ihCtxAux' S R hsc (os := minsE ++ mins ++ [m1, m]) (ρ := ρ) hf hos (by omega)
      (fun _ => by omega) hps ⟨m, m1, mins, minsK⟩ hgetm.symm hgetm1.symm (S.classCtor N c).recFields
      (fun _ h => h) ihs (l := 0) (ihsE := []) rfl).mpr hihs
  have hG : S.q.holds φ' = true →
      ∀ ws, FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
        (S.ihCtxAt (S.classCtor N c) (2 + S.n + j) ++ S.fieldCtxAt (S.classCtor N c) (2 + S.n + j)) ws →
      interp M' φ' (consList ws (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ))))
        (Expr.mkAppN (.bvar ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
            (2 + S.n + j) - 2))
          [Expr.mkAppN (.const c.name N.lsK)
            (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
                (2 + S.n + j)) ++
              Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length)])
        ∈ˢ (univ 0 : V) :=
    fun hq ws hws => by
      obtain ⟨ihsR, fs', rfl, hl₁⟩ : ∃ ihsR fs', ws = ihsR ++ fs' ∧
          ihsR.length = (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length := by
        have hl := FitsVals_length M' φ' hws
        refine ⟨ws.take (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
          ws.drop (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
          (List.take_append_drop _ _).symm, ?_⟩
        simp at hl; simp [hl]
      obtain ⟨hwsF, hwsI⟩ := (FitsVals_append M' φ' hl₁).mp hws
      have hfit' := (hfieldsF fs').mp hwsF
      have hf' := S.FitsFields_length M _ hfit'
      have hi' : ihsR.length = (S.classCtor N c).recFields.length := by
        rw [hl₁, ihCtxAt_eq, length_ihCtxAux]
      rw [consList_append, hconcl fs' ihsR hf' hi']
      have hz' := (S.q_holds φ')
      rw [hq, Bool.true_eq, beq_iff_eq] at hz'
      rw [← hz']
      exact hmot1 _ (pt_mem_classAt hnf hNS.2.2.2.2.1 hNS.2.2.1 hKS hN hz hc hp hfit')
  have key := appList_mem_of_piCtx M' φ' hmem hfitAll
  have key₂ := spineOk_of_piCtx M' φ' hmem hfitAll hG
  rw [List.reverse_append, List.reverse_reverse, consList_append,
    hconcl fs ihs.reverse hf (by rw [List.length_reverse, ListRel.length' hihs])] at key
  rw [List.reverse_append, List.reverse_reverse] at key₂
  exact ⟨key, key₂⟩

omit [LevelOracle] in
/-- **The motives are inhabited at a proposition**, on the family and
on the class: by the interleaved induction from the minors' typing,
the class's minors read at the point (`motive_inhabitedN` without the
class's laws: at a proposition every member of the family and of the
class is the point). -/
theorem motives_inhabited_prop {M : Name → List Nat → V} {ls : List Nat}
    (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env) (hN : S.nest = some N)
    (hz : S.z ls = true) (q : Bool) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c →
      ∀ fs, S.FitsFields M ls (S.Fam M ls ps) ps (S.classCtor N c).fields fs →
        ∀ ihs, ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields ihs →
          appList (minorKAt N ex.minsK j) (fs.reverse ++ ihs) ∈ˢ appList ex.m1 [pt])
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V)) :
    (∀ is t, t ∈ˢ S.Fam M ls ps is → ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [t])) ∧
    (∀ t, t ∈ˢ S.classAt M ls N ps → ∃ v, v ∈ˢ appList ex.m1 [t]) := by
  have hzK : N.KS.z (S.lsK ls N) = true := by rw [hf.z_eq]; exact hz
  have hpN : N.p < N.nPK := hf.positive.2.1
  have hu0 : S.u₀ ls = 0 := (S.z_iff ls).mp hz
  -- a member of the container's family at a proposition is the point
  have hptK : ∀ (X : V) (y : V), y ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] → y = pt := by
    intro X y hy
    have := N.KS.Fam_mem_univ M (S.lsK ls N) (S.psK M ls N ps X) []
    rw [hf.u₀_eq, hu0] at this
    exact eq_pt_of_mem_univ_zero this hy
  -- the inner induction, over the container's family at a member set inside the fibre
  have inner : ∀ (X : V), X ∈ˢ (univ (S.u₀ ls) : V) → X ⊆ˢ S.Fam M ls ps (S.memberIdx M ls N ps) →
      (∀ x, x ∈ˢ X → ∃ v, v ∈ˢ appList ex.m ((S.memberIdx M ls N ps).reverse ++ [x])) →
      ∀ y, y ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] → ∃ v, v ∈ˢ appList ex.m1 [pt] := by
    intro X hX hXF hkey y hy
    refine N.KS.Fam_induction M (S.lsK ls N) hf.noRecDep (hf.domsBoundedK hp hX) (hf.contOkK _)
      (fun _ _ => ∃ v, v ∈ˢ appList ex.m1 [pt]) ?_ [] y hy
    intro is' x hs
    obtain ⟨j, c, fs, hc, hfit, -, -⟩ := hs
    have hcm := List.mem_of_getElem? hc
    have hfitB : S.FitsFields M ls (S.Fam M ls ps) ps (S.classCtor N c).fields fs := by
      simp only [classCtor]
      exact FitsFields_classFields_of_KS hf hlen hlsK hKS hN hcm hp hX hXF
        (fun _ h => (mem_sep.mp h).1) (List.drop_zero (l := c.fields)) hfit
    obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields ihs := by
      refine ListRel.exists_of_forall fun kf hkf => ?_
      obtain ⟨k, f⟩ := kf
      obtain ⟨hf₁, hk, hrec⟩ := mem_recFields hkf
      dsimp only at hf₁ hk hrec ⊢
      obtain ⟨f₀, hf₀, hfe⟩ := S.classCtor_fields_get N c hf₁ hk
      have hlenF : fs.length = c.fields.length := N.KS.FitsFields_length M _ hfit
      have hk' : k < c.fields.length := by simpa [classCtor, S.length_classFields] using hk
      have hget := N.KS.FitsFields_get M _ hfit hf₀ hk'
      have hpf := positive_field N hf.positive hcm (List.drop_zero (l := c.fields)) hf₀
      have hkk : c.fields.length - 1 - (c.fields.length - 1 - k) = k := by omega
      cases f₀ with
      | ordinary A =>
        rcases hpf with hA | ⟨hu, -⟩
        · -- the member field
          rw [hkk] at hA
          subst hA
          simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true] at hfe
          subst hfe
          dsimp only [IhTypedN, piCtx_nil, List.length_nil, readEnv_zero, List.reverse_nil, appList_nil]
          rw [S.memberIdx_earlier M ls N ps (by omega)]
          simp only [fieldSet, interp_bvar] at hget
          rw [S.read_memberVar M ls N hlen hpN (length_earlier (by omega))] at hget
          exact hkey _ hget
        · exfalso
          rw [hkk] at hu
          rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)] at hfe
          subst hfe
          simp [Field.isRec] at hrec
      | reflexive tele es =>
        obtain ⟨rfl, rfl⟩ := hpf
        simp only [classField] at hfe
        subst hfe
        dsimp only [IhTypedN]
        simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil, mem_sep] at hget
        rw [hptK X _ hget.1]
        exact hget.2
      | container => exact hpf.elim
    exact ⟨_, hminK j c hc fs hfitB ihs hihs⟩
  -- the outer induction, over the family
  have key : ∀ is x, x ∈ˢ S.Fam M ls ps is → ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [x]) := by
    refine S.Fam_induction M ls hnr hb hco
      (fun is x => ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [x])) ?_
    intro is x hs
    obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
    have hfitF := S.FitsFields_of_sep M ls hco _ hfit
    subst his
    obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTypedN M ls q ps ex fs) c.recFields ihs := by
      refine ListRel.exists_of_forall fun kf hkf => ?_
      obtain ⟨hf₁, hk, hrec⟩ := mem_recFields hkf
      have hsep := S.sep_fields M ls N hN _ hfit hf₁ hk
      obtain ⟨k, f⟩ := kf
      cases f with
      | ordinary _ => simp [Field.isRec] at hrec
      | reflexive tele es =>
        dsimp only [IhTypedN]
        refine ⟨lamCtx M (S.ψ ls) q _ tele fun ρ' => pickMem (appList ex.m ((S.idxVals M ls ρ' es).reverse ++
          [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])),
          lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_⟩
        · have hlen := FitsVals_length M _ hys
          refine pickMem_mem ?_
          simp only [readEnv_consList hlen]
          exact (hsep ys hys).2
        · have hlen := FitsVals_length M _ hys
          simp only [readEnv_consList hlen]
          exact hmo hq _ _ (hsep ys hys).1
      | container =>
        dsimp only [IhTypedN]
        have hX : sep (S.Fam M ls ps (S.memberIdx M ls N ps))
            (fun x => ∃ v, v ∈ˢ appList ex.m ((S.memberIdx M ls N ps).reverse ++ [x]))
            ∈ˢ (univ (S.u₀ ls) : V) := sep_mem_univ (S.Fam_mem_univ M ls ps _)
        rw [S.classSet_eq_Fam hf hp hX] at hsep
        rw [hptK _ _ hsep]
        exact inner _ hX sep_sub (fun x hx => (mem_sep.mp hx).2) _ hsep
    exact ⟨_, hmin j c hc fs hfitF ihs hihs⟩
  refine ⟨key, fun t ht => ?_⟩
  unfold classAt at ht
  rw [S.classSet_eq_Fam hf hp (S.Fam_mem_univ M ls _ _)] at ht
  rw [hptK _ _ ht]
  exact inner _ (S.Fam_mem_univ M ls _ _) (Sub.refl _) (fun x hx => key _ x hx) t ht

/-! ## The recursors' sets in the final model -/

variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

omit hs in
/-- The container's constructors are stored. -/
theorem K_ctors_stored : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome :=
  fun j c hc => by rw [(K_law m hok).2.2.2.1 j c hc]; rfl

/-- **The member's index values fit the index context** at every
fitting parameter list: from the class having a sort at the block's
parameters (the check), whose member argument — the family at the
member's index expressions — is well-denoted (`famAt_wd`). -/
theorem memberIdx_fits (φ : Name → Nat) {ps : List V}
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) :
    FitsVals m.M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx m.M (S.lparams.map φ) N ps) := by
  have hNS := hok.nestScoped N hok.nest
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hp; simpa [nP] using this
  have R₀ := reader₃₀ hok m.M φ
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2.2.2.2.1
  have hwdI := (type_ok_indN hs m hok φ base (ls := S.lvls) (by simp [indInfo, lvls])).1
  simp only [indInfo] at hwdI
  rw [WellDenoted_instL] at hwdI
  simp only [lvls] at hwdI
  rw [Level.substVal_self] at hwdI
  unfold indType at hwdI
  rw [WellDenoted_mkPis] at hwdI
  have hwdP := (CtxWD_append' hwdI.1).1
  have hp' : FitsVals (S.M₃N m.M N) φ base S.params ps := (R₀.fits_params hok.scoped).mpr hp
  have hsat : Sat (S.M₃N m.M N) φ S.params (consList ps base) := Sat_of_fits _ _ hwdP hp'
  have hsem := (infer_sound (m := mIndN hs m hok) (φ := φ) hT (consList ps base) hsat).1
  rw [mIndN_M] at hsem
  unfold classTy at hsem
  have hwm := (WellDenoted_mkAppN' _ _ hsem).2 (S.famAt 0 (N.idx.map (Expr.liftN 0 ·)))
    (by unfold classArgs; simp)
  have h := (R₀.famAt_wd hok.scoped (o := 0) (ρ'' := consList ps base) (ps := ps)
    (by rw [shiftE_zero_zero, readEnv_consList hps]) (by simp [hNS.2.2.2.2.2.1]) hwm).2.1
  unfold memberIdx idxVals
  have hm : ((N.idx.map (Expr.liftN 0 ·)).map (interp (S.M₃N m.M N) φ (consList ps base)))
      = N.idx.map (interp m.M (S.ψ (S.lparams.map φ)) (envP ps)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp]
    rw [interp_liftN, shiftE_zero_zero]
    have := R₀.read (hNS.2.2.2.2.2.2.2.1 e he) (vs := []) (ps := ps) (ρ := base) (by simp [hps])
    simpa [envP] using this
  rw [hm] at h
  exact h

/-- The block's constructors' field contexts are well-denoted in the
final model at fitting parameters. -/
theorem wdFieldCtxN (φ : Name → Nat) (ρ : Nat → V) :
    ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps →
      CtxWD (S.M₃N m.M N) φ (consList ps ρ) (S.fieldCtx c.fields) := by
  intro c hc ps hps hp
  exact ((reader₃N m hok φ).R.idxFit_of_wd hok.scoped hc (wd_ctorTypeN hs m hok hc _ ρ) hps hp).1

/-- **`T.rec`'s set at concrete levels** is the abstraction over its
context read in the final model at the instantiated valuation. -/
theorem recSetN_eq (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) :
    S.M₃N m.M N S.recName (us.map (Level.eval φ)) =
      lamCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (S.q.holds (Level.substVal φ S.recLparams us)) ρ (S.recCtxN N) fun ρ' =>
          S.recSemN m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N
            (S.q.holds (Level.substVal φ S.recLparams us))
            (readEnv S.nP (shiftE (1 + S.nI + S.oN N) 0 ρ'))
            ⟨ρ' (S.nI + S.oN N), ρ' (S.nI + S.oN N - 1),
              readEnv S.n (shiftE (1 + S.nI + N.nK) 0 ρ'), readEnv N.nK (shiftE (1 + S.nI) 0 ρ')⟩
            (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0) := by
  have hS := hok.scoped
  have hagr := recAgree_of (S := S) φ hus
  have hval : ∀ n ∈ S.lparams, valOf S.recLparams (us.map (Level.eval φ)) n
      = Level.substVal φ S.recLparams us n :=
    fun n hn => recVal_agree φ hus n (S.lparams_sub_recLparams hn)
  have hls := block_levels_eq (S := S) φ hus
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have R₂ := reader₂N m hok (Level.substVal φ S.recLparams us) hval
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N) := by
    have := wd_recTypeN hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [recTypeN_eq, WellDenoted_mkPis] at this
    exact this.1
  have hagree := R₂.agree_recCtxN hS R₃ hagr hok.nest (K_law m hok).1 hok.freshI
    (K_ctors_stored m hok) base ρ (fun ps hp => memberIdx_fits hs m hok _ hp)
    (wdFieldCtxN hs m hok _ ρ) hwd
  have e : S.M₃N m.M N S.recName (us.map (Level.eval φ)) = S.recSetN m.M N (us.map (Level.eval φ)) := by
    simp [M₃N, hok.rec_ne_aux]
  rw [e]
  show lamCtx (S.M₂ m.M) (valOf S.recLparams (us.map (Level.eval φ)))
      (S.q.holds (valOf S.recLparams (us.map (Level.eval φ)))) base (S.recCtxN N)
      (fun ρ' => S.recSemN m.M (S.lparams.map (valOf S.recLparams (us.map (Level.eval φ)))) N
        (S.q.holds (valOf S.recLparams (us.map (Level.eval φ))))
        (readEnv S.nP (shiftE (1 + S.nI + S.oN N) 0 ρ'))
        ⟨ρ' (S.nI + S.oN N), ρ' (S.nI + S.oN N - 1),
          readEnv S.n (shiftE (1 + S.nI + N.nK) 0 ρ'), readEnv N.nK (shiftE (1 + S.nI) 0 ρ')⟩
        (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)) = _
  rw [hls, hagr.q_holds]
  exact lamCtx_congr₂ hagree fun vs hvs => by
    obtain ⟨t, is, minsK, mins, m1, m', ps, rfl, hi, hminsK, hmins, hps⟩ := fits_recCtxN_split S N hvs
    rw [recFN_read S m.M _ N _ hi hminsK hmins hps, recFN_read S m.M _ N _ hi hminsK hmins hps]

/-- **`T.rec_1`'s set at concrete levels** is the abstraction over its
context read in the final model at the instantiated valuation. -/
theorem rec1Set_eq (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) :
    S.M₃N m.M N N.aux (us.map (Level.eval φ)) =
      lamCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (S.q.holds (Level.substVal φ S.recLparams us)) ρ (S.rec1Ctx N) fun ρ' =>
          S.rec1Sem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N
            (S.q.holds (Level.substVal φ S.recLparams us))
            (readEnv S.nP (shiftE (1 + S.oN N) 0 ρ'))
            ⟨ρ' (S.oN N), ρ' (S.oN N - 1),
              readEnv S.n (shiftE (1 + N.nK) 0 ρ'), readEnv N.nK (shiftE 1 0 ρ')⟩
            (ρ' 0) := by
  have hS := hok.scoped
  have hagr := recAgree_of (S := S) φ hus
  have hval : ∀ n ∈ S.lparams, valOf S.recLparams (us.map (Level.eval φ)) n
      = Level.substVal φ S.recLparams us n :=
    fun n hn => recVal_agree φ hus n (S.lparams_sub_recLparams hn)
  have hls := block_levels_eq (S := S) φ hus
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have R₂ := reader₂N m hok (Level.substVal φ S.recLparams us) hval
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have hagree := R₂.agree_rec1Ctx hS R₃ hagr hok.nest (K_law m hok).1 hok.freshI
    (K_ctors_stored m hok) base ρ (fun ps hp => memberIdx_fits hs m hok _ hp)
    (wdFieldCtxN hs m hok _ ρ) hwd
  have e : S.M₃N m.M N N.aux (us.map (Level.eval φ)) = S.rec1Set m.M N (us.map (Level.eval φ)) := by
    simp [M₃N]
  rw [e]
  show lamCtx (S.M₂ m.M) (valOf S.recLparams (us.map (Level.eval φ)))
      (S.q.holds (valOf S.recLparams (us.map (Level.eval φ)))) base (S.rec1Ctx N)
      (fun ρ' => S.rec1Sem m.M (S.lparams.map (valOf S.recLparams (us.map (Level.eval φ)))) N
        (S.q.holds (valOf S.recLparams (us.map (Level.eval φ))))
        (readEnv S.nP (shiftE (1 + S.oN N) 0 ρ'))
        ⟨ρ' (S.oN N), ρ' (S.oN N - 1),
          readEnv S.n (shiftE (1 + N.nK) 0 ρ'), readEnv N.nK (shiftE 1 0 ρ')⟩
        (ρ' 0)) = _
  rw [hls, hagr.q_holds]
  exact lamCtx_congr₂ hagree fun vs hvs => by
    obtain ⟨t, minsK, mins, m1, m', ps, rfl, hminsK, hmins, hps⟩ := fits_rec1Ctx_split S N hvs
    rw [rec1F_read S m.M _ N _ hminsK hmins hps, rec1F_read S m.M _ N _ hminsK hmins hps]

/-! ## The recursors' typing at a fitting spine -/

/-- **The two recursors are typed at every fitting spine** — above a
proposition, their semantic values lie in the motives
(`recSemN_mem`); at a proposition with a large eliminator the same,
since the block is then never a proposition; at a proposition with a
small eliminator the motives are inhabited (`motives_inhabited_prop`,
with the class's minors' typing read at the point). -/
theorem recs_typed (φr : Name → Nat) (ρ : Nat → V) {ps : List V} {m1 m' : V} {mins minsK : List V}
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) φr (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) φr (cons m' (consList ps ρ)) (S.motiveTy1 N))
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hmn : FitsVals (S.M₃N m.M N) φr (consList [m1, m'] (consList ps ρ)) S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) φr (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    (hwdE : CtxWD (S.M₃N m.M N) φr (consList ps ρ) (S.extrasN N)) :
    (S.q.holds φr = false →
      (∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is →
        S.recSemN m.M (S.lparams.map φr) N false ps ⟨m', m1, mins, minsK⟩ is t ∈ˢ
          appList m' (is.reverse ++ [t])) ∧
      (∀ t, t ∈ˢ S.classAt m.M (S.lparams.map φr) N ps →
        S.rec1Sem m.M (S.lparams.map φr) N false ps ⟨m', m1, mins, minsK⟩ t ∈ˢ appList m1 [t])) ∧
    (S.q.holds φr = true →
      (∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is → appList m' (is.reverse ++ [t]) = one) ∧
      (∀ t, t ∈ˢ S.classAt m.M (S.lparams.map φr) N ps → appList m1 [t] = one)) := by
  have hS := hok.scoped
  have hN := hok.nest
  have hK := K_law m hok
  have R₃ := reader₃N m hok φr
  have hidx := memberIdx_fits hs m hok φr hp
  have hwdC := wdFieldCtxN hs m hok φr ρ
  have hwdCK : ∀ c ∈ N.K.ctors, CtxWD (S.M₃N m.M N) φr (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields) :=
    fun c hc => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      exact wdFieldCtxK hwdE hmins hminsK hm hm1 hmn hmnK j c hj
  have hres : ∀ c ∈ S.ctors, ∀ fs, S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps c.fields fs →
      FitsVals m.M (S.ψ (S.lparams.map φr)) (envP ps) S.indices
        (S.idxVals m.M (S.lparams.map φr) (consList fs (envP ps)) c.idx) :=
    fun c hc fs hfit =>
      ((R₃.R.idxFit_of_wd hS hc (wd_ctorTypeN hs m hok hc _ ρ) hps hp).2 fs hfit).2.2
  have hmot := R₃.R.motiveOk_of_mem hS hps hp hm
  have hmot1 := Reader.motive1Ok_of_mem S N hS R₃.R hN hps hp hidx hm1
  have hmin : ∀ j c, S.ctors[j]? = some c →
      S.MinorOkN m.M (S.lparams.map φr) (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ j c :=
    fun j c hc fs hfit ihs hihs =>
      (Reader₂.minorOkN_of_fits S hS R₃ hok.freshI hps hp hmins (fun c hc => hwdC c hc ps hps hp)
        hres hmot (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp)
        (contOk hs m hok φr hp) hmn j c hc fs hfit ihs
        ((ListRel_iff fun _ _ => Iff.rfl).mp hihs)).1
  have hFam : ∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is →
      FitsVals m.M (S.ψ (S.lparams.map φr)) (envP ps) S.indices is := fun is t ht =>
    S.idx_fits_of_mem_Fam m.M _ (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp)
      (contOk hs m hok φr hp) (fun j c hc fs hfit => hres c (List.mem_of_getElem? hc) fs hfit) ht
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · have hz := z_false_of_q hok φr hq
    have hcl := classLaws hs m hok φr hz hp
    have hminK : ∀ j c, N.K.ctors[j]? = some c →
        S.MinorOkK m.M (S.lparams.map φr) N (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ j c :=
      fun j c hc fs hfit ihs hihs =>
        (Reader₂.minorOkK_of_fits S N hS R₃ hN (nestFacts hs m hok φr) hK.1 hK.2.2.2.2.2.1
          (K_ctors_stored m hok) hz hps hp hmins hminsK hwdCK hidx hmot1 hmnK j c hc fs hfit
          ihs hihs).1
    rw [hq] at hmin hminK
    exact S.recSemN_mem m.M _ N false hN hz (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp)
      (contOk hs m hok φr hp) hcl ⟨m', m1, mins, minsK⟩ hmin hminK (fun h => nomatch h)
  · have hℓ := S.q_holds φr
    rw [hq, Bool.true_eq, beq_iff_eq] at hℓ
    have hmo : ∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is →
        appList m' (is.reverse ++ [t]) ∈ˢ (univ 0 : V) := fun is t ht => by
      rw [← hℓ]; exact hmot is (hFam is t ht) t ht
    have hmo1 : ∀ t, t ∈ˢ S.classAt m.M (S.lparams.map φr) N ps → appList m1 [t] ∈ˢ (univ 0 : V) :=
      fun t ht => by rw [← hℓ]; exact hmot1 t ht
    suffices h : (∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is →
          ∃ v, v ∈ˢ appList m' (is.reverse ++ [t])) ∧
        (∀ t, t ∈ˢ S.classAt m.M (S.lparams.map φr) N ps → ∃ v, v ∈ˢ appList m1 [t]) by
      refine ⟨fun is t ht => ?_, fun t ht => ?_⟩
      · obtain ⟨v, hv⟩ := h.1 is t ht
        exact eq_one_of_mem_univ_zero (hmo is t ht) hv
      · obtain ⟨v, hv⟩ := h.2 t ht
        exact eq_one_of_mem_univ_zero (hmo1 t ht) hv
    cases hz : S.z (S.lparams.map φr)
    · have hcl := classLaws hs m hok φr hz hp
      have hminK : ∀ j c, N.K.ctors[j]? = some c →
          S.MinorOkK m.M (S.lparams.map φr) N (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ j c :=
        fun j c hc fs hfit ihs hihs =>
          (Reader₂.minorOkK_of_fits S N hS R₃ hN (nestFacts hs m hok φr) hK.1 hK.2.2.2.2.2.1
            (K_ctors_stored m hok) hz hps hp hmins hminsK hwdCK hidx hmot1 hmnK j c hc fs hfit
            ihs hihs).1
      rw [hq] at hmin hminK
      exact S.motive_inhabitedN m.M _ N true hN (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp)
        (contOk hs m hok φr hp) hcl ⟨m', m1, mins, minsK⟩ hmin hminK (fun _ => hmo)
    · have hNS := hok.nestScoped N hN
      have hminK' : ∀ j c, N.K.ctors[j]? = some c →
          ∀ fs, S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps (S.classCtor N c).fields fs →
            ∀ ihs, ListRel (S.IhTypedN m.M (S.lparams.map φr) (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ fs)
                (S.classCtor N c).recFields ihs →
              appList (minorKAt N minsK j) (fs.reverse ++ ihs) ∈ˢ appList m1 [pt] :=
        fun j c hc fs hfit ihs hihs =>
          (Reader₂.minorOkK_of_fits_prop hS R₃ hN (nestFacts hs m hok φr) hK.1 hK.2.2.2.2.2.1
            (K_ctors_stored m hok) hz hps hp hmins hminsK hwdCK hidx hmot1 hmnK j c hc fs hfit
            ihs hihs).1
      rw [hq] at hmin hminK'
      exact motives_inhabited_prop (nestFacts hs m hok φr) hNS.2.2.2.2.1 hNS.2.2.1 hK.1 hN hz true hp
        (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp) (contOk hs m hok φr hp)
        ⟨m', m1, mins, minsK⟩ hmin hminK' (fun _ => hmo)

/-- **`T.rec`'s set is in `T.rec`'s type.** -/
theorem recSetN_mem (φ : Name → Nat) (ρ : Nat → V) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.recSetN m.M N (lsr.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.recTypeN N) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams lsr)
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.recCtxN N) := by
    have := wd_recTypeN hs m hok (Level.substVal φ S.recLparams lsr) ρ
    rw [recTypeN_eq, WellDenoted_mkPis] at this
    exact this.1
  have e : S.recSetN m.M N (lsr.map (Level.eval φ)) = S.M₃N m.M N S.recName (lsr.map (Level.eval φ)) := by
    simp [M₃N, hok.rec_ne_aux]
  rw [e, recSetN_eq hs m hok φ ρ hlsr, recTypeN_eq, interp_mkPis]
  refine lamCtx_mem_piCtx' _ _ (by simp [recCtxN]) ?_ ?_
  · intro hq vs hvs
    obtain ⟨t, is, minsK, mins, m1, m', ps, rfl, hi, hminsK, hmins, hps⟩ := fits_recCtxN_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩ :=
      (Reader.fits_recCtxN_iff S N hS R₃.R hi hminsK hmins hps).mp hvs
    rw [recFN_read S m.M _ N _ hi hminsK hmins hps, read_recBodyN S _ _ N hi hminsK hmins, hq]
    have hwdE := wd_extrasN_of_recCtxN hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).1 hq).1 is t ht
  · intro hq vs hvs
    obtain ⟨t, is, minsK, mins, m1, m', ps, rfl, hi, hminsK, hmins, hps⟩ := fits_recCtxN_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩ :=
      (Reader.fits_recCtxN_iff S N hS R₃.R hi hminsK hmins hps).mp hvs
    rw [read_recBodyN S _ _ N hi hminsK hmins]
    have hwdE := wd_extrasN_of_recCtxN hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).2 hq).1 is t ht

/-- **`T.rec_1`'s set is in `T.rec_1`'s type.** -/
theorem rec1Set_mem (φ : Name → Nat) (ρ : Nat → V) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.rec1Set m.M N (lsr.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.rec1Type N) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams lsr)
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok (Level.substVal φ S.recLparams lsr) ρ
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have e : S.rec1Set m.M N (lsr.map (Level.eval φ)) = S.M₃N m.M N N.aux (lsr.map (Level.eval φ)) := by
    simp [M₃N]
  have hidx := fun ps hp => memberIdx_fits hs m hok (Level.substVal φ S.recLparams lsr) (ps := ps) hp
  rw [e, rec1Set_eq hs m hok φ ρ hlsr, rec1Type_eq, interp_mkPis]
  refine lamCtx_mem_piCtx' _ _ (by simp [rec1Ctx]) ?_ ?_
  · intro hq vs hvs
    obtain ⟨t, minsK, mins, m1, m', ps, rfl, hminsK, hmins, hps⟩ := fits_rec1Ctx_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, ht⟩ :=
      (Reader.fits_rec1Ctx_iff S N hS R₃.R hok.nest hminsK hmins hps hidx).mp hvs
    rw [rec1F_read S m.M _ N _ hminsK hmins hps, read_rec1Body S _ _ N hminsK hmins, hq]
    have hwdE := wd_extrasN_of_rec1Ctx hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).1 hq).2 t ht
  · intro hq vs hvs
    obtain ⟨t, minsK, mins, m1, m', ps, rfl, hminsK, hmins, hps⟩ := fits_rec1Ctx_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, ht⟩ :=
      (Reader.fits_rec1Ctx_iff S N hS R₃.R hok.nest hminsK hmins hps hidx).mp hvs
    rw [read_rec1Body S _ _ N hminsK hmins]
    have hwdE := wd_extrasN_of_rec1Ctx hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).2 hq).2 t ht

/-- **`T.rec`'s type law.** -/
theorem type_ok_recN (φ : Name → Nat) (ρ : Nat → V) {ls : List Level}
    (hls : ls.length = (S.recInfoN N).lparams.length) :
    WellDenoted (S.M₃N m.M N) φ ρ ((S.recInfoN N).type.instL (S.recInfoN N).lparams ls) ∧
    S.M₃N m.M N S.recName (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) φ ρ ((S.recInfoN N).type.instL (S.recInfoN N).lparams ls) := by
  simp only [recInfoN] at hls ⊢
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr (wd_recTypeN hs m hok _ ρ), ?_⟩
  rw [interp_instL]
  have : S.M₃N m.M N S.recName (ls.map (Level.eval φ)) = S.recSetN m.M N (ls.map (Level.eval φ)) := by
    simp [M₃N, hok.rec_ne_aux]
  rw [this]
  exact recSetN_mem hs m hok φ ρ hls

/-- **`T.rec_1`'s type law.** -/
theorem type_ok_rec1 (φ : Name → Nat) (ρ : Nat → V) {ls : List Level}
    (hls : ls.length = (S.rec1Info N).lparams.length) :
    WellDenoted (S.M₃N m.M N) φ ρ ((S.rec1Info N).type.instL (S.rec1Info N).lparams ls) ∧
    S.M₃N m.M N N.aux (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) φ ρ ((S.rec1Info N).type.instL (S.rec1Info N).lparams ls) := by
  simp only [rec1Info] at hls ⊢
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr (wd_rec1Type hs m hok _ ρ), ?_⟩
  rw [interp_instL]
  have : S.M₃N m.M N N.aux (ls.map (Level.eval φ)) = S.rec1Set m.M N (ls.map (Level.eval φ)) := by
    simp [M₃N]
  rw [this]
  exact rec1Set_mem hs m hok φ ρ hls

/-! ## The recursors' sets applied -/

omit [LevelOracle] hs hok in
/-- The extras' context fitted: the two motives in their types, both
minor lists fitting theirs. -/
theorem fits_extrasN_iff' (φr : Name → Nat) (ρ : Nat → V) {ps minsK mins : List V} {m1 m' : V}
    (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n) :
    FitsVals (S.M₃N m.M N) φr (consList ps ρ) (S.extrasN N) (minsK ++ mins ++ [m1, m']) ↔
      m' ∈ˢ interp (S.M₃N m.M N) φr (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp (S.M₃N m.M N) φr (cons m' (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals (S.M₃N m.M N) φr (consList [m1, m'] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals (S.M₃N m.M N) φr (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK := by
  have e2 : consList mins (consList [m1, m'] (consList ps ρ))
      = consList (mins ++ [m1, m']) (consList ps ρ) := by
    rw [consList_append]
  unfold extrasN
  rw [FitsVals_append _ _ (by simp [hminsK, hmins, length_minorsCtxN, length_minorsCtxK]),
    FitsVals_append _ _ (by simp [hminsK, length_minorsCtxK]), e2]
  simp only [FitsVals_cons, FitsVals_nil_nil, true_and, consList_cons, consList_nil]
  constructor
  · rintro ⟨⟨hm, hm1⟩, hmn, hmnK⟩; exact ⟨hm, hm1, hmn, hmnK⟩
  · rintro ⟨hm, hm1, hmn, hmnK⟩; exact ⟨⟨hm, hm1⟩, hmn, hmnK⟩

/-- **`T.rec`'s set applied to a fitting spine**: the spine fits the
recursor's context, the value lies in the motive at the indices and
the major, the application chain is well-formed, and in the graph
regime the value is the semantic recursor at the major. -/
theorem rec_app_memN (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {ps : List V} {m1 m' : V} {mins minsK is : List V} {t : V}
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      (S.motiveTy1 N))
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hmn : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1, m'] (consList ps ρ))
      S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    (his : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps)
      S.indices is)
    (ht : t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps is) :
    FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N)
      (t :: is ++ minsK ++ mins ++ [m1, m'] ++ ps) ∧
    appList (S.M₃N m.M N S.recName (us.map (Level.eval φ)))
        (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse ++ [t])
      ∈ˢ appList m' (is.reverse ++ [t]) ∧
    SpineOk (S.M₃N m.M N S.recName (us.map (Level.eval φ)))
      (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse ++ [t]) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      appList (S.M₃N m.M N S.recName (us.map (Level.eval φ)))
          (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse ++ [t])
        = S.recSemN m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N false ps
            ⟨m', m1, mins, minsK⟩ is t) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have hi : is.length = S.nI := by have := FitsVals_length m.M _ his; simpa [nI] using this
  have hfit : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N)
      (t :: is ++ minsK ++ mins ++ [m1, m'] ++ ps) :=
    (Reader.fits_recCtxN_iff S N hS R₃.R hi hminsK hmins hps).mpr
      ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩
  have hrev : ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse ++ [t]
      = (t :: is ++ minsK ++ mins ++ [m1, m'] ++ ps).reverse := by
    simp [List.reverse_append]
  have e : S.M₃N m.M N S.recName (us.map (Level.eval φ)) = S.recSetN m.M N (us.map (Level.eval φ)) := by
    simp [M₃N, hok.rec_ne_aux]
  have hf := recSetN_mem hs m hok φ ρ hus
  rw [recTypeN_eq, interp_mkPis] at hf
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N) := by
    have := wd_recTypeN hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [recTypeN_eq, WellDenoted_mkPis] at this
    exact this.1
  have hG : S.q.holds (Level.substVal φ S.recLparams us) = true →
      ∀ ws, FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N) ws →
        interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ws ρ)
          (Expr.mkAppN (.bvar (S.nI + S.oN N)) (Expr.varsAt 1 S.nI ++ [.bvar 0])) ∈ˢ
          (univ 0 : V) := by
    intro hq ws hws
    obtain ⟨t', is', minsK', mins', m1', m'', ps', rfl, hi', hminsK', hmins', hps'⟩ :=
      fits_recCtxN_split S N hws
    obtain ⟨hp', hm', hm1', hmn', hmnK', his', ht'⟩ :=
      (Reader.fits_recCtxN_iff S N hS R₃.R hi' hminsK' hmins' hps').mp hws
    rw [read_recBodyN S _ _ N hi' hminsK' hmins']
    have hwdE := wd_extrasN_of_recCtxN hwd ((R₃.R.fits_params hS).mpr hp')
    rw [((recs_typed hs m hok _ ρ hps' hp' hm' hm1' hmins' hminsK' hmn' hmnK' hwdE).2 hq).1 is' t' ht']
    exact one_mem_univ_zero
  refine ⟨hfit, ?_, ?_, ?_⟩
  · rw [hrev, e]
    have := appList_mem_of_piCtx _ _ hf hfit
    rwa [read_recBodyN S _ _ N hi hminsK hmins] at this
  · rw [hrev, e]
    exact spineOk_of_piCtx _ _ hf hfit hG
  · intro hq
    rw [hrev, recSetN_eq hs m hok φ ρ hus, hq, appList_lamCtx_false hfit,
      recFN_read S m.M _ N _ hi hminsK hmins hps]

/-- **`T.rec_1`'s set applied to a fitting spine**: likewise, with the
major in the class and the value in the class's motive at it. -/
theorem rec1_app_mem (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {ps : List V} {m1 m' : V} {mins minsK : List V} {t : V}
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      (S.motiveTy1 N))
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hmn : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1, m'] (consList ps ρ))
      S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    (ht : t ∈ˢ S.classAt m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N ps) :
    FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N)
      (t :: minsK ++ mins ++ [m1, m'] ++ ps) ∧
    appList (S.M₃N m.M N N.aux (us.map (Level.eval φ)))
        (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ [t])
      ∈ˢ appList m1 [t] ∧
    SpineOk (S.M₃N m.M N N.aux (us.map (Level.eval φ)))
      (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ [t]) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      appList (S.M₃N m.M N N.aux (us.map (Level.eval φ)))
          (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ [t])
        = S.rec1Sem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N false ps
            ⟨m', m1, mins, minsK⟩ t) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have hidx := fun ps hp => memberIdx_fits hs m hok (Level.substVal φ S.recLparams us) (ps := ps) hp
  have hfit : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N)
      (t :: minsK ++ mins ++ [m1, m'] ++ ps) :=
    (Reader.fits_rec1Ctx_iff S N hS R₃.R hok.nest hminsK hmins hps hidx).mpr
      ⟨hp, hm, hm1, hmn, hmnK, ht⟩
  have hrev : ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ [t]
      = (t :: minsK ++ mins ++ [m1, m'] ++ ps).reverse := by
    simp [List.reverse_append]
  have e : S.M₃N m.M N N.aux (us.map (Level.eval φ)) = S.rec1Set m.M N (us.map (Level.eval φ)) := by
    simp [M₃N]
  have hf := rec1Set_mem hs m hok φ ρ hus
  rw [rec1Type_eq, interp_mkPis] at hf
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have hG : S.q.holds (Level.substVal φ S.recLparams us) = true →
      ∀ ws, FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N) ws →
        interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ws ρ)
          (Expr.mkAppN (.bvar (S.oN N - 1)) [.bvar 0]) ∈ˢ (univ 0 : V) := by
    intro hq ws hws
    obtain ⟨t', minsK', mins', m1', m'', ps', rfl, hminsK', hmins', hps'⟩ :=
      fits_rec1Ctx_split S N hws
    obtain ⟨hp', hm', hm1', hmn', hmnK', ht'⟩ :=
      (Reader.fits_rec1Ctx_iff S N hS R₃.R hok.nest hminsK' hmins' hps' hidx).mp hws
    rw [read_rec1Body S _ _ N hminsK' hmins']
    have hwdE := wd_extrasN_of_rec1Ctx hwd ((R₃.R.fits_params hS).mpr hp')
    rw [((recs_typed hs m hok _ ρ hps' hp' hm' hm1' hmins' hminsK' hmn' hmnK' hwdE).2 hq).2 t' ht']
    exact one_mem_univ_zero
  refine ⟨hfit, ?_, ?_, ?_⟩
  · rw [hrev, e]
    have := appList_mem_of_piCtx _ _ hf hfit
    rwa [read_rec1Body S _ _ N hminsK hmins] at this
  · rw [hrev, e]
    exact spineOk_of_piCtx _ _ hf hfit hG
  · intro hq
    rw [hrev, rec1Set_eq hs m hok φ ρ hus, hq, appList_lamCtx_false hfit,
      rec1F_read S m.M _ N _ hminsK hmins hps]

/-! ## The major: the block's constructor applied -/

/-- **The block's constructor's set applied to fitting values** is the
constructor value at the fields, and the values fit semantically. -/
theorem ctor_appN (φ : Name → Nat) (ρ : Nat → V) {usj : List Level}
    (husj : usj.length = S.lparams.length) {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c)
    {ps fs : List V} (hps : ps.length = S.nP) (hf : fs.length = c.fields.length)
    (hfit : TeleFitV (S.M₃N m.M N) (Level.substVal φ S.lparams usj) ρ (S.ctorType c)
      (ps.reverse ++ fs.reverse)) :
    FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.lparams usj))) base S.params ps ∧
    S.FitsFields m.M (S.lparams.map (Level.substVal φ S.lparams usj)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.lparams usj)) ps) ps c.fields fs ∧
    appList (S.M₃N m.M N c.name (usj.map (Level.eval φ))) (ps.reverse ++ fs.reverse)
      = S.ctorVal (S.lparams.map (Level.substVal φ S.lparams usj)) j fs := by
  have hS := hok.scoped
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have R₃ := reader₃N m hok (Level.substVal φ S.lparams usj)
  unfold ctorType at hfit
  rw [← List.reverse_append, TeleFitV_mkPis _ _ _ (by simp [hf, hps, length_fieldCtx, nP, Nat.add_comm]),
    List.reverse_reverse, FitsVals_append _ _ (by rw [hf, length_fieldCtx])] at hfit
  obtain ⟨hpF, hfF⟩ := hfit
  have hp := (R₃.R.fits_params hS).mp hpF
  have hidx := R₃.R.idxFit_of_wd hS hcm (wd_ctorTypeN hs m hok hcm _ ρ) hps hp
  have hff := (R₃.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp hidx.1).1.mp hfF
  refine ⟨hp, hff, ?_⟩
  rw [R₃.ctor j c hc, ← lparams_map_substValN hok φ husj]
  have R₁ := S.reader₁ (M := m.M) (φ := Level.substVal φ S.lparams usj) hok.freshI

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

/-! ## The rules' contexts -/

omit [LevelOracle] hs hok in
/-- Any list fitting a rule's context splits as the fields, the class's
minors, the block's minors, the two motives and the parameters. -/
theorem fits_ruleCtxN_split (φr : Name → Nat) {ρ : Nat → V} {c : CtorSpec} {vs : List V}
    (h : FitsVals (S.M₃N m.M N) φr ρ (S.ruleCtxN N c) vs) :
    ∃ (fs minsK mins : List V) (m1 m' : V) (ps : List V),
      vs = fs ++ minsK ++ mins ++ [m1, m'] ++ ps ∧ fs.length = c.fields.length ∧
        minsK.length = N.nK ∧ mins.length = S.n ∧ ps.length = S.nP := by
  have hl := FitsVals_length _ _ h
  rw [length_ruleCtxN] at hl
  simp only [oN] at hl
  obtain ⟨fs, r₁, rfl, hf⟩ := exists_split (l := vs) (a := c.fields.length) (by omega)
  obtain ⟨minsK, r₂, rfl, hminsK⟩ := exists_split (l := r₁) (a := N.nK) (by simp at hl; omega)
  obtain ⟨mins, r₃, rfl, hmins⟩ := exists_split (l := r₂) (a := S.n) (by simp at hl; omega)
  obtain ⟨m1, m', ps, rfl⟩ : ∃ m1 m' ps, r₃ = m1 :: m' :: ps := by
    match r₃, (by simp at hl; omega : 2 ≤ r₃.length) with
    | m1 :: m' :: ps, _ => exact ⟨m1, m', ps, rfl⟩
  refine ⟨fs, minsK, mins, m1, m', ps, by simp, hf, hminsK, hmins, ?_⟩
  simp at hl; omega

omit hs in
/-- **Values fitting a rule's context, for any scoped constructor whose
field context is well-denoted at the parameters**: the parameters fit,
the extras fit, and the fields fit the constructor's fields
semantically — and conversely. -/
theorem fits_ruleCtxN' (φr : Name → Nat) (ρ : Nat → V) {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {fs minsK mins : List V} {m1 m' : V} {ps : List V}
    (hf : fs.length = c.fields.length) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP)
    (hwdF : FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps →
      CtxWD (S.M₃N m.M N) φr (consList ps ρ) (S.fieldCtx c.fields)) :
    FitsVals (S.M₃N m.M N) φr ρ (S.ruleCtxN N c) (fs ++ minsK ++ mins ++ [m1, m'] ++ ps) ↔
      FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps ∧
      m' ∈ˢ interp (S.M₃N m.M N) φr (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp (S.M₃N m.M N) φr (cons m' (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals (S.M₃N m.M N) φr (consList [m1, m'] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals (S.M₃N m.M N) φr (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK ∧
      S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps c.fields fs := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok φr
  have hosl : (minsK ++ mins ++ [m1, m']).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have e1 : fs ++ minsK ++ mins ++ [m1, m'] ++ ps = fs ++ (minsK ++ mins ++ [m1, m']) ++ ps := by simp
  unfold ruleCtxN
  rw [e1, FitsVals_append _ _ (by rw [List.length_append, hf, hosl, List.length_append,
      length_fieldCtxAt, length_extrasN]),
    FitsVals_append _ _ (by simp [hf, length_fieldCtxAt]), R₃.R.fits_params hS,
    fits_extrasN_iff' m φr ρ hminsK hmins]
  unfold fieldCtxAt
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hosl]
  constructor
  · rintro ⟨hp, ⟨hm, hm1, hmn, hmnK⟩, hfF⟩
    exact ⟨hp, hm, hm1, hmn, hmnK, (R₃.R.fits_fieldCtx hS hsc hps hp (hwdF hp)).1.mp hfF⟩
  · rintro ⟨hp, hm, hm1, hmn, hmnK, hfF⟩
    exact ⟨hp, ⟨hm, hm1, hmn, hmnK⟩, (R₃.R.fits_fieldCtx hS hsc hps hp (hwdF hp)).1.mpr hfF⟩

/-- The rule's context of a block constructor. -/
theorem fits_ruleCtxN (φr : Name → Nat) (ρ : Nat → V) {c : CtorSpec} (hcm : c ∈ S.ctors)
    {fs minsK mins : List V} {m1 m' : V} {ps : List V}
    (hf : fs.length = c.fields.length) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP) :
    FitsVals (S.M₃N m.M N) φr ρ (S.ruleCtxN N c) (fs ++ minsK ++ mins ++ [m1, m'] ++ ps) ↔
      FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps ∧
      m' ∈ˢ interp (S.M₃N m.M N) φr (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp (S.M₃N m.M N) φr (cons m' (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals (S.M₃N m.M N) φr (consList [m1, m'] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals (S.M₃N m.M N) φr (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK ∧
      S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps c.fields fs :=
  fits_ruleCtxN' m hok φr ρ (hok.scoped.2.2.2.1 c hcm).1 hf hminsK hmins hps
    fun hp => wdFieldCtxN hs m hok φr ρ c hcm ps hps hp

omit hs in
/-- The rule's context of a translated constructor: the field context
is well-denoted once the extras fit (`wdFieldCtxK`). -/
theorem fits_ruleCtxK (φr : Name → Nat) (ρ : Nat → V)
    (hwdE : ∀ ps', FitsVals (S.M₃N m.M N) φr ρ S.params ps' →
      CtxWD (S.M₃N m.M N) φr (consList ps' ρ) (S.extrasN N))
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c)
    {fs minsK mins : List V} {m1 m' : V} {ps : List V}
    (hf : fs.length = (S.classCtor N c).fields.length) (hminsK : minsK.length = N.nK)
    (hmins : mins.length = S.n) (hps : ps.length = S.nP) :
    FitsVals (S.M₃N m.M N) φr ρ (S.ruleCtxN N (S.classCtor N c)) (fs ++ minsK ++ mins ++ [m1, m'] ++ ps) ↔
      FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps ∧
      m' ∈ˢ interp (S.M₃N m.M N) φr (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp (S.M₃N m.M N) φr (cons m' (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals (S.M₃N m.M N) φr (consList [m1, m'] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals (S.M₃N m.M N) φr (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK ∧
      S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps (S.classCtor N c).fields fs := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok φr
  have hsc := S.classCtor_fieldScoped N hS hok.nest (K_law m hok).1 (List.mem_of_getElem? hc)
  have hosl : (minsK ++ mins ++ [m1, m']).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have e1 : fs ++ minsK ++ mins ++ [m1, m'] ++ ps = fs ++ (minsK ++ mins ++ [m1, m']) ++ ps := by simp
  unfold ruleCtxN
  rw [e1, FitsVals_append _ _ (by rw [List.length_append, hf, hosl, List.length_append,
      length_fieldCtxAt, length_extrasN]),
    FitsVals_append _ _ (by simp [hf, length_fieldCtxAt]), R₃.R.fits_params hS,
    fits_extrasN_iff' m φr ρ hminsK hmins]
  unfold fieldCtxAt
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hosl]
  constructor
  · rintro ⟨hp, ⟨hm, hm1, hmn, hmnK⟩, hfF⟩
    have hwdF := wdFieldCtxK (hwdE ps ((R₃.R.fits_params hS).mpr hp)) hmins hminsK hm hm1 hmn hmnK j c hc
    exact ⟨hp, hm, hm1, hmn, hmnK, (R₃.R.fits_fieldCtx hS hsc hps hp hwdF).1.mp hfF⟩
  · rintro ⟨hp, hm, hm1, hmn, hmnK, hfF⟩
    have hwdF := wdFieldCtxK (hwdE ps ((R₃.R.fits_params hS).mpr hp)) hmins hminsK hm hm1 hmn hmnK j c hc
    exact ⟨hp, ⟨hm, hm1, hmn, hmnK⟩, (R₃.R.fits_fieldCtx hS hsc hps hp hwdF).1.mpr hfF⟩

/-! ## The inductive hypotheses' terms -/

omit hs in
/-- A field's domain is well-denoted at fitting earlier fields, for any
scoped constructor whose field context is well-denoted. -/
theorem wd_fieldDomN (φr : Name → Nat) (ρ : Nat → V) {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {ps fs : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps)
    (hwdF : CtxWD (S.M₃N m.M N) φr (consList ps ρ) (S.fieldCtx c.fields))
    (hfit : S.FitsFields m.M (S.lparams.map φr) (S.Fam m.M (S.lparams.map φr) ps) ps c.fields fs)
    {k : Nat} {f : Field} (hkf : c.fields[c.fields.length - 1 - k]? = some f)
    (hk : k < c.fields.length) :
    WellDenoted (S.M₃N m.M N) φr (consList (earlier fs k) (consList ps ρ)) (S.fieldDom k f) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok φr
  have hf := S.FitsFields_length m.M _ hfit
  have hfF := (R₃.R.fits_fieldCtx hS hsc hps hp hwdF).1.mpr hfit
  have hA : (S.fieldCtx c.fields)[c.fields.length - 1 - k]? = some (S.fieldDom k f) := by
    rw [fieldCtx_getElem?, hkf]
    simp only [Option.map_some, Option.some.injEq]
    congr 1
    omega
  have hdrop := FitsVals_drop (S.M₃N m.M N) φr (c.fields.length - k) hfF
  rw [show c.fields.length - k = c.fields.length - 1 - k + 1 by omega] at hdrop
  have := CtxWD_getElem? (S.M₃N m.M N) φr hwdF hA _ hdrop
  rwa [show fs.drop (c.fields.length - 1 - k + 1) = earlier fs k by
    unfold earlier; rw [hf]; congr 1; omega] at this

/-- **A `T.rec` call in a rule of a nested block**, at the parameters,
all the extras, index expressions `es` lifted into the rule's frame and
a last argument denoting `t`: well-denoted; a member of the motive at
the index values and `t`; and, in the graph regime, the semantic
recursor at `t` (`rec_app_memN`). -/
theorem recCall_okN (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {c : CtorSpec}
    {k mt : Nat} (hk : k ≤ c.fields.length) {es : List Expr}
    (hsc : ∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k + mt) e)
    {ys fs minsK mins : List V} {m1 m' : V} {ps : List V} (hy : ys.length = mt)
    (hf : fs.length = c.fields.length) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      (S.motiveTy1 N))
    (hmn : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1, m'] (consList ps ρ))
      S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    {last : Expr} {t : V}
    (hlast : interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))) last = t)
    (hwdl : WellDenoted (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))) last)
    (hwdes : ∀ e ∈ es, WellDenoted (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList (earlier fs k) (consList ps ρ))) e)
    (his : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps)
      S.indices (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
        (consList ys (consList (earlier fs k) (envP ps))) es))
    (ht : t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps
      (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
        (consList ys (consList (earlier fs k) (envP ps))) es)) :
    WellDenoted (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
      (Expr.mkAppN (.const S.recName S.recLvls)
        (Expr.varsAt (mt + c.fields.length + S.oN N) S.nP ++ Expr.varsAt (mt + c.fields.length) (S.oN N) ++
          es.map (Expr.atCtx c.fields.length k 0 (S.oN N) mt) ++ [last])) ∧
    appList (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        (mt + c.fields.length + S.oN N - 1))
      ((es.map fun e => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
        (Expr.atCtx c.fields.length k 0 (S.oN N) mt e)) ++
        [interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))) last])
      = appList m' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t]) ∧
    interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
      (Expr.mkAppN (.const S.recName S.recLvls)
        (Expr.varsAt (mt + c.fields.length + S.oN N) S.nP ++ Expr.varsAt (mt + c.fields.length) (S.oN N) ++
          es.map (Expr.atCtx c.fields.length k 0 (S.oN N) mt) ++ [last]))
      ∈ˢ appList m' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t]) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
        (Expr.mkAppN (.const S.recName S.recLvls)
          (Expr.varsAt (mt + c.fields.length + S.oN N) S.nP ++ Expr.varsAt (mt + c.fields.length) (S.oN N) ++
            es.map (Expr.atCtx c.fields.length k 0 (S.oN N) mt) ++ [last]))
        = S.recSemN m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N false ps
            ⟨m', m1, mins, minsK⟩
            (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
              (consList ys (consList (earlier fs k) (envP ps))) es) t) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have hosl : (minsK ++ mins ++ [m1, m']).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  -- the head
  have hhead : interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
      (.const S.recName S.recLvls) = S.M₃N m.M N S.recName (us.map (Level.eval φ)) := by
    rw [interp_const, recLvls_map_eval hS φ hus]
  -- the motive's slot, the parameter and extras slots
  have hmot : consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
      (mt + c.fields.length + S.oN N - 1) = m' := by
    rw [show consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        = consList (ys ++ fs ++ minsK ++ mins) (consList [m1, m'] (consList ps ρ)) by
        simp [consList_append],
      show mt + c.fields.length + S.oN N - 1 = 1 + (ys ++ fs ++ minsK ++ mins).length by
        simp [hy, hf, hminsK, hmins, oN]; omega,
      consList_ge]
    rfl
  have hparams : readEnv S.nP (shiftE (mt + c.fields.length + S.oN N) 0
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))) = ps := by
    rw [show consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        = consList (ys ++ fs ++ (minsK ++ mins ++ [m1, m'])) (consList ps ρ) by simp [consList_append],
      shiftE_consList' (by rw [List.length_append, List.length_append, hy, hf, hosl]),
      readEnv_consList hps]
  have hextras : readEnv (S.oN N) (shiftE (mt + c.fields.length) 0
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))))
      = minsK ++ mins ++ [m1, m'] := by
    rw [show consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        = consList (ys ++ fs) (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)) by simp [consList_append],
      shiftE_consList' (by simp [hy, hf]), readEnv_consList hosl]
  -- the index expressions
  have hes : es.map (fun e => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
      (Expr.atCtx c.fields.length k 0 (S.oN N) mt e))
      = (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse := by
    unfold idxVals
    rw [List.reverse_reverse]
    apply List.map_congr_left
    intro e he
    have h1 := interp_atCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ e (ys := ys) (ihs := [])
      (l := 0) (fs := fs) (os := minsK ++ mins ++ [m1, m']) (ps := ps) hy rfl hf hosl hk
    simp only [consList_nil] at h1
    rw [h1, hkd, ← consList_append ys (earlier fs k) (consList ps ρ),
      ← consList_append ys (earlier fs k) (envP ps)]
    refine R₃.R.read (hsc e he) ?_
    simp only [List.length_append, hy, earlier, List.length_drop, hf, hps]
    omega
  have hargs : (Expr.varsAt (mt + c.fields.length + S.oN N) S.nP ++
        Expr.varsAt (mt + c.fields.length) (S.oN N) ++
        es.map (Expr.atCtx c.fields.length k 0 (S.oN N) mt) ++ [last]).map
        (interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))))
      = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++
        (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList ys (consList (earlier fs k) (envP ps))) es).reverse ++ [t] := by
    simp only [List.map_append, List.map_singleton, List.map_map, interp_varsAt]
    rw [hparams, hextras, hlast, ← hes]
    simp [List.reverse_append]
  have key := rec_app_memN hs m hok φ ρ hus hps hp hm hm1 hmins hminsK hmn hmnK his ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
    · intro a ha
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with (((ha | ha) | ⟨e, he, rfl⟩) | rfl)
      · exact Expr.wd_of_mem_varsAt ha
      · exact Expr.wd_of_mem_varsAt ha
      · have h := WellDenoted_atCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ e (ys := ys)
          (ihs := []) (l := 0) (fs := fs) (os := minsK ++ mins ++ [m1, m']) (ps := ps) hy rfl hf hosl hk
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

/-- **A `T.rec_1` call in a rule of a nested block** at a container
field: well-denoted; a member of the class's motive at the field; and,
in the graph regime, the semantic auxiliary recursor at the field
(`rec1_app_mem`). -/
theorem rec1Call_ok (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {nF k : Nat}
    {fs minsK mins : List V} {m1 m' : V} {ps : List V}
    (hf : fs.length = nF) (hk : k < nF) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      (S.motiveTy1 N))
    (hmn : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1, m'] (consList ps ρ))
      S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    (ht : fieldVal fs k ∈ˢ S.classAt m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N ps) :
    WellDenoted (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
      (Expr.mkAppN (.const N.aux S.recLvls)
        (Expr.varsAt (nF + S.oN N) S.nP ++ Expr.varsAt nF (S.oN N) ++ [.bvar (nF - 1 - k)])) ∧
    interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
      (Expr.mkAppN (.const N.aux S.recLvls)
        (Expr.varsAt (nF + S.oN N) S.nP ++ Expr.varsAt nF (S.oN N) ++ [.bvar (nF - 1 - k)]))
      ∈ˢ appList m1 [fieldVal fs k] ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        (Expr.mkAppN (.const N.aux S.recLvls)
          (Expr.varsAt (nF + S.oN N) S.nP ++ Expr.varsAt nF (S.oN N) ++ [.bvar (nF - 1 - k)]))
        = S.rec1Sem m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N false ps
            ⟨m', m1, mins, minsK⟩ (fieldVal fs k)) := by
  have hS := hok.scoped
  have hosl : (minsK ++ mins ++ [m1, m']).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have hhead : interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
      (.const N.aux S.recLvls) = S.M₃N m.M N N.aux (us.map (Level.eval φ)) := by
    rw [interp_const, recLvls_map_eval hS φ hus]
  have hfv : consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)) (nF - 1 - k)
      = fieldVal fs k := by
    rw [consList_getD (by omega)]
    unfold fieldVal
    rw [hf]
  have hparams : readEnv S.nP (shiftE (nF + S.oN N) 0
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))) = ps := by
    rw [← consList_append, shiftE_consList' (by rw [List.length_append, hf, hosl]), readEnv_consList hps]
  have hextras : readEnv (S.oN N) (shiftE nF 0
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))) = minsK ++ mins ++ [m1, m'] := by
    rw [shiftE_consList' hf, readEnv_consList hosl]
  have hargs : (Expr.varsAt (nF + S.oN N) S.nP ++ Expr.varsAt nF (S.oN N) ++ [Expr.bvar (nF - 1 - k)]).map
        (interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
      = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ [fieldVal fs k] := by
    simp only [List.map_append, List.map_singleton, interp_varsAt, interp_bvar]
    rw [hparams, hextras, hfv]
    simp [List.reverse_append]
  have key := rec1_app_mem hs m hok φ ρ hus hps hp hm hm1 hmins hminsK hmn hmnK ht
  refine ⟨?_, ?_, ?_⟩
  · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
    · intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ((ha | ha) | rfl)
      · exact Expr.wd_of_mem_varsAt ha
      · exact Expr.wd_of_mem_varsAt ha
      · simp
    · rw [hhead, hargs]
      exact key.2.2.1
  · rw [interp_mkAppN_appList, hhead, hargs]
    exact key.2.1
  · intro hq
    rw [interp_mkAppN_appList, hhead, hargs]
    exact key.2.2.2 hq

/-- **An inductive hypothesis' term in a rule of a nested block, read**
(for any scoped constructor whose field context is well-denoted):
well-denoted, a member of the hypothesis' set (`IhTypedN`), and in the
graph regime the semantic inductive hypothesis — a `T.rec` call at a
reflexive field (through its telescope), a `T.rec_1` call at a
container field. -/
theorem ihValN_ok (φ : Name → Nat) (ρ : Nat → V) {us : List Level}
    (hus : us.length = S.recLparams.length) {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {kf : Nat × Field} (hkf : kf ∈ c.recFields)
    {fs minsK mins : List V} {m1 m' : V} {ps : List V}
    (hf : fs.length = c.fields.length) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps)
    (hm : m' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) S.motiveTy)
    (hm1 : m1 ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m' (consList ps ρ))
      (S.motiveTy1 N))
    (hmn : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1, m'] (consList ps ρ))
      S.minorsCtxN mins)
    (hmnK : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList (mins ++ [m1, m']) (consList ps ρ)) (S.minorsCtxK N) minsK)
    (hwdF : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps ρ) (S.fieldCtx c.fields))
    (hfit : S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps) ps c.fields fs) :
    WellDenoted (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
      (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
      (S.ihValN N c.fields.length kf.1 kf.2) ∧
    S.IhTypedN m.M (S.lparams.map (Level.substVal φ S.recLparams us))
      (S.q.holds (Level.substVal φ S.recLparams us)) ps ⟨m', m1, mins, minsK⟩ fs kf
      (interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        (S.ihValN N c.fields.length kf.1 kf.2)) ∧
    (S.q.holds (Level.substVal φ S.recLparams us) = false →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        (S.ihValN N c.fields.length kf.1 kf.2)
      = S.ihSemN m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N false ps
          ⟨m', m1, mins, minsK⟩ fs kf) := by
  have hS := hok.scoped
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  obtain ⟨k, f⟩ := kf
  obtain ⟨hkf', hk, hrec⟩ := mem_recFields hkf
  dsimp only at hkf' hk hrec ⊢
  have hosl : (minsK ++ mins ++ [m1, m']).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  have hsc' := hsc _ f hkf'
  rw [show c.fields.length - 1 - (c.fields.length - 1 - k) = k by omega] at hsc'
  have hget := S.FitsFields_get m.M _ hfit hkf' hk
  have hwdD := wd_fieldDomN m hok _ ρ hsc hps hp hwdF hfit hkf' hk
  have hidx := (R₃.R.fits_fieldCtx hS hsc hps hp hwdF).2 hfit
  have hfv : consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)) (c.fields.length - 1 - k)
      = fieldVal fs k := by
    rw [consList_getD (by omega)]
    unfold fieldVal
    rw [hf]
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    have ht : fieldVal fs k ∈ˢ S.classAt m.M (S.lparams.map (Level.substVal φ S.recLparams us)) N ps := by
      rw [S.fieldSet_container_Fam m.M _ N hok.nest] at hget
      exact hget
    have h := rec1Call_ok hs m hok φ ρ hus hf hk hminsK hmins hps hp hm hm1 hmn hmnK ht
    exact ⟨h.1, h.2.1, h.2.2⟩
  | reflexive tele es =>
    simp only [fieldDom] at hwdD
    rw [WellDenoted_mkPis] at hwdD
    obtain ⟨hwdT, hwdB⟩ := hwdD
    simp only [fieldSet] at hget
    have hagree := R₃.R.agree_tele hsc'.1 (vs := earlier fs k) (ps := ps) (ρ := ρ)
      (by simp [earlier, hf]; omega) hps
    have hfitT : ∀ ys, FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
        (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)))
        (Expr.liftCtx (fun t T => Expr.atCtx c.fields.length k 0 (S.oN N) t T) tele) ys ↔
        FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us)))
          (consList (earlier fs k) (envP ps)) tele ys := by
      intro ys
      have h := FitsVals_liftCtx_atCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ tele ys
        (ihs := []) (l := 0) (fs := fs) (os := minsK ++ mins ++ [m1, m']) (ps := ps) rfl hf hosl
        (Nat.le_of_lt hk)
      simp only [consList_nil] at h
      rw [h, hkd]
      exact FitsVals_congr₂ hagree
    have hcall := fun ys (hys : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us)))
        (consList (earlier fs k) (envP ps)) tele ys) =>
        have hlen := FitsVals_length m.M _ hys
        have hys' : FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
            (consList (earlier fs k) (consList ps ρ)) tele ys := (FitsVals_congr₂ hagree).mpr hys
        have hmem := appList_mem_of_piCtx m.M _ hget hys
        have hspine := spineOk_of_piCtx m.M _ hget hys fun hz _ _ =>
          S.fibre_mem_univ_zero _ (S.Fam_inUniv m.M _ ps) hz _
        have hlastV : interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
            (consList ys (consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ))))
            (Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k)) (Expr.varsAt 0 tele.length))
            = appList (fieldVal fs k) ys.reverse := by
          rw [interp_mkAppN_appList, interp_bvar, interp_varsAt, shiftE_zero_zero,
            readEnv_consList hlen,
            show tele.length + c.fields.length - 1 - k = (c.fields.length - 1 - k) + ys.length by
              rw [hlen]; omega,
            consList_ge, hfv]
        recCall_okN hs m hok φ ρ hus (c := c) (mt := tele.length) (Nat.le_of_lt hk) (es := es)
          (fun e he => hsc'.2.2 e he) (ys := ys) hlen hf hminsK hmins hps hp hm hm1 hmn hmnK
          (last := Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k))
            (Expr.varsAt 0 tele.length))
          (t := appList (fieldVal fs k) ys.reverse) hlastV
          (WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) (fun a ha => Expr.wd_of_mem_varsAt ha)
            (by rw [interp_bvar, interp_varsAt, shiftE_zero_zero, readEnv_consList hlen,
              show tele.length + c.fields.length - 1 - k = (c.fields.length - 1 - k) + ys.length by
                rw [hlen]; omega,
              consList_ge, hfv]; exact hspine))
          (fun e he => (WellDenoted_mkAppN' _ _ (hwdB ys hys').1).2 e (List.mem_append_right _ he))
          (hidx k _ hkf' hk ys hys) hmem
    have hl := R₃.R.lamCtx_liftCtx_atCtx (ihsE := []) (l := 0) (fs := fs) (os := minsK ++ mins ++ [m1, m'])
      (ps := ps) (ρ := ρ) rfl hf hosl (Nat.le_of_lt hk) hps (S.q.holds (Level.substVal φ S.recLparams us))
      tele hsc'.1
    simp only [consList_nil] at hl
    have hmot : ∀ is, FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps)
        S.indices is → ∀ t, t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps is →
        appList m' (is.reverse ++ [t]) ∈ˢ (univ (Level.eval (Level.substVal φ S.recLparams us) S.ℓ) : V) :=
      R₃.R.motiveOk_of_mem hS hps hp hm
    refine ⟨?_, ?_, ?_⟩
    · -- the invariant
      simp only [ihValN]
      refine WellDenoted_mkLams_sem _ _ ?_ ?_ ?_
        (G := fun ρ₁ => appList (ρ₁ (tele.length + c.fields.length + S.oN N - 1))
          ((es.map fun e => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ₁
            (Expr.atCtx c.fields.length k 0 (S.oN N) tele.length e)) ++
            [interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ₁
              (Expr.mkAppN (.bvar (tele.length + c.fields.length - 1 - k))
                (Expr.varsAt 0 tele.length))]))
      · have h := CtxWD_liftCtx_atCtx (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ
          (ihs := []) (l := 0) (fs := fs) (os := minsK ++ mins ++ [m1, m']) (ps := ps) rfl hf hosl
          (Nat.le_of_lt hk) tele
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
        exact hmot _ (hidx k _ hkf' hk ys ((hfitT ys).mp hys)) _
          (appList_mem_of_piCtx m.M _ hget ((hfitT ys).mp hys))
    · -- the hypothesis' set
      dsimp only [IhTypedN, ihValN]
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
        exact hmot _ (hidx k _ hkf' hk ys hys) _ (appList_mem_of_piCtx m.M _ hget hys)
    · -- the graph regime
      intro hq
      dsimp only [ihSemN, ihValN]
      rw [interp_mkLams, hl, hkd, hq]
      refine lamCtx_congr m.M _ fun ys hys => ?_
      have hlen := FitsVals_length m.M _ hys
      rw [readEnv_consList hlen]
      exact (hcall ys hys).2.2.2 hq

/-! ## The ι law of `T.rec`'s rules -/

/-- **The ι law of a `T.rec` rule** (`RecRuleLaw`, `EnvModel.lean`) for
the recursor's constant and the block's constructor's, at `nP`
parameters, `nP + 2 + (n + nK)` arguments before the indices and the
major at `nP + 2 + (n + nK) + nI`. -/
theorem rec_rule_lawN {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) :
    RecRuleLaw (S.M₃N m.M N) S.recName (S.recInfoN N) S.nP (S.nP + 2 + (S.n + N.nK))
      (S.nP + 2 + (S.n + N.nK) + S.nI) ⟨c.name, c.fields.length, S.ruleRhsN N c j, none⟩
      (S.ctorInfo c) := by
  intro φ ρ us usj xs ys hus husj hxs hys hfitR hfitC hlv hpar hidx
  have hS := hok.scoped
  have hN := hok.nest
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
  simp only [recInfoN, ctorInfo] at hus husj hfitR hfitC hlv hidx ⊢
  rw [TeleFitV_instL] at hfitR hfitC
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have hLj : S.lparams.map (Level.substVal φ S.lparams usj)
      = S.lparams.map (Level.substVal φ S.recLparams us) :=
    block_valuation_eq hS φ hus husj hlv
  -- the recursor's spine, split
  have hfitR' := hfitR
  rw [recTypeN_eq, TeleFitV_mkPis _ _ _ (by
      simp only [List.length_append, List.length_singleton, hxs, length_recCtxN, oN]; omega),
    List.reverse_append, List.reverse_singleton, List.singleton_append] at hfitR'
  obtain ⟨t, is, minsK, mins, m1, m', ps, heq, hi, hminsK, hmins, hps⟩ := fits_recCtxN_split S N hfitR'
  obtain ⟨rfl, hxs'⟩ := List.cons.inj heq
  rw [hxs'] at hfitR'
  have hxs'' : xs = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse := by
    rw [← List.reverse_reverse xs, hxs']
    simp [List.reverse_append]
  subst hxs''
  obtain ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩ :=
    (Reader.fits_recCtxN_iff S N hS R₃.R hi hminsK hmins hps).mp hfitR'
  -- the constructor's spine, split
  obtain ⟨ps₂, fs, hys₂, hps₂, hf⟩ : ∃ ps₂ fs, ys = ps₂.reverse ++ fs.reverse ∧
      ps₂.length = S.nP ∧ fs.length = c.fields.length :=
    ⟨(ys.take S.nP).reverse, (ys.drop S.nP).reverse, by simp,
      by rw [List.length_reverse, List.length_take, hys]; omega,
      by rw [List.length_reverse, List.length_drop, hys, Nat.add_sub_cancel_left]⟩
  subst hys₂
  have htake₁ : (ps₂.reverse ++ fs.reverse).take S.nP = ps₂.reverse := by
    rw [List.take_append_of_le_length (by simp [hps₂]), List.take_of_length_le (by simp [hps₂])]
  have htake₂ : (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ is.reverse).take S.nP
      = ps.reverse := by
    rw [List.take_append_of_le_length (by simp [hps]),
      List.take_append_of_le_length (by simp [hps]),
      List.take_append_of_le_length (by simp [hps]),
      List.take_append_of_le_length (by simp [hps]), List.take_of_length_le (by simp [hps])]
  rw [htake₁, htake₂, List.reverse_inj] at hpar
  subst ps₂
  -- the major is the constructor value at the fields
  obtain ⟨-, hfitF, hmajor⟩ := ctor_appN hs m hok φ ρ husj hc hps hf hfitC
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
    rw [List.drop_left' (by simp [hps, hmins, hminsK]; omega)] at hB
    have hlen : ((c.idx.map (·.instL S.lparams usj)).map (interp (S.M₃N m.M N) φ (consList (fs ++ ps) ρ))).length
        = is.reverse.length := by
      simp [hi, (hS.2.2.2.1 c hcm).2.2.1]
    have := List.map_eq_of_zip id hlen hB
    simp only [List.map_id, List.map_map, Function.comp_def, id_eq, interp_instL, consList_append] at this
    rw [← List.reverse_reverse is, ← this,
      (reader₃N m hok (Level.substVal φ S.lparams usj)).R.idxVals_eq
        (hS.2.2.2.1 c hcm).2.2.2 (by simp [hf, hps]; omega), hLj]
  subst hisv
  rw [hmajor] at ht ⊢
  -- the left-hand side: the semantic recursor at the constructor value
  have key := rec_app_memN hs m hok φ ρ hus hps hp hm hm1 hmins hminsK hmn hmnK his ht
  -- the right-hand side's context and spine
  have hfitRule := (fits_ruleCtxN hs m hok _ ρ hcm hf hminsK hmins hps).mpr
    ⟨hp, hm, hm1, hmn, hmnK, hfitF⟩
  have hspineR : (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++
        (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (consList fs (envP ps)) c.idx).reverse).take (S.nP + 2 + (S.n + N.nK)) ++
        (ps.reverse ++ fs.reverse).drop S.nP
      = (fs ++ minsK ++ mins ++ [m1, m'] ++ ps).reverse := by
    rw [List.take_left' (by simp [hps, hmins, hminsK]; omega), List.drop_left' (by simp [hps])]
    simp [List.reverse_append]
  have henv : consList (fs ++ minsK ++ mins ++ [m1, m'] ++ ps) ρ
      = consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)) := by
    simp [consList_append]
  -- the minor's slot in a rule's environment
  have hminor : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = c.fields.length → minsK'.length = N.nK → mins'.length = S.n →
      consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ))
          (c.fields.length + N.nK + S.n - 1 - j)
        = S.minorAt mins' j := by
    intro fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins'
    rw [show c.fields.length + N.nK + S.n - 1 - j = ((S.n - 1 - j) + minsK'.length) + fs'.length by
        rw [hf', hminsK']; omega,
      consList_ge, consList_append, consList_append, consList_ge, consList_getD (by omega)]
    rfl
  -- the rule's body, read at fitting values
  have hbody : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = c.fields.length → minsK'.length = N.nK → mins'.length = S.n →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
          (Expr.mkAppN (.bvar (c.fields.length + N.nK + S.n - 1 - j))
            (Expr.varsAt 0 c.fields.length ++
              c.recFields.map fun kf => S.ihValN N c.fields.length kf.1 kf.2))
        = appList (S.minorAt mins' j) (fs'.reverse ++ c.recFields.map fun kf =>
            interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
              (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
              (S.ihValN N c.fields.length kf.1 kf.2)) := by
    intro fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins'
    rw [interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map, interp_varsAt,
      shiftE_zero_zero, readEnv_consList hf', hminor fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins']
    rfl
  -- the rule's type, read: the motive at the constructor's index values and value
  have hty : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = c.fields.length → minsK'.length = N.nK → mins'.length = S.n → ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps') ps' c.fields fs' →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ))) (S.ruleBodyTyN N c)
        = appList m'' ((S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us))
            (consList fs' (envP ps')) c.idx).reverse ++
            [S.ctorVal (S.lparams.map (Level.substVal φ S.recLparams us)) j fs']) := by
    intro fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins' hps' hp' hfitF'
    have hidx' := (R₃.R.idxFit_of_wd hS hcm (wd_ctorTypeN hs m hok hcm _ ρ) hps' hp').2 fs' hfitF'
    have hos : (minsK' ++ mins' ++ [m1', m'']).length = S.oN N := by
      simp only [List.length_append, List.length_cons, List.length_nil, hminsK', hmins', oN]; omega
    have h := R₃.read_concl hS hok.freshI hc (ihsE := []) (nIh := 0) (o := S.oN N)
      (os := minsK' ++ mins' ++ [m1', m'']) (ρ := ρ) rfl hf' hos (by unfold oN; omega) hps' hp' hfitF'
      hidx'.2.1
    have hg : (minsK' ++ mins' ++ [m1', m'']).getD (S.oN N - 1) pt = m'' := by
      rw [show S.oN N - 1 = (minsK' ++ mins').length + 1 by
        simp only [List.length_append, hminsK', hmins', oN]; omega]
      exact (getD_append_two _ _).2
    rw [consList_nil, show 0 + c.fields.length + S.oN N - 1 = c.fields.length + S.oN N - 1 by omega,
      show 0 + c.fields.length + S.oN N = c.fields.length + S.oN N by omega, hg] at h
    exact h
  -- the rule's right-hand side is well-denoted and in the rule's type
  have hT := wd_ruleTypeN hs m hok hcm (Level.substVal φ S.recLparams us) ρ
  unfold ruleTypeN at hT
  have hres : ∀ ps', ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      ∀ c' ∈ S.ctors, ∀ fs', S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps') ps' c'.fields fs' →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) (envP ps') S.indices
        (S.idxVals m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (consList fs' (envP ps')) c'.idx) :=
    fun ps' hps' hp' c' hc' fs' hfit' =>
      ((R₃.R.idxFit_of_wd hS hc' (wd_ctorTypeN hs m hok hc' _ ρ) hps' hp').2 fs' hfit').2.2
  have hrhs := mkLams_ok _ _ hT (b := Expr.mkAppN (.bvar (c.fields.length + N.nK + S.n - 1 - j))
      (Expr.varsAt 0 c.fields.length ++ c.recFields.map fun kf => S.ihValN N c.fields.length kf.1 kf.2))
    fun vs hvs => by
      obtain ⟨fs', minsK', mins', m1', m'', ps', rfl, hf', hminsK', hmins', hps'⟩ :=
        fits_ruleCtxN_split m _ hvs
      obtain ⟨hp', hm', hm1', hmn', hmnK', hfitF'⟩ :=
        (fits_ruleCtxN hs m hok _ ρ hcm hf' hminsK' hmins' hps').mp hvs
      rw [show consList (fs' ++ minsK' ++ mins' ++ [m1', m''] ++ ps') ρ
          = consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)) by
          simp [consList_append]]
      have hwdF' := wdFieldCtxN hs m hok _ ρ c hcm ps' hps' hp'
      have hih := fun kf (hkf : kf ∈ c.recFields) =>
        ihValN_ok hs m hok φ ρ hus (hS.2.2.2.1 c hcm).1 hkf hf' hminsK' hmins' hps' hp' hm' hm1'
          hmn' hmnK' hwdF' hfitF'
      have hmin := Reader₂.minorOkN_of_fits S hS R₃ hok.freshI hps' hp' hmins'
        (fun c' hc' => wdFieldCtxN hs m hok _ ρ c' hc' ps' hps' hp') (hres ps' hps' hp')
        (R₃.R.motiveOk_of_mem hS hps' hp' hm') (noRecDepN hok)
        (domsBounded_ofN hs m hok _ ρ hps' hp') (contOk hs m hok _ hp')
        hmn' j c hc fs' hfitF'
        (c.recFields.map fun kf => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
          (S.ihValN N c.fields.length kf.1 kf.2))
        (ListRel.map (f := fun kf => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
            (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
            (S.ihValN N c.fields.length kf.1 kf.2))
          fun kf hkf => (hih kf hkf).2.1)
      refine ⟨?_, ?_⟩
      · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
        · intro a ha
          simp only [List.mem_append, List.mem_map] at ha
          rcases ha with ha | ⟨kf, hkf, rfl⟩
          · exact Expr.wd_of_mem_varsAt ha
          · exact (hih kf hkf).1
        · rw [interp_bvar, List.map_append, List.map_map, interp_varsAt, shiftE_zero_zero,
            readEnv_consList hf', hminor fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins']
          exact hmin.2
      · rw [hbody fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins',
          hty fs' minsK' mins' m1' m'' ps' hf' hminsK' hmins' hps' hp' hfitF']
        exact hmin.1
  refine ⟨?_, ?_, ?_⟩
  · -- the equation
    rw [hspineR, interp_instL]
    cases hq : S.q.holds (Level.substVal φ S.recLparams us)
    · have hz := z_false_of_q hok (Level.substVal φ S.recLparams us) hq
      have hcl := classLaws hs m hok _ hz hp
      rw [key.2.2.2 hq, S.recSemN_eq m.M _ N false hN hz (noRecDepN hok) (domsBounded_ofN hs m hok _ ρ hps hp)
        (contOk hs m hok _ hp) hcl ⟨m', m1, mins, minsK⟩ hc hfitF]
      unfold ruleRhsN
      rw [interp_mkLams, hq, appList_lamCtx_false hfitRule, henv,
        hbody fs minsK mins m1 m' ps hf hminsK hmins]
      congr 2
      exact List.map_congr_left fun kf hkf =>
        ((ihValN_ok hs m hok φ ρ hus (hS.2.2.2.1 c hcm).1 hkf hf hminsK hmins hps hp hm hm1 hmn hmnK
          (wdFieldCtxN hs m hok _ ρ c hcm ps hps hp) hfitF).2.2 hq).symm
    · rw [recSetN_eq hs m hok φ ρ hus, hq, lamCtx_true_eq_pt _ _ (by simp [recCtxN]), appList_pt]
      unfold ruleRhsN
      rw [interp_mkLams, hq, lamCtx_true_eq_pt _ _ (by simp [ruleCtxN, extrasN]), appList_pt]
  · -- the invariant
    rw [WellDenoted_instL]
    exact hrhs.1
  · -- the application chain
    rw [hspineR, interp_instL]
    refine spineOk_of_teleFitV _ _ hT hrhs.2 ?_
    rw [TeleFitV_mkPis _ _ _ (by
        rw [List.length_reverse, length_ruleCtxN]
        simp only [List.length_append, List.length_cons, List.length_nil, hf, hmins, hminsK, hps, oN]
        omega),
      List.reverse_reverse]
    exact hfitRule

/-! ## The ι laws of `T.rec_1`'s rules -/

omit [LevelOracle] hs m hok in
/-- The point applied to values each lying in some set is a
well-formed application chain (at a proposition the chain's slots are
propositional products, which the point inhabits). -/
theorem spineOk_pt_of_mem : ∀ {vs : List V}, (∀ v ∈ vs, ∃ A : V, v ∈ˢ A) → SpineOk (pt : V) vs
  | [], _ => trivial
  | v :: vs, h => by
    obtain ⟨A, hA⟩ := h v List.mem_cons_self
    refine ⟨⟨true, A, fun _ => one, ?_, hA, fun _ _ _ => one_mem_univ_zero⟩, ?_⟩
    · rw [piR_true]; exact pt_mem_truthVal fun _ _ => rfl
    · rw [app_pt]; exact spineOk_pt_of_mem fun w hw => h w (List.mem_cons_of_mem v hw)

omit [LevelOracle] hs m hok in
/-- Every value of a telescope fit lies in the domain it meets. -/
theorem TeleFitV_mem (M' : Name → List Nat → V) (φ' : Name → Nat) :
    ∀ {ρ : Nat → V} {T : Expr} {vs : List V}, TeleFitV M' φ' ρ T vs → ∀ v ∈ vs, ∃ A : V, v ∈ˢ A
  | _, _, [], _, _, h => by simp at h
  | _, .pi A _ B, v :: vs, ⟨hv, hrest⟩, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨_, hv⟩
    · exact TeleFitV_mem M' φ' hrest w hw
  | _, .bvar _, _ :: _, h, _, _ => h.elim
  | _, .sort _, _ :: _, h, _, _ => h.elim
  | _, .const _ _, _ :: _, h, _, _ => h.elim
  | _, .app _ _, _ :: _, h, _, _ => h.elim
  | _, .lam _ _ _, _ :: _, h, _, _ => h.elim

omit [LevelOracle] hs m hok in
/-- No value walks into an application of a constant (a telescope ends
there). -/
theorem TeleFitV_mkAppN_not_pi (M' : Name → List Nat → V) (φ' : Name → Nat) (ρ : Nat → V)
    {w : V} {ws : List V} :
    ∀ (args : List Expr) (f : Expr), (∀ A pw B, f ≠ .pi A pw B) →
      ¬ TeleFitV M' φ' ρ (Expr.mkAppN f args) (w :: ws)
  | [], f, hf, h => by
    cases f <;> first | exact h | exact hf _ _ _ rfl
  | a :: args, f, hf, h =>
    TeleFitV_mkAppN_not_pi M' φ' ρ args (.app f a) (fun _ _ _ h' => Expr.noConfusion h')
      (by rwa [Expr.mkAppN_cons] at h)

/-- **The container's constructor's set applied to fitting values** is
the container's constructor value at the fields (at the constructor's
own levels and parameters, which the nested law does not compare with
the recursor's). -/
theorem ctor_appK (φ : Name → Nat) (ρ : Nat → V) {usj : List Level}
    (husj : usj.length = N.KS.lparams.length) {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c)
    {ps₂ fs : List V} (hps₂ : ps₂.length = N.nPK) (hf : fs.length = c.fields.length)
    (hfit : TeleFitV (S.M₃N m.M N) (Level.substVal φ N.KS.lparams usj) ρ (N.KS.ctorType c)
      (ps₂.reverse ++ fs.reverse)) :
    appList (S.M₃N m.M N c.name (usj.map (Level.eval φ))) (ps₂.reverse ++ fs.reverse)
      = N.KS.ctorVal (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj)) j fs := by
  have hK := K_law m hok
  have hKS := hK.1
  have hNS := hok.nestScoped N hok.nest
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hstored : (env.find? c.name).isSome := K_ctors_stored m hok j c hc
  have hwd : WellDenoted (S.M₃N m.M N) (Level.substVal φ N.KS.lparams usj) ρ (N.KS.ctorType c) := by
    have := ((m₃N hs m hok).type_ok c.name (N.KS.ctorInfo c) (hK.2.2.2.1 j c hc) φ ρ usj husj).1
    rw [m₃N_M, WellDenoted_instL] at this
    exact this
  -- the container's reader at the final assignment
  have RK : N.KS.Reader (env := env) m.M (Level.substVal φ N.KS.lparams usj) (N.KS.Fam m.M) (S.M₃N m.M N)
      (Level.substVal φ N.KS.lparams usj) :=
    { agree := agree_M₃N hok m.M
      fam := fun ls' => by
        show S.M₃N m.M N N.K.name ls' = N.KS.famSetF m.M ls' (N.KS.Fam m.M)
        rw [← agree_M₃N hok m.M _ hNS.1]; exact hK.2.2.2.2.1 ls'
      val := fun _ _ => rfl
      mem := fun ls' ps is => N.KS.Fam_mem_univ m.M ls' ps is }
  have hM₁ : N.KS.M₁ m.M = m.M := by
    funext n ls'
    simp only [M₁, M₁F]
    split
    · rename_i h; subst h; exact (hK.2.2.2.2.1 ls').symm
    · rfl
  have RK₁ : N.KS.Reader (env := env) m.M (Level.substVal φ N.KS.lparams usj) (N.KS.Fam m.M) (N.KS.M₁ m.M)
      (N.KS.ψ (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj))) :=
    { agree := by rw [hM₁]; exact fun _ _ _ => rfl
      fam := fun ls' => by simp [M₁, M₁F]
      val := fun n hn => (ψ_map_agree N.KS _ n hn).symm
      mem := fun ls' ps is => N.KS.Fam_mem_univ m.M ls' ps is }
  have hps₂' : ps₂.length = N.KS.nP := hps₂
  unfold ctorType at hfit
  rw [← List.reverse_append, TeleFitV_mkPis _ _ _ (by
      simp only [List.length_reverse, List.length_append, hf, hps₂, List.length_append,
        length_fieldCtx]
      rfl),
    List.reverse_reverse, FitsVals_append _ _ (by rw [hf, length_fieldCtx])] at hfit
  obtain ⟨hpF, hfF⟩ := hfit
  have hp := (RK.fits_params hKS).mp hpF
  have hidx := RK.idxFit_of_wd hKS hcm hwd hps₂' hp
  have hff := (RK.fits_fieldCtx hKS (hKS.2.2.2.1 c hcm).1 hps₂' hp hidx.1).1.mp hfF
  rw [← agree_M₃N hok m.M _ hstored, hK.2.2.2.2.2.1 j c hc,
    ← map_substVal_eq φ hKS.2.2.2.2.2.1 husj]
  cases hz : N.KS.z (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj))
  · have hfit₁ : FitsVals (N.KS.M₁ m.M) (N.KS.ψ (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj))) base
        (N.KS.fieldCtx c.fields ++ N.KS.params) (fs ++ ps₂) :=
      (FitsVals_append _ _ (by rw [hf, N.KS.length_fieldCtx])).mpr
        ⟨(RK₁.fits_params hKS).mpr hp,
         RK₁.fits_fieldCtx_of_idx hKS (hKS.2.2.2.1 c hcm).1 (ρ := base) hps₂' hp hff (hidx.2 fs hff).2.1⟩
    unfold ctorSet
    rw [hz, ← List.reverse_append, appList_lamCtx_false hfit₁, consList_append, readEnv_consList hf]
  · rw [KS_ctorSet_eq_pt m.M _ hz, appList_pt]
    simp [ctorVal, hz]

/-- **The core of the ι law of a `T.rec_1` rule**: from the two
telescope fits alone — the recursor's spine, ending in the container's
constructor applied, and the constructor's own spine — the equation,
the right-hand side's invariant and its application chain.  Above a
proposition the major sits in the class, which pins the fields
(`ClassLaws.inv`); at a proposition both sides are the point, and the
chain's values each lie in the domain they meet in their own
telescope. -/
theorem rule1_core (φ : Name → Nat) (ρ : Nat → V) {us usj : List Level} {xs ys : List V}
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c)
    (hus : us.length = (S.rec1Info N).lparams.length)
    (husj : usj.length = (N.KS.ctorInfo c).lparams.length)
    (hxs : xs.length = S.nP + 2 + (S.n + N.nK) + 0) (hys : ys.length = N.nPK + c.fields.length)
    (hfitR : TeleFitV (S.M₃N m.M N) φ ρ ((S.rec1Info N).type.instL (S.rec1Info N).lparams us)
      (xs ++ [appList (S.M₃N m.M N c.name (usj.map (Level.eval φ))) ys]))
    (hfitC : TeleFitV (S.M₃N m.M N) φ ρ ((N.KS.ctorInfo c).type.instL (N.KS.ctorInfo c).lparams usj) ys)
    (nd : Nat) (hnd : nd = N.nPK) :
    appList (S.M₃N m.M N N.aux (us.map (Level.eval φ)))
        (xs ++ [appList (S.M₃N m.M N c.name (usj.map (Level.eval φ))) ys])
      = appList (interp (S.M₃N m.M N) φ ρ ((S.rule1Rhs N c j).instL (S.rec1Info N).lparams us))
          (xs.take (S.nP + 2 + (S.n + N.nK)) ++ ys.drop nd) ∧
    WellDenoted (S.M₃N m.M N) φ ρ ((S.rule1Rhs N c j).instL (S.rec1Info N).lparams us) ∧
    SpineOk (interp (S.M₃N m.M N) φ ρ ((S.rule1Rhs N c j).instL (S.rec1Info N).lparams us))
      (xs.take (S.nP + 2 + (S.n + N.nK)) ++ ys.drop nd) := by
  subst hnd
  have hS := hok.scoped
  have hN := hok.nest
  have hK := K_law m hok
  have hKS := hK.1
  have hNS := hok.nestScoped N hN
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hj : j < N.nK := (List.getElem?_eq_some_iff.mp hc).1
  simp only [rec1Info, ctorInfo] at hus husj hfitR hfitC ⊢
  rw [TeleFitV_instL] at hfitR hfitC
  have R₃ := reader₃N m hok (Level.substVal φ S.recLparams us)
  have hidxM := fun ps hp => memberIdx_fits hs m hok (Level.substVal φ S.recLparams us) (ps := ps) hp
  -- the recursor's spine, split
  have hfitR' := hfitR
  rw [rec1Type_eq, TeleFitV_mkPis _ _ _ (by
      simp only [List.length_append, List.length_singleton, hxs, length_rec1Ctx, oN]; omega),
    List.reverse_append, List.reverse_singleton, List.singleton_append] at hfitR'
  obtain ⟨t, minsK, mins, m1, m', ps, heq, hminsK, hmins, hps⟩ := fits_rec1Ctx_split S N hfitR'
  obtain ⟨rfl, hxs'⟩ := List.cons.inj heq
  rw [hxs'] at hfitR'
  have hxs'' : xs = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse := by
    rw [← List.reverse_reverse xs, hxs']
    simp [List.reverse_append]
  subst hxs''
  obtain ⟨hp, hm, hm1, hmn, hmnK, hmaj⟩ :=
    (Reader.fits_rec1Ctx_iff S N hS R₃.R hN hminsK hmins hps hidxM).mp hfitR'
  -- the constructor's spine, split
  obtain ⟨ps₂, fs, hys₂, hps₂, hf⟩ : ∃ ps₂ fs, ys = ps₂.reverse ++ fs.reverse ∧
      ps₂.length = N.nPK ∧ fs.length = c.fields.length :=
    ⟨(ys.take N.nPK).reverse, (ys.drop N.nPK).reverse, by simp,
      by rw [List.length_reverse, List.length_take, hys]; omega,
      by rw [List.length_reverse, List.length_drop, hys, Nat.add_sub_cancel_left]⟩
  subst hys₂
  have hf' : fs.length = (S.classCtor N c).fields.length := by
    rw [hf]; exact (S.length_classFields N c.fields).symm
  have hmajor := ctor_appK hs m hok φ ρ husj hc hps₂ hf hfitC
  -- the right-hand side's spine
  have hdrop : (ps₂.reverse ++ fs.reverse).drop N.nPK = fs.reverse := List.drop_left' (by simp [hps₂])
  have htake : (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse).take (S.nP + 2 + (S.n + N.nK))
      = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse :=
    List.take_of_length_le (by simp [hps, hmins, hminsK]; omega)
  have hspineR : ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ++ fs.reverse
      = (fs ++ minsK ++ mins ++ [m1, m'] ++ ps).reverse := by
    simp [List.reverse_append]
  rw [hdrop, htake, hspineR, interp_instL]
  -- the common facts
  have hwd1 : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have hsc := S.classCtor_fieldScoped N hS hN hKS hcm
  have hwdE' : ∀ ps', FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ S.params ps' →
      CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps' ρ) (S.extrasN N) :=
    fun ps' hp' => wd_extrasN_of_rec1Ctx hwd1 hp'
  -- the minor's slot in a rule's environment
  have hminor : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = (S.classCtor N c).fields.length → minsK'.length = N.nK →
      consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ))
          ((S.classCtor N c).fields.length + N.nK - 1 - j)
        = minorKAt N minsK' j := by
    intro fs' minsK' mins' m1' m'' ps' hf'' hminsK'
    rw [show (S.classCtor N c).fields.length + N.nK - 1 - j = (N.nK - 1 - j) + fs'.length by
        rw [hf'']; omega,
      consList_ge, consList_append, consList_append, consList_getD (by omega)]
    rfl
  -- the rule's body, read at fitting values
  have hbody : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = (S.classCtor N c).fields.length → minsK'.length = N.nK →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
          (Expr.mkAppN (.bvar ((S.classCtor N c).fields.length + N.nK - 1 - j))
            (Expr.varsAt 0 (S.classCtor N c).fields.length ++
              (S.classCtor N c).recFields.map fun kf => S.ihValN N (S.classCtor N c).fields.length kf.1 kf.2))
        = appList (minorKAt N minsK' j) (fs'.reverse ++ (S.classCtor N c).recFields.map fun kf =>
            interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
              (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
              (S.ihValN N (S.classCtor N c).fields.length kf.1 kf.2)) := by
    intro fs' minsK' mins' m1' m'' ps' hf'' hminsK'
    rw [interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map, interp_varsAt,
      shiftE_zero_zero, readEnv_consList hf'', hminor fs' minsK' mins' m1' m'' ps' hf'' hminsK']
    rfl
  -- the conclusion's head, read: the container's constructor value at the fields
  have hhead : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = (S.classCtor N c).fields.length → minsK'.length = N.nK → mins'.length = S.n →
      ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps') ps' (S.classCtor N c).fields fs' →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
          (Expr.mkAppN (.const c.name N.lsK)
            (S.classArgs N ((S.classCtor N c).fields.length + S.oN N) ++
              Expr.varsAt 0 (S.classCtor N c).fields.length))
        = N.KS.ctorVal (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) j fs' := by
    intro fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hfitF'
    have hos : (minsK' ++ mins' ++ [m1', m'']).length = S.oN N := by
      simp only [List.length_append, List.length_cons, List.length_nil, hminsK', hmins', oN]; omega
    cases hz : S.z (S.lparams.map (Level.substVal φ S.recLparams us))
    · have hzK : N.KS.z (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) = false := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      have hfitCl := (S.ClassFits_iff_FitsFields N hN _ ps' c.fields).mpr hfitF'
      have h := Reader.classCtorApp_eq S N hS R₃.R hN (nestFacts hs m hok _) hKS
        hK.2.2.2.2.2.1 (K_ctors_stored m hok) hz hc (ihsE := []) (nIh := 0) (o := S.oN N)
        (os := minsK' ++ mins' ++ [m1', m'']) (ρ := ρ) rfl hf'' hos hps' hp' (hidxM ps' hp') hfitCl
      rw [consList_nil, Nat.zero_add] at h
      rw [h]
      simp [ctorVal, hzK, KS_tagOf]
    · have hzK : N.KS.z (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) = true := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      have h := Reader.classCtorApp_read hS R₃.R hN (K_ctors_stored m hok j c hc)
        (ihsE := []) (nIh := 0) (o := S.oN N) (os := minsK' ++ mins' ++ [m1', m'']) (ρ := ρ) rfl hf''
        hos hps' hp' (hidxM ps' hp')
      rw [consList_nil, Nat.zero_add] at h
      rw [h, hK.2.2.2.2.2.1 j c hc, KS_ctorSet_eq_pt m.M _ hzK, appList_pt]
      simp [ctorVal, hzK]
  -- the rule's type's body, read
  have hty : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = (S.classCtor N c).fields.length → minsK'.length = N.nK → mins'.length = S.n →
      ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps') ps' (S.classCtor N c).fields fs' →
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ))) (S.rule1BodyTy N c)
        = appList m1' [N.KS.ctorVal (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) j fs'] := by
    intro fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hfitF'
    have hg : (minsK' ++ mins' ++ [m1', m'']).getD (S.oN N - 2) pt = m1' := by
      rw [show S.oN N - 2 = (minsK' ++ mins').length by
        simp only [List.length_append, hminsK', hmins', oN]; omega]
      exact (getD_append_two _ _).1
    show interp _ _ _ (Expr.mkAppN (.bvar ((S.classCtor N c).fields.length + S.oN N - 2))
      [Expr.mkAppN (.const c.name N.lsK)
        (S.classArgs N ((S.classCtor N c).fields.length + S.oN N) ++
          Expr.varsAt 0 (S.classCtor N c).fields.length)]) = _
    have hidx2 : (S.classCtor N c).fields.length + S.oN N - 2 = (S.oN N - 2) + fs'.length := by
      rw [hf'']; unfold oN; omega
    have hlt2 : S.oN N - 2 < (minsK' ++ mins' ++ [m1', m'']).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hminsK', hmins', oN]; omega
    rw [interp_mkAppN_appList, interp_bvar, List.map_singleton,
      hhead fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hfitF', hidx2, consList_ge,
      consList_getD hlt2, hg]
  -- the class minor's typing, in either regime
  have hminTyped : ∀ (fs' minsK' mins' : List V) (m1' m'' : V) (ps' : List V),
      fs'.length = (S.classCtor N c).fields.length → minsK'.length = N.nK → mins'.length = S.n →
      ps'.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams us))) base S.params ps' →
      m'' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps' ρ) S.motiveTy →
      m1' ∈ˢ interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (cons m'' (consList ps' ρ)) (S.motiveTy1 N) →
      FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList [m1', m''] (consList ps' ρ)) S.minorsCtxN mins' →
      FitsVals (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList (mins' ++ [m1', m'']) (consList ps' ρ)) (S.minorsCtxK N) minsK' →
      S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps') ps' (S.classCtor N c).fields fs' →
      ∀ ihs, ListRel (S.IhTypedN m.M (S.lparams.map (Level.substVal φ S.recLparams us))
          (S.q.holds (Level.substVal φ S.recLparams us)) ps' ⟨m'', m1', mins', minsK'⟩ fs')
          (S.classCtor N c).recFields ihs →
        appList (minorKAt N minsK' j) (fs'.reverse ++ ihs) ∈ˢ
          appList m1' [N.KS.ctorVal (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) j fs'] ∧
        SpineOk (minorKAt N minsK' j) (fs'.reverse ++ ihs) := by
    intro fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hm' hm1' hmn' hmnK' hfitF' ihs hihs
    have hwdCK : ∀ c' ∈ N.K.ctors, CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) (consList ps' ρ)
        (S.fieldCtx (S.classCtor N c').fields) := fun c' hc' => by
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hc'
      exact wdFieldCtxK (wd_extrasN_of_rec1Ctx hwd1 ((R₃.R.fits_params hS).mpr hp')) hmins' hminsK'
        hm' hm1' hmn' hmnK' j' c' hj'
    have hmot1 := Reader.motive1Ok_of_mem S N hS R₃.R hN hps' hp' (hidxM ps' hp') hm1'
    cases hz : S.z (S.lparams.map (Level.substVal φ S.recLparams us))
    · have hzK : N.KS.z (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) = false := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      have hfitCl := (S.ClassFits_iff_FitsFields N hN _ ps' c.fields).mpr hfitF'
      have h := Reader₂.minorOkK_of_fits S N hS R₃ hN (nestFacts hs m hok _) hKS hK.2.2.2.2.2.1
        (K_ctors_stored m hok) hz hps' hp' hmins' hminsK' hwdCK (hidxM ps' hp') hmot1 hmnK' j c hc
        fs' hfitCl ihs hihs
      simp only [ctorVal, hzK, Bool.false_eq_true, if_false, KS_tagOf]
      exact h
    · have hzK : N.KS.z (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) = true := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      have h := Reader₂.minorOkK_of_fits_prop hS R₃ hN (nestFacts hs m hok _) hKS hK.2.2.2.2.2.1
        (K_ctors_stored m hok) hz hps' hp' hmins' hminsK' hwdCK (hidxM ps' hp') hmot1 hmnK' j c hc
        fs' hfitF' ihs hihs
      simp only [ctorVal, hzK, if_true]
      exact h
  -- the right-hand side is well-denoted and in the rule's type
  have hT := wd_rule1Type hs m hok hcm (Level.substVal φ S.recLparams us) ρ
  unfold rule1Type at hT
  have hrhs := mkLams_ok _ _ hT (b := Expr.mkAppN (.bvar ((S.classCtor N c).fields.length + N.nK - 1 - j))
      (Expr.varsAt 0 (S.classCtor N c).fields.length ++
        (S.classCtor N c).recFields.map fun kf => S.ihValN N (S.classCtor N c).fields.length kf.1 kf.2))
    fun vs hvs => by
      obtain ⟨fs', minsK', mins', m1', m'', ps', rfl, hf'', hminsK', hmins', hps'⟩ :=
        fits_ruleCtxN_split m _ hvs
      obtain ⟨hp', hm', hm1', hmn', hmnK', hfitF'⟩ :=
        (fits_ruleCtxK m hok _ ρ hwdE' hc hf'' hminsK' hmins' hps').mp hvs
      rw [show consList (fs' ++ minsK' ++ mins' ++ [m1', m''] ++ ps') ρ
          = consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)) by
          simp [consList_append]]
      have hwdF' := wdFieldCtxK (hwdE' ps' ((R₃.R.fits_params hS).mpr hp')) hmins' hminsK' hm' hm1'
        hmn' hmnK' j c hc
      have hih := fun kf (hkf : kf ∈ (S.classCtor N c).recFields) =>
        ihValN_ok hs m hok φ ρ hus hsc hkf hf'' hminsK' hmins' hps' hp' hm' hm1' hmn' hmnK' hwdF' hfitF'
      have hmin := hminTyped fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hm' hm1' hmn'
        hmnK' hfitF'
        ((S.classCtor N c).recFields.map fun kf => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
          (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
          (S.ihValN N (S.classCtor N c).fields.length kf.1 kf.2))
        (ListRel.map (f := fun kf => interp (S.M₃N m.M N) (Level.substVal φ S.recLparams us)
            (consList fs' (consList (minsK' ++ mins' ++ [m1', m'']) (consList ps' ρ)))
            (S.ihValN N (S.classCtor N c).fields.length kf.1 kf.2))
          fun kf hkf => (hih kf hkf).2.1)
      refine ⟨?_, ?_⟩
      · refine WellDenoted_mkAppN_of_spineOk _ _ _ (by simp) ?_ ?_
        · intro a ha
          simp only [List.mem_append, List.mem_map] at ha
          rcases ha with ha | ⟨kf, hkf, rfl⟩
          · exact Expr.wd_of_mem_varsAt ha
          · exact (hih kf hkf).1
        · rw [interp_bvar, List.map_append, List.map_map, interp_varsAt, shiftE_zero_zero,
            readEnv_consList hf'', hminor fs' minsK' mins' m1' m'' ps' hf'' hminsK']
          exact hmin.2
      · rw [hbody fs' minsK' mins' m1' m'' ps' hf'' hminsK',
          hty fs' minsK' mins' m1' m'' ps' hf'' hminsK' hmins' hps' hp' hfitF']
        exact hmin.1
  cases hq : S.q.holds (Level.substVal φ S.recLparams us)
  · -- the graph regime: the major is the tagged tuple of its fields, which fit
    have hz := z_false_of_q hok (Level.substVal φ S.recLparams us) hq
    have hcl := classLaws hs m hok _ hz hp
    have hzK : N.KS.z (S.lsK (S.lparams.map (Level.substVal φ S.recLparams us)) N) = false := by
      rw [(nestFacts hs m hok _).z_eq]; exact hz
    have hmaj' : N.KS.ctorVal (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj)) j fs
        = tag j (tuple fs.reverse) := by
      cases hzj : N.KS.z (N.KS.lparams.map (Level.substVal φ N.KS.lparams usj))
      · simp [ctorVal, hzj, KS_tagOf]
      · exfalso
        rw [hmajor] at hmaj
        simp only [ctorVal, hzj, if_true] at hmaj
        unfold classAt at hmaj
        have hnf := nestFacts hs m hok (Level.substVal φ S.recLparams us)
        rw [S.classSet_eq_Fam hnf hp (S.Fam_mem_univ m.M _ _ _),
          N.KS.mem_Fam_false m.M _ hnf.noRecDep (hnf.domsBoundedK hp (S.Fam_mem_univ m.M _ _ _))
            (hnf.contOkK _) hzK] at hmaj
        obtain ⟨j', c', fs', -, -, -, h⟩ := hmaj
        exact tag_ne_pt h.symm
    rw [hmajor, hmaj'] at hmaj
    rw [hmajor, hmaj']
    unfold classAt at hmaj
    obtain ⟨j', c', fs', hc', hfitCl, heq'⟩ := hcl.inv _ (S.Fam_mem_univ m.M _ _ _) _ hmaj
    obtain ⟨rfl, hfs⟩ := tag_inj heq'
    obtain rfl := List.reverse_inj.mp (tuple_inj hfs)
    rw [hc] at hc'
    cases hc'
    have hfitF : S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams us)) (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams us)) ps) ps (S.classCtor N c).fields fs := by
      simp only [classCtor] at hfitCl ⊢
      exact (S.ClassFits_iff_FitsFields N hN _ ps c.fields).mp hfitCl
    have hfitRule := (fits_ruleCtxK m hok _ ρ hwdE' hc hf' hminsK hmins hps).mpr
      ⟨hp, hm, hm1, hmn, hmnK, hfitF⟩
    have key := rec1_app_mem hs m hok φ ρ hus hps hp hm hm1 hmins hminsK hmn hmnK hmaj
    refine ⟨?_, ?_, ?_⟩
    · rw [key.2.2.2 hq, S.rec1Sem_eq m.M _ N false hN hz (noRecDepN hok) (domsBounded_ofN hs m hok _ ρ hps hp)
        (contOk hs m hok _ hp) hcl ⟨m', m1, mins, minsK⟩ hc hfitCl]
      unfold rule1Rhs
      rw [interp_mkLams, hq, appList_lamCtx_false hfitRule,
        show consList (fs ++ minsK ++ mins ++ [m1, m'] ++ ps) ρ
          = consList fs (consList (minsK ++ mins ++ [m1, m']) (consList ps ρ)) by simp [consList_append],
        hbody fs minsK mins m1 m' ps hf' hminsK]
      congr 2
      exact List.map_congr_left fun kf hkf =>
        ((ihValN_ok hs m hok φ ρ hus hsc hkf hf' hminsK hmins hps hp hm hm1 hmn hmnK
          (wdFieldCtxK (hwdE' ps ((R₃.R.fits_params hS).mpr hp)) hmins hminsK hm hm1 hmn hmnK j c hc)
          hfitF).2.2 hq).symm
    · rw [WellDenoted_instL]
      exact hrhs.1
    · refine spineOk_of_teleFitV _ _ hT hrhs.2 ?_
      rw [TeleFitV_mkPis _ _ _ (by
          rw [List.length_reverse, length_ruleCtxN]
          simp only [List.length_append, List.length_cons, List.length_nil, hf', hmins, hminsK, hps, oN]
          omega),
        List.reverse_reverse]
      exact hfitRule
  · -- at a proposition both sides are the point
    refine ⟨?_, ?_, ?_⟩
    · rw [rec1Set_eq hs m hok φ ρ hus, hq, lamCtx_true_eq_pt _ _ (by simp [rec1Ctx]), appList_pt]
      unfold rule1Rhs
      rw [interp_mkLams, hq, lamCtx_true_eq_pt _ _ (by simp [ruleCtxN, extrasN]), appList_pt]
    · rw [WellDenoted_instL]
      exact hrhs.1
    · unfold rule1Rhs
      rw [interp_mkLams, hq, lamCtx_true_eq_pt _ _ (by simp [ruleCtxN, extrasN])]
      refine spineOk_pt_of_mem fun v hv => ?_
      rw [← hspineR] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact TeleFitV_mem _ _ hfitR v (List.mem_append_left _ hv)
      · exact TeleFitV_mem _ _ hfitC v (List.mem_append_right _ hv)

/-- **The nested ι law of a `T.rec_1` rule** (`RecRuleLawN`,
`EnvModel.lean`): at the container's parameter count. -/
theorem rec_rule_law1N {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) :
    RecRuleLawN (S.M₃N m.M N) N.aux (S.rec1Info N) N.nPK (S.nP + 2 + (S.n + N.nK))
      (S.nP + 2 + (S.n + N.nK) + 0)
      ⟨c.name, c.fields.length, S.rule1Rhs N c j, some (N.lsK, S.classArgs N 0)⟩ (N.KS.ctorInfo c) := by
  intro φ ρ us usj xs ys hus husj hxs hys hfitR hfitC _
  exact rule1_core hs m hok φ ρ hc hus husj hxs hys hfitR hfitC N.nPK rfl

end IndSpec

end Fragment
