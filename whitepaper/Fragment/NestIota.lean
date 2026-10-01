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

**What is left out.**  At a proposition with a small eliminator the
class's laws are not available (`classLaws` needs `z = false`, and
inversion is false there: every member is the point); the inhabitation
of the motives there is stated as the named hypothesis
`MotivesInhabitedProp`, consumed only in that case.  The plain law of
a `T.rec_1` rule drops the RECURSOR's parameter count from the
constructor's spine; when the container has more parameters than the
block the dropped list is not the fields, and the law is not provable
from its hypotheses — `rec_rule_law1` assumes `N.nPK ≤ S.nP`.
-/

namespace Fragment
open SetLib IndLib

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
theorem Reader.classCtorApp_read (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
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
theorem ReaderG.agree_fieldCtxAt' (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.ReaderG (env := env) M φ M₁ φ₁) (R₂ : S.ReaderG (env := env) M φ M₂ φ₂)
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
    (R₁ : S.Reader (env := env) M φ M₁ φ₁) (R₂ : S.Reader (env := env) M φ M₂ φ₂)
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
      S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ)) (S.Mem M (S.lparams.map φ))
        ps c.fields fs ∧
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
    exact R₁.R.agree_ihCtxAux hS R₂.R.toReader hq hcm hf hos (by omega) (fun _ => by omega) hps
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
    exact R₁.R.agree_ihCtxAux' R₂.R.toReader hq hsc hf hos (by omega) (fun _ => by omega) hps
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
      Reader.classCtorApp_read hS R₁.R.toReader hN hcst (o := 2 + S.n + j) hi hf hos hps hp hidx,
      Reader.classCtorApp_read hS R₂.R.toReader hN hcst (o := 2 + S.n + j) hi hf hos hps hp hidx]

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
      rw [Reader.read_motiveTy1 S N hS R₁.R.toReader hN hps hp hidx,
        Reader.read_motiveTy1 S N hS R₂.R.toReader hN hps hp hidx, hq]
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

end IndSpec

end Fragment
