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
  have hagP := R₁.R.agree_params₂ hS R₂.R.toReader ρ₁ ρ₂
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
    exact R₁.R.read₂ R₂.R.toReader (hS.2.1 i A₀ hA₀) (by simp only [hvl, hps, nI]; omega)
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
  have hagP := R₁.R.agree_params₂ hS R₂.R.toReader ρ₁ ρ₂
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

/-! ## The recursors' sets in the final model -/

variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

/-- The container's constructors are stored. -/
theorem K_ctors_stored : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome :=
  fun j c hc => by rw [(K_law hs m hok).2.2.2.1 j c hc]; rfl

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
  exact ((reader₃N hs m hok φ).R.idxFit_of_wd hok.scoped hc (wd_ctorTypeN hs m hok hc _ ρ) hps hp).1

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
  have R₃ := reader₃N hs m hok (Level.substVal φ S.recLparams us)
  have R₂ := reader₂N hs m hok (Level.substVal φ S.recLparams us) hval
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.recCtxN N) := by
    have := wd_recTypeN hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [recTypeN_eq, WellDenoted_mkPis] at this
    exact this.1
  have hagree := R₂.agree_recCtxN hS R₃ hagr hok.nest (K_law hs m hok).1 hok.freshI
    (K_ctors_stored hs m hok) base ρ (fun ps hp => memberIdx_fits hs m hok _ hp)
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
  have R₃ := reader₃N hs m hok (Level.substVal φ S.recLparams us)
  have R₂ := reader₂N hs m hok (Level.substVal φ S.recLparams us) hval
  have hwd : CtxWD (S.M₃N m.M N) (Level.substVal φ S.recLparams us) ρ (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok (Level.substVal φ S.recLparams us) ρ
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have hagree := R₂.agree_rec1Ctx hS R₃ hagr hok.nest (K_law hs m hok).1 hok.freshI
    (K_ctors_stored hs m hok) base ρ (fun ps hp => memberIdx_fits hs m hok _ hp)
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
  have hK := K_law hs m hok
  have R₃ := reader₃N hs m hok φr
  have hidx := memberIdx_fits hs m hok φr hp
  have hwdC := wdFieldCtxN hs m hok φr ρ
  have hwdCK : ∀ c ∈ N.K.ctors, CtxWD (S.M₃N m.M N) φr (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields) :=
    fun c hc => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      exact wdFieldCtxK hwdE hmins hminsK hm hm1 hmn hmnK j c hj
  have hres : ∀ c ∈ S.ctors, ∀ fs, S.FitsFields m.M (S.lparams.map φr) (S.bound m.M (S.lparams.map φr))
      (S.Mem m.M (S.lparams.map φr)) ps c.fields fs →
      FitsVals m.M (S.ψ (S.lparams.map φr)) (envP ps) S.indices
        (S.idxVals m.M (S.lparams.map φr) (consList fs (envP ps)) c.idx) :=
    fun c hc fs hfit =>
      ((R₃.R.idxFit_of_wd hS hc (wd_ctorTypeN hs m hok hc _ ρ) hps hp).2 fs hfit).2.2
  have hmot := R₃.R.motiveOk_of_mem hS hps hp hm
  have hmot1 := Reader.motive1Ok_of_mem S N hS R₃.R.toReader hN hps hp hidx hm1
  have hmin : ∀ j c, S.ctors[j]? = some c →
      S.MinorOkN m.M (S.lparams.map φr) (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ j c :=
    fun j c hc fs hfit ihs hihs =>
      (Reader₂.minorOkN_of_fits S hS R₃ hok.freshI hps hp hmins (fun c hc => hwdC c hc ps hps hp)
        hres hmot (noRecDepN hok) (domsBounded_ofN hs m hok φr ρ hps hp)
        (S.contInBound_of (nestFacts hs m hok φr) hN hp) hmn j c hc fs hfit ihs
        ((ListRel_iff fun _ _ => S.IhTypedN_iff.trans S.IhTypedN_iff.symm).mp hihs)).1
  have hFam : ∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map φr) ps is →
      FitsVals m.M (S.ψ (S.lparams.map φr)) (envP ps) S.indices is := fun is t ht =>
    S.idx_fits_of_mem_Fam m.M _ (fun j c hc fs hfit => hres c (List.mem_of_getElem? hc) fs hfit) ht
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · have hz := z_false_of_q hok φr hq
    have hcl := classLaws hs m hok φr hz hp
    have hminK : ∀ j c, N.K.ctors[j]? = some c →
        S.MinorOkK m.M (S.lparams.map φr) N (S.q.holds φr) ps ⟨m', m1, mins, minsK⟩ j c :=
      fun j c hc fs hfit ihs hihs =>
        (Reader₂.minorOkK_of_fits S N hS R₃ hN (nestFacts hs m hok φr) hK.1 hK.2.2.2.2.2.1
          (K_ctors_stored hs m hok) hz hps hp hmins hminsK hwdCK hidx hmot1 hmnK j c hc fs hfit
          ihs hihs).1
    rw [hq] at hmin hminK
    exact S.recSemN_mem m.M _ N false hN hz hcl ⟨m', m1, mins, minsK⟩ hmin hminK
      (fun h => nomatch h)
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
            (K_ctors_stored hs m hok) hz hps hp hmins hminsK hwdCK hidx hmot1 hmnK j c hc fs hfit
            ihs hihs).1
      rw [hq] at hmin hminK
      exact S.motive_inhabitedN m.M _ N true hN hcl ⟨m', m1, mins, minsK⟩ hmin hminK (fun _ => hmo)
    · sorry

/-- **`T.rec`'s set is in `T.rec`'s type.** -/
theorem recSetN_mem (φ : Name → Nat) (ρ : Nat → V) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.recSetN m.M N (lsr.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.recTypeN N) := by
  have hS := hok.scoped
  have R₃ := reader₃N hs m hok (Level.substVal φ S.recLparams lsr)
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
      (Reader.fits_recCtxN_iff S N hS R₃.R.toReader hi hminsK hmins hps).mp hvs
    rw [recFN_read S m.M _ N _ hi hminsK hmins hps, read_recBodyN S _ _ N hi hminsK hmins, hq]
    have hwdE := wd_extrasN_of_recCtxN hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).1 hq).1 is t ht
  · intro hq vs hvs
    obtain ⟨t, is, minsK, mins, m1, m', ps, rfl, hi, hminsK, hmins, hps⟩ := fits_recCtxN_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩ :=
      (Reader.fits_recCtxN_iff S N hS R₃.R.toReader hi hminsK hmins hps).mp hvs
    rw [read_recBodyN S _ _ N hi hminsK hmins]
    have hwdE := wd_extrasN_of_recCtxN hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).2 hq).1 is t ht

/-- **`T.rec_1`'s set is in `T.rec_1`'s type.** -/
theorem rec1Set_mem (φ : Name → Nat) (ρ : Nat → V) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.rec1Set m.M N (lsr.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) (Level.substVal φ S.recLparams lsr) ρ (S.rec1Type N) := by
  have hS := hok.scoped
  have R₃ := reader₃N hs m hok (Level.substVal φ S.recLparams lsr)
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
      (Reader.fits_rec1Ctx_iff S N hS R₃.R.toReader hok.nest hminsK hmins hps hidx).mp hvs
    rw [rec1F_read S m.M _ N _ hminsK hmins hps, read_rec1Body S _ _ N hminsK hmins, hq]
    have hwdE := wd_extrasN_of_rec1Ctx hwd ((R₃.R.fits_params hS).mpr hp)
    exact ((recs_typed hs m hok _ ρ hps hp hm hm1 hmins hminsK hmn hmnK hwdE).1 hq).2 t ht
  · intro hq vs hvs
    obtain ⟨t, minsK, mins, m1, m', ps, rfl, hminsK, hmins, hps⟩ := fits_rec1Ctx_split S N hvs
    obtain ⟨hp, hm, hm1, hmn, hmnK, ht⟩ :=
      (Reader.fits_rec1Ctx_iff S N hS R₃.R.toReader hok.nest hminsK hmins hps hidx).mp hvs
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

end IndSpec

end Fragment
