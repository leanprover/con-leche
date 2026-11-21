module

public import Fragment.IotaRead
public import Fragment.NestInstall

@[expose] public section

/-!
# The rules of a nested block, read off the recursors' own types

The twin of `IotaRead.lean` for a nested block's two recursors, which
share one binder prefix — the parameters, the block's motive, the
class's motive, the block's minor premises, the class's minor premises
(`extrasN`, `Decl.lean`).  `T.rec` concludes with the block's motive,
whose minors are the block's minor premises: rule `j` of `T.rec` reads
minor premise `j` (`minorsOf_recTypeN`).  `T.rec_1` concludes with the
class's motive, whose minors are the class's minor premises, after the
block's: rule `j` of `T.rec_1` reads the class's minor premise `j`,
the binder `n + j` among the minors (`minorsOf_rec1Type`).  The
equations are the cores of the stored laws at a constructor value
(`rec_rule_coreN`, `rule1_coreB`, `NestIota.lean`), which hold
unconditionally.
-/

namespace Fragment
open NestInfo (nPK nK)
open SetLib UnivLib IndLib

universe u

namespace IndSpec

variable {V : Type u} [IndLib V] [LevelOracle] {env : Env} {S : IndSpec} {N : NestInfo}

omit [IndLib V] [LevelOracle] in
/-- The nested recursors' common binders, outermost first. -/
theorem extrasN_params_reverse :
    (S.extrasN N ++ S.params).reverse = (S.params.reverse ++ [S.motiveTy, S.motiveTy1 N]) ++
      (List.range S.n).map (fun j => S.minorTyN (S.ctors.getD j ⟨"", [], []⟩) j) ++
      (List.range N.nK).map (fun j => S.minorTyK N (N.K.ctors.getD j ⟨"", [], []⟩) j) := by
  simp [extrasN, minorsCtxN, minorsCtxK, List.reverse_append]

omit [IndLib V] [LevelOracle] in
theorem recCtxN_reverse :
    (S.recCtxN N).reverse = (S.extrasN N ++ S.params).reverse ++
      ((S.indicesAt (S.oN N)).reverse ++ [S.famVars (S.oN N)]) := by
  simp [recCtxN, List.reverse_append]

omit [IndLib V] [LevelOracle] in
theorem rec1Ctx_reverse :
    (S.rec1Ctx N).reverse = (S.extrasN N ++ S.params).reverse ++ [S.classTy N (S.oN N)] := by
  simp [rec1Ctx, List.reverse_append]

omit [IndLib V] [LevelOracle] in
theorem extras_at_minorN {j : Nat} (hj : j < S.n) :
    (S.extrasN N ++ S.params).reverse[S.nP + 2 + j]? =
      some (S.minorTyN (S.ctors.getD j ⟨"", [], []⟩) j) := by
  rw [extrasN_params_reverse, show S.nP + 2 + j = (S.params.reverse ++ [S.motiveTy, S.motiveTy1 N]).length + j by
    simp [nP], getElem?_mid _ _ _ (by simpa using hj)]
  simp [hj]

omit [IndLib V] [LevelOracle] in
theorem extras_at_minorK {j : Nat} (hj : j < N.nK) :
    (S.extrasN N ++ S.params).reverse[S.nP + 2 + S.n + j]? =
      some (S.minorTyK N (N.K.ctors.getD j ⟨"", [], []⟩) j) := by
  rw [extrasN_params_reverse, List.append_assoc,
    show S.nP + 2 + S.n + j = (S.params.reverse ++ [S.motiveTy, S.motiveTy1 N]).length + (S.n + j) by
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil, nP]; omega,
    List.getElem?_append_right (by simp only [List.length_append, List.length_reverse,
      List.length_cons, List.length_nil]; omega),
    List.getElem?_append_right (by simp only [List.length_append, List.length_reverse,
      List.length_cons, List.length_nil, List.length_map, List.length_range, n]; omega)]
  simp [n, hj]

omit [IndLib V] [LevelOracle] in
theorem extras_at_motive1 :
    (S.extrasN N ++ S.params).reverse[S.nP + 1]? = some (S.motiveTy1 N) := by
  rw [extrasN_params_reverse, List.append_assoc,
    List.getElem?_append_left (by simp [nP])]
  simp [nP]

omit [IndLib V] [LevelOracle] in
theorem length_extras_params : (S.extrasN N ++ S.params).length = S.nP + 2 + (S.n + N.nK) := by
  simp [length_extrasN, oN, nP]; omega

omit [IndLib V] [LevelOracle] in
theorem minorTyN_shape (c : CtorSpec) (j : Nat) :
    S.minorTyN c j = Expr.mkPis (S.fieldCtxAt c (2 + j))
      (Expr.mkPis (IndSpec.ihCtxAt c (2 + j))
        (Expr.mkAppN (.bvar (c.recFields.length + c.fields.length + (2 + j) - 1))
          (c.idx.map (Expr.atCtx c.fields.length c.fields.length c.recFields.length (2 + j) 0) ++
            [Expr.mkAppN (.const c.name S.lvls)
              (Expr.varsAt (c.recFields.length + c.fields.length + (2 + j)) S.nP ++
                Expr.varsAt c.recFields.length c.fields.length)]))) := by
  rw [minorTyN, Expr.mkPis_append]

omit [IndLib V] [LevelOracle] in
theorem minorTyK_shape (c : CtorSpec) (j : Nat) :
    S.minorTyK N c j = Expr.mkPis (S.fieldCtxAt (S.classCtor N c) (2 + S.n + j))
      (Expr.mkPis (IndSpec.ihCtxAt (S.classCtor N c) (2 + S.n + j))
        (Expr.mkAppN (.bvar ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
            (2 + S.n + j) - 2))
          [Expr.mkAppN (.const c.name N.lsK)
            (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
                (2 + S.n + j)) ++
              Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length)])) := by
  rw [minorTyK, Expr.mkPis_append]

omit [IndLib V] [LevelOracle] in
theorem length_ihCtxAt (c : CtorSpec) (o : Nat) : (IndSpec.ihCtxAt c o).length = c.recFields.length := by
  simp [ihCtxAt]

omit [IndLib V] [LevelOracle] in
theorem motivePos_recTypeN : (S.recTypeN N).motivePos = some S.nP := by
  rw [recTypeN]
  simp only [Expr.motivePos, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
    Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_recCtxN, Option.map_some]
  congr 1
  omega

omit [IndLib V] [LevelOracle] in
theorem motivePos_rec1Type : (S.rec1Type N).motivePos = some (S.nP + 1) := by
  rw [rec1Type]
  simp only [Expr.motivePos, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
    Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_rec1Ctx, Option.map_some]
  congr 1
  unfold oN
  omega

omit [IndLib V] [LevelOracle] in
/-- The binders of the common prefix, in either recursor's type. -/
theorem piDom?_prefix {T : Expr} (hT : T = Expr.mkPis (S.recCtxN N) (Expr.mkAppN (.bvar (S.nI + S.oN N))
      (Expr.varsAt 1 S.nI ++ [.bvar 0])) ∨
      T = Expr.mkPis (S.rec1Ctx N) (Expr.mkAppN (.bvar (S.oN N - 1)) [.bvar 0]))
    {q : Nat} (hq : q < S.nP + 2 + (S.n + N.nK)) :
    T.piDom? q = (S.extrasN N ++ S.params).reverse[q]? := by
  rcases hT with rfl | rfl
  · rw [Expr.piDom?_mkPis_lt _ _ _ (by rw [length_recCtxN]; unfold oN; omega), recCtxN_reverse,
      List.getElem?_append_left (by rw [List.length_reverse, length_extras_params]; exact hq)]
  · rw [Expr.piDom?_mkPis_lt _ _ _ (by rw [length_rec1Ctx]; unfold oN; omega), rec1Ctx_reverse,
      List.getElem?_append_left (by rw [List.length_reverse, length_extras_params]; exact hq)]

omit [IndLib V] [LevelOracle] in
theorem headVar_minorTyN (c : CtorSpec) (j : Nat) :
    (S.minorTyN c j).piConcl.headVar? = some (c.recFields.length + c.fields.length + (2 + j) - 1) ∧
    (S.minorTyN c j).piCount = c.recFields.length + c.fields.length := by
  simp only [minorTyN_shape, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
    Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_ihCtxAt, length_fieldCtxAt]
  exact ⟨by first | rfl | trivial, by first | rfl | trivial | omega⟩

omit [IndLib V] [LevelOracle] in
theorem headVar_minorTyK (c : CtorSpec) (j : Nat) :
    (S.minorTyK N c j).piConcl.headVar? =
      some ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length + (2 + S.n + j) - 2) ∧
    (S.minorTyK N c j).piCount = (S.classCtor N c).recFields.length + (S.classCtor N c).fields.length := by
  simp only [minorTyK_shape, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
    Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_ihCtxAt, length_fieldCtxAt]
  exact ⟨by first | rfl | trivial, by first | rfl | trivial | omega⟩

omit [IndLib V] [LevelOracle] in
theorem headVar_motiveTy1 : (S.motiveTy1 N).piConcl.headVar? = none := by
  simp [motiveTy1, Expr.mkPis, Expr.piConcl, Expr.headVar?, Expr.head]

omit [IndLib V] [LevelOracle] in
/-- **The minors of `T.rec`'s motive** are the block's minor premises:
rule `j` reads minor premise `j`. -/
theorem minorsOf_recTypeN :
    minorsOf (S.recTypeN N) (S.nP + 2 + (S.n + N.nK)) S.nP = (List.range S.n).map (S.nP + 2 + ·) := by
  have hT : S.recTypeN N = _ := rfl
  unfold minorsOf
  rw [show S.nP + 2 + (S.n + N.nK) = S.nP + 2 + S.n + N.nK by omega]
  refine filter_range_interval _ _ _ _ (fun q hq => ?_) (fun j hj => ?_) (fun j hj => ?_)
  · by_cases hq1 : q = S.nP + 1
    · subst hq1
      rw [piDom?_prefix (.inl hT) (by omega), extras_at_motive1]
      simp [headVar_motiveTy1]
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left; omega
  · rw [piDom?_prefix (.inl hT) (by omega), extras_at_minorN hj]
    obtain ⟨h1, h2⟩ := headVar_minorTyN (S := S) (S.ctors.getD j ⟨"", [], []⟩) j
    simp only [h1, h2, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq]
    omega
  · rw [show S.nP + 2 + S.n + j = S.nP + 2 + S.n + j by rfl,
      piDom?_prefix (.inl hT) (by omega), extras_at_minorK hj]
    obtain ⟨h1, h2⟩ := headVar_minorTyK (S := S) (N := N) (N.K.ctors.getD j ⟨"", [], []⟩) j
    simp only [h1, h2, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq,
      Option.some.injEq]
    right; omega

omit [IndLib V] [LevelOracle] in
/-- **The minors of `T.rec_1`'s motive** are the class's minor premises,
after the block's: rule `j` reads the class's minor premise `j`. -/
theorem minorsOf_rec1Type :
    minorsOf (S.rec1Type N) (S.nP + 2 + (S.n + N.nK)) (S.nP + 1) =
      (List.range N.nK).map (S.nP + 2 + S.n + ·) := by
  have hT : S.rec1Type N = _ := rfl
  unfold minorsOf
  rw [show S.nP + 2 + (S.n + N.nK) = S.nP + 2 + S.n + N.nK + 0 by omega]
  refine filter_range_interval _ _ _ _ (fun q hq => ?_) (fun j hj => ?_) (fun j hj => by omega)
  · by_cases hq1 : S.nP + 1 < q
    · obtain ⟨j, rfl⟩ : ∃ j, q = S.nP + 2 + j := ⟨q - (S.nP + 2), by omega⟩
      have hj : j < S.n := by omega
      rw [piDom?_prefix (.inr hT) (by omega), extras_at_minorN hj]
      obtain ⟨h1, h2⟩ := headVar_minorTyN (S := S) (S.ctors.getD j ⟨"", [], []⟩) j
      simp only [h1, h2, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq,
        Option.some.injEq]
      right; omega
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left; omega
  · rw [piDom?_prefix (.inr hT) (by omega), extras_at_minorK hj]
    obtain ⟨h1, h2⟩ := headVar_minorTyK (S := S) (N := N) (N.K.ctors.getD j ⟨"", [], []⟩) j
    simp only [h1, h2, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq]
    omega

omit [IndLib V] [LevelOracle] in
/-- Values fitting the nested recursors' first binders split as the
parameters, the two motives, the block's minors and the class's. -/
theorem split_prefixN {xs : List V} (hxs : xs.length = S.nP + 2 + (S.n + N.nK)) :
    ∃ (ps : List V) (m' m1 : V) (mins minsK : List V),
      xs = ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse ∧ ps.length = S.nP ∧
        mins.length = S.n ∧ minsK.length = N.nK := by
  obtain ⟨m', m1, rest, hd⟩ : ∃ m' m1 rest, xs.drop S.nP = m' :: m1 :: rest := by
    match hd : xs.drop S.nP with
    | m' :: m1 :: rest => exact ⟨m', m1, rest, rfl⟩
    | [] => have := congrArg List.length hd; simp [hxs] at this; omega
    | [_] => have := congrArg List.length hd; simp [hxs] at this; omega
  have hrest : rest.length = S.n + N.nK := by
    have := congrArg List.length hd; simp [hxs] at this; omega
  refine ⟨(xs.take S.nP).reverse, m', m1, (rest.take S.n).reverse, (rest.drop S.n).reverse, ?_,
    by simp [hxs]; omega, by simp [hrest], by simp [hrest]⟩
  have hx : xs = xs.take S.nP ++ m' :: m1 :: rest := by rw [← hd, List.take_append_drop]
  calc xs = xs.take S.nP ++ m' :: m1 :: rest := hx
    _ = _ := by simp

variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

/-- **`T.rec`'s rules hold, read off its type** (`RuleHolds`), in the
model of the installed nested block. -/
theorem rule_holdsN (vals : List Nat) (hvals : vals.length = S.recLparams.length)
    {i : Nat} {rl : RecRule} (hrl : (S.rulesN N)[i]? = some rl) :
    RuleHolds (S.M₃N m.M N) (valOf S.recLparams vals) (S.M₃N m.M N S.recName vals) (S.recTypeN N)
      (S.nP + 2 + (S.n + N.nK)) i rl := by
  intro mot q hmot hq xs ys D B C ρq ρc hxs hfit hD hys hfitD hC
  have hS := hok.scoped
  generalize hφdef : valOf S.recLparams vals = φ at hfit hfitD ⊢
  -- the rule: constructor `i`'s
  have hi : i < S.n := by
    have := (List.getElem?_eq_some_iff.mp hrl).1; simpa [rulesN] using this
  obtain ⟨c, hc⟩ : ∃ c, S.ctors[i]? = some c :=
    ⟨S.ctors.getD i ⟨"", [], []⟩, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl⟩
  have hcD : S.ctors.getD i ⟨"", [], []⟩ = c := by rw [List.getD_eq_getElem?_getD, hc]; rfl
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hrl' : rl = ⟨c.name, c.fields.length, S.ruleRhsN N c i, none, false⟩ := by
    simp only [rulesN, List.getElem?_map, List.getElem?_range hi, Option.map_some, hcD,
      Option.some.injEq] at hrl
    exact hrl.symm
  subst hrl'
  rw [motivePos_recTypeN] at hmot
  cases hmot
  rw [minorsOf_recTypeN, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at hq
  subst hq
  obtain ⟨ps, m', m1, mins, minsK, rfl, hps, hmins, hminsK⟩ := split_prefixN hxs
  have R₃ := reader₃N hs m hok φ
  -- the values before the indices
  have hsplit : S.recCtxN N = (S.famVars (S.oN N) :: S.indicesAt (S.oN N)) ++
      (S.extrasN N ++ S.params) := by simp [recCtxN]
  rw [recTypeN, hsplit, Expr.mkPis_append, TeleFitV_mkPis _ _ (by
    rw [length_extras_params]; simp [hps, hmins, hminsK]; omega)] at hfit
  rw [show (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse).reverse
      = minsK ++ mins ++ [m1, m'] ++ ps by simp,
    FitsVals_append _ _ (by simp [length_extrasN, hmins, hminsK, oN]; omega)] at hfit
  obtain ⟨hpF, hE⟩ := hfit
  obtain ⟨hm, hm1, hmn, hmnK⟩ := (fits_extrasN_iff' m φ base hminsK hmins).mp hE
  have hp := (R₃.R.fits_params hS).mp hpF
  -- the minor premise's domain and the values before it
  obtain ⟨minsE, hminsE⟩ : ∃ l, l = (mins.reverse.take i).reverse := ⟨_, rfl⟩
  have hlE : minsE.length = i := by simp [hminsE, hmins]; omega
  have htake : (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse).take (S.nP + 2 + i) =
      (minsE ++ [m1, m'] ++ ps).reverse := by
    rw [List.append_assoc, show S.nP + 2 + i = (ps.reverse ++ [m', m1]).length + i by simp [hps],
      List.take_length_add_append, List.take_append_of_le_length (by simp [hmins]; omega), hminsE]
    simp
  rw [recTypeN, htake] at hD
  have hpos : (S.recCtxN N).reverse[S.nP + 2 + i]? = some (S.minorTyN c i) := by
    rw [recCtxN_reverse, List.getElem?_append_left
      (by rw [List.length_reverse, length_extras_params]; omega), extras_at_minorN hi, hcD]
  obtain ⟨B', hB'⟩ := Expr.piBodyV_mkPis_at hpos (vs := (minsE ++ [m1, m'] ++ ps).reverse)
    (by simp [hlE, hps]; omega) base
  rw [hB', List.reverse_reverse] at hD
  simp only [Option.some.injEq, Prod.mk.injEq, Expr.pi.injEq] at hD
  obtain ⟨⟨rfl, -⟩, rfl⟩ := hD
  have hρq : consList (minsE ++ [m1, m'] ++ ps) base = consList (minsE ++ [m1, m']) (consList ps base) := by
    simp [consList_append]
  have hos : (minsE ++ [m1, m']).length = 2 + i := by simp [hlE]; omega
  -- the fields
  have hys' : ys.length = c.fields.length := hys
  rw [minorTyN_shape] at hfitD
  obtain ⟨fs, hfsdef⟩ : ∃ l, l = ys.reverse := ⟨_, rfl⟩
  have hfs := ((TeleFitV_mkPis_append _ _ (Γ := S.fieldCtxAt c (2 + i)) (vs := ys) (ws := [])
    (by simp [hys', length_fieldCtxAt])).mp (by rw [List.append_nil]; exact hfitD)).1
  rw [← hfsdef, hρq] at hfs
  have hf : fs.length = c.fields.length := by simp [hfsdef, hys']
  unfold fieldCtxAt at hfs
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hos] at hfs
  have hwd := wdFieldCtxN hs m hok φ base c hcm ps hps hp
  have hiff := R₃.R.fits_fieldCtx hS (nestFit hs m hok _) (hS.2.2.2.1 c hcm).1 hps hp hwd (vs := fs)
  have hfitF := hiff.1.mp hfs
  have hidx := hiff.2 hfitF
  -- the conclusion: the constructor's index values, then its value
  rw [minorTyN_shape, piBodyV_mkPis (by simp [hys', length_fieldCtxAt]), Option.map_some,
    conclV_mkPis, conclV_mkAppN_bvar, Option.some.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl⟩ := hC
  rw [Expr.args_mkAppN, Expr.args_bvar, List.nil_append, ← hfsdef, hρq]
  dsimp only
  rw [R₃.read_concl_args hS hok.freshI hc (by simp [length_ihCtxAt]) hf hos hps hp hfitF hidx]
  -- the ι equation at the constructor value
  have hφ : Level.substVal φ S.recLparams (vals.map Level.ofNat) = φ := by
    rw [← hφdef]; exact Level.substVal_ofNat _ _ hvals
  have core := (rec_rule_coreN hs m hok φ base (us := vals.map Level.ofNat) (by simpa using hvals)
    hc hps hmins hminsK hf (by rw [hφ]; exact hp) (by rw [hφ]; exact hm) (by rw [hφ]; exact hm1)
    (by rw [hφ]; exact hmn) (by rw [hφ]; exact hmnK) (by rw [hφ]; exact hfitF)).1
  rw [Level.map_eval_ofNat, hφ, interp_instL, hφ] at core
  rw [List.take_left' (by simp [hps, hmins, hminsK]; omega), List.drop_left' (by simp [hps])] at core
  simpa [hfsdef, List.append_assoc] using core

/-- **`T.rec_1`'s rules hold, read off its type** (`RuleHolds`), in the
model of the installed nested block: rule `i` reads the class's minor
premise `i`, whose conclusion is the class's motive at the container's
constructor `i` applied to the class's arguments and the fields. -/
theorem rule_holds1 (vals : List Nat) (hvals : vals.length = S.recLparams.length)
    {i : Nat} {rl : RecRule} (hrl : (S.rules1 N)[i]? = some rl) :
    RuleHolds (S.M₃N m.M N) (valOf S.recLparams vals) (S.M₃N m.M N N.aux vals) (S.rec1Type N)
      (S.nP + 2 + (S.n + N.nK)) i rl := by
  intro mot q hmot hq xs ys D B C ρq ρc hxs hfit hD hys hfitD hC
  have hS := hok.scoped
  have hN := hok.nest
  have hK := K_law m hok
  have hKS := hK.1
  generalize hφdef : valOf S.recLparams vals = φ at hfit hfitD ⊢
  -- the rule: the container's constructor `i`'s
  have hi : i < N.nK := by
    have := (List.getElem?_eq_some_iff.mp hrl).1; simpa [rules1] using this
  obtain ⟨c, hc⟩ : ∃ c, N.K.ctors[i]? = some c :=
    ⟨N.K.ctors.getD i ⟨"", [], []⟩, by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [nK] using hi)]; rfl⟩
  have hcD : N.K.ctors.getD i ⟨"", [], []⟩ = c := by rw [List.getD_eq_getElem?_getD, hc]; rfl
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hrl' : rl = ⟨c.name, c.fields.length, S.rule1Rhs N c i, some (N.lsK, S.classArgs N 0), false⟩ := by
    simp only [rules1, List.getElem?_map, List.getElem?_range hi, Option.map_some, hcD,
      Option.some.injEq] at hrl
    exact hrl.symm
  subst hrl'
  rw [motivePos_rec1Type] at hmot
  cases hmot
  rw [minorsOf_rec1Type, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at hq
  subst hq
  obtain ⟨ps, m', m1, mins, minsK, rfl, hps, hmins, hminsK⟩ := split_prefixN hxs
  have R₃ := reader₃N hs m hok φ
  have hidxM := fun ps hp => memberIdx_fits hs m hok φ (ps := ps) hp
  -- the values before the major
  have hsplit : S.rec1Ctx N = [S.classTy N (S.oN N)] ++ (S.extrasN N ++ S.params) := by
    simp [rec1Ctx]
  rw [rec1Type, hsplit, Expr.mkPis_append, TeleFitV_mkPis _ _ (by
    rw [length_extras_params]; simp [hps, hmins, hminsK]; omega)] at hfit
  rw [show (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse).reverse
      = minsK ++ mins ++ [m1, m'] ++ ps by simp,
    FitsVals_append _ _ (by simp [length_extrasN, hmins, hminsK, oN]; omega)] at hfit
  obtain ⟨hpF, hE⟩ := hfit
  obtain ⟨hm, hm1, hmn, hmnK⟩ := (fits_extrasN_iff' m φ base hminsK hmins).mp hE
  have hp := (R₃.R.fits_params hS).mp hpF
  -- the minor premise's domain and the values before it
  obtain ⟨minsKE, hminsKE⟩ : ∃ l, l = (minsK.reverse.take i).reverse := ⟨_, rfl⟩
  have hlE : minsKE.length = i := by simp [hminsKE, hminsK]; omega
  have htake : (ps.reverse ++ [m', m1] ++ mins.reverse ++ minsK.reverse).take (S.nP + 2 + S.n + i) =
      (minsKE ++ mins ++ [m1, m'] ++ ps).reverse := by
    rw [show S.nP + 2 + S.n + i = (ps.reverse ++ [m', m1] ++ mins.reverse).length + i by
        simp [hps, hmins]; omega,
      List.take_length_add_append, hminsKE]
    simp
  rw [rec1Type, htake] at hD
  have hpos : (S.rec1Ctx N).reverse[S.nP + 2 + S.n + i]? = some (S.minorTyK N c i) := by
    rw [rec1Ctx_reverse, List.getElem?_append_left
      (by rw [List.length_reverse, length_extras_params]; omega), extras_at_minorK hi, hcD]
  obtain ⟨B', hB'⟩ := Expr.piBodyV_mkPis_at hpos (vs := (minsKE ++ mins ++ [m1, m'] ++ ps).reverse)
    (by simp [hlE, hps, hmins]; omega) base
  rw [hB', List.reverse_reverse] at hD
  simp only [Option.some.injEq, Prod.mk.injEq, Expr.pi.injEq] at hD
  obtain ⟨⟨rfl, -⟩, rfl⟩ := hD
  have hρq : consList (minsKE ++ mins ++ [m1, m'] ++ ps) base
      = consList (minsKE ++ mins ++ [m1, m']) (consList ps base) := by
    simp [consList_append]
  have hos : (minsKE ++ mins ++ [m1, m']).length = 2 + S.n + i := by simp [hlE, hmins]; omega
  -- the fields: the translated constructor's
  have hys' : ys.length = (S.classCtor N c).fields.length := by
    rw [hys]; exact (S.length_classFields N c.fields).symm
  rw [minorTyK_shape] at hfitD
  obtain ⟨fs, hfsdef⟩ : ∃ l, l = ys.reverse := ⟨_, rfl⟩
  have hfs := ((TeleFitV_mkPis_append _ _ (Γ := S.fieldCtxAt (S.classCtor N c) (2 + S.n + i))
    (vs := ys) (ws := []) (by simp [hys', length_fieldCtxAt])).mp
    (by rw [List.append_nil]; exact hfitD)).1
  rw [← hfsdef, hρq] at hfs
  have hf' : fs.length = (S.classCtor N c).fields.length := by simp [hfsdef, hys']
  unfold fieldCtxAt at hfs
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hos] at hfs
  have hwd1 : CtxWD (S.M₃N m.M N) φ base (S.rec1Ctx N) := by
    have := wd_rec1Type hs m hok φ base
    rw [rec1Type_eq, WellDenoted_mkPis] at this
    exact this.1
  have hwd := wdFieldCtxK (wd_extrasN_of_rec1Ctx hwd1 hpF) hmins hminsK hm hm1 hmn hmnK i c hc
  have hiff := R₃.R.fits_fieldCtx hS (nestFit hs m hok _) (S.classCtor_fieldScoped N hS hN hKS hcm)
    hps hp hwd (vs := fs)
  have hfitF := hiff.1.mp hfs
  -- the conclusion: the class's motive at the container's constructor value
  rw [minorTyK_shape, piBodyV_mkPis (by simp [hys', length_fieldCtxAt]), Option.map_some,
    conclV_mkPis, conclV_mkAppN_bvar, Option.some.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl⟩ := hC
  rw [Expr.args_mkAppN, Expr.args_bvar, List.nil_append, ← hfsdef, hρq]
  dsimp only
  have hmaj : interp (S.M₃N m.M N) φ
      (consList (List.replicate (IndSpec.ihCtxAt (S.classCtor N c) (2 + S.n + i)).length pt)
        (consList fs (consList (minsKE ++ mins ++ [m1, m']) (consList ps base))))
      (Expr.mkAppN (.const c.name N.lsK)
        (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
            (2 + S.n + i)) ++
          Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length))
      = N.KS.ctorVal (S.lsK (S.lparams.map φ) N) i fs := by
    have hl : (List.replicate (IndSpec.ihCtxAt (S.classCtor N c) (2 + S.n + i)).length (pt : V)).length
        = (S.classCtor N c).recFields.length := by simp [length_ihCtxAt]
    cases hz : S.z (S.lparams.map φ)
    · have hzK : N.KS.z (S.lsK (S.lparams.map φ) N) = false := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      have hfitCl := (S.ClassFits_iff_FitsFields N hN _ ps (fam_adm hs m hok _ ps _ hp (hidxM ps hp))
        c.fields).mpr hfitF
      rw [Reader.classCtorApp_eq S N hS R₃.R hN (nestFacts hs m hok _) hKS hK.2.2.2.2.2.1
        (K_ctors_stored m hok) hz hc hl hf' hos hps hp (hidxM ps hp) hfitCl]
      simp [ctorVal, hzK, KS_tagOf]
    · have hzK : N.KS.z (S.lsK (S.lparams.map φ) N) = true := by
        rw [(nestFacts hs m hok _).z_eq]; exact hz
      rw [Reader.classCtorApp_read hS R₃.R hN (K_ctors_stored m hok i c hc) hl hf' hos hps hp
        (hidxM ps hp), hK.2.2.2.2.2.1 i c hc, KS_ctorSet_eq_pt m.M _ hzK, appList_pt]
      simp [ctorVal, hzK]
  simp only [List.map_cons, List.map_nil]
  rw [hmaj]
  -- the ι equation at the container's constructor value
  have hφ : Level.substVal φ S.recLparams (vals.map Level.ofNat) = φ := by
    rw [← hφdef]; exact Level.substVal_ofNat _ _ hvals
  have core := (rule1_coreB hs m hok φ base (us := vals.map Level.ofNat)
    (by simpa [rec1Info] using hvals) hc hps hmins hminsK hf' (by rw [hφ]; exact hp)
    (by rw [hφ]; exact hm) (by rw [hφ]; exact hm1) (by rw [hφ]; exact hmn) (by rw [hφ]; exact hmnK)
    (by rw [hφ]; exact hfitF)).1
  simp only [rec1Info] at core
  rw [Level.map_eval_ofNat, hφ, interp_instL, hφ] at core
  simpa [hfsdef, List.append_assoc] using core

end IndSpec

end Fragment
