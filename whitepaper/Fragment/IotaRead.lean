module

public import Fragment.InstallIota

@[expose] public section

/-!
# The rules read off a recursor's own type

`RuleHolds` (`IsModel.lean`) reads a recursor's rule off the
recursor's type: the minor premise of the rule's position among the
minors of the recursor's motive (`minorsOf`), its fields, and its
conclusion's arguments as the indices and the major.  This file shows
that the generated recursor of a plain block satisfies it in the model
the checker's installation builds (`IndSpec.rule_holds`).

The syntactic half computes the reading on the generated type: the
motive is the binder after the parameters (`motivePos_recType`), the
minors of it are the block's minor premises in order
(`minorsOf_recType`), so rule `j`, the rule of constructor `j`, reads
minor premise `j`; behind its fields and its induction hypotheses
(`conclV_mkPis`) the conclusion is the motive at the constructor's
index expressions and the constructor applied.

The semantic half: values fitting the recursor's first binders split
as the parameters, the motive and the minors; values fitting the minor
premise's fields fit the constructor's fields at the recursor's
parameters (`Reader.fits_fieldCtx`); the conclusion's arguments read
as the constructor's index values and its value at the fields
(`Reader₂.read_concl_args`); and the ι equation at the constructor
value is `rec_rule_core` (`InstallIota.lean`), which holds
unconditionally.
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u

/-! ## The syntactic readings on generated telescopes -/

namespace Expr

theorem piCount_mkPis : ∀ (Γ : List Expr) (b : Expr), (mkPis Γ b).piCount = b.piCount + Γ.length
  | [], _ => rfl
  | A :: Γ, b => by
    rw [mkPis_cons, piCount_mkPis Γ, piCount, List.length_cons]; omega

theorem piConcl_mkPis : ∀ (Γ : List Expr) (b : Expr), (mkPis Γ b).piConcl = b.piConcl
  | [], _ => rfl
  | A :: Γ, b => by rw [mkPis_cons, piConcl_mkPis Γ]; rfl

theorem piDom?_mkPis_lt : ∀ (Γ : List Expr) (b : Expr) (q : Nat), q < Γ.length →
    (mkPis Γ b).piDom? q = Γ.reverse[q]?
  | [], _, _, h => by simp at h
  | A :: Γ, b, q, h => by
    rw [mkPis_cons, List.reverse_cons]
    by_cases hq : q < Γ.length
    · rw [piDom?_mkPis_lt Γ _ q hq, List.getElem?_append_left (by simpa using hq)]
    · have hq' : q = Γ.length := by simp at h; omega
      subst hq'
      have h0 := piDom?_mkPis_ge Γ (A.pi b) 0
      rw [Nat.add_zero] at h0
      rw [h0, List.getElem?_append_right (by simp)]
      simp [piDom?]
where
  piDom?_mkPis_ge : ∀ (Γ : List Expr) (b : Expr) (q : Nat),
      (mkPis Γ b).piDom? (Γ.length + q) = b.piDom? q
    | [], _, q => by simp
    | A :: Γ, b, q => by
      rw [mkPis_cons, List.length_cons, show Γ.length + 1 + q = Γ.length + (q + 1) by omega,
        piDom?_mkPis_ge Γ]
      rfl

theorem head_mkAppN : ∀ (f : Expr) (as : List Expr), (mkAppN f as).head = f.head
  | _, [] => rfl
  | f, a :: as => by rw [mkAppN_cons, head_mkAppN]; rfl

theorem args_mkAppN : ∀ (f : Expr) (as : List Expr), (mkAppN f as).args = f.args ++ as
  | _, [] => by simp
  | f, a :: as => by rw [mkAppN_cons, args_mkAppN, args]; simp

theorem args_bvar (k : Nat) : (Expr.bvar k).args = [] := rfl

/-- An application spine headed by a variable is no `∀`. -/
theorem mkAppN_bvar_cases (k : Nat) (as : List Expr) :
    mkAppN (.bvar k) as = .bvar k ∨ ∃ f a, mkAppN (.bvar k) as = .app f a := by
  rcases List.eq_nil_or_concat as with rfl | ⟨as, a, rfl⟩
  · exact .inl rfl
  · rw [List.concat_eq_append, mkAppN_append]
    exact .inr ⟨_, _, rfl⟩

theorem piConcl_mkAppN_bvar (k : Nat) (as : List Expr) :
    (mkAppN (.bvar k) as).piConcl = mkAppN (.bvar k) as := by
  rcases mkAppN_bvar_cases k as with h | ⟨f, a, h⟩ <;> rw [h] <;> rfl

theorem piCount_mkAppN_bvar (k : Nat) (as : List Expr) : (mkAppN (.bvar k) as).piCount = 0 := by
  rcases mkAppN_bvar_cases k as with h | ⟨f, a, h⟩ <;> rw [h] <;> rfl

theorem headVar?_mkAppN_bvar (k : Nat) (as : List Expr) :
    (mkAppN (.bvar k) as).headVar? = some k := by
  simp only [headVar?, head_mkAppN, head]

/-- **The domain at a position of a telescope with a given value
prefix**: the binder `q` of `∀ Γ, b` is the `q`-th of `Γ` from the
outside, and the walk along `q` values stops in front of it. -/
theorem piBodyV_mkPis_at {V : Type u} {Γ : List Expr} {b A : Expr} {q : Nat}
    (hA : Γ.reverse[q]? = some A) {vs : List V} (hv : vs.length = q) (ρ : Nat → V) :
    ∃ B, piBodyV ρ (mkPis Γ b) vs = some (.pi A B, consList vs.reverse ρ) := by
  have hq : q < Γ.length := by
    have := (List.getElem?_eq_some_iff.mp hA).1; simpa using this
  obtain ⟨Γ₂, Γ₁, hΓ, hl⟩ : ∃ Γ₂ Γ₁, Γ = Γ₂ ++ A :: Γ₁ ∧ Γ₁.length = q := by
    refine ⟨(Γ.reverse.drop (q + 1)).reverse, (Γ.reverse.take q).reverse, ?_, by simp; omega⟩
    have hlt : q < Γ.reverse.length := by simpa using hq
    have h1 : Γ.reverse = Γ.reverse.take q ++ A :: Γ.reverse.drop (q + 1) := by
      have hget : Γ.reverse[q] = A := by
        rw [List.getElem?_eq_getElem hlt] at hA; exact Option.some.inj hA
      rw [← hget, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
    calc Γ = Γ.reverse.reverse := by simp
      _ = (Γ.reverse.take q ++ A :: Γ.reverse.drop (q + 1)).reverse := by rw [← h1]
      _ = _ := by simp
  subst hΓ
  refine ⟨mkPis Γ₂ b, ?_⟩
  rw [mkPis_append, mkPis_cons, piBodyV_mkPis (by rw [hv, hl])]

end Expr

/-- `conclV` behind a context: every binder read as the point. -/
theorem conclV_mkPis {V : Type u} [SetLib V] : ∀ (Γ : List Expr) (b : Expr) (ρ : Nat → V),
    conclV ρ (Expr.mkPis Γ b) = conclV (consList (List.replicate Γ.length pt) ρ) b
  | [], _, _ => rfl
  | A :: Γ, b, ρ => by rw [Expr.mkPis_cons, conclV_mkPis Γ]; rfl

/-- `conclV` at an application spine headed by a variable: the spine
itself. -/
theorem conclV_mkAppN_bvar {V : Type u} [SetLib V] (ρ : Nat → V) (k : Nat) (as : List Expr) :
    conclV ρ (Expr.mkAppN (.bvar k) as) = (Expr.mkAppN (.bvar k) as, ρ) := by
  rcases Expr.mkAppN_bvar_cases k as with h | ⟨f, a, h⟩ <;> rw [h] <;> rfl

/-- The middle of three lists. -/
theorem getElem?_mid {α : Type _} (L₁ L L₂ : List α) {j : Nat} (hj : j < L.length) :
    (L₁ ++ L ++ L₂)[L₁.length + j]? = L[j]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

/-- **A filter over a range that keeps exactly an interval.** -/
theorem filter_range_interval (p : Nat → Bool) (a n e : Nat) (hlo : ∀ q < a, p q = false)
    (hin : ∀ j < n, p (a + j) = true) (hhi : ∀ j < e, p (a + n + j) = false) :
    (List.range (a + n + e)).filter p = (List.range n).map (a + ·) := by
  rw [List.range_add, List.range_add, List.filter_append, List.filter_append]
  rw [List.filter_eq_nil_iff.mpr (fun q hq => by simp [hlo q (List.mem_range.mp hq)]),
    List.filter_eq_self.mpr (fun q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq; exact hin j (List.mem_range.mp hj)),
    List.filter_eq_nil_iff.mpr (fun q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq; simp [hhi j (List.mem_range.mp hj)])]
  simp

/-! ## Level values -/

/-- A natural number as a level: `succ` iterated on `zero`. -/
def Level.ofNat : Nat → Level
  | 0 => .zero
  | k + 1 => .succ (Level.ofNat k)

@[simp] theorem Level.eval_ofNat (φ : Name → Nat) : ∀ k, Level.eval φ (Level.ofNat k) = k
  | 0 => rfl
  | k + 1 => by simp [Level.ofNat, Level.eval_ofNat φ k]

theorem Level.map_eval_ofNat (φ : Name → Nat) (vals : List Nat) :
    (vals.map Level.ofNat).map (Level.eval φ) = vals := by
  simp [List.map_map, Function.comp_def]

/-- **Instantiating the level parameters at values is the valuation of
the values**: at the parameters' positional valuation, substituting
the values as levels changes nothing. -/
theorem Level.substVal_ofNat (ps : List Name) (vals : List Nat) (hl : vals.length = ps.length) :
    Level.substVal (valOf ps vals) ps (vals.map Level.ofNat) = valOf ps vals := by
  funext n
  by_cases hn : n ∈ ps
  · rw [← valOf_map_eval (valOf ps vals) (by simpa using hl) hn, Level.map_eval_ofNat]
  · simp only [Level.substVal, Level.lookupLevel]
    rw [lookup_zip_none hn]
    rfl

/-! ## The plain recursor -/

namespace IndSpec

variable {V : Type u} [IndLib V] [LevelOracle] {env : Env} {S : IndSpec}

omit [IndLib V] [LevelOracle] in
/-- The recursor's binders, outermost first. -/
theorem recCtx_reverse :
    S.recCtx.reverse = (S.params.reverse ++ [S.motiveTy]) ++
      (List.range S.n).map (fun j => S.minorTy (S.ctors.getD j ⟨"", [], []⟩) j) ++
      ((S.indicesAt (S.n + 1)).reverse ++ [S.famVars (S.n + 1)]) := by
  simp [recCtx, minorsCtx, List.reverse_append]

omit [IndLib V] [LevelOracle] in
/-- The binder at the position of minor premise `j`. -/
theorem recCtx_reverse_minor {j : Nat} (hj : j < S.n) :
    S.recCtx.reverse[S.nP + 1 + j]? = some (S.minorTy (S.ctors.getD j ⟨"", [], []⟩) j) := by
  rw [recCtx_reverse, show S.nP + 1 + j = (S.params.reverse ++ [S.motiveTy]).length + j by
    simp [nP], getElem?_mid _ _ _ (by simpa using hj)]
  simp [hj]

omit [IndLib V] [LevelOracle] in
theorem minorTy_shape (c : CtorSpec) (j : Nat) :
    S.minorTy c j = Expr.mkPis (S.fieldCtxAt c (j + 1))
      (Expr.mkPis (IndSpec.ihCtx c j)
        (Expr.mkAppN (.bvar (c.recFields.length + c.fields.length + j))
          (c.idx.map (Expr.atCtx c.fields.length c.fields.length c.recFields.length (j + 1) 0) ++
            [Expr.mkAppN (.const c.name S.lvls)
              (Expr.varsAt (c.recFields.length + c.fields.length + j + 1) S.nP ++
                Expr.varsAt c.recFields.length c.fields.length)]))) := by
  rw [minorTy, Expr.mkPis_append]

omit [IndLib V] [LevelOracle] in
theorem length_ihCtx (c : CtorSpec) (j : Nat) : (IndSpec.ihCtx c j).length = c.recFields.length := by
  simp [ihCtx]

omit [IndLib V] [LevelOracle] in
/-- **The motive of the recursor's type** is the binder after the
parameters. -/
theorem motivePos_recType : S.recType.motivePos = some S.nP := by
  rw [recType_eq]
  simp only [Expr.motivePos, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
    Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_recCtx, Option.map_some]
  congr 1
  omega

omit [IndLib V] [LevelOracle] in
/-- **The minors of the recursor's motive** are the block's minor
premises, in order: rule `j` reads minor premise `j`. -/
theorem minorsOf_recType :
    minorsOf S.recType (S.nP + 1 + S.n) S.nP = (List.range S.n).map (S.nP + 1 + ·) := by
  unfold minorsOf
  rw [show S.nP + 1 + S.n = S.nP + 1 + S.n + 0 by rfl]
  refine filter_range_interval _ _ _ _ (fun q hq => ?_) (fun j hj => ?_) (fun j hj => by omega)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left; omega
  · rw [recType_eq, Expr.piDom?_mkPis_lt _ _ _ (by rw [length_recCtx]; omega),
      recCtx_reverse_minor hj]
    simp only [minorTy_shape, Expr.piConcl_mkPis, Expr.piCount_mkPis, Expr.piConcl_mkAppN_bvar,
      Expr.headVar?_mkAppN_bvar, Expr.piCount_mkAppN_bvar, length_ihCtx, length_fieldCtxAt]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq]
    omega

variable (hpl : S.nest = none) (hs : Env.Scoped env) (m : EnvModel V env) (hok : S.Ok env)
include hpl hs m hok

/-- **The generated recursor's rules hold, read off its type**
(`RuleHolds`, `IsModel.lean`), in the model of the installed block. -/
theorem rule_holds (vals : List Nat) (hvals : vals.length = S.recLparams.length)
    {i : Nat} {rl : RecRule} (hrl : S.rules[i]? = some rl) :
    RuleHolds (S.M₃ m.M) (valOf S.recLparams vals) (S.M₃ m.M S.recName vals) S.recType
      (S.nP + 1 + S.n) i rl := by
  intro mot q hmot hq xs ys D B C ρq ρc hxs hfit hD hys hfitD hC
  have hS := hok.scoped
  generalize hφdef : valOf S.recLparams vals = φ at hfit hfitD ⊢
  -- the rule: constructor `i`'s
  have hi : i < S.n := by
    have := (List.getElem?_eq_some_iff.mp hrl).1; simpa [rules] using this
  obtain ⟨c, hc⟩ : ∃ c, S.ctors[i]? = some c :=
    ⟨S.ctors.getD i ⟨"", [], []⟩, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl⟩
  have hcD : S.ctors.getD i ⟨"", [], []⟩ = c := by rw [List.getD_eq_getElem?_getD, hc]; rfl
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hrl' : rl = ⟨c.name, c.fields.length, S.ruleRhs c i, none, S.isK⟩ := by
    simp only [rules, List.getElem?_map, List.getElem?_range hi, Option.map_some, hcD,
      Option.some.injEq] at hrl
    exact hrl.symm
  subst hrl'
  -- the minor premise read: `i`'s
  rw [motivePos_recType] at hmot
  cases hmot
  rw [minorsOf_recType, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at hq
  subst hq
  -- the values before the indices: the parameters, the motive, the minors
  obtain ⟨ps, m', mins, rfl, hps, hmins⟩ : ∃ (ps : List V) (m' : V) (mins : List V),
      xs = ps.reverse ++ [m'] ++ mins.reverse ∧ ps.length = S.nP ∧ mins.length = S.n := by
    obtain ⟨m', rest, hd⟩ : ∃ m' rest, xs.drop S.nP = m' :: rest := by
      cases hd : xs.drop S.nP with
      | nil => have := congrArg List.length hd; simp [hxs] at this; omega
      | cons m' rest => exact ⟨m', rest, rfl⟩
    have hrest : rest.length = S.n := by
      have := congrArg List.length hd; simp [hxs] at this; omega
    refine ⟨(xs.take S.nP).reverse, m', rest.reverse, ?_, by simp [hxs]; omega, by simp [hrest]⟩
    rw [List.reverse_reverse, List.reverse_reverse, List.append_assoc, List.singleton_append, ← hd,
      List.take_append_drop]
  have R₃ := reader₃ hpl hok m.M φ
  rw [recType_eq] at hfit hD
  have hsplit : S.recCtx = (S.famVars (S.n + 1) :: S.indicesAt (S.n + 1)) ++
      (S.minorsCtx ++ [S.motiveTy] ++ S.params) := by simp [recCtx]
  rw [hsplit, Expr.mkPis_append, TeleFitV_mkPis _ _ (by simp [hps, hmins, length_minorsCtx, nP]; omega)]
    at hfit
  rw [show (ps.reverse ++ [m'] ++ mins.reverse).reverse = mins ++ [m'] ++ ps by simp] at hfit
  rw [FitsVals_append _ _ (by simp [hmins, length_minorsCtx]),
    FitsVals_append _ _ (by simp [hmins, length_minorsCtx])] at hfit
  obtain ⟨hpF, hmF, hmn⟩ := hfit
  simp only [FitsVals_cons, FitsVals_nil_nil, true_and, consList_nil] at hmF
  have hp := (R₃.R.fits_params hS).mp hpF
  -- the minor premise's domain and the values before it
  obtain ⟨minsE, hminsE⟩ : ∃ l, l = (mins.reverse.take i).reverse := ⟨_, rfl⟩
  have hlE : minsE.length = i := by simp [hminsE, hmins]; omega
  have htake : (ps.reverse ++ [m'] ++ mins.reverse).take (S.nP + 1 + i) =
      (minsE ++ [m'] ++ ps).reverse := by
    rw [show S.nP + 1 + i = (ps.reverse ++ [m']).length + i by simp [hps],
      List.take_length_add_append, hminsE]
    simp
  rw [htake] at hD
  have hpos : S.recCtx.reverse[S.nP + 1 + i]? = some (S.minorTy c i) := by
    rw [recCtx_reverse_minor hi, hcD]
  obtain ⟨B', hB'⟩ := Expr.piBodyV_mkPis_at hpos (vs := (minsE ++ [m'] ++ ps).reverse)
    (by simp [hlE, hps]; omega) base
  rw [hB', List.reverse_reverse] at hD
  simp only [Option.some.injEq, Prod.mk.injEq, Expr.pi.injEq] at hD
  obtain ⟨⟨rfl, -⟩, rfl⟩ := hD
  have hρq : consList (minsE ++ [m'] ++ ps) base = consList (minsE ++ [m']) (consList ps base) := by
    simp [consList_append]
  have hos : (minsE ++ [m']).length = i + 1 := by simp [hlE]
  -- the fields
  have hys' : ys.length = c.fields.length := hys
  rw [minorTy_shape] at hfitD
  obtain ⟨fs, hfsdef⟩ : ∃ l, l = ys.reverse := ⟨_, rfl⟩
  have hfs := ((TeleFitV_mkPis_append _ _ (Γ := S.fieldCtxAt c (i + 1)) (vs := ys) (ws := [])
    (by simp [hys', length_fieldCtxAt])).mp
    (by rw [List.append_nil]; exact hfitD)).1
  rw [← hfsdef] at hfs
  have hf : fs.length = c.fields.length := by simp [hfsdef, hys']
  rw [hρq] at hfs
  unfold fieldCtxAt at hfs
  rw [FitsVals_liftCtx_liftN _ _ _ _ _ hos] at hfs
  have hwd := (R₃.R.idxFit_of_wd hS hcm (wd_ctorType hpl hs m hok hcm φ base)
    (ty_ctorType hpl hs m hok hcm φ base) (NestFit_of_plain hpl) hps hp).1
  have hiff := R₃.R.fits_fieldCtx hS (NestFit_of_plain hpl) (hS.2.2.2.1 c hcm).1 hps hp hwd (vs := fs)
  have hfitF := hiff.1.mp hfs
  have hidx := hiff.2 hfitF
  -- the conclusion: the constructor's index values, then its value
  rw [minorTy_shape, piBodyV_mkPis (by simp [hys', length_fieldCtxAt]), Option.map_some,
    conclV_mkPis, conclV_mkAppN_bvar, Option.some.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl⟩ := hC
  rw [Expr.args_mkAppN, Expr.args_bvar, List.nil_append, ← hfsdef, hρq]
  dsimp only
  rw [Nat.add_assoc (c.recFields.length + c.fields.length) i 1,
    R₃.read_concl_args hS hok.freshI hc (by simp [length_ihCtx]) hf hos hps hp hfitF hidx]
  -- the ι equation at the constructor value
  have hφ : Level.substVal φ S.recLparams (vals.map Level.ofNat) = φ := by
    rw [← hφdef]; exact Level.substVal_ofNat _ _ hvals
  have hm : m' ∈ˢ interp (S.M₃ m.M) (Level.substVal φ S.recLparams (vals.map Level.ofNat))
      (consList ps base) S.motiveTy := by rw [hφ]; exact hmF
  have hp' : FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams (vals.map Level.ofNat))))
      base S.params ps := by rw [hφ]; exact hp
  have hmn' : FitsVals (S.M₃ m.M) (Level.substVal φ S.recLparams (vals.map Level.ofNat))
      (cons m' (consList ps base)) S.minorsCtx mins := by
    rw [hφ]; simpa [consList_append] using hmn
  have hfitF' : S.FitsFields m.M (S.lparams.map (Level.substVal φ S.recLparams (vals.map Level.ofNat)))
      (S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams (vals.map Level.ofNat))) ps)
      ps c.fields fs := by rw [hφ]; exact hfitF
  have core := (rec_rule_core hpl hs m hok φ base (us := vals.map Level.ofNat) (by simpa using hvals)
    hc hps hmins hf hp' hm hmn' hfitF').1
  rw [Level.map_eval_ofNat, hφ, interp_instL, hφ] at core
  rw [List.take_left' (by simp [hps, hmins]; omega), List.drop_left' (by simp [hps])] at core
  simpa [hfsdef, List.append_assoc] using core

end IndSpec

end Fragment
