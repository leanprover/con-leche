module

public import ConLeche.Model.AxiomPin
import ConLeche.Verify.OfReducePin
import ConLeche.Model.AxiomMem

public section

/-!
# `DeclAxiomRun`'s `ofReduceNat`/`ofReduceBool` branch (task #161)

* **the membership is three `pt_mem_piV_of`s.**  The pin's innermost
  codomain is an `Eq`-spine over the *nose-pinned* `Eq`
  (`ofReduceAxOk`'s own first conjunct), whose value at two elements is
  a truth value (`eq_law`); so every function space of the telescope
  reads as a truth value (`piV_eq_zero`), the witness is `pt`, and
  `.prf` is the leaf that denotes `pt`;
* **the innermost fibre needs the `ReduceOps` field** of `EnvModelM`.
  The hypothesis spine reads to `eqv (op x) y` and the conclusion to
  `eqv x y`; `eq_law` gives both values and `ReduceOps` collapses `op x`
  to `x`, so an inhabitant of the one inhabits the other.

`axiomStepPB_of` (`Model/Fold.lean`) assembles the four branches.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The pinned telescope, inverted -/

/-- **The `ofReduce*` pinned telescope**, read off the pin (the pin
comparison is plain equality). -/
theorem ofReduce_shapeS {n : Name} {type' : Expr}
    (hn : n = ConLeche.ofReduceNatName ∨ n = ConLeche.ofReduceBoolName)
    (h : type'
      = (ConLeche.ofReducePinA n).type) :
    type' = .forallE
        (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp n)) [])
        (.forallE
          (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp n)) [])
          (.forallE
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp n)) []))
              (.app (.const (ConLeche.ofReduceOp n) []) (.bvar 1)))
              (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp n)) []))
              (.bvar 2)) (.bvar 1)))) := by
  rw [ConLeche.Verify.ofReducePin_type hn] at h
  simp only [Expr.mkAppN] at h
  subst h
  rfl

/-! ## The gates, unpacked -/

/-- `ofReduceAxOk`'s four conjuncts, in the forms the membership
reads. -/
theorem ofReduce_gatesS {cv : ConstantVal}
    (hok : ConLeche.ofReduceAxOk env cv = true) :
    env.find? eqName = some eqA ∧
    ConLeche.reduceElemOk env (ConLeche.ofReduceOp cv.name) = true ∧
    (∃ cvR, env.find? (ConLeche.ofReduceOp cv.name)
        = some (.axiomInfo cvR) ∧
      ConstantVal.matchesPin cvR
        (ConLeche.reduceOpCvA (ConLeche.ofReduceOp cv.name)) = true) ∧
    cv.type
      = (ConLeche.ofReducePinA cv.name).type := by
  simp only [ConLeche.ofReduceAxOk, Bool.and_eq_true,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hEq, helem⟩, hstored⟩, hpin⟩ := hok
  refine ⟨hEq, helem, ?_, ?_⟩
  · rw [ConLeche.reduceStoredOk] at hstored
    cases hf : env.find? (ConLeche.ofReduceOp cv.name) with
    | none => rw [hf] at hstored; exact nomatch hstored
    | some ci =>
      rw [hf] at hstored
      cases ci with
      | axiomInfo cvR => exact ⟨cvR, rfl, hstored⟩
      | _ => exact nomatch hstored
  · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hpin
    exact hpin.2

/-! ## The membership -/

/-- **`ofReduce*`'s canonical proof inhabits its stored type's
reading.**  Three `pt_mem_piV_of`s (every fibre is an equality's truth
value, so every function space is a truth value); the innermost fibre is
where `ReduceOps` pays: the hypothesis spine's value is `eqv (op x) y`, the conclusion's
is `eqv x y`, and the field says those are the same set. -/
theorem ofReduce_mem (mp : EnvModelM V μ env)
    {cv : ConstantVal} (hok : ConLeche.ofReduceAxOk env cv = true)
    (hor : cv.name = ConLeche.ofReduceNatName ∨
      cv.name = ConLeche.ofReduceBoolName)
    (ψ : Name → Nat) (ta : Term)
    (hta : denote mp.base2.acval env ψ 0 cv.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (Term.prf) ∈ˢ interp V ρ ta := by
  obtain ⟨hEq, helem, ⟨cvR, hfR, hmpR⟩, hApinT⟩ := ofReduce_gatesS hok
  obtain ⟨ciE, hfE, hlpE, htyE⟩ := ConLeche.Verify.reduceElem_sort helem
  obtain ⟨-, hlpR⟩ := ConLeche.Verify.matchesPin_invT hmpR
  rw [show (ConLeche.reduceOpCvA
      (ConLeche.ofReduceOp cv.name)).levelParams = [] from by
    unfold ConLeche.reduceOpCvA; split <;> rfl] at hlpR
  have hmemOp : ConLeche.ofReduceOp cv.name ∈ ConLeche.reduceOpNames := by
    unfold ConLeche.ofReduceOp; split <;> decide
  have hsh := ofReduce_shapeS hor hApinT
  rw [hsh] at hta
  -- the `Eq` former's one level parameter is pinned to `1`
  have heqψ : Level.substFn ψ eqA.toConstantVal.levelParams
      [Level.zero.succ] uN = 1 := rfl
  have hEd : ∀ e, denote mp.base2.acval env ψ e
      (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) [])
      = some (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) :=
    fun e => denote_levelless_const hfE hlpE
  have hOd : ∀ e, denote mp.base2.acval env ψ e
      (.const (ConLeche.ofReduceOp cv.name) [])
      = some (mp.base2.acval (ConLeche.ofReduceOp cv.name) ψ) :=
    fun e => denote_levelless_const hfR
      (show (ConstantInfo.axiomInfo cvR).toConstantVal.levelParams = []
        from hlpR)
  have hQd : ∀ e, denote mp.base2.acval env ψ e
      (.const eqName [Level.zero.succ])
      = some (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) :=
    fun e => denote_const hEq rfl
  -- the stored type's reading
  have hden : denote mp.base2.acval env ψ 0
      (.forallE
        (.const (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) [])
        (.forallE
          (.const (ConLeche.reduceElemName
            (ConLeche.ofReduceOp cv.name)) [])
          (.forallE
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp cv.name)) []))
              (.app (.const (ConLeche.ofReduceOp cv.name) []) (.bvar 1)))
              (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.const (ConLeche.reduceElemName
                  (ConLeche.ofReduceOp cv.name)) []))
              (.bvar 2)) (.bvar 1)))))
      = some (.pi (mp.base2.acval (ConLeche.reduceElemName
            (ConLeche.ofReduceOp cv.name)) ψ)
          (.pi (mp.base2.acval (ConLeche.reduceElemName
              (ConLeche.ofReduceOp cv.name)) ψ)
            (.pi (.app (.app (.app (mp.base2.acval eqName
                    (Level.substFn ψ eqA.toConstantVal.levelParams
                      [Level.zero.succ]))
                  (mp.base2.acval (ConLeche.reduceElemName
                    (ConLeche.ofReduceOp cv.name)) ψ))
                (.app (mp.base2.acval (ConLeche.ofReduceOp cv.name) ψ)
                  (.bvar 1))) (.bvar 0))
              (.app (.app (.app (mp.base2.acval eqName
                    (Level.substFn ψ eqA.toConstantVal.levelParams
                      [Level.zero.succ]))
                  (mp.base2.acval (ConLeche.reduceElemName
                    (ConLeche.ofReduceOp cv.name)) ψ))
                (.bvar 2)) (.bvar 1))))) := by
    simp [denote_forallE, denote_app, denote_fvar,
      Expr.instantiate1, hEd, hOd, hQd]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  -- the three leaves' interpretations do not read the environment
  have hclE : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ)
        = interp V ρ (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  have hclO : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval (ConLeche.ofReduceOp cv.name) ψ)
        = interp V ρ (mp.base2.acval (ConLeche.ofReduceOp cv.name) ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  have hclQ : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval eqName
          (Level.substFn ψ eqA.toConstantVal.levelParams
            [Level.zero.succ]))
        = interp V ρ (mp.base2.acval eqName
          (Level.substFn ψ eqA.toConstantVal.levelParams
            [Level.zero.succ])) :=
    fun ρ' => acval_interp_closed mp.base2 _ _ ρ' ρ
  -- the element type inhabits `Sort 1`
  have hEmem : interp V ρ (mp.base2.acval
      (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ)
      ∈ˢ (univ 1 : V) := by
    have h := mp.mem_type ciE (ConLeche.Env.find?_mem hfE) ψ
      (.sort 1) (by rw [htyE, denote_sort]; rfl) ρ
    rwa [ConLeche.Env.find?_name hfE, interp_sort] at h
  -- the `Eq` spine at two elements is their equality's truth value
  have hQ : ∀ x y, x ∈ˢ interp V ρ (mp.base2.acval
        (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) →
      y ∈ˢ interp V ρ (mp.base2.acval
        (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) →
      SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])))
        (interp V ρ (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ))) x) y
        = eqv x y :=
    fun x y hx hy => (mp.eq_law hEq _).1 ρ _ x y (by rw [heqψ]; exact hEmem) hx hy
  -- **the field pays here**: the trusted operation is the identity
  have hopx : ∀ x, x ∈ˢ interp V ρ (mp.base2.acval
        (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) →
      SetTheory.app (interp V ρ
        (mp.base2.acval (ConLeche.ofReduceOp cv.name) ψ)) x = x :=
    fun x hx => (mp.reduce_ops _ hmemOp cvR hfR hmpR).2 ψ ρ x hx
  -- three truth-valued function spaces (every fibre is an equality),
  -- all `pt`-inhabited
  show (pt : V) ∈ˢ _
  simp only [interp_pi, interp_app, interp_bvar, cons_zero,
    cons_succ, hclE, hclO, hclQ]
  have htv : ∀ x y, x ∈ˢ interp V ρ (mp.base2.acval
        (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) →
      y ∈ˢ interp V ρ (mp.base2.acval
        (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ) →
      SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])))
        (interp V ρ (mp.base2.acval
          (ConLeche.reduceElemName (ConLeche.ofReduceOp cv.name)) ψ))) x) y
        ∈ˢ (univZero : V) :=
    fun x y hx hy => by rw [hQ x y hx hy]; exact eqv_mem_univZero x y
  refine pt_mem_piV_of fun x hx =>
    ⟨piV_mem_univZero_of fun y hy => piV_mem_univZero_of fun _ _ => htv x y hx hy,
      pt_mem_piV_of fun y hy =>
        ⟨piV_mem_univZero_of fun _ _ => htv x y hx hy,
          pt_mem_piV_of fun h hh => ⟨htv x y hx hy, ?_⟩⟩⟩
  rw [hopx x hx, hQ x y hx hy] at hh
  rw [hQ x y hx hy, eq_of_mem_eqv hh]
  exact pt_mem_eqv_self y

/-! ## The branch -/

/-- **The `ofReduce*` branch, discharged.**  The leaf is `.prf`, the
canonical proof, which is why every syntactic obligation is `rfl`
or a `simp` on a leaf clause and the whole content is the
membership. -/
theorem axiomOfReduce (hμ : μ.isVerified = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hor : cv.name = ConLeche.ofReduceNatName ∨
      cv.name = ConLeche.ofReduceBoolName)
    (hok : ConLeche.ofReduceAxOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    CoverStep mp
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hnd, hlbt, hitf, hann, htp, htr,
    -⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  have hwfc : ConLeche.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts, env.tables⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  refine harvestAxiom (V := V) hμ mp hcv
    (A := fun _ => Term.prf) (fun _ => trivial)
    (fun _ _ _ => rfl) (fun _ _ => by simp) ?_
    (by rcases hor with h | h <;> rw [h] <;> decide)
  intro ψ ta hta ρ
  exact ofReduce_mem mp hok hor ψ ta hta ρ

end ConLeche.Model
