module

public import ConLeche.Verify.StdAxiomPin
public import ConLeche.Model.Env.EnvModelM
import ConLeche.Model.NatEqs
import ConLeche.Verify.OfReducePin

public section

/-!
# The pinned axioms' `interp` memberships (task #161)

The standard axioms' forcing arguments at the graded currency.

## The shapes

`matchesPin` is plain equality, so a pinned axiom's stored type, and
its stored companions' (`Iff`, `Iff.rec`, …), are the pins' on the
nose.  The reading takes each binder's regime off the values
(`piV`/`lamV`), so elimination is `app_mem_piV` with no side
condition and the motive's β is `app_lamV`.

## The minor is not built positively

See `iff_forces_eq`: `Classical.byContradiction` on `A = B` makes the
minor's binders vacuous, so the stored `Iff.intro` never appears.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
 )

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

/-! ## Elimination at a reading -/

/-- Elimination at a `pi` reading: no side condition. -/
theorem app_mem_pi {ρ : Nat → V} {Aa Ba : Term}
    {f a : V} (hf : f ∈ˢ interp V ρ (.pi Aa Ba))
    (ha : a ∈ˢ interp V ρ Aa) :
    SetTheory.app f a ∈ˢ interp V (cons a ρ) Ba := by
  rw [interp_pi] at hf
  exact app_mem_piV hf ha

/-- `pt` inhabits a function space whose fibres are inhabited truth
values. -/
theorem pt_mem_piV_of {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ B x) :
    (pt : V) ∈ˢ piV A B := by
  rw [piV_eq_zero fun x hx => (h x hx).1]
  exact pt_mem_piR_zero_of fun x hx => (h x hx).2

/-- A function space whose fibres are truth values is a truth value. -/
theorem piV_mem_univZero_of {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) : piV A B ∈ˢ (univZero : V) := by
  rw [piV_eq_zero h]; exact piR_zero_mem_univZero

/-! ## The stored `Iff` family's shapes

The pin comparison is plain equality, so each stored type is its pin,
read off by unfolding — as `propext_shapeS` does, at three longer
shapes. -/

/-- The stored `Iff` former's shape. -/
theorem iff_shapeS {ty : Expr}
    (h : ty
      = iffA.toConstantVal.type) :
    ty = .forallE (.sort .zero)
      (.forallE (.sort .zero) (.sort .zero)) := by
  simp only [iffA, ConstantInfo.toConstantVal] at h
  subst h
  rfl

/-- The stored `Iff.rec`'s shape.  Five telescope binders and four
nested ones. -/
theorem iffRec_shapeS {ty : Expr}
    (h : ty
      = iffRecA.toConstantVal.type) :
    ty = .forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.forallE
              (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
              (.sort (.param uN)))
            (.forallE
              (.forallE (.forallE (.bvar 2) (.bvar 2))
                (.forallE (.forallE (.bvar 2) (.bvar 4))
                  (.app (.bvar 2)
                    (.app (.app (.app (.app (.const iffIntroName [])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0)))))
              (.forallE
                (.app (.app (.const iffName []) (.bvar 3)) (.bvar 2))
                (.app (.bvar 2) (.bvar 0)))))) := by
  simp only [iffRecA, ConstantInfo.toConstantVal] at h
  subst h
  rfl

/-! ## The stored `Iff` family's `interp` memberships

Each is `mem_type` at the stored constant, its reading computed off
the shape, and `app_mem_pi` once per argument. -/

/-- The stored `Iff`, applied to two propositions, is a proposition. -/
theorem iffVal_app₂_memP (mp : EnvModelM V env)
    {cvI : ConstantVal} {caps : ConLeche.IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (htyI : cvI.type
      = iffA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A B : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V)) :
    SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval iffName ψ)) A) B
      ∈ˢ (univ 0 : V) := by
  have hsh := iff_shapeS htyI
  have hden : denote mp.base2.acval env ψ 0
      (ConstantInfo.indInfo cvI caps).toConstantVal.type
      = some (.pi (.sort 0)
          (.pi (.sort 0) (.sort 0))) := by
    show denote mp.base2.acval env ψ 0 cvI.type = _
    rw [hsh]
    simp [denote_forallE, denote_sort, Expr.instantiate1, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfI) ψ _ hden ρ
  rw [Env.find?_name hfI] at hmem
  have h1 := app_mem_pi hmem (by rw [interp_sort]; exact hA)
  have h2 := app_mem_pi h1 (by rw [interp_sort]; exact hB)
  rw [interp_sort] at h2
  exact h2

/-- **Two mutually inverse implications identify their propositions.** -/
theorem eq_of_impls {A B f g : V} (hA : A ∈ˢ (univ 0 : V))
    (hB : B ∈ˢ (univ 0 : V))
    (hf : f ∈ˢ piV A fun _ => B) (hg : g ∈ˢ piV B fun _ => A) :
    A = B := by
  refine prop_ext hA hB (fun hptA => ?_) (fun hptB => ?_)
  · have h1 := app_mem_piV hf hptA
    rwa [mem_univ_zero hB h1] at h1
  · have h1 := app_mem_piV hg hptB
    rwa [mem_univ_zero hA h1] at h1

/-- **Interpreted `Iff` forces equality of truth values, at the graded
currency.**

The minor is not built *positively* (by applying the stored
`Iff.intro` to the recursor's own minor arguments): `Classical.byContradiction`
on `A = B` makes the minor's *binders* vacuous — the moment both an
implication and its converse are in hand, `eq_of_impls` closes, so the
minor is `lamV`-of-`lamV` over an unreachable body and the stored
`Iff.intro` never appears at all.  The only computation needed is the
motive's β, `app_lamV`.  The level assignment
is then free: this instantiates at `ψ0 uN = 0`, where `eqv A B ∈ˢ
univ 0` is `eqv_mem_univ` outright and no `univ_mono` residue
arises. -/
theorem iff_forces_eq (mp : EnvModelM V env)
    {cvI : ConstantVal} {caps : ConLeche.IndCaps} {cvIi cvIr : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List ConLeche.RecRule}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = [])
    (hfIr : env.find? iffRecName = some (.recInfo cvIr mI rP isK rules))
    (htyIr : cvIr.type
      = iffRecA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A B w : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V))
    (hw : w ∈ˢ SetTheory.app (SetTheory.app
      (interp V ρ (mp.base2.acval iffName ψ)) A) B) :
    A = B := by
  refine Classical.byContradiction fun hne => ?_
  have hsh := iffRec_shapeS htyIr
  -- the parameterless family members do not read the assignment, so
  -- the recursor may be read at **any** level assignment
  have hIval : mp.base2.acval iffName (fun _ => 0)
      = mp.base2.acval iffName ψ :=
    mp.base2.acval_params _ _ hfI _ _ (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI]
      intro p hp; cases hp)
  have hI : ∀ d, denote mp.base2.acval env (fun _ => 0) d
      (.const iffName []) = some (mp.base2.acval iffName (fun _ => 0)) :=
    fun d => denote_levelless_const hfI (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI])
  have hIi : ∀ d, denote mp.base2.acval env (fun _ => 0) d
      (.const iffIntroName [])
        = some (mp.base2.acval iffIntroName (fun _ => 0)) :=
    fun d => denote_levelless_const hfIi (by
      rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi
        from rfl, hlpIi])
  -- the recursor's stored type, read at the zero assignment
  have hden : denote mp.base2.acval env (fun _ => 0) 0
      (ConstantInfo.recInfo cvIr mI rP isK rules).toConstantVal.type
      = some (.pi (.sort 0)
        (.pi (.sort 0)
          (.pi (.pi (.app (.app (mp.base2.acval iffName (fun _ => 0))
                (.bvar 1)) (.bvar 0)) (.sort 0))
            (.pi (.pi (.pi (.bvar 2) (.bvar 2))
                (.pi (.pi (.bvar 2) (.bvar 4))
                  (.app (.bvar 2)
                    (.app (.app (.app (.app
                      (mp.base2.acval iffIntroName (fun _ => 0))
                      (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0)))))
              (.pi (.app (.app (mp.base2.acval iffName (fun _ => 0))
                  (.bvar 3)) (.bvar 2))
                (.app (.bvar 2) (.bvar 0))))))) := by
    show denote mp.base2.acval env (fun _ => 0) 0 cvIr.type = _
    rw [hsh]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, hI, hIi, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfIr) _ _ hden ρ
  rw [Env.find?_name hfIr] at hmem
  rw [hIval] at hmem
  -- the family leaf's interpretation does not read the environment
  have hIc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval iffName ψ)
        = interp V ρ (mp.base2.acval iffName ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  -- ARG 1 and 2: the two propositions
  have hAd : A ∈ˢ interp V ρ (Term.sort 0) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi hmem hAd
  have hBd : B ∈ˢ interp V (cons A ρ) (Term.sort 0) := by
    rw [interp_sort]; exact hB
  have h2 := app_mem_pi h1 hBd
  -- ARG 3: the constantly-`eqv A B` motive
  obtain ⟨M, hME⟩ : ∃ M : V, M = lamV
      (SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval iffName ψ)) A) B)
      (fun _ => eqv A B) := ⟨_, rfl⟩
  have hMd : M ∈ˢ interp V (cons B (cons A ρ))
      (.pi (.app (.app (mp.base2.acval iffName ψ) (.bvar 1)) (.bvar 0))
        (.sort 0)) := by
    rw [hME, interp_pi]
    simp only [interp_app, interp_bvar, cons_zero, cons_succ,
      interp_sort, hIc]
    exact lamV_mem (fun _ _ => eqv_mem_univ A B) fun _ _ => IsTy_univ 0
  have h3 := app_mem_pi h2 hMd
  -- ARG 4: the minor.  **Vacuous**: an implication and its converse in
  -- hand contradict `hne`, so the stored `Iff.intro` never appears
  obtain ⟨Min, hMinE⟩ : ∃ Min : V, Min = lamV
      (piV A fun _ => B)
      (fun _ => lamV (piV B fun _ => A) fun _ => pt) :=
    ⟨_, rfl⟩
  have hMind : Min ∈ˢ interp V (cons M (cons B (cons A ρ)))
      (.pi (.pi (.bvar 2) (.bvar 2))
        (.pi (.pi (.bvar 2) (.bvar 4))
          (.app (.bvar 2)
            (.app (.app (.app (.app
              (mp.base2.acval iffIntroName (fun _ => 0))
              (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))))) := by
    rw [hMinE]
    simp only [interp_pi, interp_bvar, cons_zero, cons_succ]
    refine lamV_mem (fun x hx => ?_) fun _ _ => IsTy_piV
    exact lamV_mem (fun y hy => absurd (eq_of_impls hA hB hx hy) hne)
      fun y hy => absurd (eq_of_impls hA hB hx hy) hne
  have h4 := app_mem_pi h3 hMind
  -- ARG 5: the major, and the motive's β
  have hwd' : w ∈ˢ interp V (cons Min (cons M (cons B (cons A ρ))))
      (.app (.app (mp.base2.acval iffName ψ) (.bvar 3)) (.bvar 2)) := by
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hIc]
    exact hw
  have h5 := app_mem_pi h4 hwd'
  simp only [interp_app, interp_bvar, cons_zero, cons_succ] at h5
  rw [hME, app_lamV hw] at h5
  exact hne (eq_of_mem_eqv h5)

/-- **`propext`'s pinned telescope**, read off the pin. -/
theorem propext_shapeS {type' : Expr}
    (h : type'
      = propextA.type) :
    type' = .forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)))) := by
  simp only [propextA] at h
  subst h
  rfl

/-! ## `propext`'s membership

The leaf is the layer's own `propext` constant, whose `bval` is `pt`.
Every fibre of the stored type's reading is a truth value, so all three
function spaces are truth values (`piV_eq_zero`) and `pt_mem_piV_of`
descends through them.  The innermost fibre is the `Eq`-spine, whose
value is `eq_law`'s (the field, at the pin's own level instantiation
`u ↦ 1`), and `iff_forces_eq` supplies the equation. -/

/-- **`propext` inhabits its stored type's reading.** -/
theorem propext_mem (mp : EnvModelM V env)
    {cv : ConstantVal} (hok : ConLeche.stdAxiomOk env cv = true)
    (hn : cv.name = propextName)
    (ψ : Name → Nat) (ta : Term)
    (hta : denote mp.base2.acval env ψ 0 cv.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (.const .propext []) ∈ˢ interp V ρ ta := by
  obtain ⟨hEq, ⟨cvI, caps, hfI, hlpI, htyI⟩, ⟨cvIi, hfIi, hlpIi, htyIi⟩,
    ⟨cvIr, mI, rP, isK, rules, hfIr, hlpIr, htyIr⟩, hApin⟩ :=
    iff_shapes hok hn
  have hApinT : cv.type
      = propextA.type := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hApin
    exact hApin.2
  have hsh := propext_shapeS hApinT
  rw [hsh] at hta
  -- the `Eq` former's one level parameter is pinned to `1`
  have heqψ : Level.substFn ψ eqA.toConstantVal.levelParams
      [Level.zero.succ] uN = 1 := rfl
  have hI : ∀ e, denote mp.base2.acval env ψ e (.const iffName [])
      = some (mp.base2.acval iffName ψ) :=
    fun e => denote_levelless_const hfI (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI])
  have hQ : ∀ e, denote mp.base2.acval env ψ e
      (.const eqName [Level.zero.succ])
      = some (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) :=
    fun e => denote_const hEq rfl
  -- the stored type's reading
  have hden : denote mp.base2.acval env ψ 0
      (.forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)))))
      = some (.pi (.sort 0) (.pi (.sort 0)
          (.pi (.app (.app (mp.base2.acval iffName ψ) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (mp.base2.acval eqName
                (Level.substFn ψ eqA.toConstantVal.levelParams
                  [Level.zero.succ])) (.sort 0)) (.bvar 2))
              (.bvar 1))))) := by
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, hI, hQ, Level.eval]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  -- the leaves' interpretations do not read the environment
  have hIc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval iffName ψ)
        = interp V ρ (mp.base2.acval iffName ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  -- three function spaces over truth values, all `pt`-inhabited
  show (pt : V) ∈ˢ _
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ, hIc]
  refine pt_mem_piV_of fun A hA =>
    ⟨piV_mem_univZero_of fun B hB => piV_mem_univZero_of fun w hw => ?_,
     pt_mem_piV_of fun B hB =>
      ⟨piV_mem_univZero_of fun w hw => ?_, pt_mem_piV_of fun w hw => ⟨?_, ?_⟩⟩⟩
  all_goals
    rw [(mp.eq_law hEq _).1 (cons w (cons B (cons A ρ)))
      (univ 0) A B (by rw [heqψ]; exact univ_mem_univ 0) hA hB]
  any_goals exact eqv_mem_univZero A B
  have hAB : A = B :=
    iff_forces_eq mp hfI hlpI hfIi hlpIi hfIr htyIr ψ
      (cons w (cons B (cons A ρ))) hA hB (by
        simp only [hIc]; exact hw)
  exact hAB ▸ pt_mem_eqv_self A

/-! ## The stored `Nonempty` family

`Classical.choice`'s companions.  `Nonempty.rec`'s minor binds a plain
element of `α`, so over an empty `α` it is vacuous by the ambient
contradiction hypothesis; the motive's β is `app_lamV`. -/

/-- The stored `Nonempty` former's shape. -/
theorem nonempty_shapeS {ty : Expr}
    (h : ty
      = nonemptyA.toConstantVal.type) :
    ty = .forallE (.sort (.param uN)) (.sort .zero) := by
  simp only [nonemptyA, ConstantInfo.toConstantVal] at h
  subst h
  rfl

/-- The stored `Nonempty.intro`'s shape. -/
theorem nonemptyIntro_shapeS {ty : Expr}
    (h : ty
      = nonemptyIntroA.toConstantVal.type) :
    ty = .forallE (.sort (.param uN))
      (.forallE (.bvar 0)
        (.app (.const nonemptyName [.param uN]) (.bvar 1))) := by
  simp only [nonemptyIntroA, ConstantInfo.toConstantVal] at h
  subst h
  rfl

/-- The stored `Nonempty.rec`'s shape. -/
theorem nonemptyRec_shapeS {ty : Expr}
    (h : ty
      = nonemptyRecA.toConstantVal.type) :
    ty = .forallE (.sort (.param uN))
        (.forallE
          (.forallE
            (.app (.const nonemptyName [.param uN]) (.bvar 0))
            (.sort .zero))
          (.forallE
            (.forallE (.bvar 1)
              (.app (.bvar 1)
                (.app (.app (.const nonemptyIntroName [.param uN])
                  (.bvar 2)) (.bvar 0))))
            (.forallE
              (.app (.const nonemptyName [.param uN]) (.bvar 2))
              (.app (.bvar 2) (.bvar 0))))) := by
  simp only [nonemptyRecA, ConstantInfo.toConstantVal] at h
  subst h
  rfl

/-- A member of the `Nonempty` family, referenced at its own level
parameter, reads to its leaf at the plain assignment. -/
theorem denote_selfParam_constS {acval : Name → (Name → Nat) → Term}
    {ψ : Name → Nat} {d : Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = [uN]) :
    denote acval env ψ d (.const n [.param uN]) = some (acval n ψ) := by
  have h : denote acval env ψ d (.const n [.param uN])
      = some (acval n (Level.substFn ψ
          ci.toConstantVal.levelParams [Level.param uN])) :=
    denote_const hf (by rw [hlp]; rfl)
  rwa [hlp, show Level.substFn ψ [uN] [Level.param uN] = ψ from
    funext fun _ => Level.substFn_map_param] at h

/-- The interpreted `Nonempty A` is a truth value. -/
theorem nonemptyVal_app_mem (mp : EnvModelM V env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (htyN : cvN.type
      = nonemptyA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A
      ∈ˢ (univ 0 : V) := by
  have hsh := nonempty_shapeS htyN
  have hden : denote mp.base2.acval env ψ 0
      (ConstantInfo.indInfo cvN capsN).toConstantVal.type
      = some (.pi (.sort (ψ uN)) (.sort 0)) := by
    show denote mp.base2.acval env ψ 0 cvN.type = _
    rw [hsh]
    simp [denote_forallE, denote_sort, Expr.instantiate1, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfN) ψ _ hden ρ
  rw [Env.find?_name hfN] at hmem
  have h1 := app_mem_pi hmem (by rw [interp_sort]; exact hA)
  rwa [interp_sort] at h1

/-- The interpreted `Nonempty.intro A a` inhabits `Nonempty A`. -/
theorem nonemptyIntroVal_app₂_memP (mp : EnvModelM V env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps} {cvNi : ConstantVal}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (htyNi : cvNi.type
      = nonemptyIntroA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A a : V} (hA : A ∈ˢ univ (ψ uN))
    (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval nonemptyIntroName ψ)) A) a
      ∈ˢ SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A := by
  have hsh := nonemptyIntro_shapeS htyNi
  have hN : ∀ e, denote mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denote_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hden : denote mp.base2.acval env ψ 0
      (ConstantInfo.ctorInfo cvNi 1 1).toConstantVal.type
      = some (.pi (.sort (ψ uN))
          (.pi (.bvar 0)
            (.app (mp.base2.acval nonemptyName ψ) (.bvar 1)))) := by
    show denote mp.base2.acval env ψ 0 cvNi.type = _
    rw [hsh]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, hN, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfNi) ψ _ hden ρ
  rw [Env.find?_name hfNi] at hmem
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  have hAd : A ∈ˢ interp V ρ (Term.sort (ψ uN)) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi hmem hAd
  have had : a ∈ˢ interp V (cons A ρ) (Term.bvar 0) := ha
  have h2 := app_mem_pi h1 had
  simpa only [interp_app, interp_bvar, cons_zero, cons_succ, hNc]
    using h2

/-- **A witness of the interpreted `Nonempty A` forces `A`
inhabited.**  The constantly-`∅` motive — and here the minor
really *is* vacuous by the ambient contradiction hypothesis rather than
by restructuring, because `Nonempty.rec`'s minor binds a plain element
of `α`.  The motive's β is `app_lamV`. -/
theorem nonemptyVal_forces (mp : EnvModelM V env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    {cvNi cvNr : ConstantVal} {mI rP : Nat}
    {rulesN : List ConLeche.RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP isK rulesN))
    (htyNr : cvNr.type
      = nonemptyRecA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A h : V} (hA : A ∈ˢ univ (ψ uN))
    (hh : h ∈ˢ SetTheory.app
      (interp V ρ (mp.base2.acval nonemptyName ψ)) A) :
    ∃ x, x ∈ˢ A := by
  refine Classical.byContradiction fun hno => ?_
  have hsh := nonemptyRec_shapeS htyNr
  have hN : ∀ e, denote mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denote_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hNi : ∀ e, denote mp.base2.acval env ψ e
      (.const nonemptyIntroName [.param uN])
      = some (mp.base2.acval nonemptyIntroName ψ) :=
    fun e => denote_selfParam_constS hfNi (by
      show cvNi.levelParams = [uN]; rw [hlpNi]; rfl)
  have hden : denote mp.base2.acval env ψ 0
      (ConstantInfo.recInfo cvNr mI rP isK rulesN).toConstantVal.type
      = some (.pi (.sort (ψ uN))
        (.pi (.pi (.app (mp.base2.acval nonemptyName ψ) (.bvar 0)) (.sort 0))
          (.pi (.pi (.bvar 1)
              (.app (.bvar 1)
                (.app (.app (mp.base2.acval nonemptyIntroName ψ)
                  (.bvar 2)) (.bvar 0))))
            (.pi (.app (mp.base2.acval nonemptyName ψ) (.bvar 2))
              (.app (.bvar 2) (.bvar 0)))))) := by
    show denote mp.base2.acval env ψ 0 cvNr.type = _
    rw [hsh]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, hN, hNi, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfNr) ψ _ hden ρ
  rw [Env.find?_name hfNr] at hmem
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  -- ARG 1: the type
  have hAd : A ∈ˢ interp V ρ (Term.sort (ψ uN)) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi hmem hAd
  -- ARG 2: the constantly-`∅` motive
  obtain ⟨M, hME⟩ : ∃ M : V, M = lamV
      (SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A)
      (fun _ => (empty : V)) := ⟨_, rfl⟩
  have hMd : M ∈ˢ interp V (cons A ρ)
      (.pi (.app (mp.base2.acval nonemptyName ψ) (.bvar 0)) (.sort 0)) := by
    rw [hME, interp_pi]
    simp only [interp_app, interp_bvar, cons_zero, interp_sort, hNc]
    exact lamV_mem (fun _ _ => empty_mem_univ 0) fun _ _ => IsTy_univ 0
  have h2 := app_mem_pi h1 hMd
  -- ARG 3: the minor, vacuous over an empty `A`
  obtain ⟨Min, hMinE⟩ : ∃ Min : V,
      Min = lamV A (fun _ => (empty : V)) := ⟨_, rfl⟩
  have hMind : Min ∈ˢ interp V (cons M (cons A ρ))
      (.pi (.bvar 1)
        (.app (.bvar 1)
          (.app (.app (mp.base2.acval nonemptyIntroName ψ)
            (.bvar 2)) (.bvar 0)))) := by
    rw [hMinE]
    simp only [interp_pi, interp_bvar, cons_zero, cons_succ]
    exact lamV_mem (fun v hv => absurd ⟨v, hv⟩ hno) fun v hv => absurd ⟨v, hv⟩ hno
  have h3 := app_mem_pi h2 hMind
  -- ARG 4: the major, and the motive's β
  have hhd' : h ∈ˢ interp V (cons Min (cons M (cons A ρ)))
      (.app (mp.base2.acval nonemptyName ψ) (.bvar 2)) := by
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hNc]
    exact hh
  have h4 := app_mem_pi h3 hhd'
  simp only [interp_app, interp_bvar, cons_zero, cons_succ] at h4
  rw [hME, app_lamV hh] at h4
  exact not_mem_empty _ h4

/-- **The two domains agree.**  The layer's `¬¬A` and the checker's
stored `Nonempty A` are propositions with the same inhabitation, hence
the same set. -/
theorem dneg_eq_nonempty (mp : EnvModelM V env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    {cvNi cvNr : ConstantVal} {mI rP : Nat}
    {rulesN : List ConLeche.RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (htyN : cvN.type
      = nonemptyA.toConstantVal.type)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (htyNi : cvNi.type
      = nonemptyIntroA.toConstantVal.type)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP isK rulesN))
    (htyNr : cvNr.type
      = nonemptyRecA.toConstantVal.type)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    dnegSpace V A
      = SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A := by
  have hNE := nonemptyVal_app_mem mp hfN htyN ψ ρ hA
  have hdn : dnegSpace V A ∈ˢ (univ 0 : V) := by
    rw [univ_zero, dnegSpace]; exact piR_zero_mem_univZero
  refine prop_ext hdn hNE (fun hpt => ?_) (fun hpt => ?_)
  · obtain ⟨x, hx⟩ := exists_mem_of_dneg V hpt
    have hi := nonemptyIntroVal_app₂_memP mp hfN hlpN hfNi htyNi ψ ρ hA hx
    rwa [mem_univ_zero hNE hi] at hi
  · obtain ⟨x, hx⟩ := nonemptyVal_forces mp hfN hlpN hfNi hlpNi hfNr
      htyNr ψ ρ hA hpt
    rw [dnegSpace]
    exact pt_mem_piR_zero fun g hg =>
      absurd (app_mem_piR hg hx (fun _ _ _ =>
        univ_zero (V := V) ▸ empty_mem_univ 0)) (not_mem_empty _)

/-- **`Classical.choice`'s pinned telescope**, read off the pin: the
stored `Nonempty` reference is pinned to `[.param u]`. -/
theorem choice_shapeS {type' : Expr}
    (h : type' = choiceA.type) :
    type' = .forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1)) := by
  simp only [choiceA] at h
  subst h
  rfl

/-- **`Classical.choice` inhabits its stored type's reading.**  The
leaf is the layer's own `choice` constant; `dneg_eq_nonempty`
identifies the witness's double-negation domain with the checker's
stored `Nonempty`. -/
theorem choice_mem (mp : EnvModelM V env)
    {cv : ConstantVal} (hok : ConLeche.stdAxiomOk env cv = true)
    (hn : cv.name = choiceName)
    (ψ : Name → Nat) (ta : Term)
    (hta : denote mp.base2.acval env ψ 0 cv.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (.const .choice [ψ uN]) ∈ˢ interp V ρ ta := by
  obtain ⟨⟨cvN, capsN, hfN, hlpN, htyN⟩, ⟨cvNi, hfNi, hlpNi, htyNi⟩,
    ⟨cvNr, mI, rP, isK, rulesN, hfNr, hlpNr, htyNr⟩, hApin⟩ :=
    nonempty_shapes hok hn
  have hApinT : cv.type
      = choiceA.type := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hApin
    exact hApin.2
  have hsh := choice_shapeS hApinT
  rw [hsh] at hta
  have hN : ∀ e, denote mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denote_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hden : denote mp.base2.acval env ψ 0
      (.forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1)))
      = some (.pi (.sort (ψ uN))
          (.pi (.app (mp.base2.acval nonemptyName ψ) (.bvar 0))
            (.bvar 1))) := by
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, hN, Level.eval]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closed mp.base2 _ ψ ρ' ρ
  show choiceV V (ψ uN) ∈ˢ _
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ, hNc]
  rw [choiceV]
  refine lamV_mem (fun A hA => ?_) fun _ _ => IsTy_piV
  rw [← dneg_eq_nonempty mp hfN hlpN htyN hfNi hlpNi htyNi hfNr htyNr ψ ρ hA]
  exact lamV_mem (fun _ hh => schoice_mem (exists_mem_of_dneg V hh).choose_spec)
    fun _ _ => IsTy_of_mem_univ hA
