module

public import ConLeche.Semantics.BasisType
import ConLeche.Semantics.Interp
public import ConLeche.Semantics.WellDenoted

@[expose] public section

/-!
# `bval_mem_type` — every built-in inhabits its spelled type

The skeleton's `const` row's supplier: every built-in's value lies in
the reading of `BConst.typeAV`, over `piV`/`lamV`.

## The proof pattern

Each case is three moves, and the first two are mechanical:

1. `show` the value at its own tower (`bval` is a `match`, so this is
   definitional);
2. `simp only` with `BConst.typeAV`, the smart constructors it mentions,
   and the `interp` clause equations — this reduces
   `interp ρ (typeAV c us)` to the tower's *own space*: the constants'
   spaces are the value reading of their spelled binder types;
3. apply the tower's membership argument — `lamV_mem` down the
   binders (each fibre a type), then the constant's own semantic fact.

No universe side condition is needed.  `Empty.rec` is the point (its
inner abstraction is over `∅`), and its type's inner function space is
`{pt}`.

## The `Nat.succ` wrinkle

`typeAV`'s step premise mentions `Nat.succ`'s *value*
(`natSuccAV (.bvar 1)` interprets to `app (natSuccV V) n`) while
`natStepSpace` is written with the operator `natsucc`.  They agree on
`ω`, which is what the outer function space quantifies over
(`natStepSpace_eq`).
-/

namespace ConLeche.Semantics
open ConLeche.Verify (projNV)
open ConLeche.SetModel

open SetTheory
open ConLeche.Term (Term BConst lv emptyT quotCl le_quotCl)
open ConLeche.SetTheory.Tower (mkTower projS)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat` -/

theorem bval_mem_nat (us : List Nat) (ρ : Nat → V) :
    bval V .nat us ∈ˢ interp V ρ (BConst.typeAV .nat us) := by
  show (omega : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact omega_mem_univ_succ 0

theorem bval_mem_natZero (us : List Nat) (ρ : Nat → V) :
    bval V .natZero us ∈ˢ interp V ρ (BConst.typeAV .natZero us) := by
  show natzero ∈ˢ _
  simp only [BConst.typeAV, natTyAV, interp_const, bval]
  exact natzero_mem

theorem bval_mem_natSucc (us : List Nat) (ρ : Nat → V) :
    bval V .natSucc us ∈ˢ interp V ρ (BConst.typeAV .natSucc us) := by
  show natSuccV V ∈ˢ _
  simp only [BConst.typeAV, arrowA, natTyAV, interp_pi, interp_const,
    Term.lift, Term.liftN, bval]
  exact natSuccV_memV V

/-- The step space as `interp` produces it (with `Nat.succ`'s *value*
applied) is the one the tower is written with (`natsucc`): they agree
on `ω`. -/
theorem natStepSpace_eq (M : V) :
    (piV (omega : V) fun n => piV (app M n) fun _ => app M (app (natSuccV V) n))
      = natStepSpace V M :=
  piV_congr fun n hn => by rw [natSuccV_app V hn]

/-- `Nat.rec`'s type, as `interp` produces it. -/
theorem interp_type_natRec (us : List Nat) (ρ : Nat → V) :
    interp V ρ (BConst.typeAV .natRec us) =
      piV (natMotiveSpace V (lv us 0)) fun M =>
        piV (app M natzero) fun _ =>
          piV (natStepSpace V M) fun _ =>
            piV omega fun n => app M n := by
  simp only [BConst.typeAV, arrowA, natTyAV, natZeroAV, natSuccAV,
    interp_pi, interp_const, interp_app, interp_bvar, interp_sort,
    Term.lift, Term.liftN, cons_zero, cons_succ, bval, natMotiveSpace]
  refine piV_congr fun M _ => piV_congr fun z _ => ?_
  rw [natStepSpace_eq]

theorem bval_mem_natRec (us : List Nat) (ρ : Nat → V) :
    bval V .natRec us ∈ˢ interp V ρ (BConst.typeAV .natRec us) := by
  rw [interp_type_natRec]
  exact natRecV_mem V (lv us 0)

/-! ## `PUnit` -/

theorem bval_mem_punit (us : List Nat) (ρ : Nat → V) :
    bval V .punit us ∈ˢ interp V ρ (BConst.typeAV .punit us) := by
  show (unitSetAt (lv us 0) : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact unitSetAt_mem_univ _

theorem bval_mem_punitUnit (us : List Nat) (ρ : Nat → V) :
    bval V .punitUnit us
      ∈ˢ interp V ρ (BConst.typeAV .punitUnit us) := by
  show (unitAt (lv us 0) : V) ∈ˢ _
  simp only [BConst.typeAV, punitAV, interp_const, bval]
  exact unitAt_mem_unitSetAt _

/-! ## `Empty` -/

theorem bval_mem_empty (us : List Nat) (ρ : Nat → V) :
    bval V .empty us ∈ˢ interp V ρ (BConst.typeAV .empty us) := by
  show (empty : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact empty_mem_univ _

/-- `Empty.rec`: its inner abstraction is over `∅`, so it is the point,
and so is the whole constant; its type's inner function space is
`{pt}`. -/
theorem bval_mem_emptyRec (us : List Nat) (ρ : Nat → V) :
    bval V .emptyRec us
      ∈ˢ interp V ρ (BConst.typeAV .emptyRec us) := by
  show emptyRecV V (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, emptyT, interp_pi, interp_const,
    interp_app, interp_bvar, interp_sort, Term.lift, Term.liftN, cons_zero,
    cons_succ, bval]
  exact lamV_mem (fun _ _ => lamV_mem (fun t ht => absurd ht (not_mem_empty t))
    fun t ht => absurd ht (not_mem_empty t)) fun _ _ => IsTy_piV

/-! ## The dependent pair `.psigma` -/

theorem bval_mem_psigma (us : List Nat) (ρ : Nat → V) :
    bval V .psigma us ∈ˢ interp V ρ (BConst.typeAV .psigma us) := by
  show psigmaV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, interp_pi, interp_bvar,
    interp_sort, Term.lift, Term.liftN, cons_zero]
  exact psigmaV_mem V _ _

/-- A dependent pair type is a type. -/
theorem IsTy_psigmaV_app {u v : Nat} {A B : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) : IsTy (app (app (psigmaV V u v) A) B) := by
  rw [psigmaV_app V hA hB]
  exact IsTy_of_mem_univ (sigma_mem_univ hA fun x hx => psigmaFibre_apply V hB hx)

/-- **`.psigmaMk`**: four abstractions; the pair is the point where its
type is a truth value (`max u v = 0`). -/
theorem bval_mem_psigmaMk (us : List Nat) (ρ : Nat → V) :
    bval V .psigmaMk us
      ∈ˢ interp V ρ (BConst.typeAV .psigmaMk us) := by
  show psigmaMkV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, psigmaAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, Term.lift, Term.liftN,
    Term.mkAppN, cons_zero, cons_succ, bval, lv, List.getD_cons_zero,
    List.getD_cons_succ]
  refine lamV_mem (fun A hA => lamV_mem (fun B hB => lamV_mem (fun a ha =>
    lamV_mem (fun b hb => ?_) fun _ _ => IsTy_psigmaV_app V hA hB)
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  rw [psigmaV_app V hA hB]
  split
  · rename_i hw
    rw [hw]
    exact pt_mem_sigma ha hb
  · rename_i hw
    exact spair_mem hw ha hb

/-! ## `Quot` -/

/-- The type argument of a quotient constant is small enough for its construction level. -/
theorem mem_univ_quotCl {us : List Nat} {i : Nat} {A : V} (hA : A ∈ˢ (univ (lv us 0) : V)) :
    A ∈ˢ (univ (quotCl us i) : V) :=
  univ_mono (le_quotCl us i) _ hA

theorem bval_mem_quot (us : List Nat) (ρ : Nat → V) :
    bval V .quot us ∈ˢ interp V ρ (BConst.typeAV .quot us) := by
  show quotV V (lv us 0) (quotCl us 1) ∈ˢ _
  simp only [BConst.typeAV, relAV, interp_pi, interp_bvar,
    interp_sort, Term.lift, Term.liftN, cons_zero]
  exact lamV_mem (fun _ hA => lamV_mem (fun _ _ => quotSet_mem_univ (mem_univ_quotCl V hA))
    fun _ _ => IsTy_univ _) fun _ _ => IsTy_piV

/-- A quotient is a type. -/
theorem IsTy_quotV_app {u c : Nat} (huc : u ≤ c) {A R : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) : IsTy (app (app (quotV V u c) A) R) := by
  rw [quotV_app V hA hR]; exact IsTy_of_mem_univ (quotSet_mem_univ (univ_mono huc _ hA))

theorem bval_mem_quotMk (us : List Nat) (ρ : Nat → V) :
    bval V .quotMk us ∈ˢ interp V ρ (BConst.typeAV .quotMk us) := by
  show quotMkV V (lv us 0) (quotCl us 1) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, Term.lift, Term.liftN,
    Term.mkAppN, cons_zero, cons_succ, bval, lv, List.getD_cons_zero]
  refine lamV_mem (fun A hA => lamV_mem (fun R hR => lamV_mem (fun a ha => ?_)
    fun _ _ => IsTy_quotV_app V (le_quotCl us 1) hA hR) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  rw [quotV_app V hA hR]
  exact quotClass_mem ha

/-- **`Quot.lift`**: five abstractions, and the tail is
`quotLiftR_mem`. -/
theorem bval_mem_quotLift (us : List Nat) (ρ : Nat → V) :
    bval V .quotLift us
      ∈ˢ interp V ρ (BConst.typeAV .quotLift us) := by
  show quotLiftV V (lv us 0) (lv us 1) (quotCl us 2) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, interp_eqE, Term.lift,
    Term.liftN, Term.mkAppN, cons_zero, cons_succ, bval, lv, List.getD_cons_zero]
  refine lamV_mem (fun A hA => lamV_mem (fun R hR => lamV_mem (fun B hB =>
    lamV_mem (fun f hf => lamV_mem (fun _ _ => ?_) fun _ _ => IsTy_piV)
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  rw [quotV_app V hA hR]
  exact quotLiftR_mem V hf (IsTy_of_mem_univ hB)

/-! ## The `pt`-valued propositions

`Quot.ind`, `Quot.sound` and `propext` have `bval = pt`, so their
cases are *inhabitation* arguments rather than typings: every binder's
abstraction of the point is the point (`pt_mem_piV_ty`). -/

/-- The point inhabits a function space whose fibres are types holding
it. -/
theorem pt_mem_piV_ty {A : V} {B : V → V} (h : ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x)
    (hB : ∀ x, x ∈ˢ A → IsTy (B x)) : (pt : V) ∈ˢ piV A B := by
  have hm := lamV_mem (F := fun _ => (pt : V)) h hB
  rwa [lamV_eq_pt fun _ _ => rfl] at hm

theorem bval_mem_quotInd (us : List Nat) (ρ : Nat → V) :
    bval V .quotInd us ∈ˢ interp V ρ (BConst.typeAV .quotInd us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, quotMkAV, interp_pi,
    interp_bvar, interp_sort, interp_app, interp_const, Term.lift,
    Term.liftN, Term.mkAppN, cons_zero, cons_succ, bval, lv, List.getD_cons_zero]
  refine pt_mem_piV_ty V (fun A hA => pt_mem_piV_ty V (fun R hR => pt_mem_piV_ty V (fun M hM =>
    pt_mem_piV_ty V (fun mi hmi => pt_mem_piV_ty V (fun q hq => ?_) fun q hq => ?_)
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  · have hMq : app M q ∈ˢ (univ 0 : V) := app_mem_piV hM hq
    rw [quotV_app V hA hR] at hq
    obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
    have h1 := app_mem_piV hmi ha
    rw [quotMkV_app V hA hR ha] at h1
    exact mem_univ_zero hMq h1 ▸ h1
  · exact IsTy_of_mem_univ (app_mem_piV hM hq)

theorem bval_mem_quotSound (us : List Nat) (ρ : Nat → V) :
    bval V .quotSound us
      ∈ˢ interp V ρ (BConst.typeAV .quotSound us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotMkAV, interp_pi,
    interp_bvar, interp_sort, interp_app, interp_const,
    interp_eqE, Term.lift, Term.liftN, Term.mkAppN, cons_zero, cons_succ,
    bval, lv, List.getD_cons_zero]
  refine pt_mem_piV_ty V (fun A hA => pt_mem_piV_ty V (fun R hR => pt_mem_piV_ty V (fun a ha =>
    pt_mem_piV_ty V (fun b hb => pt_mem_piV_ty V (fun _wv hwv => ?_) fun _ _ => IsTy_eqv _ _)
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  rw [quotMkV_app V hA hR ha, quotMkV_app V hA hR hb,
    SetTheory.quotSound ha hb hwv]
  exact pt_mem_eqv_self _

theorem bval_mem_propext (us : List Nat) (ρ : Nat → V) :
    bval V .propext us ∈ˢ interp V ρ (BConst.typeAV .propext us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, interp_pi, interp_bvar, interp_sort,
    interp_eqE, cons_zero, cons_succ]
  refine pt_mem_piV_ty V (fun A hA => pt_mem_piV_ty V (fun B hB => pt_mem_piV_ty V (fun f hf =>
    pt_mem_piV_ty V (fun g hg => ?_) fun _ _ => IsTy_eqv _ _)
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  have hAB : A = B := by
    refine prop_ext hA hB (fun hp => ?_) (fun hp => ?_)
    · have h1 : app f pt ∈ˢ B := app_mem_piV hf hp
      exact mem_univ_zero hB h1 ▸ h1
    · have h1 : app g pt ∈ˢ A := app_mem_piV hg hp
      exact mem_univ_zero hA h1 ▸ h1
  rw [hAB]
  exact pt_mem_eqv_self _

/-! ## `Classical.choice` -/

theorem bval_mem_choice (us : List Nat) (ρ : Nat → V) :
    bval V .choice us ∈ˢ interp V ρ (BConst.typeAV .choice us) := by
  show choiceV V (lv us 0) ∈ˢ _
  simp only [BConst.typeAV, negTyAV, arrowA, emptyT, interp_pi,
    interp_bvar, interp_sort, interp_const, Term.lift, Term.liftN, cons_zero,
    cons_succ, bval, piV_dneg_eq]
  exact choiceV_mem V _

/-! ## `lfpFam` (task #188) -/

theorem bval_mem_lfpFam (us : List Nat) (ρ : Nat → V) :
    bval V .lfpFam us ∈ˢ interp V ρ (BConst.typeAV .lfpFam us) := by
  show lfpFamV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, interp_pi, interp_sort, interp_bvar, Term.lift,
    Term.liftN, cons_zero, cons_succ]
  exact lfpFamV_mem V (lv us 0) (lv us 1)

/-! ## `lfpTuple k` (#315)

The block carrier's constant binds two pair towers — the index-set
tuple `Is` and the family tuple — and reads the members' index sets off
`Is` with `projNV`.  Both towers are non-dependent (`ndTowerAV`), so
their readings and gradings need only that each component reads to the
carrier's own at the tower's depth and is itself graded; the tower's application clauses are supplied by the `[r, r]`
instance of the pinned pair former's function-space membership, exactly as the
dependent tower kit's are. -/

/-- **The uniform projection spelling reads back as `projS`** — the
definitional commutation, no premises at all (matching the tier's
unconditional iota discipline). -/
theorem projNV_interp :
    ∀ (i : Nat) (e : Term) (ρ : Nat → V),
      interp V ρ (projNV i e) = projS i (interp V ρ e)
  | 0, _, _ => rfl
  | i + 1, e, ρ => by
    show interp V ρ (projNV i (.snd e)) = projS i (ssnd (interp V ρ e))
    rw [projNV_interp i (.snd e) ρ]
    rfl

/-- The `[r, r]` instance of the pinned pair former's function-space
membership (`sigma_mem_univ` at the joint level `max r r = r`). -/
theorem psigmaV_rr_mem (r : Nat) :
    psigmaV V r r ∈ˢ piR (r + 1) (univ r : V)
      (fun A => piR (r + 1) (psigmaFibreSpace V r A) fun _ => (univ r : V)) := by
  rw [psigmaV_eq_lamR, show Nat.max r r = r from Nat.max_self r]
  exact lamR_mem fun A hA => lamR_mem fun B hB => by
    have h := sigma_mem_univ (u := r) (v := r) hA
      (fun x hx => psigmaFibre_apply V hB hx)
    rwa [show Nat.max r r = r from Nat.max_self r] at h

/-- **The non-dependent tower reads back as its carrier.**  Its
components are read at the BASE frame `ρ` — the former lifted them to
their depth, so the tower's own binders do not reach them. -/
theorem ndTowerAV_interp {r : Nat} {F : Nat → V} {G : Nat → Term} {ρ : Nat → V} :
    ∀ (n s d : Nat) (σ : Nat → V), shiftE d 0 σ = ρ →
      (∀ m, m < s + n → interp V ρ (G m) = F m) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      interp V σ (ndTowerAV r G s d n) = ndTowerSet V r F s n
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, s, d, σ, hσ, hG, hF => by
    have hC : interp V σ ((G s).liftN d 0) = F s := by
      rw [interp_liftN, hσ]; exact hG s (by omega)
    have hA : interp V σ ((G s).liftN d 0) ∈ˢ (univ r : V) := hC ▸ hF s (by omega)
    have hrest : ∀ x : V, interp V (cons x σ) (ndTowerAV r G (s + 1) (d + 1) n)
        = ndTowerSet V r F (s + 1) n := fun x =>
      ndTowerAV_interp n (s + 1) (d + 1) (cons x σ)
        (by rw [shiftE_succ_cons]; exact hσ) (fun m hm => hG m (by omega))
        (fun m hm => hF m (by omega))
    have hB : (lamV (interp V σ ((G s).liftN d 0))
          fun x => interp V (cons x σ) (ndTowerAV r G (s + 1) (d + 1) n))
        ∈ˢ psigmaFibreSpace V r (interp V σ ((G s).liftN d 0)) :=
      lamV_mem_psigmaFibreSpace V fun x _ => by
        rw [hrest x]; exact ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hbv : bval V .psigma [r, r] = psigmaV V r r := rfl
    show SetTheory.app (SetTheory.app (bval V .psigma [r, r])
        (interp V σ ((G s).liftN d 0)))
        (lamV (interp V σ ((G s).liftN d 0))
          fun x => interp V (cons x σ) (ndTowerAV r G (s + 1) (d + 1) n))
      = ndTowerSet V r F s (n + 1)
    rw [hbv, psigmaV_app V hA hB, show Nat.max r r = r from Nat.max_self r]
    show sigmaSet r _ _ = sigmaSet r (F s) _
    rw [← hC]
    exact sigma_congr fun x hx => by rw [app_lamV hx, hrest x]

/-- **The non-dependent tower is graded** (`WellDenoted`). -/
theorem ndTowerAV_wellDenoted {r : Nat} {F : Nat → V} {G : Nat → Term} {ρ : Nat → V} :
    ∀ (n s d : Nat) (σ : Nat → V), shiftE d 0 σ = ρ →
      (∀ m, m < s + n → interp V ρ (G m) = F m) →
      (∀ m, m < s + n → WellDenoted V ρ (G m)) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      WellDenoted V σ (ndTowerAV r G s d n)
  | 0, _, _, _, _, _, _, _ => by simp [ndTowerAV]
  | n + 1, s, d, σ, hσ, hG, hok, hF => by
    have hC : interp V σ ((G s).liftN d 0) = F s := by
      rw [interp_liftN, hσ]; exact hG s (by omega)
    have hCok : WellDenoted V σ ((G s).liftN d 0) := by
      rw [WellDenoted_liftN, hσ]; exact hok s (by omega)
    have hA : interp V σ ((G s).liftN d 0) ∈ˢ (univ r : V) := hC ▸ hF s (by omega)
    have hrest : ∀ x : V, interp V (cons x σ) (ndTowerAV r G (s + 1) (d + 1) n)
        = ndTowerSet V r F (s + 1) n := fun x =>
      ndTowerAV_interp V n (s + 1) (d + 1) (cons x σ)
        (by rw [shiftE_succ_cons]; exact hσ) (fun m hm => hG m (by omega))
        (fun m hm => hF m (by omega))
    have hfib : ∀ x, x ∈ˢ interp V σ ((G s).liftN d 0) →
        interp V (cons x σ) (ndTowerAV r G (s + 1) (d + 1) n) ∈ˢ (univ r : V) := fun x _ => by
      rw [hrest x]; exact ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hbv : interp V σ (.const .psigma [r, r]) = psigmaV V r r := rfl
    have hvac : ¬ r + 1 = 0 := Nat.succ_ne_zero r
    show WellDenoted V σ (.app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
      (.lam ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n)))
    rw [WellDenoted_app]
    refine ⟨?_, ?_, ?_⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, hCok,
        appliesTo_of_mem_piR (hbv ▸ psigmaV_rr_mem V r) (IsTy_univ r) hA⟩
    · rw [WellDenoted_lam]
      exact ⟨hCok, IsTy_of_mem_univ hA,
        fun x _ => ndTowerAV_wellDenoted n (s + 1) (d + 1) (cons x σ)
          (by rw [shiftE_succ_cons]; exact hσ) (fun m hm => hG m (by omega))
          (fun m hm => hok m (by omega)) (fun m hm => hF m (by omega))⟩
    · refine appliesTo_of_mem_piR (v := r + 1) (A := psigmaFibreSpace V r
        (interp V σ ((G s).liftN d 0))) (B := fun _ => (univ r : V)) ?_ IsTy_piV ?_
      · show SetTheory.app (interp V σ (.const .psigma [r, r]))
          (interp V σ ((G s).liftN d 0)) ∈ˢ _
        rw [hbv]
        exact app_mem_piR_pos hvac (psigmaV_rr_mem V r) hA
      · exact lamV_mem_psigmaFibreSpace V hfib

/-- **The projection chain into a tower is graded.** -/
theorem projNV_wellDenoted_ndTower {r : Nat} (hr : r ≠ 0) {F : Nat → V} :
    ∀ (i n s : Nat) (e : Term) (ρ : Nat → V), i < n →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      WellDenoted V ρ e → interp V ρ e ∈ˢ ndTowerSet V r F s n →
      WellDenoted V ρ (projNV i e)
  | _, 0, _, _, _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | 0, n + 1, s, e, ρ, _, hF, hok, he => by
    have he' : interp V ρ e ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n := he
    show WellDenoted V ρ (.fst e)
    rw [WellDenoted_fst]
    refine ⟨hok, r, r, F s, (fun _ => ndTowerSet V r F (s + 1) n), ?_, hF s (by omega),
      fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)⟩
    rwa [show Nat.max r r = r from Nat.max_self r]
  | i + 1, n + 1, s, e, ρ, hi, hF, hok, he => by
    have he' : interp V ρ e ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n := he
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim he'
    have hsnd : WellDenoted V ρ (.snd e) := by
      rw [WellDenoted_snd]
      refine ⟨hok, r, r, F s, (fun _ => ndTowerSet V r F (s + 1) n), ?_, hF s (by omega),
        fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)⟩
      rwa [show Nat.max r r = r from Nat.max_self r]
    have hmem : interp V ρ (.snd e) ∈ˢ ndTowerSet V r F (s + 1) n := by
      show ssnd (interp V ρ e) ∈ˢ _
      rw [hpos hr, ssnd_spair]
      exact hb
    exact projNV_wellDenoted_ndTower hr i n (s + 1) (.snd e) ρ
      (Nat.lt_of_succ_lt_succ hi) (fun m hm => hF m (by omega)) hsnd hmem

/-! ### The two towers of `lfpTuple k`'s type -/

/-- **The index-set tuple's type**: its value and its grading, at every
environment (its components are closed sorts). -/
theorem tupleSortsAV_facts (k : Nat) (us : List Nat) (ρ : Nat → V) :
    interp V ρ (tupleSortsAV k us) = tupleSortsSpace V k us ∧
      WellDenoted V ρ (tupleSortsAV k us) :=
  ⟨ndTowerAV_interp V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) (fun _ _ => rfl)
      (fun m _ => univ_lv_mem_tupleIdxSort V us m),
   ndTowerAV_wellDenoted V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) (fun _ _ => rfl)
      (fun _ _ => trivial) (fun m _ => univ_lv_mem_tupleIdxSort V us m)⟩

/-- The family tuple's components live in the family tuple's own
universe, below `k`. -/
theorem famComp_mem_univ {k : Nat} {us : List Nat} {Is : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us) (m : Nat) (hm : m < k) :
    lfpFamSpace V (lv us k) (projS m Is) ∈ˢ (univ (ConLeche.Term.tupleFamSort k us) : V) := by
  have hproj : projS m Is ∈ˢ (univ (lv us m) : V) := by
    have := projS_mem_ndTowerSet V (tupleIdxSort_ne_zero us) k 0 hIs m hm
    rwa [Nat.zero_add] at this
  have h := piV_mem_univ (u := lv us m) (v := lv us k + 1) hproj
    (fun _ _ => univ_mem_univ (lv us k))
  rw [ite_eq_right (Nat.succ_ne_zero _)] at h
  refine univ_mono ?_ _ h
  refine Nat.max_le_of_le_of_le ?_ ?_
  · exact Nat.le_trans (ConLeche.Term.lv_le_levMax us m) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-- The index-set tuples are a type. -/
theorem IsTy_tupleSortsSpace (k : Nat) (us : List Nat) : IsTy (tupleSortsSpace V k us) :=
  IsTy_of_mem_univ (ndTowerSet_mem_univ V k 0 fun m _ => univ_lv_mem_tupleIdxSort V us m)

/-- The family tuples at an index-set tuple are a type. -/
theorem IsTy_tupleFamsSpace {k : Nat} {us : List Nat} {Is : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us) : IsTy (tupleFamsSpace V k us Is) :=
  IsTy_of_mem_univ (ndTowerSet_mem_univ V k 0 fun m hm => famComp_mem_univ V hIs m (by omega))

/-- **The family tuple's type**: its value and its grading, at an
environment whose `j`-th variable is an index-set tuple. -/
theorem tupleFamsAV_facts {k : Nat} {us : List Nat} {j : Nat} {ρ : Nat → V}
    (hIs : ρ j ∈ˢ tupleSortsSpace V k us) :
    interp V ρ (tupleFamsAV k us j) = tupleFamsSpace V k us (ρ j) ∧
      WellDenoted V ρ (tupleFamsAV k us j) := by
  have hG : ∀ m, m < k → interp V ρ (.pi (projNV m (.bvar j))
      (.sort (lv us k)) : Term) = lfpFamSpace V (lv us k) (projS m (ρ j)) := by
    intro m _
    show piV (interp V ρ (projNV m (.bvar j))) _ = _
    rw [projNV_interp, interp_bvar]
    rfl
  have hok : ∀ m, m < k → WellDenoted V ρ (.pi (projNV m (.bvar j))
      (.sort (lv us k)) : Term) := by
    intro m hm
    rw [WellDenoted_pi]
    refine ⟨?_, ?_, fun _ _ => trivial, fun _ _ => IsTy_univ _⟩
    rotate_left
    · rw [projNV_interp, interp_bvar]
      have := projS_mem_ndTowerSet V (tupleIdxSort_ne_zero us) k 0 hIs m hm
      rw [Nat.zero_add] at this
      exact IsTy_of_mem_univ this
    refine projNV_wellDenoted_ndTower V (tupleIdxSort_ne_zero us) m k 0
      (.bvar j) ρ hm (fun i _ => univ_lv_mem_tupleIdxSort V us i) trivial ?_
    rw [interp_bvar]; exact hIs
  exact ⟨ndTowerAV_interp V k 0 0 ρ (shiftE_zero_zero ρ) (fun m hm => hG m (by omega))
      (fun m hm => famComp_mem_univ V hIs m (by omega)),
   ndTowerAV_wellDenoted V k 0 0 ρ (shiftE_zero_zero ρ) (fun m hm => hG m (by omega))
      (fun m hm => hok m (by omega)) (fun m hm => famComp_mem_univ V hIs m (by omega))⟩

theorem bval_mem_lfpTuple (k : Nat) (us : List Nat) (ρ : Nat → V) :
    bval V (.lfpTuple k) us ∈ˢ interp V ρ (BConst.typeAV (.lfpTuple k) us) := by
  show lfpTupleV V k us ∈ˢ _
  simp only [BConst.typeAV, interp_pi]
  rw [(tupleSortsAV_facts V k us ρ).1]
  have hfams1 : ∀ Is x : V, Is ∈ˢ tupleSortsSpace V k us →
      interp V (cons x (cons Is ρ)) (tupleFamsAV k us 1) = tupleFamsSpace V k us Is :=
    fun Is x hIs => (tupleFamsAV_facts V (j := 1) (ρ := cons x (cons Is ρ)) hIs).1
  have hdom : ∀ Is : V, Is ∈ˢ tupleSortsSpace V k us →
      (piV (interp V (cons Is ρ) (tupleFamsAV k us 0)) fun x =>
          interp V (cons x (cons Is ρ)) (tupleFamsAV k us 1))
        = piV (tupleFamsSpace V k us Is) fun _ => tupleFamsSpace V k us Is := fun Is hIs => by
    rw [(tupleFamsAV_facts V (j := 0) (ρ := cons Is ρ) hIs).1]
    exact piV_congr fun x _ => hfams1 Is x hIs
  have h := lfpTupleV_mem V k us
  rw [piV_congr fun Is hIs => show _ = piV (interp V (cons Is ρ) (.pi (tupleFamsAV k us 0)
      (tupleFamsAV k us 1))) (fun x => interp V (cons x (cons Is ρ)) (tupleFamsAV k us 1)) by
    rw [interp_pi, hdom Is hIs]
    exact piV_congr fun x _ => (hfams1 Is x hIs).symm] at h
  exact h

/-! ## The capstone

`bval_mem_type`, over `interp` and `BConst.typeAV`: what the skeleton's
`const` row waits on. -/

/-- **Every built-in constant inhabits its spelled type.** -/
theorem bval_mem_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    bval V c us ∈ˢ interp V ρ (BConst.typeAV c us) := by
  cases c with
  | nat => exact bval_mem_nat V us ρ
  | natZero => exact bval_mem_natZero V us ρ
  | natSucc => exact bval_mem_natSucc V us ρ
  | natRec => exact bval_mem_natRec V us ρ
  | punit => exact bval_mem_punit V us ρ
  | punitUnit => exact bval_mem_punitUnit V us ρ
  | psigma => exact bval_mem_psigma V us ρ
  | psigmaMk => exact bval_mem_psigmaMk V us ρ
  | empty => exact bval_mem_empty V us ρ
  | emptyRec => exact bval_mem_emptyRec V us ρ
  | quot => exact bval_mem_quot V us ρ
  | quotMk => exact bval_mem_quotMk V us ρ
  | quotLift => exact bval_mem_quotLift V us ρ
  | quotInd => exact bval_mem_quotInd V us ρ
  | quotSound => exact bval_mem_quotSound V us ρ
  | propext => exact bval_mem_propext V us ρ
  | choice => exact bval_mem_choice V us ρ
  | lfpFam => exact bval_mem_lfpFam V us ρ
  | lfpTuple k => exact bval_mem_lfpTuple V k us ρ

end ConLeche.Semantics
