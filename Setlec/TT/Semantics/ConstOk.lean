import Setlec.TT.Semantics.Interp

/-!
# Every built-in constant inhabits its type

`bval_mem_type` is the semantic content of the `const` typing rule: for
each `c : BConst` and each level instantiation, the value of `c` is a
member of the interpretation of `c.type`.

Each constant gets two lemmas: one computing the interpretation of its
type into set-theoretic vocabulary, and one discharging the
membership.  The first is where the `de Bruijn` indices of
`Setlec/TT/Const.lean` are actually *checked* — an off-by-one there
makes the membership unprovable.
-/

namespace Setlec.TT

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat` -/

theorem bval_mem_nat (us : List Nat) (ρ : Nat → V) :
    bval V .nat us ∈ˢ interp V ρ (BConst.type .nat us) :=
  omega_mem_univ

theorem bval_mem_natZero (us : List Nat) (ρ : Nat → V) :
    bval V .natZero us ∈ˢ interp V ρ (BConst.type .natZero us) :=
  natzero_mem

theorem bval_mem_natSucc (us : List Nat) (ρ : Nat → V) :
    bval V .natSucc us ∈ˢ interp V ρ (BConst.type .natSucc us) :=
  natSuccV_mem V

/-- The `Nat.rec` minor-premise space as the interpretation produces it
(with `Nat.succ`'s *value* applied) is the one the model works with
(with `natsucc`): they agree on `ω`, which is what the outer product
quantifies over. -/
theorem natStepSpace_eq (M : V) :
    (piC (omega : V) fun n =>
      piC (app M n) fun _ => app M (app (natSuccV V) n)) = natStepSpace V M :=
  piC_congr fun n hn => by rw [natSuccV_app V hn]

theorem interp_type_natRec (us : List Nat) (ρ : Nat → V) :
    interp V ρ (BConst.type .natRec us) =
      piC (piC (omega : V) fun _ => univ (lv us 0)) fun M =>
        piC (app M natzero) fun _ =>
          piC (natStepSpace V M) fun _ =>
            piC omega fun t => app M t := by
  show piC (piC (omega : V) fun _ => univ (lv us 0)) _ = _
  congr 1
  funext M
  show piC (app M natzero) _ = _
  congr 1
  funext z
  show piC (piC (omega : V) fun n =>
      piC (app M n) fun _ => app M (app (natSuccV V) n)) _ = _
  rw [natStepSpace_eq]
  rfl

theorem bval_mem_natRec (us : List Nat) (ρ : Nat → V) :
    bval V .natRec us ∈ˢ interp V ρ (BConst.type .natRec us) := by
  rw [interp_type_natRec]
  refine lamC_mem fun M _ => lamC_mem fun z hz => lamC_mem fun s hs => ?_
  refine lamC_mem fun n hn => ?_
  refine natrec_mem hz (fun k hk ih hih => ?_) hn
  exact app_mem_piC (app_mem_piC hs hk) hih

/-! ## `PUnit` -/

theorem bval_mem_punit (us : List Nat) (ρ : Nat → V) :
    bval V .punit us ∈ˢ interp V ρ (BConst.type .punit us) :=
  unitSet_mem_univ _

theorem bval_mem_punitUnit (us : List Nat) (ρ : Nat → V) :
    bval V .punitUnit us ∈ˢ interp V ρ (BConst.type .punitUnit us) :=
  pt_mem_unitSet

theorem bval_mem_punitRec (us : List Nat) (ρ : Nat → V) :
    bval V .punitRec us ∈ˢ interp V ρ (BConst.type .punitRec us) := by
  show punitRecV V (lv us 1) ∈ˢ
    piC (piC (unitSet : V) fun _ => univ (lv us 1)) fun M =>
      piC (app M pt) fun _ => piC unitSet fun t => app M t
  refine lamC_mem fun M _ => lamC_mem fun m hm => lamC_mem fun t ht => ?_
  rw [mem_unitSet ht]
  exact hm

/-! ## `Empty` -/

theorem bval_mem_empty (us : List Nat) (ρ : Nat → V) :
    bval V .empty us ∈ˢ interp V ρ (BConst.type .empty us) :=
  empty_mem_univ _

theorem bval_mem_emptyRec (us : List Nat) (ρ : Nat → V) :
    bval V .emptyRec us ∈ˢ interp V ρ (BConst.type .emptyRec us) := by
  show (pt : V) ∈ˢ
    piC (piC (empty : V) fun _ => univ (lv us 1)) fun M =>
      piC empty fun t => app M t
  refine pt_mem_piC_iff.mpr fun M _ => ?_
  rw [piC_empty]
  exact pt_mem_unitSet

/-! ## `PSigma'` -/

theorem bval_mem_psigma (us : List Nat) (ρ : Nat → V) :
    bval V .psigma us ∈ˢ interp V ρ (BConst.type .psigma us) := by
  show psigmaV V (lv us 0) (lv us 1) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (piC A fun _ => univ (lv us 1)) fun _ =>
        univ (Nat.max (lv us 0) (lv us 1))
  rw [psigmaV]
  exact lamC_mem fun A hA => lamC_mem fun B hB =>
    sigma_mem_univ hA fun x hx => app_mem_piC hB hx

theorem bval_mem_psigmaMk (us : List Nat) (ρ : Nat → V) :
    bval V .psigmaMk us ∈ˢ interp V ρ (BConst.type .psigmaMk us) := by
  show psigmaMkV V (lv us 0) (lv us 1) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (piC A fun _ => univ (lv us 1)) fun B =>
        piC A fun a =>
          piC (app B a) fun _ =>
            app (app (psigmaV V (lv us 0) (lv us 1)) A) B
  rw [psigmaMkV]
  refine lamC_mem fun A hA => lamC_mem fun B hB => lamC_mem fun a ha =>
    lamC_mem fun b hb => ?_
  rw [psigmaV_app V hA hB]
  split
  · next h => rw [h]; exact pt_mem_sigma ha hb
  · next h => exact spair_mem h ha hb

/-! ## `Quot` -/

theorem bval_mem_quot (us : List Nat) (ρ : Nat → V) :
    bval V .quot us ∈ˢ interp V ρ (BConst.type .quot us) := by
  show quotV V (lv us 0) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (relSpace V A) fun _ => univ (lv us 0)
  rw [quotV]
  exact lamC_mem fun A hA => lamC_mem fun _ _ => quotSet_mem_univ hA

theorem bval_mem_quotMk (us : List Nat) (ρ : Nat → V) :
    bval V .quotMk us ∈ˢ interp V ρ (BConst.type .quotMk us) := by
  show quotMkV V (lv us 0) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (relSpace V A) fun R =>
        piC A fun _ => app (app (quotV V (lv us 0)) A) R
  rw [quotMkV]
  refine lamC_mem fun A hA => lamC_mem fun R hR => ?_
  rw [quotV_app V hA hR]
  exact lamC_mem fun _ ha => quotClass_mem ha

theorem bval_mem_quotLift (us : List Nat) (ρ : Nat → V) :
    bval V .quotLift us ∈ˢ interp V ρ (BConst.type .quotLift us) := by
  show quotLiftV V (lv us 0) (lv us 1) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (relSpace V A) fun R =>
        piC (univ (lv us 1) : V) fun B =>
          piC (piC A fun _ => B) fun f =>
            piC (quotInvSpace V A R f) fun _ =>
              piC (app (app (quotV V (lv us 0)) A) R) fun _ => B
  rw [quotLiftV]
  refine lamC_mem fun A hA => lamC_mem fun R hR => lamC_mem fun B _ =>
    lamC_mem fun f hf => lamC_mem fun h hh => ?_
  rw [quotV_app V hA hR]
  exact quotLift_mem hA hf (quotInv_of_mem V hh)

theorem bval_mem_quotInd (us : List Nat) (ρ : Nat → V) :
    bval V .quotInd us ∈ˢ interp V ρ (BConst.type .quotInd us) := by
  show (pt : V) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (relSpace V A) fun R =>
        piC (piC (app (app (quotV V (lv us 0)) A) R) fun _ => univ 0) fun M =>
          piC (piC A fun a =>
              app M (app (app (app (quotMkV V (lv us 0)) A) R) a)) fun _ =>
            piC (app (app (quotV V (lv us 0)) A) R) fun q => app M q
  refine pt_mem_piC_iff.mpr fun A hA => ?_
  refine pt_mem_piC_iff.mpr fun R hR => ?_
  refine pt_mem_piC_iff.mpr fun M hM => ?_
  refine pt_mem_piC_iff.mpr fun mi hmi => ?_
  refine pt_mem_piC_iff.mpr fun q hq => ?_
  have hMq : app M q ∈ˢ (univ 0 : V) := app_mem_piC hM hq
  rw [quotV_app V hA hR] at hq
  obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
  have h1 : app mi a ∈ˢ app M (app (app (app (quotMkV V (lv us 0)) A) R) a) :=
    app_mem_piC hmi ha
  rw [quotMkV_app V hA hR ha] at h1
  exact mem_univ_zero hMq h1 ▸ h1

theorem bval_mem_quotSound (us : List Nat) (ρ : Nat → V) :
    bval V .quotSound us ∈ˢ interp V ρ (BConst.type .quotSound us) := by
  show (pt : V) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (relSpace V A) fun R =>
        piC A fun a => piC A fun b =>
          piC (app (app R a) b) fun _ =>
            eqv (app (app (app (quotMkV V (lv us 0)) A) R) a)
              (app (app (app (quotMkV V (lv us 0)) A) R) b)
  refine pt_mem_piC_iff.mpr fun A hA => ?_
  refine pt_mem_piC_iff.mpr fun R hR => ?_
  refine pt_mem_piC_iff.mpr fun a ha => ?_
  refine pt_mem_piC_iff.mpr fun b hb => ?_
  refine pt_mem_piC_iff.mpr fun _wv hwv => ?_
  rw [quotMkV_app V hA hR ha, quotMkV_app V hA hR hb,
    SetTheory.quotSound ha hb hwv]
  exact pt_mem_eqv_self _

/-! ## The standard axioms -/

theorem bval_mem_propext (us : List Nat) (ρ : Nat → V) :
    bval V .propext us ∈ˢ interp V ρ (BConst.type .propext us) := by
  show (pt : V) ∈ˢ
    piC (univ 0 : V) fun A => piC (univ 0 : V) fun B =>
      piC (piC A fun _ => B) fun _ =>
        piC (piC B fun _ => A) fun _ => eqv A B
  refine pt_mem_piC_iff.mpr fun A hA => ?_
  refine pt_mem_piC_iff.mpr fun B hB => ?_
  refine pt_mem_piC_iff.mpr fun f hf => ?_
  refine pt_mem_piC_iff.mpr fun g hg => ?_
  have hAB : A = B := by
    refine prop_ext hA hB (fun hp => ?_) (fun hp => ?_)
    · have h1 : app f pt ∈ˢ B := app_mem_piC hf hp
      exact mem_univ_zero hB h1 ▸ h1
    · have h1 : app g pt ∈ˢ A := app_mem_piC hg hp
      exact mem_univ_zero hA h1 ▸ h1
  rw [hAB]
  exact pt_mem_eqv_self _

theorem bval_mem_choice (us : List Nat) (ρ : Nat → V) :
    bval V .choice us ∈ˢ interp V ρ (BConst.type .choice us) := by
  show choiceV V (lv us 0) ∈ˢ
    piC (univ (lv us 0) : V) fun A =>
      piC (piC (piC A fun _ => (empty : V)) fun _ => empty) fun _ => A
  rw [choiceV]
  refine lamC_mem fun A _ => lamC_mem fun h hh => ?_
  obtain ⟨x, hx⟩ := exists_mem_of_dneg V hh
  exact schoice_mem hx

/-! ## The `const` rule's semantic content -/

/-- **Every built-in constant inhabits its type.** -/
theorem bval_mem_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    bval V c us ∈ˢ interp V ρ (c.type us) := by
  cases c with
  | nat => exact bval_mem_nat V us ρ
  | natZero => exact bval_mem_natZero V us ρ
  | natSucc => exact bval_mem_natSucc V us ρ
  | natRec => exact bval_mem_natRec V us ρ
  | punit => exact bval_mem_punit V us ρ
  | punitUnit => exact bval_mem_punitUnit V us ρ
  | punitRec => exact bval_mem_punitRec V us ρ
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

end Setlec.TT
