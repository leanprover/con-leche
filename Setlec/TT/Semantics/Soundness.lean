import Setlec.TT.Semantics.ConstOk

/-!
# Soundness

**One induction, no mutual recursion.**  `HasType.sound` is a single
induction over the typing derivation.  There is no companion induction
for definitional equality, because there is no definitional-equality
judgment: an equation is a *typing* statement `Γ ⊢ prf : eqE T a b`, and
membership in `⟦eqE T a b⟧ = eqv ⟦a⟧ ⟦b⟧` **is** the equation
`⟦a⟧ = ⟦b⟧`.  Equality reflection (`conv`) is therefore sound by
`mem_eqv` alone.

Two structural payoffs of the design show up in the proof:

* the `app` case gets `⟦a⟧ ∈ ⟦A⟧` from its own premise, so `beta`
  (`app_lamC`) fires with no side condition at all — the checker has to
  re-establish exactly this fact at every reduction site, because the
  collapsed `app` is non-invertible;
* nothing corresponding to `AnnotOk` appears: the interpretation is
  total, and every fibre/membership fact the model needs is read off a
  premise.
-/

namespace Setlec.TT

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-- `ρ` satisfies `Γ`: each variable's value inhabits its declared type,
interpreted in the environment that variable's type actually lives in
(the outer part of `ρ`). -/
def Sat (Γ : List VExpr) (ρ : Nat → V) : Prop :=
  ∀ i A, Γ[i]? = some A → ρ i ∈ˢ interp V (fun j => ρ (j + i + 1)) A

theorem Sat_nil (ρ : Nat → V) : Sat V [] ρ := by
  intro i A hi
  cases hi

theorem Sat_cons {Γ : List VExpr} {A : VExpr} {ρ : Nat → V} {x : V}
    (hρ : Sat V Γ ρ) (hx : x ∈ˢ interp V ρ A) : Sat V (A :: Γ) (cons V x ρ) := by
  intro i A' hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact hx
  | succ j =>
    simp only [List.getElem?_cons_succ] at hi
    exact hρ j A' hi

/-- **Soundness.**  Every derivable typing holds in the set model. -/
theorem HasType.sound {Γ : List VExpr} {e A : VExpr} (h : HasType Γ e A) :
    ∀ ρ : Nat → V, Sat V Γ ρ → interp V ρ e ∈ˢ interp V ρ A := by
  induction h with
  | bvar hi =>
    intro ρ hρ
    rw [interp_liftN, shiftE_zero]
    exact hρ _ _ hi
  | sort => intro ρ _; exact univ_mem_univ _
  | const => intro ρ _; exact bval_mem_type V _ _ ρ
  | pi _ _ ihA ihB =>
    intro ρ hρ
    exact piC_mem_univ (ihA ρ hρ) fun x hx => ihB (cons V x ρ) (Sat_cons V hρ hx)
  | lam _ ihb =>
    intro ρ hρ
    exact lamC_mem fun x hx => ihb (cons V x ρ) (Sat_cons V hρ hx)
  | app _ _ ihf iha =>
    intro ρ hρ
    rw [interp_inst0]
    exact app_mem_piC (ihf ρ hρ) (iha ρ hρ)
  | letE _ _ _ _ _ ihbody =>
    intro ρ hρ
    have hb := ihbody ρ hρ
    rwa [interp_inst0] at hb
  | eqType => intro ρ _; exact eqv_mem_univ _ _
  | conv _ _ iht ihp =>
    intro ρ hρ
    exact mem_eqv (ihp ρ hρ) ▸ iht ρ hρ
  | refl => intro ρ _; exact pt_mem_eqv_self _
  | symm _ ihp =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [mem_eqv (ihp ρ hρ)]
    exact pt_mem_eqv_self _
  | trans _ _ ihp ihq =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [mem_eqv (ihp ρ hρ), mem_eqv (ihq ρ hρ)]
    exact pt_mem_eqv_self _
  | congrApp _ _ ihp ihq =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_app]
    rw [mem_eqv (ihp ρ hρ), mem_eqv (ihq ρ hρ)]
    exact pt_mem_eqv_self _
  | congrLam _hp _hq ihp ihq =>
    rename_i A A' b b' _ _
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_lam]
    have hA : interp V ρ A = interp V ρ A' := mem_eqv (ihp ρ hρ)
    have hbb : ∀ x, x ∈ˢ interp V ρ A →
        interp V (cons V x ρ) b = interp V (cons V x ρ) b' :=
      fun x hx => mem_eqv (ihq (cons V x ρ) (Sat_cons V hρ hx))
    rw [← hA, lamC_congr hbb]
    exact pt_mem_eqv_self _
  | congrPi _hp _hq ihp ihq =>
    rename_i A A' B B' _ _
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_pi]
    have hA : interp V ρ A = interp V ρ A' := mem_eqv (ihp ρ hρ)
    have hbb : ∀ x, x ∈ˢ interp V ρ A →
        interp V (cons V x ρ) B = interp V (cons V x ρ) B' :=
      fun x hx => mem_eqv (ihq (cons V x ρ) (Sat_cons V hρ hx))
    rw [← hA, piC_congr hbb]
    exact pt_mem_eqv_self _
  | congrEq _ _ ihp ihq =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [mem_eqv (ihp ρ hρ), mem_eqv (ihq ρ hρ)]
    exact pt_mem_eqv_self _
  | beta _ iha =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_app, interp_lam]
    rw [app_lamC (iha ρ hρ), interp_inst0]
    exact pt_mem_eqv_self _
  | zeta =>
    intro ρ _
    simp only [interp_prf, interp_eqE, interp_letE]
    rw [interp_inst0]
    exact pt_mem_eqv_self _
  | eta _hf ihf =>
    rename_i _ _ f
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_lam, interp_app, interp_bvar,
      cons_zero]
    have hfun : (fun x => SetTheory.app (interp V (cons V x ρ) (f.liftN 1)) x)
        = fun x => SetTheory.app (interp V ρ f) x := by
      funext x; rw [interp_lift_cons]
    rw [hfun, lamC_eta (ihf ρ hρ)]
    exact pt_mem_eqv_self _
  | funext _hf _hg _hp ihf ihg ihp =>
    rename_i A _ _ f g _
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    have hpt : ∀ x, x ∈ˢ interp V ρ A →
        SetTheory.app (interp V ρ f) x = SetTheory.app (interp V ρ g) x := by
      intro x hx
      have hx' := ihp (cons V x ρ) (Sat_cons V hρ hx)
      simp only [interp_eqE, interp_app, interp_bvar, cons_zero] at hx'
      rw [interp_lift_cons, interp_lift_cons] at hx'
      exact mem_eqv hx'
    rw [eq_of_mem_piC_app_eq (ihf ρ hρ) (ihg ρ hρ) hpt]
    exact pt_mem_eqv_self _
  | proofIrrel _ _ _ ihP ihh ihh' =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [mem_univ_zero (ihP ρ hρ) (ihh ρ hρ),
      mem_univ_zero (ihP ρ hρ) (ihh' ρ hρ)]
    exact pt_mem_eqv_self _
  | natRecZero _ _ _ ihM ihz ihs =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    have hsm := ihs ρ hρ
    rw [interp_natStepT] at hsm
    rw [interp_natRecT, interp_natZeroT,
      natRecV_app V (ihM ρ hρ) (ihz ρ hρ) hsm natzero_mem, natrec_zero]
    exact pt_mem_eqv_self _
  | natRecSucc _ _ _ _ ihM ihz ihs ihn =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_app]
    have hsm := ihs ρ hρ
    rw [interp_natStepT] at hsm
    have hnm := ihn ρ hρ
    rw [interp_natRecT, interp_natSuccT, natSuccV_app V hnm,
      natRecV_app V (ihM ρ hρ) (ihz ρ hρ) hsm (natsucc_mem hnm),
      natrec_succ _ _ hnm, interp_natRecT,
      natRecV_app V (ihM ρ hρ) (ihz ρ hρ) hsm hnm]
    exact pt_mem_eqv_self _
  | punitRecUnit _ _ ihM ihm =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [interp_punitRecT, interp_punitUnitT,
      punitRecV_app V (ihM ρ hρ) (ihm ρ hρ) pt_mem_unitSet]
    exact pt_mem_eqv_self _
  | punitEta _ _ ihx ihy =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    rw [mem_unitSet (ihx ρ hρ), mem_unitSet (ihy ρ hρ)]
    exact pt_mem_eqv_self _
  | psigmaFstMk _ _ _ _ ihA ihB iha ihb =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    have hBm := ihB ρ hρ
    simp only [interp_arrow, interp_sort] at hBm
    rw [interp_psigmaFstT, interp_psigmaMkT,
      psigmaFst_mk V (ihA ρ hρ) hBm (iha ρ hρ) (ihb ρ hρ)]
    exact pt_mem_eqv_self _
  | psigmaSndMk _ _ _ _ ihA ihB iha ihb =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    have hBm := ihB ρ hρ
    simp only [interp_arrow, interp_sort] at hBm
    rw [interp_psigmaSndT, interp_psigmaMkT,
      psigmaSnd_mk V (ihA ρ hρ) hBm (iha ρ hρ) (ihb ρ hρ)]
    exact pt_mem_eqv_self _
  | psigmaEta _ _ _ ihA ihB ihp =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE]
    have hBm := ihB ρ hρ
    simp only [interp_arrow, interp_sort] at hBm
    have hAm := ihA ρ hρ
    have hpm := ihp ρ hρ
    rw [interp_psigmaT, psigmaV_app V hAm hBm] at hpm
    rw [interp_psigmaMkT, interp_psigmaFstT, interp_psigmaSndT,
      psigmaFstV_app V hAm hBm hpm, psigmaSndV_app V hAm hBm hpm,
      psigmaEta_law V hAm hBm hpm]
    exact pt_mem_eqv_self _
  | quotLiftMk _ _ _ _ _ _ ihA ihr ihB ihf ihh iha =>
    intro ρ hρ
    simp only [interp_prf, interp_eqE, interp_app]
    have hAm := ihA ρ hρ
    have hRm := ihr ρ hρ
    rw [interp_relT] at hRm
    have hfm := ihf ρ hρ
    simp only [interp_arrow] at hfm
    have hhm := ihh ρ hρ
    rw [interp_quotInvT] at hhm
    have ham := iha ρ hρ
    rw [interp_quotLiftT, interp_quotMkT,
      quotLiftV_app V hAm hRm (ihB ρ hρ) hfm hhm, quotMkV_app V hAm hRm ham,
      quotLift_beta hAm ham (quotInv_of_mem V hhm)]
    exact pt_mem_eqv_self _

end Setlec.TT
