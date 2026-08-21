import Setlec.SetTheory.Basic
import Setlec.SetTheory.Derive.Sigma
import Setlec.SetTheory.Derive.Natrec
import Setlec.SetTheory.Derive.Quot
import Setlec.SetTheory.Derive.Choice

/-!
# `SetTheory` from the minimal core

The operator class `SetTheory` (`Setlec/SetTheory/Basic.lean`) is
constructed from the minimal `TG` core: every field is one of the
derived operators/laws of `Setlec/SetTheory/Derive/*`.  With this
instance, "assuming a model of `SetTheory`" weakens to "assuming a
model of the seven TG axioms" (plus Lean's own classical meta-logic).

Everything the interface asks for — including the quotient laws,
`prop_ext` (from `univZero_ext`; `univ 0 = univZero` by `rfl`) and
the global selector `schoice` — is one of the derived theorems; no
field has independent axiomatic content beyond the `TG` core.
-/

namespace Setlec

universe u

open TG

noncomputable instance TG.toSetTheory {V : Type u} [TG V] : SetTheory V where
  Mem := TG.Mem
  empty := TG.empty
  not_mem_empty := TG.not_mem_empty
  univ := TG.univ
  univ_mem_univ := TG.univ_mem_univ
  empty_mem_univ := TG.empty_mem_univ
  pi := TG.pi
  pi_mem_univ := TG.pi_mem_univ
  pi_congr := TG.pi_congr
  lam := TG.lam
  app := TG.app
  lam_congr := TG.lam_congr
  lam_mem := TG.lam_mem
  app_mem := fun hf ha hB =>
    TG.app_mem hf ha (fun hv x hx => by subst hv; exact hB x hx)
  app_lam := fun ha hF hB =>
    TG.app_lam ha hF (fun hv x hx => by subst hv; exact hB x hx)
  pt := TG.pt
  mem_univ_zero := TG.eq_pt_of_mem_univZero
  mem_pi_zero := TG.mem_pi_zero
  lam_ne_pt := fun hv => TG.lam_ne_pt hv
  lam_dom := TG.lam_dom
  eqv := TG.eqv
  eqv_mem_univ := TG.eqv_mem_univZero
  mem_eqv := TG.eq_of_mem_eqv
  pt_mem_eqv_self := TG.pt_mem_eqv_self
  unitSet := TG.unitSet
  pt_mem_unitSet := TG.pt_mem_unitSet
  mem_unitSet := TG.mem_unitSet.mp
  unitSet_mem_univ := TG.unitSet_mem_univ
  omega := TG.omega
  omega_mem_univ := TG.omega_mem_univ_succ 0
  natzero := TG.empty
  natzero_mem := TG.empty_mem_omega
  natsucc := TG.vsucc
  natsucc_mem := TG.vsucc_mem_omega
  natrec := TG.natrec
  natrec_zero := TG.natrec_empty
  natrec_succ := fun z s {_n} hn => TG.natrec_vsucc z s hn
  natrec_mem := TG.natrec_mem
  sigmaSet := TG.sigmaSet
  spair := TG.spair
  sfst := TG.sfst
  ssnd := TG.ssnd
  sigma_congr := TG.sigma_congr
  sigma_mem_univ := TG.sigma_mem_univ
  spair_mem := TG.spair_mem
  pt_mem_sigma := TG.pt_mem_sigma
  mem_sigma_elim := TG.mem_sigma_elim
  sfst_spair := TG.sfst_spair
  ssnd_spair := TG.ssnd_spair
  sfst_pt := TG.sfst_pt
  ssnd_pt := TG.ssnd_pt
  app_pt := TG.app_pt
  lam_eta := TG.lam_eta
  lam_zero := TG.lam_zero
  quotSet := TG.quotSet
  quotClass := TG.quotClass
  quotLift := TG.quotLift
  quotSet_mem_univ := TG.quotSet_mem_univ
  quotClass_mem := TG.quotClass_mem
  quotClass_surj := TG.quotClass_surj
  quotSound := TG.quotSound
  quotLift_mem := TG.quotLift_mem
  quotLift_beta := TG.quotLift_beta
  prop_ext := TG.univZero_ext
  schoice := TG.schoice
  schoice_mem := TG.schoice_mem

end Setlec
