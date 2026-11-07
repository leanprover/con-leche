module

public import InLeanProof.IndTele
/- `ConstantInfo.type`/`levelParams` are read as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `Level.instantiateParams` on a parameter (`pinLinkOk`). -/
import all Lean.Level

/-!
# O7: a pinned basis block against master's (task #451, lane O7)

`basisBlockSimI : BasisBlockSimI`.  A block at a pinned block's names
(`basisNameHit`) is compared with the pin (`pinListOk`) and its constants are
added if fresh.

* The pins: InLean's (`InLean/Inductives/Basis.lean`, Lean entries) translate
  to master's (`ConLeche/Kernel/Basis/*`) up to an inductive's capabilities,
  which master's `pinAgrees` does not read (`pins_tr`, by evaluation), and
  their terms have closed readings (`pins_ok`).
* `pinCopyOk_tr`: InLean's comparison (`pinAgrees` up to `mdata` and binder
  data, at `ciAtLps`) implies master's on the translation: `Expr.clEq` gives
  equal readings (`toExpr_of_clEq`), level instantiation reads as master's
  (`toExpr_instantiateLevelParams`; it wrote no marker since the compared
  record has a reading).
* `blockLinksOk_tr`: the links (`pinLinkOk` through
  `Level.instantiateParams` at a parameter, master's `Level.subst`).
* The fold: InLean's freshness checks against its growing environment give
  distinct names, fresh in `fe` (`EnvLaws`), hence in `L` (`EnvPresI.none`);
  master's `installBasisDecl` fold then succeeds.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## The pins -/

/-- Master's constant with an inductive's capabilities dropped. -/
@[expose] def capsFree : ConLeche.ConstantInfo → ConLeche.ConstantInfo
  | .indInfo cv _ => .indInfo cv {}
  | c => c

/-- **InLean's pins translate to master's**, up to capabilities. -/
theorem pins_tr (k : InLean.BasisKind) : k.decls.map trCI = (trKind k).decls.map capsFree := by
  cases k <;> decide

/-- A pin's terms have closed readings (Boolean, for evaluation). -/
@[expose] def ciOkB : Lean.ConstantInfo → Bool
  | .recInfo v => okC v.type && v.rules.all fun r => okC r.rhs
  | ci => okC ci.toConstantVal.type

theorem CIOk_of_ciOkB {ci : Lean.ConstantInfo} (h : ciOkB ci = true) : CIOk ci := by
  cases ci with
  | recInfo v =>
    simp only [ciOkB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨h.1, h.2⟩
  | _ => exact h

theorem pins_ok (k : InLean.BasisKind) : ∀ p ∈ k.decls, CIOk p := by
  have : k.decls.all ciOkB = true := by cases k <;> decide
  intro p hp
  exact CIOk_of_ciOkB (List.all_eq_true.1 this p hp)

theorem pins_names (k : InLean.BasisKind) : ∀ p ∈ k.decls, p.name ≠ InLean.sorryAxName := by
  have : ∀ p ∈ k.decls, toName p.name ≠ toName InLean.sorryAxName := by cases k <;> decide
  intro p hp he
  exact this p hp (congrArg toName he)

/-! ## Level instantiation read through a comparison -/

theorem emvarS_of_toExpr {fv : FVarId → Option ConLeche.Expr} :
    ∀ {e : Lean.Expr} {c : ConLeche.Expr}, toExpr fv e = some c → emvarS e = false := by
  intro e
  induction e with
  | mvar _ => intro c h; simp [toExpr] at h
  | app f a ihf iha =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨cf, hf, ca, ha, _⟩ := h
    simp [emvarS, ihf hf, iha ha]
  | lam _ t b _ iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨ct, ht, cb, hb, _⟩ := h
    simp [emvarS, iht ht, ihb hb]
  | forallE _ t b _ iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨ct, ht, cb, hb, _⟩ := h
    simp [emvarS, iht ht, ihb hb]
  | letE _ t v b _ iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, _⟩ := h
    simp [emvarS, iht ht, ihv hv, ihb hb]
  | mdata _ x ih => intro c h; simp only [toExpr] at h; simp [emvarS, ih h]
  | proj _ _ x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, _⟩ := h
    simp [emvarS, ih hx]
  | _ => intro _ _; rfl

theorem toExprC_of_okC {e : Lean.Expr} (h : okC e = true) : toExprC e = some (trC e) :=
  toExpr_of_okE _ h

theorem fvarS_of_okC : ∀ {e : Lean.Expr}, okC e = true → fvarS e = false := by
  intro e
  induction e <;> simp_all [okC, okE, fvarS]

theorem toLevels_params (ps : List Lean.Name) :
    toLevels (ps.map Level.param) = some ((ps.map toName).map ConLeche.Level.param) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [toLevels, toLevel, ih]

/-- **A comparison with a pin at other level names, read through the
translation.** -/
theorem trC_of_clEq_inst {a e : Lean.Expr} (ha : okC a = true) (he : okC e = true)
    (lps ps : List Lean.Name)
    (h : Expr.clEq a (EO.instantiateLevelParams e lps (ps.map Level.param)) = true) :
    trC a = (trC e).instantiateLevelParams (lps.map toName) ((ps.map toName).map ConLeche.Level.param) := by
  have h1 := toExpr_of_clEq (fun _ => none) h
  rw [show toExpr (fun _ => none) a = some (trC a) from toExprC_of_okC ha] at h1
  have hnp := emvarS_of_toExpr h1.symm
  have h2 := toExpr_instantiateLevelParams (RangeOk_of_okE he) (fvarS_of_okC he)
    (toExprC_of_okC he) lps (toLevels_params ps) hnp
  rw [h2] at h1
  exact Option.some.inj h1

/-! ## One constant against its pin -/

theorem pinAgrees_capsFree (x P : ConLeche.ConstantInfo) (qs : List ConLeche.Name) :
    ConLeche.pinAgrees x (P.atLps qs) = ConLeche.pinAgrees x ((capsFree P).atLps qs) := by
  cases P <;> cases x <;> rfl

theorem beqP_of_eq {a b : ConLeche.ConstantVal} (h : a = b) : a.beqP b = true := by
  subst h; simp [ConLeche.ConstantVal.beqP]

/-- **InLean's comparison with a pin implies master's**, on the translation. -/
theorem pinAgrees_tr {ci pin : Lean.ConstantInfo} (hci : CIOk ci) (hpin : CIOk pin)
    (h : InLean.pinAgrees ci (ciAtLps pin ci.levelParams) = true) :
    ConLeche.pinAgrees (trCI ci) ((trCI pin).atLps (ci.levelParams.map toName)) = true := by
  cases ci with
  | inductInfo v =>
    cases pin with
    | inductInfo vp =>
      simp only [ciAtLps, InLean.pinAgrees, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hn, ht⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
      simp only [trCI, ConLeche.pinAgrees, ConLeche.ConstantInfo.atLps,
        ConLeche.ConstantVal.atLps]
      apply beqP_of_eq
      simp only [trCV, ConLeche.ConstantVal.mk.injEq, hn, true_and]
      refine ⟨rfl, ?_⟩
      exact trC_of_clEq_inst hci hpin _ _ ht
    | _ => simp [ciAtLps, InLean.pinAgrees] at h
  | ctorInfo v =>
    cases pin with
    | ctorInfo vp =>
      simp only [ciAtLps, InLean.pinAgrees, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hn, ht⟩, -⟩, hp⟩, hf⟩ := h
      simp only [trCI, ConLeche.pinAgrees, ConLeche.ConstantInfo.atLps,
        ConLeche.ConstantVal.atLps, ConLeche.ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨beqP_of_eq ?_, hp⟩, hf⟩
      simp only [trCV, ConLeche.ConstantVal.mk.injEq, hn, true_and]
      exact ⟨rfl, trC_of_clEq_inst hci hpin _ _ ht⟩
    | _ => simp [ciAtLps, InLean.pinAgrees] at h
  | recInfo v =>
    cases pin with
    | recInfo vp =>
      obtain ⟨hct, hcr⟩ := hci
      obtain ⟨hpt, hpr⟩ := hpin
      simp only [ciAtLps, InLean.pinAgrees, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hn, ht⟩, -⟩, hmI⟩, hrP⟩, hk⟩, hlen⟩, hrules⟩ := h
      simp only [trCI, ConLeche.pinAgrees, ConLeche.ConstantInfo.atLps,
        ConLeche.ConstantVal.atLps, ConLeche.ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨beqP_of_eq ?_, hmI⟩, hrP⟩, hk⟩, ?_⟩
      · simp only [trCV, ConLeche.ConstantVal.mk.injEq, hn, true_and]
        exact ⟨rfl, trC_of_clEq_inst hct hpt _ _ ht⟩
      · simp only [List.map_map]
        -- the rules, pairwise
        generalize v.rules = rs at hcr hlen hrules
        generalize vp.rules = rps at hpr hlen hrules
        induction rs generalizing rps with
        | nil => cases rps <;> simp_all [ConLeche.listBeqBy]
        | cons r rs ih =>
          cases rps with
          | nil => simp at hlen
          | cons rp rps =>
            simp only [List.length_cons] at hlen
            rw [List.map_cons, List.zip_cons_cons] at hrules
            simp only [List.map_cons, ConLeche.listBeqBy, Bool.and_eq_true]
            refine ⟨?_, ih (fun x hx => hcr x (List.mem_cons_of_mem _ hx)) rps
              (fun x hx => hpr x (List.mem_cons_of_mem _ hx)) (by simpa using hlen)
              (fun x hx => hrules x (List.mem_cons_of_mem _ hx))⟩
            have h1 := hrules _ List.mem_cons_self
            obtain ⟨⟨hc, hnf⟩, hrhs⟩ := h1
            simp only [Function.comp_apply, trRule, ConLeche.RecRule.beqP, Bool.and_eq_true,
              beq_iff_eq, ConLeche.RecRuleFire.atLps, ConLeche.RecRuleFire.beqP, and_true]
            refine ⟨⟨congrArg toName hc, hnf⟩, ?_⟩
            have := trC_of_clEq_inst (hcr r List.mem_cons_self) (hpr rp List.mem_cons_self) _ _ hrhs
            simp only [List.map_map, ConLeche.ConstantInfo.toConstantVal, trCV] at this ⊢
            exact this
    | _ => simp [ciAtLps, InLean.pinAgrees] at h
  | axiomInfo _ | defnInfo _ | thmInfo _ | opaqueInfo _ | quotInfo _ =>
    simp [InLean.pinAgrees] at h

end InLeanProof
