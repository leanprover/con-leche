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

theorem trCI_levelParams (ci : Lean.ConstantInfo) :
    (trCI ci).toConstantVal.levelParams = ci.levelParams.map toName := by
  cases ci <;> rfl

theorem capsFree_toConstantVal (P : ConLeche.ConstantInfo) :
    (capsFree P).toConstantVal = P.toConstantVal := by
  cases P <;> rfl

theorem capsFree_name (P : ConLeche.ConstantInfo) : (capsFree P).name = P.name := by
  cases P <;> rfl

theorem nodup_tr : ∀ (l : List Lean.Name), ConLeche.Name.nodup (l.map toName) = InLean.namesNodup l
  | [] => rfl
  | n :: l => by
    simp only [List.map_cons, ConLeche.Name.nodup, InLean.namesNodup, contains_map_toName, nodup_tr l]

/-- **One constant against its pin**, master's at the translation. -/
theorem pinCopyOk_tr {ci pin : Lean.ConstantInfo} {P : ConLeche.ConstantInfo}
    (hci : CIOk ci) (hpin : CIOk pin) (hP : capsFree P = trCI pin)
    (h : InLean.pinCopyOk ci pin = true) : ConLeche.pinCopyOk (trCI ci) P = true := by
  simp only [InLean.pinCopyOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hnd, hlen⟩, hag⟩ := h
  have hPl : P.toConstantVal.levelParams = pin.levelParams.map toName := by
    rw [← capsFree_toConstantVal, hP, trCI_levelParams]
  simp only [ConLeche.pinCopyOk, trCI_levelParams, nodup_tr, hnd, hPl, List.length_map, hlen,
    beq_self_eq_true, Bool.true_and]
  rw [pinAgrees_capsFree, hP]
  exact pinAgrees_tr hci hpin hag

/-- The lists, pairwise. -/
theorem listBeqBy_tr : ∀ {block pins : List Lean.ConstantInfo} {Ps : List ConLeche.ConstantInfo},
    Ps.map capsFree = pins.map trCI → (∀ ci ∈ block, CIOk ci) → (∀ p ∈ pins, CIOk p) →
    InLean.listBeqBy InLean.pinCopyOk block pins = true →
    ConLeche.listBeqBy ConLeche.pinCopyOk (block.map trCI) Ps = true
  | [], [], [], _, _, _, _ => rfl
  | c :: cs, p :: ps, P :: Ps, hPs, hb, hp, h => by
    simp only [List.map_cons, List.cons.injEq] at hPs
    simp only [InLean.listBeqBy, Bool.and_eq_true] at h
    simp only [List.map_cons, ConLeche.listBeqBy, Bool.and_eq_true]
    exact ⟨pinCopyOk_tr (hb c List.mem_cons_self) (hp p List.mem_cons_self) hPs.1 h.1,
      listBeqBy_tr hPs.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h.2⟩
  | [], [], _ :: _, hPs, _, _, _ => by simp at hPs
  | [], _ :: _, _, _, _, _, h => by simp [InLean.listBeqBy] at h
  | _ :: _, [], _, _, _, _, h => by simp [InLean.listBeqBy] at h
  | _ :: _, _ :: _, [], hPs, _, _, _ => by simp at hPs

/-! ## The links -/

theorem getParamSubst_tr (p : Lean.Name) :
    ∀ (Rp : List Lean.Name) (us : List Lean.Level),
      trL ((Level.param p).substParams (Level.getParamSubst Rp us)) =
        ConLeche.Level.subst.go (Rp.map toName) (us.map trL) (toName p)
  | [], us => by cases us <;> simp [Level.substParams, Level.substParams.go, Level.getParamSubst,
      ConLeche.Level.subst.go, trL]
  | _ :: _, [] => by simp [Level.substParams, Level.substParams.go, Level.getParamSubst,
      ConLeche.Level.subst.go, trL]
  | r :: Rp, u :: us => by
    have ih := getParamSubst_tr p Rp us
    simp only [Level.substParams, Level.substParams.go, Level.getParamSubst] at ih ⊢
    simp only [List.map_cons, ConLeche.Level.subst.go]
    rw [name_beq_eq_decide]
    by_cases h : toName r = toName p
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

theorem okL_param_list (C : List Lean.Name) : (C.map Level.param).all okL = true := by
  simp [okL]

theorem pinLinkOk_tr (R Rp C Cp : List Lean.Name) (h : InLean.pinLinkOk R Rp C Cp = true) :
    ConLeche.pinLinkOk (R.map toName) (Rp.map toName) (C.map toName) (Cp.map toName) = true := by
  simp only [InLean.pinLinkOk, beq_iff_eq] at h
  simp only [ConLeche.pinLinkOk, beq_iff_eq]
  have := congrArg (List.map trL) h
  simp only [List.map_map] at this
  simp only [List.map_map]
  have e1 : List.map (ConLeche.Level.param ∘ toName) C = List.map (trL ∘ Level.param) C :=
    List.map_congr_left fun _ _ => rfl
  have e2 : List.map ((fun p => ConLeche.Level.subst (List.map toName Rp)
      (List.map (ConLeche.Level.param ∘ toName) R) (ConLeche.Level.param p)) ∘ toName) Cp =
      List.map (trL ∘ fun p => (Level.param p).instantiateParams Rp (List.map Level.param R)) Cp := by
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Level.instantiateParams, ConLeche.Level.subst]
    rw [getParamSubst_tr]
    simp [Function.comp_def, trL]
  rw [e1, e2]
  exact this

/-- A list's constant by name, translated. -/
theorem constNamed?_tr (n : Lean.Name) (l : List Lean.ConstantInfo) :
    ConLeche.constNamed? (l.map trCI) (toName n) = (InLean.constNamed? l n).map trCI := by
  simp only [ConLeche.constNamed?, InLean.constNamed?, List.find?_map]
  congr 2
  funext c
  simp only [Function.comp_apply, trCI_name, toName_beq]

theorem constNamed?_caps (n : Lean.Name) : ∀ (Ps : List ConLeche.ConstantInfo) (l : List Lean.ConstantInfo),
    Ps.map capsFree = l.map trCI →
    (ConLeche.constNamed? Ps (toName n)).map capsFree = (InLean.constNamed? l n).map trCI
  | [], [], _ => rfl
  | P :: Ps, c :: l, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hn : P.name = toName c.name := by rw [← capsFree_name, h.1, trCI_name]
    simp only [ConLeche.constNamed?, InLean.constNamed?, List.find?_cons, hn, toName_beq]
    split
    · simp [h.1]
    · exact constNamed?_caps n Ps l h.2
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem levelParams_capsFree_some {o : Option ConLeche.ConstantInfo} {o' : Option Lean.ConstantInfo}
    (h : o.map capsFree = o'.map trCI) :
    o.map (·.toConstantVal.levelParams) = o'.map (fun c => c.levelParams.map toName) := by
  cases o <;> cases o' <;> simp_all
  rename_i P c
  rw [← capsFree_toConstantVal, h, trCI_levelParams]

/-- **The links**, master's at the translation. -/
theorem blockLinksOk_tr {block pins : List Lean.ConstantInfo} {Ps : List ConLeche.ConstantInfo}
    (hPs : Ps.map capsFree = pins.map trCI) (h : InLean.blockLinksOk block pins = true) :
    ConLeche.blockLinksOk (block.map trCI) Ps = true := by
  unfold InLean.blockLinksOk at h
  unfold ConLeche.blockLinksOk
  have hF : ((block.map trCI).head?.map (·.toConstantVal.levelParams)).getD [] =
      ((block.head?.map (·.levelParams)).getD []).map toName := by
    cases block <;> simp [trCI_levelParams]
  rw [hF]
  generalize (block.head?.map (·.levelParams)).getD [] = F at h ⊢
  -- pairwise, keeping the whole lists for `constNamed?`
  have key : ∀ (bs : List Lean.ConstantInfo) (qs : List Lean.ConstantInfo)
      (Qs : List ConLeche.ConstantInfo), Qs.map capsFree = qs.map trCI →
      ((bs.zip qs).all fun (cp : Lean.ConstantInfo × Lean.ConstantInfo) =>
        match cp.1, cp.2 with
        | .ctorInfo v, _ => v.levelParams == F
        | .recInfo v, .recInfo vp =>
          vp.rules.all fun rl =>
            match InLean.constNamed? block rl.ctor, InLean.constNamed? pins rl.ctor with
            | some C, some Cp =>
              InLean.pinLinkOk v.levelParams vp.levelParams C.levelParams Cp.levelParams
            | _, _ => false
        | _, _ => true) = true →
      (((bs.map trCI).zip Qs).all fun (cp : ConLeche.ConstantInfo × ConLeche.ConstantInfo) =>
        match cp.1, cp.2 with
        | .ctorInfo cv _ _, _ => cv.levelParams == F.map toName
        | .recInfo cv .., .recInfo cvp _ _ _ rules =>
          rules.all fun rl =>
            match ConLeche.constNamed? (block.map trCI) rl.ctor, ConLeche.constNamed? Ps rl.ctor with
            | some C, some Cp =>
              ConLeche.pinLinkOk cv.levelParams cvp.levelParams C.toConstantVal.levelParams
                Cp.toConstantVal.levelParams
            | _, _ => false
        | _, _ => true) = true := by
    intro bs
    induction bs with
    | nil => intro _ _ _ _; rfl
    | cons c bs ih =>
      intro qs Qs hQ hall
      cases qs with
      | nil => cases Qs with
        | nil => rfl
        | cons _ _ => simp at hQ
      | cons q qs =>
        cases Qs with
        | nil => simp at hQ
        | cons Q Qs =>
          simp only [List.map_cons, List.cons.injEq] at hQ
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih qs Qs hQ.2 hall.2⟩
          have h1 := hall.1
          cases c with
          | ctorInfo v =>
            simp only [trCI] at h1 ⊢
            rw [show (trCV v.toConstantVal).levelParams = v.levelParams.map toName from rfl,
              map_toName_beq]
            exact h1
          | recInfo v =>
            cases q with
            | recInfo vp =>
              have hQ' : Q = .recInfo (trCV vp.toConstantVal) (majorIdxOf vp) (rulePrefixOf vp) vp.k
                  (vp.rules.map trRule) := by
                have hq1 := hQ.1
                cases Q with
                | recInfo cv mI rP k rules => exact hq1
                | indInfo _ _ => simp [capsFree, trCI] at hq1
                | _ => simp [capsFree, trCI] at hq1
              subst hQ'
              simp only [trCI, List.all_map, List.all_eq_true, Function.comp_apply] at h1 ⊢
              intro rl hrl
              have h2 := h1 rl hrl
              simp only [trRule]
              rw [constNamed?_tr]
              have hc := levelParams_capsFree_some (constNamed?_caps rl.ctor Ps pins hPs)
              generalize InLean.constNamed? block rl.ctor = A at h2 ⊢
              generalize InLean.constNamed? pins rl.ctor = B at h2 hc
              generalize ConLeche.constNamed? Ps (toName rl.ctor) = Cc at hc ⊢
              cases A with
              | none => simp at h2
              | some a =>
                cases B with
                | none => simp at h2
                | some b =>
                  cases Cc with
                  | none => simp at hc
                  | some cc =>
                    simp only [Option.map_some, Option.some.injEq] at hc h2 ⊢
                    rw [trCI_levelParams, hc]
                    exact pinLinkOk_tr _ _ _ _ h2
            | _ =>
              have hq1 := hQ.1
              cases Q with
              | recInfo cv mI rP k rules => simp [capsFree, trCI] at hq1
              | _ => rfl
          | _ => cases Q <;> rfl
  exact key block pins Ps hPs h

end InLeanProof
