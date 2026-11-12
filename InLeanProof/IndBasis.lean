module

public import InLeanProof.IndTele
/- `ConstantInfo.type`/`levelParams` are read as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `Level.instantiateParams` on a parameter (`pinLinkOk`). -/
import all Lean.Level
/- `FEnv.push` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push

/-!
# The reserved names' check against master's (task #451, lanes O7 and follow-master)

A pinned basis block is generated and checked like any other block; the
reserved names' check after the declaration's own checks
(`InLean.basisNamesOk`, twin of `ConLeche.basisNamesOk`) compares a block at a
pinned block's names (`basisNameHit`) with the pin (`pinListOk`) and keeps
every other declaration off the reserved names.

* The pins: InLean's (`InLean/Inductives/Basis.lean`, Lean entries) translate
  to master's (`ConLeche/Kernel/Basis/*`) exactly (`pins_tr`, by evaluation),
  and their terms have closed readings (`pins_ok`).
* `pinCopyOk_tr`: InLean's comparison (`pinAgrees` up to `mdata` and binder
  data, at `ciAtLps`) implies master's on the translation: `Expr.clEq` gives
  equal readings (`toExpr_of_clEq`), level instantiation reads as master's
  (`toExpr_instantiateLevelParams`; it wrote no marker since the compared
  record has a reading).
* `blockLinksOk_tr`: the links (`pinLinkOk` through
  `Level.instantiateParams` at a parameter, master's `Level.subst`).
* `basisNamesOk_ind_tr`: an inductive declaration's check, on the generated
  block's record; `basisNamesOk_toDecl`: a one-constant record's;
  `checkDecl_of_kind`: master's step from its kind's checks and the names'.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## The pins -/

/-- **InLean's pins translate to master's.** -/
theorem pins_tr (k : InLean.BasisKind) : k.decls.map trCI = (trKind k).decls := by
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
      obtain ⟨hn, ht⟩ := h
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
      obtain ⟨⟨⟨⟨hn, ht⟩, hp⟩, hf⟩, hT⟩ := h
      simp only [trCI, ConLeche.pinAgrees, ConLeche.ConstantInfo.atLps,
        ConLeche.ConstantVal.atLps, ConLeche.ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨beqP_of_eq ?_, hp⟩, hf⟩, by rw [hT]⟩
      simp only [trCV, ConLeche.ConstantVal.mk.injEq, hn, true_and]
      exact ⟨rfl, trC_of_clEq_inst hci hpin _ _ ht⟩
    | _ => simp [ciAtLps, InLean.pinAgrees] at h
  | recInfo v =>
    cases pin with
    | recInfo vp =>
      obtain ⟨hct, hcr⟩ := hci
      obtain ⟨hpt, hpr⟩ := hpin
      simp only [ciAtLps, InLean.pinAgrees, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨hn, ht⟩, hmI⟩, hrP⟩, hk⟩, hlen⟩, hrules⟩ := h
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

theorem nodup_tr : ∀ (l : List Lean.Name), ConLeche.Name.nodup (l.map toName) = InLean.namesNodup l
  | [] => rfl
  | n :: l => by
    simp only [List.map_cons, ConLeche.Name.nodup, InLean.namesNodup, contains_map_toName, nodup_tr l]

/-- **One constant against its pin**, master's at the translation. -/
theorem pinCopyOk_tr {ci pin : Lean.ConstantInfo}
    (hci : CIOk ci) (hpin : CIOk pin)
    (h : InLean.pinCopyOk ci pin = true) : ConLeche.pinCopyOk (trCI ci) (trCI pin) = true := by
  simp only [InLean.pinCopyOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hnd, hlen⟩, hag⟩ := h
  simp only [ConLeche.pinCopyOk, trCI_levelParams, nodup_tr, hnd, List.length_map, hlen,
    beq_self_eq_true, Bool.true_and]
  exact pinAgrees_tr hci hpin hag

/-- The lists, pairwise. -/
theorem listBeqBy_tr : ∀ {block pins : List Lean.ConstantInfo},
    (∀ ci ∈ block, CIOk ci) → (∀ p ∈ pins, CIOk p) →
    InLean.listBeqBy InLean.pinCopyOk block pins = true →
    ConLeche.listBeqBy ConLeche.pinCopyOk (block.map trCI) (pins.map trCI) = true
  | [], [], _, _, _ => rfl
  | c :: cs, p :: ps, hb, hp, h => by
    simp only [InLean.listBeqBy, Bool.and_eq_true] at h
    simp only [List.map_cons, ConLeche.listBeqBy, Bool.and_eq_true]
    exact ⟨pinCopyOk_tr (hb c List.mem_cons_self) (hp p List.mem_cons_self) h.1,
      listBeqBy_tr (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h.2⟩
  | [], _ :: _, _, _, h => by simp [InLean.listBeqBy] at h
  | _ :: _, [], _, _, h => by simp [InLean.listBeqBy] at h

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

/-- **The links**, master's at the translation. -/
theorem blockLinksOk_tr {block pins : List Lean.ConstantInfo} {Ps : List ConLeche.ConstantInfo}
    (hPs : Ps = pins.map trCI) (h : InLean.blockLinksOk block pins = true) :
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
      (Qs : List ConLeche.ConstantInfo), Qs = qs.map trCI →
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
        | .ctorInfo cv _ _ _, _ => cv.levelParams == F.map toName
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
                  (vp.rules.map trRule) := hQ.1
              subst hQ'
              simp only [trCI, List.all_map, List.all_eq_true, Function.comp_apply] at h1 ⊢
              intro rl hrl
              have h2 := h1 rl hrl
              simp only [trRule]
              rw [constNamed?_tr]
              have hc : (ConLeche.constNamed? Ps (toName rl.ctor)).map
                  (·.toConstantVal.levelParams) =
                  (InLean.constNamed? pins rl.ctor).map (fun c => c.levelParams.map toName) := by
                rw [hPs, constNamed?_tr]
                cases InLean.constNamed? pins rl.ctor <;> simp [trCI_levelParams]
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
              | recInfo cv mI rP k rules => simp [trCI] at hq1
              | _ => rfl
          | _ => cases Q <;> rfl
  exact key block pins Ps hPs h

/-! ## Lookups -/

/-- A name the environment does not hold, no check sees. -/
theorem FEnv_find_none {fe : InLean.FEnv} {n : Lean.Name} (h : fe.env.find? n = none) :
    fe.find? n = none := by
  simp only [FEnv.find?_eq_filter, h, Option.filter_none]

theorem env_find_cons (env : ConLeche.Env) (d : ConLeche.ConstantInfo) (n : ConLeche.Name) :
    (⟨d :: env.consts, env.tables⟩ : ConLeche.Env).find? n =
      if d.name = n then some d else env.find? n := by
  simp only [ConLeche.Env.find?, List.find?_cons]
  by_cases h : d.name = n
  · simp [h]
  · have : (d.name == n) = false := by simpa using h
    simp [this, h]

/-! ## The reserved names' check -/

/-- **The block's comparison with its pin**, master's at the translation. -/
theorem pinListOk_tr {block : List Lean.ConstantInfo} {kind : InLean.BasisKind}
    (hok : ∀ ci ∈ block, CIOk ci) (h : InLean.pinListOk block kind.decls = true) :
    ConLeche.pinListOk (block.map trCI) (trKind kind).decls = true := by
  simp only [InLean.pinListOk, Bool.and_eq_true] at h
  simp only [ConLeche.pinListOk, Bool.and_eq_true]
  rw [← pins_tr kind]
  exact ⟨listBeqBy_tr hok (pins_ok kind) h.1, blockLinksOk_tr rfl h.2⟩

/-- **An inductive declaration's reserved names**: InLean's check on the
generated block is master's on its record, at any parameter count. -/
theorem basisNamesOk_ind_tr {lps : List Name} {nP : Nat} {types : List InductiveType}
    {isUnsafe : Bool} {a : InLean.Added} {cb : List ConLeche.ConstantInfo} {n : Nat}
    (hb : toBlock (storedBlock a.consts) = some cb)
    (hr : ∀ ci ∈ storedBlock a.consts, CIRange ci)
    (h : InLean.basisNamesOk (.inductDecl lps nP types isUnsafe) a = true) :
    ConLeche.basisNamesOk (.indDecl cb n) = true := by
  have hok := toBlock_CIOk hb hr
  obtain ⟨rfl, -⟩ := toBlock_eq hb hr
  simp only [InLean.basisNamesOk] at h
  simp only [ConLeche.basisNamesOk, basisNameHit_tr]
  cases hk : InLean.basisNameHit (storedBlock a.consts) with
  | some kind =>
    rw [hk] at h
    simp only [Bool.and_eq_true] at h
    exact pinListOk_tr hok h.2
  | none =>
    rw [hk] at h
    simp only [Option.map_none, List.all_map, Function.comp_def, trCI_name, reserved_tr]
    exact h

/-- **Master's step from its two parts**: the kind's checks, then the
reserved names'. -/
theorem checkDecl_of_kind {pins : List ConLeche.NatOpPinSet} {F : Nat} {L L' : ConLeche.Env}
    {d : ConLeche.Declaration}
    (h : ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pins L d = .ok L')
    (hn : ConLeche.basisNamesOk d = true) :
    ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins L d = .ok L' := by
  simp only [ConLeche.checkDecl, h, hn]
  rfl

end InLeanProof
