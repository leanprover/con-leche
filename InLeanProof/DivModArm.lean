module

public import InLeanProof.CertDivMod
/- `ConstantInfo.name`/`levelParams`/`type` are read as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (core's private add, behind `InLean/Push.lean`) is read to find the pushed definition. -/
import all InLean.Push

/-!
# DivModArm: the pin-certified `Nat` operations' arm (task #451, lane CertArm)

InLean's `checkDivModPin` (`InLean/CheckerC.lean`) against master's
(`ConLeche/Kernel/Checker.lean`), at the decoded variants (`loadedPins`).

* **The guards, both ways** at decoded terms (closed readings: the decoder
  builds no free variable and no metavariable, `loadPinSets_okC`):
  `divModPinGuard_eq`, `divModCertGuard_eq`, `divModCertsGuard_eq`.  Both
  loops move on at the same variants only if the guards agree exactly.
* **The data**: `trPinSet`'s fields at an operation's name (`divModDeclPin_tr`
  & co.), `substConstAll` (`trC_substConstAll`), the statements over the
  interned variables (`divModCertStmts_tr`).
* **The attempt**: `checkTypePins_sim`, `checkDivModCerts_sim`,
  `checkDivModPinAt_sim`; **the loop**: `checkDivModPinLoop_sim`; **the arm**:
  `checkDefnC_divMod_sim`, hence `divModArmSimI` and `checkDecl_sim_nk'`.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## Cached flags of a closed reading -/

theorem trL_allParamsDefined_nil : ∀ u : Level,
    (trL u).allParamsDefined [] = !lparamS u := by
  intro u
  induction u <;> simp_all [trL, lparamS, ConLeche.Level.allParamsDefined]

/-- Master's level-parameter guard at no parameter is InLean's flag, structurally. -/
theorem trC_allLevelParamsDefined_nil : ∀ e : Expr,
    (trC e).allLevelParamsDefined [] = !elparamS e := by
  intro e
  induction e with
  | sort u => exact trL_allParamsDefined_nil u
  | const n us =>
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, elparamS, List.all_map]
    induction us with
    | nil => rfl
    | cons u us ih =>
      simp only [List.all_cons, List.any_cons, Bool.not_or]
      rw [← ih]
      simp [trL_allParamsDefined_nil]
  | app f a ihf iha =>
    simp only [trC, trE] at ihf iha ⊢
    simp [ConLeche.Expr.allLevelParamsDefined, elparamS, ihf, iha]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    simp only [trC, trE] at iht ihb ⊢
    simp [ConLeche.Expr.allLevelParamsDefined, elparamS, iht, ihb]
  | letE _ t v b _ iht ihv ihb =>
    simp only [trC, trE] at iht ihv ihb ⊢
    simp [ConLeche.Expr.allLevelParamsDefined, elparamS, iht, ihv, ihb, Bool.and_assoc]
  | mdata _ x ih => simpa [trC, trE, elparamS] using ih
  | proj _ _ x ih => simpa [trC, trE, elparamS, ConLeche.Expr.allLevelParamsDefined] using ih
  | bvar | fvar | mvar | lit => rfl

/-- The three cached-flag guards of a closed reading, as master reads them. -/
theorem flags_trC {e : Expr} (h : okC e = true) :
    (trC e).looseBVarsBounded 0 = !e.hasLooseBVars ∧ e.hasFVar = false ∧
      (trC e).allLevelParamsDefined [] = !e.hasLevelParam := by
  have hr : Expr.RangeOk e := RangeOk_of_okE h
  refine ⟨?_, by rw [Expr.hasFVar_eq hr]; exact fvarS_of_okC h, ?_⟩
  · rw [hasLooseBVars_eq hr]
    have hb := bvarBound_toExpr (fv := fun _ => none) (fun _ _ h => nomatch h) e (trC e)
      (toExprC_of_okC h)
    apply Bool.eq_iff_iff.2
    simp only [ConLeche.Expr.looseBVarsBounded_iff, hb, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  · rw [trC_allLevelParamsDefined_nil, Expr.hasLevelParam_eq hr]

/-! ## Resolution, both ways -/

/-- **Master's resolution gives InLean's** on a reading (free variables are
not InLean's concern). -/
theorem constsResolve_trE_conv {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr) :
    ∀ (e : Expr) (k : Nat), okE fv e = true → (trE fv e).constsResolve L = true →
      anySpec (fun x _ => if unresI fe x then some true else none) e k = false := by
  have hdom := envDomI_of hP
  have hnone : ∀ n, (L.find? (toName n)).isSome = true → (fe.find? n).isNone = false := by
    intro n h
    cases hf : fe.find? n
    · rw [hP.none n hf] at h; exact absurd h (by simp)
    · rfl
  intro e
  induction e with
  | bvar | sort | fvar => intro _ _ _; rfl
  | mvar => intro _ h; simp [okE] at h
  | const n us =>
    intro _ _ ha
    simp only [trE, ConLeche.Expr.constsResolve] at ha
    simp [anySpec, unresI, hnone n ha]
  | lit l =>
    intro k _ ha
    cases l with
    | natVal m =>
      have : natLitStoredF fe = true := by
        rw [natLitStoredF_I hdom]
        simpa [trE, toLit, ConLeche.Expr.constsResolve, ConLeche.natLitStored, Bool.and_assoc]
          using ha
      simp [anySpec, unresI, this]
    | strVal m =>
      have : strLitStoredF fe = true := by
        rw [strLitStoredF_I hdom]
        simpa [trE, toLit, ConLeche.Expr.constsResolve, ConLeche.strLitStored,
          ConLeche.natLitStored, Bool.and_assoc] using ha
      simp [anySpec, unresI, this]
  | app f a ihf iha =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true] at ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff]
    exact ⟨ihf k hok.1 ha.1, iha k hok.2 ha.2⟩
  | lam nm t b bi iht ihb | forallE nm t b bi iht ihb =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true] at ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff]
    exact ⟨iht k hok.1 ha.1, ihb (k + 1) hok.2 ha.2⟩
  | letE nm t v b nd iht ihv ihb =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true] at ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff]
    exact ⟨⟨iht k hok.1.1 ha.1.1, ihv k hok.1.2 ha.1.2⟩, ihb (k + 1) hok.2 ha.2⟩
  | mdata m x ih =>
    intro k hok ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
    exact ih k hok ha
  | proj s i x ih =>
    intro k hok ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true] at ha
    simp only [anySpec, unresI, hnone s ha.1, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
    exact ih k hok ha.2

theorem constsResolve_anySpec (fe : InLean.FEnv) (e : Expr) :
    InLean.constsResolve fe e = !anySpec (fun x _ => if unresI fe x then some true else none) e 0 := by
  unfold InLean.constsResolve
  rw [any_eq_anySpec]
  congr 2

/-- **InLean's resolution is master's**, both ways, on a reading whose free
variables resolve at master's. -/
theorem constsResolve_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr)
    (hfv : ∀ id, okE fv (.fvar id) = true → (trE fv (.fvar id)).constsResolve L = true)
    {e : Expr} (hok : okE fv e = true) :
    (trE fv e).constsResolve L = InLean.constsResolve fe e := by
  cases h : InLean.constsResolve fe e
  · cases h' : (trE fv e).constsResolve L
    · rfl
    · have ha := constsResolve_trE_conv hP fv e 0 hok h'
      rw [constsResolve_anySpec, ha] at h
      exact absurd h (by decide)
  · exact constsResolve_tr hP fv hfv hok h

theorem constsResolve_eqC {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {e : Expr}
    (hok : okC e = true) : (trC e).constsResolve L = InLean.constsResolve fe e :=
  constsResolve_eq hP _ (fun _ h => by simp [okE] at h) hok

/-- A stored constant's type is a closed reading. -/
theorem find_storedT {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {ci : Lean.ConstantInfo} (h : fe.find? n = some ci) :
    ∃ cci, L.find? (toName n) = some cci ∧ StoredT ci.type cci.toConstantVal.type := by
  obtain ⟨cci, hc, hr⟩ := find_rel hP h
  obtain ⟨-, -, h3⟩ := hr.cv
  exact ⟨cci, hc, by rw [ci_cv_type]; exact h3⟩

theorem StoredT.okC {t : Expr} {c : ConLeche.Expr} (h : StoredT t c) : okC t = true ∧ trC t = c :=
  trC_of_toExprC h.2.2 h.2.1

/-! ## The decoder builds closed terms

The share-table decoder (`InLean.PinDecode`) has no constructor for a free
variable, an expression metavariable or a level metavariable, so every term
it decodes is free of them; with the range check (`loadPinSets_range`)
every decoded term is a closed reading. -/

/-- No free variable, no metavariable of either kind. -/
@[expose] def NoVarS (e : Expr) : Prop := fvarS e = false ∧ emvarS e = false ∧ elmvarS e = false

/-- What a decoded share-table entry satisfies. -/
@[expose] def ObjOk : PinDecode.Obj → Prop
  | .name _ => True
  | .level l => lmvarS l = false
  | .expr e => NoVarS e

theorem except_mapM_all {ε α β : Type} {f : α → Except ε β} {P : β → Prop}
    (hf : ∀ a b, f a = .ok b → P b) : ∀ (l : List α) (r : List β), l.mapM f = .ok r → ∀ b ∈ r, P b := by
  intro l
  induction l with
  | nil => intro r h; simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | cons a l ih =>
    intro r h
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨r', hr', h⟩ := except_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hf _ _ hb
    · exact ih r' hr' x hx

theorem except_mapM_all_arr {ε α β : Type} {f : α → Except ε β} {P : β → Prop}
    (hf : ∀ a b, f a = .ok b → P b) {xs : Array α} {r : Array β} (h : xs.mapM f = .ok r) :
    ∀ b ∈ r, P b := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; exact nomatch h
  | ok l =>
    rw [hl] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    intro b hb
    exact except_mapM_all hf _ l hl b (by simpa using hb)

theorem except_forIn_inv {ε α β : Type} {f : α → β → Except ε (ForInStep β)} {I : β → Prop}
    (hf : ∀ a b r, I b → f a b = .ok r → I r.value) :
    ∀ (l : List α) (b r : β), I b → forIn l b f = .ok r → I r := by
  intro l
  induction l with
  | nil => intro b r hb h; simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | cons a l ih =>
    intro b r hb h
    simp only [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := except_bind_ok h
    have := hf a b st hb hst
    cases st with
    | done x => simp only [pure, Except.pure, Except.ok.injEq] at h; exact h ▸ this
    | yield x => exact ih x r this h

section decoder
variable {tab : Array PinDecode.Obj}

theorem getRef_ok (ht : ∀ o ∈ tab, ObjOk o) {j : Json} {o : PinDecode.Obj}
    (h : PinDecode.getRef tab j = .ok o) : ObjOk o := by
  unfold PinDecode.getRef at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; trivial
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · obtain ⟨i, -, h⟩ := except_bind_ok h
    split at h
    · rename_i hi
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ht _ (Array.mem_of_getElem? hi)
    · exact nomatch h

theorem refLevel_ok (ht : ∀ o ∈ tab, ObjOk o) {j : Json} {l : Level}
    (h : PinDecode.refLevel tab j = .ok l) : lmvarS l = false := by
  unfold PinDecode.refLevel at h
  obtain ⟨o, ho, h⟩ := except_bind_ok h
  have := getRef_ok ht ho
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact this
  · exact nomatch h

theorem refExpr_ok (ht : ∀ o ∈ tab, ObjOk o) {j : Json} {e : Expr}
    (h : PinDecode.refExpr tab j = .ok e) : NoVarS e := by
  unfold PinDecode.refExpr at h
  obtain ⟨o, ho, h⟩ := except_bind_ok h
  have := getRef_ok ht ho
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact this
  · exact nomatch h

set_option maxHeartbeats 1000000 in
-- the entry decoder's sixteen tags, each a chain of binds
theorem entry_ok (ht : ∀ o ∈ tab, ObjOk o) {j : Json} {o : PinDecode.Obj}
    (h : PinDecode.entry tab j = .ok o) : ObjOk o := by
  have hE := fun j e => refExpr_ok (tab := tab) ht (j := j) (e := e)
  have hL := fun j l => refLevel_ok (tab := tab) ht (j := j) (l := l)
  have hM := except_mapM_all (fun j l => refLevel_ok (tab := tab) ht (j := j) (l := l))
  unfold PinDecode.entry at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq] at h; subst h
       first
         | trivial
         | simp only [ObjOk, NoVarS, lmvarS, fvarS, emvarS, elmvarS,
             Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at *
           grind)

end decoder



theorem blob_ok {j : Json} {e : Expr} (h : PinDecode.blob j = .ok e) : NoVarS e := by
  unfold PinDecode.blob at h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨es, -, h⟩ := except_bind_ok h
  obtain ⟨tab, htab, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  rw [← Array.forIn_toList] at htab
  have hI := except_forIn_inv (I := fun tab : Array PinDecode.Obj => ∀ o ∈ tab, ObjOk o) ?_ _ _ _
    (by simp) htab
  · exact refExpr_ok hI h
  · intro a b r hb hr
    obtain ⟨o, ho, hr⟩ := except_bind_ok hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hb x hx
    · exact entry_ok hb ho

theorem opDump_ok {j : Json} {op : PinOp} (h : PinDecode.opDump j = .ok op) :
    NoVarS op.pin ∧ (∀ p ∈ op.proofs, NoVarS p) ∧ ∀ t ∈ op.typePins, NoVarS t.2 := by
  unfold PinDecode.opDump at h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨pin, hpin, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨proofs, hproofs, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨tps, htps, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨blob_ok hpin, except_mapM_all_arr (fun _ _ hb => blob_ok hb) hproofs, ?_⟩
  refine except_mapM_all_arr (P := fun t : Name × Expr => NoVarS t.2) ?_ htps
  intro a b hb
  obtain ⟨_, -, hb⟩ := except_bind_ok hb
  obtain ⟨_, -, hb⟩ := except_bind_ok hb
  obtain ⟨_, -, hb⟩ := except_bind_ok hb
  obtain ⟨e, he, hb⟩ := except_bind_ok hb
  simp only [pure, Except.pure, Except.ok.injEq] at hb
  subst hb
  exact blob_ok he

theorem pinSet_ok {s : String} {ps : PinSet} (h : PinDecode.pinSet s = .ok ps) :
    ∀ op ∈ ps.ops, NoVarS op.pin ∧ (∀ p ∈ op.proofs, NoVarS p) ∧ ∀ t ∈ op.typePins, NoVarS t.2 := by
  unfold PinDecode.pinSet at h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨ops, hops, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact except_mapM_all_arr (fun _ _ hb => opDump_ok hb) hops

/-- **Every decoded term is a closed reading**: in range (the decoder's check)
and free of free variables and metavariables (the decoder builds none). -/
theorem loadPinSets_okC {sets : Array InLean.PinSet} (h : InLean.loadPinSets () = .ok sets) :
    ∀ ps ∈ sets, ∀ op ∈ ps.ops, okC op.pin = true ∧ (∀ p ∈ op.proofs, okC p = true) ∧
      ∀ t ∈ op.typePins, okC t.2 = true := by
  have hR := loadPinSets_range h
  have hV : ∀ ps ∈ sets, ∀ op ∈ ps.ops,
      NoVarS op.pin ∧ (∀ p ∈ op.proofs, NoVarS p) ∧ ∀ t ∈ op.typePins, NoVarS t.2 := by
    unfold InLean.loadPinSets at h
    obtain ⟨sets', h1, h2⟩ := except_bind_ok h
    have : sets' = sets := by
      split at h2
      · simpa [pure, Except.pure] using h2
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h2
    subst this
    exact except_mapM_all_arr (fun _ _ hb => pinSet_ok hb) h1
  intro ps hps op hop
  obtain ⟨⟨r1, -⟩, r2, r3⟩ := hR ps hps op hop
  obtain ⟨⟨f1, e1, l1⟩, v2, v3⟩ := hV ps hps op hop
  refine ⟨okC_of_flags r1 f1 e1 l1, fun p hp => ?_, fun t ht => ?_⟩
  · obtain ⟨f, e, l⟩ := v2 p hp; exact okC_of_flags (r2 p hp).1 f e l
  · obtain ⟨f, e, l⟩ := v3 t ht; exact okC_of_flags (r3 t ht).1 f e l

/-! ## Free variables, restricted -/

/-- Every free variable of `e` satisfies `P`. -/
@[expose] def AllFv (P : FVarId → Prop) : Expr → Prop
  | .fvar id => P id
  | .app f a | .lam _ f a _ | .forallE _ f a _ => AllFv P f ∧ AllFv P a
  | .letE _ t v b _ => AllFv P t ∧ AllFv P v ∧ AllFv P b
  | .mdata _ x | .proj _ _ x => AllFv P x
  | .bvar _ | .mvar _ | .sort _ | .const .. | .lit _ => True

open Classical in
/-- The translation answering only at the free variables `P` admits. -/
noncomputable def fvR (fv : FVarId → Option ConLeche.Expr) (P : FVarId → Prop) :
    FVarId → Option ConLeche.Expr :=
  fun id => if P id then fv id else none

theorem trE_fvR (fv : FVarId → Option ConLeche.Expr) (P : FVarId → Prop) :
    ∀ e : Expr, AllFv P e → okE (fvR fv P) e = okE fv e ∧ trE (fvR fv P) e = trE fv e := by
  intro e
  induction e with
  | fvar id => intro h; simp [AllFv] at h; simp [okE, trE, fvR, h]
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro h
    obtain ⟨o1, t1⟩ := ihf h.1
    obtain ⟨o2, t2⟩ := iha h.2
    simp [okE, trE, o1, t1, o2, t2]
  | letE _ t v b _ iht ihv ihb =>
    intro h
    obtain ⟨o1, t1⟩ := iht h.1
    obtain ⟨o2, t2⟩ := ihv h.2.1
    obtain ⟨o3, t3⟩ := ihb h.2.2
    simp [okE, trE, o1, t1, o2, t2, o3, t3]
  | mdata _ x ih | proj _ _ x ih =>
    intro h
    obtain ⟨o1, t1⟩ := ih h
    simp [okE, trE, o1, t1]
  | bvar | mvar | sort | const | lit => intro _; exact ⟨rfl, rfl⟩

/-- **Resolution, both ways**, where the term's own free variables resolve at
master's. -/
theorem constsResolve_eqA {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr) {e : Expr}
    (hA : AllFv (fun id => (trE fv (.fvar id)).constsResolve L = true) e)
    (hok : okE fv e = true) :
    (trE fv e).constsResolve L = InLean.constsResolve fe e := by
  obtain ⟨o, t⟩ := trE_fvR fv _ e hA
  rw [← t]
  refine constsResolve_eq hP _ ?_ (by rw [o]; exact hok)
  intro id h
  simp only [okE, fvR] at h
  split at h
  · rename_i hp
    have hp' : ConLeche.Expr.constsResolve L ((fv id).getD (.bvar 0)) = true := hp
    simp only [trE, fvR, hp', ite_true]
  · simp at h

theorem allFv_of_okC (P : FVarId → Prop) : ∀ {e : Expr}, okC e = true → AllFv P e := by
  intro e
  induction e with
  | fvar => intro h; simp [okC, okE] at h
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h; exact ⟨ihf h.1, iha h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | mdata _ x ih | proj _ _ x ih => intro h; exact ih h
  | bvar | mvar | sort | const | lit => intro _; trivial

theorem allFv_of_trE_fvar {fv : FVarId → Option ConLeche.Expr} {L : ConLeche.Env} :
    ∀ {e : Expr} {d : Nat} {t : ConLeche.Expr}, trE fv e = .fvar d t → t.constsResolve L = true →
      AllFv (fun id => (trE fv (.fvar id)).constsResolve L = true) e := by
  intro e
  induction e with
  | fvar id => intro d t h ht; simp only [AllFv]; rw [h]; exact ht
  | mdata _ x ih => intro d t h ht; exact ih h ht
  | bvar | mvar | sort | const | lit | app | lam | forallE | letE | proj =>
    intro d t h; simp [trE] at h

theorem allFv_substConst0 {P : FVarId → Prop} {n : Name} {r : Expr} (hr : AllFv P r) :
    ∀ {e : Expr}, AllFv P e → AllFv P (InLean.substConst0 n r e) := by
  intro e
  induction e with
  | const c us =>
    intro h
    cases us with
    | nil => simp only [InLean.substConst0]; split <;> assumption
    | cons => exact h
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | _ => intro h; exact h

/-! ## The statements, over the interned variables -/

/-- **A property of the statements' terms**, from its closure under
application and constants and its holding at the two variables. -/
theorem divModCertStmts_all {x y : Expr} (c : Name) (Q : Expr → Prop)
    (hC : ∀ n (us : List Level), (∀ u ∈ us, u = .succ .zero) → Q (.const n us)) (hA : ∀ f a, Q f → Q a → Q (.app f a)) (hx : Q x) (hy : Q y) :
    ∀ p ∈ InLean.divModCertStmts x y c, (∀ h ∈ p.1, Q h) ∧ Q p.2 := by
  unfold InLean.divModCertStmts
  repeat' split
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    try simp only [imp_false, IsEmpty.forall_iff, implies_true, and_true]
  all_goals (repeat' constructor) <;> intros <;> subst_vars
  all_goals (repeat (first | exact hx | exact hy | apply hA |
    (apply hC; intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; try exact hu)))

/-- An application spine of constants over leaves reading as free variables. -/
@[expose] def SpineF (s : InLean.CState) : Expr → Prop
  | .app f a => SpineF s f ∧ SpineF s a
  | .const _ _ => True
  | e => ∃ d t, TrS s e = .fvar d t

theorem spineF_of_fvar {s : InLean.CState} {e : Expr} {d : Nat} {t : ConLeche.Expr}
    (h : TrS s e = .fvar d t) : SpineF s e := by
  cases e with
  | app => simp [TrS_app] at h
  | const => simp [TrS_const] at h
  | _ => exact ⟨d, t, h⟩

/-- **`substConst0` commutes with the reading** on a spine. -/
theorem TrS_substConst0 {s : InLean.CState} (n : Name) (r : Expr) :
    ∀ {e : Expr}, SpineF s e →
      TrS s (InLean.substConst0 n r e) = ConLeche.Expr.substConst0 (toName n) (TrS s r) (TrS s e) := by
  intro e
  induction e with
  | const c us =>
    intro _
    cases us with
    | nil =>
      simp only [InLean.substConst0, TrS_const, List.map_nil, ConLeche.Expr.substConst0, and_true,
        toName_eq_iff]
      by_cases h : c = n
      · subst h; simp
      · simp [h]; rfl
    | cons u us => simp [InLean.substConst0, TrS_const, ConLeche.Expr.substConst0]
  | app f a ihf iha =>
    intro h
    simp only [InLean.substConst0, TrS_app, ConLeche.Expr.substConst0, ihf h.1, iha h.2]
  | bvar | fvar | mvar | sort | lit | lam | forallE | letE | mdata | proj =>
    intro h
    obtain ⟨d, t, h⟩ := h
    simp only [InLean.substConst0]
    rw [h]; rfl

/-- **`substConstAll`'s reading** (InLean's memoised walk, master's under binders). -/
theorem substConstAll_tr {n : Name} {r : Expr} (hr : okC r = true) :
    ∀ (e : Expr) (k : Nat), okC e = true →
      okC (mapSpec (fun x _ => match x with
        | .const c [] => if c == n then some r else none
        | _ => none) e k) = true ∧
      trC (mapSpec (fun x _ => match x with
        | .const c [] => if c == n then some r else none
        | _ => none) e k) = ConLeche.Expr.substConstAll (toName n) (trC r) (trC e) := by
  intro e
  induction e with
  | const c us =>
    intro k h
    cases us with
    | nil =>
      by_cases hc : c = n
      · subst hc; simp [mapSpec, ConLeche.Expr.substConstAll, trC, trE, hr]
      · have : (c == n) = false := by simpa using hc
        simp only [mapSpec, this, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
        refine ⟨h, ?_⟩
        simp [ConLeche.Expr.substConstAll, trC, trE, toName_eq_iff, hc]
    | cons u us =>
      simp only [mapSpec, Option.getD_none]
      exact ⟨h, by simp [ConLeche.Expr.substConstAll, trC, trE]⟩
  | app f a ihf iha =>
    intro k h
    simp only [okC, okE, Bool.and_eq_true] at h
    obtain ⟨o1, t1⟩ := ihf k h.1
    obtain ⟨o2, t2⟩ := iha k h.2
    simp only [okC, trC] at o1 t1 o2 t2
    simp only [mapSpec, Option.getD_none, okC, okE, o1, o2, trC, trE, t1, t2, Bool.and_self,
      ConLeche.Expr.substConstAll, and_self]
  | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro k h
    simp only [okC, okE, Bool.and_eq_true] at h
    obtain ⟨o1, t1⟩ := ihf k h.1
    obtain ⟨o2, t2⟩ := iha (k + 1) h.2
    simp only [okC, trC] at o1 t1 o2 t2
    simp only [mapSpec, Option.getD_none, okC, okE, o1, o2, trC, trE, t1, t2, Bool.and_self,
      ConLeche.Expr.substConstAll, and_self]
  | letE _ t v b _ iht ihv ihb =>
    intro k h
    simp only [okC, okE, Bool.and_eq_true] at h
    obtain ⟨o1, t1⟩ := iht k h.1.1
    obtain ⟨o2, t2⟩ := ihv k h.1.2
    obtain ⟨o3, t3⟩ := ihb (k + 1) h.2
    simp only [okC, trC] at o1 t1 o2 t2 o3 t3
    simp only [mapSpec, Option.getD_none, okC, okE, o1, o2, o3, trC, trE, t1, t2, t3,
      Bool.and_self, ConLeche.Expr.substConstAll, and_self]
  | mdata _ x ih =>
    intro k h
    obtain ⟨o1, t1⟩ := ih k h
    simp only [okC, trC] at o1 t1
    simp only [mapSpec, Option.getD_none, okC, okE, o1, trC, trE, t1, and_self]
  | proj _ _ x ih =>
    intro k h
    obtain ⟨o1, t1⟩ := ih k h
    simp only [okC, trC] at o1 t1
    simp only [mapSpec, Option.getD_none, okC, okE, o1, trC, trE, t1, ConLeche.Expr.substConstAll,
      and_self]
  | bvar | fvar | mvar | sort | lit =>
    intro k h
    simp only [mapSpec, Option.getD_none]
    exact ⟨h, rfl⟩

theorem substConstAll_trC {n : Name} {r e : Expr} (hr : okC r = true) (he : okC e = true) :
    okC (InLean.substConstAll n r e) = true ∧
      trC (InLean.substConstAll n r e) = ConLeche.Expr.substConstAll (toName n) (trC r) (trC e) := by
  unfold InLean.substConstAll Expr.replaceI EO.replace
  rw [mapOff_fresh]
  exact substConstAll_tr hr e 0 he

theorem natDivModNames_cases {c : Name} (hc : InLean.natDivModNames.contains c = true) :
    c = InLean.natDivName ∨ c = InLean.natModName ∨ c = InLean.natGcdName ∨
      c = InLean.natLandName ∨ c = InLean.natLorName ∨ c = InLean.natXorName ∨
      c = InLean.natShiftLeftName ∨ c = InLean.natShiftRightName := by
  simpa [InLean.natDivModNames] using hc

set_option linter.unusedSimpArgs false in
/-- **The statements over the interned variables are master's.** -/
theorem divModCertStmts_tr {s : InLean.CState} {x y : Expr}
    (hx : TrS s x = .fvar 0 (.const ConLeche.natName []))
    (hy : TrS s y = .fvar 1 (.const ConLeche.natName [])) {c : Name}
    (hc : InLean.natDivModNames.contains c = true) :
    (InLean.divModCertStmts x y c).map (fun p => (p.1.map (TrS s), TrS s p.2)) =
      ConLeche.divModCertStmts (toName c) := by
  rcases natDivModNames_cases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [InLean.divModCertStmts, ConLeche.divModCertStmts,
    ← toName_beq, ← cl_natDivName, ← cl_natModName, ← cl_natGcdName, ← cl_natLandName,
    ← cl_natLorName, ← cl_natXorName, ← cl_natShiftLeftName, ← cl_natShiftRightName,
    List.map_cons, List.map_nil, TrS_app, TrS_const, hx, hy, ↓reduceIte] <;> rfl

set_option linter.unusedSimpArgs false in
/-- **`trPinSet`'s fields at an operation's name.** -/
theorem trPinSet_fields (ps : InLean.PinSet) {c : Name} (hc : InLean.natDivModNames.contains c = true) :
    ConLeche.divModDeclPin (trPinSet ps) (toName c) = trOpPin ps c ∧
      ConLeche.divModCertProofs (trPinSet ps) (toName c) = trOpProofs ps c ∧
      ConLeche.divModTypePins (trPinSet ps) (toName c) = trOpTypePins ps c := by
  rcases natDivModNames_cases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [ConLeche.divModDeclPin, ConLeche.divModCertProofs,
    ConLeche.divModTypePins, ← cl_natDivName, ← cl_natModName, ← cl_natGcdName,
    ← cl_natLandName, ← cl_natLorName, ← cl_natXorName, ← cl_natShiftLeftName,
    ← cl_natShiftRightName, ↓reduceIte] <;> exact ⟨rfl, rfl, rfl⟩

/-! ## The guards, both ways -/

theorem list_all_congr {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      list_all_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem typePinStored_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) (n : Name) :
    ConLeche.typePinStored L (toName n) = trC (match fe.find? n with
      | some ci => ci.type
      | none => .sort .zero) ∧
    okC (match fe.find? n with
      | some ci => ci.type
      | none => .sort .zero) = true := by
  unfold ConLeche.typePinStored
  cases hf : fe.find? n with
  | none => rw [hP.none n hf]; exact ⟨rfl, rfl⟩
  | some ci =>
    obtain ⟨cci, hc, hST⟩ := find_storedT hP hf
    obtain ⟨o, t⟩ := hST.okC
    rw [hc]; exact ⟨t.symm, o⟩

/-- One type pin's guard. -/
theorem typePinGuard_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) (n : Name)
    {ty : Expr} (hty : okC ty = true) :
    ((L.find? (toName n)).isSome && !(ConLeche.typePinStored L (toName n)).hasFvar &&
      (trC ty).looseBVarsBounded 0 && !(trC ty).hasFvar && (trC ty).constsResolve L) =
    (match fe.find? n with
      | some ci => !ci.type.hasFVar && !ty.hasLooseBVars && !ty.hasFVar && InLean.constsResolve fe ty
      | none => false) := by
  obtain ⟨f1, f2, -⟩ := flags_trC hty
  cases hf : fe.find? n with
  | none => simp [hP.none n hf]
  | some ci =>
    obtain ⟨cci, hc, hST⟩ := find_storedT hP hf
    have hfv : ci.type.hasFVar = false := by rw [Expr.hasFVar_eq hST.2.1]; exact hST.1
    unfold ConLeche.typePinStored
    simp [hc, ← hST.okC.2, trC_hasFvar, f1, f2, hfv, constsResolve_eqC hP hty]

/-- **The variant's pin guard is master's**, where the variant holds the operation. -/
theorem divModPinGuard_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {ps : InLean.PinSet} {op : InLean.PinOp} {c : Name}
    (hc : InLean.natDivModNames.contains c = true) (hop : ps.op? c = some op)
    (hpin : okC op.pin = true) (htp : ∀ t ∈ op.typePins, okC t.2 = true) :
    ConLeche.divModPinGuard (trPinSet ps) L (toName c) = InLean.divModPinGuard fe op := by
  obtain ⟨e1, -, e3⟩ := trPinSet_fields ps hc
  have hp1 : trOpPin ps c = trC op.pin := by simp [trOpPin, hop]
  have hp3 : trOpTypePins ps c = op.typePins.toList.map fun p => (toName p.1, trC p.2) := by
    simp [trOpTypePins, hop]
  obtain ⟨f1, f2, f3⟩ := flags_trC hpin
  unfold ConLeche.divModPinGuard InLean.divModPinGuard
  rw [e1, e3, hp1, hp3, f1, f3, trC_hasFvar, f2, constsResolve_eqC hP hpin, List.all_map,
    ← Array.all_toList]
  congr 1
  refine list_all_congr fun t ht => ?_
  obtain ⟨n, ty⟩ := t
  exact typePinGuard_eq hP n (htp _ (Array.mem_toList_iff.1 ht))

/-- Where the variant lacks the operation, master's guard refuses it. -/
theorem divModPinGuard_none {L : ConLeche.Env} {ps : InLean.PinSet} {c : Name}
    (hc : InLean.natDivModNames.contains c = true) (hop : ps.op? c = none) :
    ConLeche.divModPinGuard (trPinSet ps) L (toName c) = false := by
  obtain ⟨e1, -, -⟩ := trPinSet_fields ps hc
  unfold ConLeche.divModPinGuard
  rw [e1]
  simp [trOpPin, hop, ConLeche.Expr.looseBVarsBounded]

/-- A free variable whose master type resolves. -/
@[expose] def FvRes (s : InLean.CState) (L : ConLeche.Env) (id : FVarId) : Prop :=
  (TrS s (.fvar id)).constsResolve L = true

/-- What a statement term satisfies at a state where the variables read as
`fvar 0`/`fvar 1` of type `Nat`, `Nat` stored. -/
@[expose] def StmtOk (s : InLean.CState) (L : ConLeche.Env) (h : Expr) : Prop :=
  SpineF s h ∧ OkS s h = true ∧ AllFv (FvRes s L) h

theorem stmtOk_all {s : InLean.CState} {L : ConLeche.Env} {x y : Expr}
    (hokx : OkS s x = true) (hoky : OkS s y = true)
    (hx : TrS s x = .fvar 0 (.const ConLeche.natName []))
    (hy : TrS s y = .fvar 1 (.const ConLeche.natName []))
    (hN : (L.find? ConLeche.natName).isSome = true) (c : Name) :
    ∀ p ∈ InLean.divModCertStmts x y c, (∀ h ∈ p.1, StmtOk s L h) ∧ StmtOk s L p.2 := by
  refine divModCertStmts_all c _ ?_ ?_ ?_ ?_
  · intro n us hus
    refine ⟨trivial, ?_, trivial⟩
    simp only [OkS_const, List.all_eq_true]
    intro u hu; rw [hus u hu]; rfl
  · intro f a hf ha
    exact ⟨⟨hf.1, ha.1⟩, by simp [OkS_app, hf.2.1, ha.2.1], ⟨hf.2.2, ha.2.2⟩⟩
  · exact ⟨spineF_of_fvar hx, hokx, allFv_of_trE_fvar hx (by simpa [ConLeche.Expr.constsResolve] using hN)⟩
  · exact ⟨spineF_of_fvar hy, hoky, allFv_of_trE_fvar hy (by simpa [ConLeche.Expr.constsResolve] using hN)⟩

theorem constsResolve_subst_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {s : InLean.CState} {c : Name} {annVal h : Expr} (hv : okC annVal = true) (hh : StmtOk s L h) :
    (ConLeche.Expr.substConst0 (toName c) (trC annVal) (TrS s h)).constsResolve L =
      InLean.constsResolve fe (InLean.substConst0 c annVal h) := by
  rw [← TrS_of_okC s hv, ← TrS_substConst0 c annVal hh.1]
  exact constsResolve_eqA hP _ (allFv_substConst0 (allFv_of_okC _ hv) hh.2.2)
    (OkS_substConst0 (OkS_of_okC s hv) _ hh.2.1)

/-- **One certificate's guard is master's.** -/
theorem divModCertGuard_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {s : InLean.CState} {c : Name} {annVal proof eqE : Expr} {hyps : List Expr}
    (hv : okC annVal = true) (hp : okC proof = true) (hh : ∀ h ∈ hyps, StmtOk s L h)
    (he : StmtOk s L eqE) :
    ConLeche.divModCertGuard L (toName c) (trC annVal) (hyps.map (TrS s)) (TrS s eqE) (trC proof) =
      InLean.divModCertGuard fe c annVal hyps eqE proof := by
  obtain ⟨o, t⟩ := substConstAll_trC (n := c) hv hp
  obtain ⟨f1, f2, f3⟩ := flags_trC o
  unfold ConLeche.divModCertGuard InLean.divModCertGuard
  simp only []
  rw [← t, f1, f3, trC_hasFvar, f2, constsResolve_eqC hP o, constsResolve_subst_eq hP hv he,
    List.map_map, List.all_map, List.all_map]
  congr 2
  exact list_all_congr fun h hm => constsResolve_subst_eq hP hv (hh h hm)

/-- **The variant's certificates' guards are master's**, where the variant
holds the operation. -/
theorem divModCertsGuard_eq {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {s : InLean.CState} {x y : Expr} (hokx : OkS s x = true) (hoky : OkS s y = true)
    (hx : TrS s x = .fvar 0 (.const ConLeche.natName []))
    (hy : TrS s y = .fvar 1 (.const ConLeche.natName []))
    (hN : (L.find? ConLeche.natName).isSome = true)
    {ps : InLean.PinSet} {op : InLean.PinOp} {c : Name} {annVal : Expr}
    (hc : InLean.natDivModNames.contains c = true) (hop : ps.op? c = some op)
    (hv : okC annVal = true) (hpr : ∀ p ∈ op.proofs, okC p = true) :
    ConLeche.divModCertsGuard (trPinSet ps) L (toName c) (trC annVal) =
      ((InLean.divModCertStmts x y c).zip op.proofs.toList).all
        (fun p => InLean.divModCertGuard fe c annVal p.1.1 p.1.2 p.2) := by
  obtain ⟨-, e2, -⟩ := trPinSet_fields ps hc
  have hp2 : trOpProofs ps c = op.proofs.toList.map trC := by simp [trOpProofs, hop]
  unfold ConLeche.divModCertsGuard
  rw [e2, hp2, ← divModCertStmts_tr hx hy hc, List.zip_map, List.all_map]
  refine list_all_congr fun p hp => ?_
  obtain ⟨⟨hyps, eqE⟩, proof⟩ := p
  have hm1 := List.of_mem_zip hp
  obtain ⟨hh, he⟩ := stmtOk_all hokx hoky hx hy hN c _ hm1.1
  exact divModCertGuard_eq hP hv (hpr _ (Array.mem_toList_iff.1 hm1.2)) hh he

end InLeanProof
