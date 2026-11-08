module

public import InLeanProof.CertDivMod
import ConLeche.Verify.Cached.BridgeCS1
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

/-! ## The attempt -/

theorem typePinStored_lbb {L : ConLeche.Env} (hw : ConLeche.EnvWF L) (n : ConLeche.Name) :
    (ConLeche.typePinStored L n).looseBVarsBounded 0 = true := by
  unfold ConLeche.typePinStored
  split
  · rename_i ci hc; exact (hw.consts _ (ConLeche.Env.find?_mem hc)).2.2.2.1
  · rfl

/-- **The type pins** (`checkTypePins`, master's against `typePinStored`). -/
theorem checkTypePins_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) :
    ∀ (l : List (Name × Expr)) {s₀ s' : InLean.CState} {b : Bool},
      CSOKI .verified false L s₀ → (∀ t ∈ l, okC t.2 = true ∧ (trC t.2).looseBVarsBounded 0 = true) →
      InLean.checkTypePins .verified fe l s₀ = .ok (b, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkTypePins (ConLeche.fueledOpsM .verified) L
          (l.map fun p => (toName p.1, trC p.2))) b := by
  intro l
  induction l with
  | nil =>
    intro s₀ s' b hs _ h
    unfold InLean.checkTypePins at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, by simp only [List.map_nil, ConLeche.checkTypePins]; exact Runs.pure _⟩
  | cons p rest ih =>
    intro s₀ s' b hs hp h
    obtain ⟨n, ty⟩ := p
    unfold InLean.checkTypePins at h
    obtain ⟨b1, s₁, hD, h⟩ := bindI_ok h
    obtain ⟨hty, hlbb⟩ := hp (n, ty) (List.mem_cons_self ..)
    obtain ⟨hst, hsto⟩ := typePinStored_tr hJ.pres n
    obtain ⟨hs₁, ht₁, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₀) (d := 0)
      hs (OkS_of_okC _ hsto) (OkS_of_okC _ hty)
      (by rw [TrS_of_okC _ hsto]; exact trC_wscoped _ _) (by rw [TrS_of_okC _ hty]; exact trC_wscoped _ _)
      (by rw [TrS_of_okC _ hsto, ← hst]; exact typePinStored_lbb hJ.wf _)
      (by rw [TrS_of_okC _ hty]; exact hlbb)) b1 s₁ hD
    rw [TrS_of_okC _ hsto, TrS_of_okC _ hty, ← hst] at hRD
    simp only [List.map_cons, ConLeche.checkTypePins]
    have hp' : ∀ t ∈ rest, okC t.2 = true ∧ (trC t.2).looseBVarsBounded 0 = true :=
      fun t ht => hp t (List.mem_cons_of_mem _ ht)
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      exact ⟨hs₁, ht₁, Runs.bind hRD (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _)⟩
    · simp only [↓reduceIte] at h
      obtain ⟨hs₂, ht₂, hR⟩ := ih hs₁ hp' h
      exact ⟨hs₂, ht₁.trans ht₂, Runs.bind hRD (by simp only [↓reduceIte]; exact hR)⟩

/-- The statement terms read scoped at the two variables and closed. -/
theorem stmtScope_all {s : InLean.CState} {x y : Expr}
    (hx : TrS s x = .fvar 0 (.const ConLeche.natName []))
    (hy : TrS s y = .fvar 1 (.const ConLeche.natName [])) (c : Name) :
    ∀ p ∈ InLean.divModCertStmts x y c,
      (∀ h ∈ p.1, (TrS s h).wscopedB 2 = true ∧ (TrS s h).looseBVarsBounded 0 = true) ∧
      ((TrS s p.2).wscopedB 2 = true ∧ (TrS s p.2).looseBVarsBounded 0 = true) := by
  refine divModCertStmts_all c (fun h => (TrS s h).wscopedB 2 = true ∧
    (TrS s h).looseBVarsBounded 0 = true) ?_ ?_ ?_ ?_
  · intro n us _; simp [TrS_const, ConLeche.Expr.wscopedB, ConLeche.Expr.looseBVarsBounded]
  · intro f a hf ha
    simp [TrS_app, ConLeche.Expr.wscopedB, ConLeche.Expr.looseBVarsBounded, hf.1, hf.2, ha.1, ha.2]
  · simp [hx, ConLeche.Expr.wscopedB, ConLeche.Expr.looseBVarsBounded]
  · simp [hy, ConLeche.Expr.wscopedB, ConLeche.Expr.looseBVarsBounded]

/-- The facts about the two variables a state carries. -/
@[expose] def VarsOk (s : InLean.CState) (x y : Expr) : Prop :=
  OkS s x = true ∧ OkS s y = true ∧ TrS s x = .fvar 0 (.const ConLeche.natName []) ∧
    TrS s y = .fvar 1 (.const ConLeche.natName [])

theorem VarsOk.mono {s₀ s₁ : InLean.CState} {x y : Expr} (h : VarsOk s₀ x y) (ht : TabLe s₀ s₁) :
    VarsOk s₁ x y :=
  ⟨okS_of_tabLe ht h.1, okS_of_tabLe ht h.2.1, by rw [TrS_of_tabLe ht h.1, h.2.2.1],
    by rw [TrS_of_tabLe ht h.2.1, h.2.2.2]⟩

/-- The statements' list, read at a later state. -/
theorem stmts_map_tabLe {L : ConLeche.Env} {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁)
    {S : List (List Expr × Expr)}
    (hS : ∀ p ∈ S, (∀ h ∈ p.1, StmtOk s₀ L h) ∧ StmtOk s₀ L p.2) :
    S.map (fun p => (p.1.map (TrS s₁), TrS s₁ p.2)) = S.map (fun p => (p.1.map (TrS s₀), TrS s₀ p.2)) := by
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨hh, he⟩ := hS p hp
  rw [TrS_of_tabLe ht he.2.1, List.map_congr_left fun h hm => TrS_of_tabLe ht (hh h hm).2.1]

theorem divModCertApplied_lbb (q : ConLeche.Expr) (hs : List ConLeche.Expr) :
    (ConLeche.divModCertApplied q hs).looseBVarsBounded 0 = q.looseBVarsBounded 0 := by
  unfold ConLeche.divModCertApplied
  split <;> simp [ConLeche.Expr.looseBVarsBounded]

/-- What the applied certificate satisfies at the state after it. -/
@[expose] def AppliedOk (L : ConLeche.Env) (s₀ s₁ : InLean.CState) (p : Expr) (hs : List Expr)
    (applied : Expr) : Prop :=
  CSOKI .verified false L s₁ ∧ TabLe s₀ s₁ ∧ OkS s₁ applied = true ∧
    TrS s₁ applied = ConLeche.divModCertApplied (TrS s₀ p) (hs.map (TrS s₀))

theorem base_tr {s₀ : InLean.CState} {p x y : Expr} (hV : VarsOk s₀ x y) (hp : OkS s₀ p = true) :
    OkS s₀ (mkApp2 p x y) = true ∧
      TrS s₀ (mkApp2 p x y) = .app (.app (TrS s₀ p) (.fvar 0 (.const ConLeche.natName [])))
        (.fvar 1 (.const ConLeche.natName [])) := by
  obtain ⟨hox, hoy, hx, hy⟩ := hV
  exact ⟨by simp only [mkApp2, mkAppB, mkApp, OkS_app, hp, hox, hoy, Bool.and_self],
    by simp only [mkApp2, mkAppB, mkApp, TrS_app, hx, hy]⟩

/-- **The applied certificate, no hypothesis variable** (no hypothesis, or more than two). -/
theorem applied0 {L : ConLeche.Env} {s₀ : InLean.CState} {p x y : Expr} {hs : List Expr}
    (hs₀ : CSOKI .verified false L s₀) (hV : VarsOk s₀ x y) (hp : OkS s₀ p = true)
    (h1 : ∀ a, hs ≠ [a]) (h2 : ∀ a b, hs ≠ [a, b]) :
    AppliedOk L s₀ s₀ p hs (mkApp2 p x y) := by
  obtain ⟨o, t⟩ := base_tr hV hp
  refine ⟨hs₀, TabLe.refl _, o, ?_⟩
  rw [t]
  unfold ConLeche.divModCertApplied
  split
  · rename_i a he
    rcases hs with _ | ⟨a', _ | ⟨b', t'⟩⟩
    · simp at he
    · exact (h1 a' rfl).elim
    · simp at he
  · rename_i a b he
    rcases hs with _ | ⟨a', _ | ⟨b', _ | ⟨c', t'⟩⟩⟩
    · simp at he
    · simp at he
    · exact (h2 a' b' rfl).elim
    · simp at he
  · rfl

/-- **The applied certificate, one hypothesis variable** (`mkFVarM 2`). -/
theorem applied1 {L : ConLeche.Env} {s₀ s₁ : InLean.CState} {p x y h1 a : Expr}
    (hs₀ : CSOKI .verified false L s₀) (hV : VarsOk s₀ x y) (hp : OkS s₀ p = true)
    (o1 : OkS s₀ h1 = true) (l1 : (TrS s₀ h1).looseBVarsBounded 0 = true)
    (hA : mkFVarM 2 h1 s₀ = .ok (a, s₁)) :
    AppliedOk L s₀ s₁ p [h1] (.app (mkApp2 p x y) a) := by
  obtain ⟨o, t⟩ := base_tr hV hp
  obtain ⟨hs₁, ht₁, hoa, hTa⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₀ 2 o1 l1) a s₁ hA
  refine ⟨hs₁, ht₁, ?_, ?_⟩
  · simp only [OkS_app, okS_of_tabLe ht₁ o, hoa, Bool.and_self]
  · rw [TrS_app, TrS_of_tabLe ht₁ o, t, hTa]; rfl

/-- **The applied certificate, two hypothesis variables** (`mkFVarM 2`, `3`). -/
theorem applied2 {L : ConLeche.Env} {s₀ s₁ s₂ : InLean.CState} {p x y h1 h2 a b : Expr}
    (hs₀ : CSOKI .verified false L s₀) (hV : VarsOk s₀ x y) (hp : OkS s₀ p = true)
    (o1 : OkS s₀ h1 = true) (l1 : (TrS s₀ h1).looseBVarsBounded 0 = true)
    (o2 : OkS s₀ h2 = true) (l2 : (TrS s₀ h2).looseBVarsBounded 0 = true)
    (hA : mkFVarM 2 h1 s₀ = .ok (a, s₁)) (hB : mkFVarM 3 h2 s₁ = .ok (b, s₂)) :
    AppliedOk L s₀ s₂ p [h1, h2] (mkApp2 (mkApp2 p x y) a b) := by
  obtain ⟨o, t⟩ := base_tr hV hp
  obtain ⟨hs₁, ht₁, hoa, hTa⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₀ 2 o1 l1) a s₁ hA
  obtain ⟨hs₂, ht₂, hob, hTb⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₁ 3 (okS_of_tabLe ht₁ o2)
    (by rw [TrS_of_tabLe ht₁ o2]; exact l2)) b s₂ hB
  have ht := ht₁.trans ht₂
  refine ⟨hs₂, ht, ?_, ?_⟩
  · simp only [mkApp2, mkAppB, mkApp] at o ⊢
    simp only [OkS_app, okS_of_tabLe ht o, okS_of_tabLe ht₂ hoa, hob, Bool.and_self]
  · have e1 : TrS s₂ (mkApp2 (mkApp2 p x y) a b) =
        .app (.app (TrS s₂ (mkApp2 p x y)) (TrS s₂ a)) (TrS s₂ b) := by
      simp only [mkApp2, mkAppB, mkApp, TrS_app]
    rw [e1, TrS_of_tabLe ht o, t, TrS_of_tabLe ht₂ hoa, hTa, hTb, TrS_of_tabLe ht₁ o2]
    rfl

/-- **The certificate loop** (`checkDivModCerts`, at depth 4 over the
interned variables and hypotheses). -/
theorem checkDivModCerts_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {c : Name} {annVal x y : Expr} (hv : okC annVal = true)
    (hvl : (trC annVal).looseBVarsBounded 0 = true)
    (hN : (L.find? ConLeche.natName).isSome = true) :
    ∀ (S : List (List Expr × Expr)) (P : List Expr) {s₀ s' : InLean.CState} {b : Bool},
      CSOKI .verified false L s₀ → VarsOk s₀ x y → (∀ p ∈ S, p ∈ InLean.divModCertStmts x y c) →
      (∀ p ∈ P, okC p = true) →
      InLean.checkDivModCerts .verified fe c annVal x y S P s₀ = .ok (b, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkDivModCerts (ConLeche.fueledOpsM .verified) L (toName c) (trC annVal)
          (S.map fun p => (p.1.map (TrS s₀), TrS s₀ p.2)) (P.map trC)) b := by
  intro S
  induction S with
  | nil =>
    intro P s₀ s' b hs _ _ _ h
    cases P with
    | nil =>
      unfold InLean.checkDivModCerts at h
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      exact ⟨hs, TabLe.refl _, by simp only [List.map_nil, ConLeche.checkDivModCerts]; exact Runs.pure _⟩
    | cons =>
      unfold InLean.checkDivModCerts at h
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      exact ⟨hs, TabLe.refl _, by simp only [List.map_nil, List.map_cons, ConLeche.checkDivModCerts]; exact Runs.pure _⟩
  | cons q srest ih =>
    intro P s₀ s' b hs hV hSm hPm h
    obtain ⟨hyps, eqE⟩ := q
    cases P with
    | nil =>
      unfold InLean.checkDivModCerts at h
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      exact ⟨hs, TabLe.refl _, by simp only [List.map_nil, List.map_cons, ConLeche.checkDivModCerts]; exact Runs.pure _⟩
    | cons proof prest =>
      obtain ⟨hox, hoy, hx, hy⟩ := hV
      have hpS := hSm _ (List.mem_cons_self ..)
      obtain ⟨hhO, heO⟩ := stmtOk_all (L := L) hox hoy hx hy hN c _ hpS
      obtain ⟨hhW, heW⟩ := stmtScope_all hx hy c _ hpS
      have hpr := hPm proof (List.mem_cons_self ..)
      have hG := divModCertGuard_eq (c := c) hJ.pres hv hpr hhO heO
      have hSrest : ∀ p ∈ srest, p ∈ InLean.divModCertStmts x y c :=
        fun p hp => hSm p (List.mem_cons_of_mem _ hp)
      have hSrO : ∀ p ∈ srest, (∀ h ∈ p.1, StmtOk s₀ L h) ∧ StmtOk s₀ L p.2 :=
        fun p hp => stmtOk_all hox hoy hx hy hN c _ (hSrest p hp)
      simp only [List.map_cons, ConLeche.checkDivModCerts]
      rw [hG]
      unfold InLean.checkDivModCerts at h
      split at h
      rotate_left
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := pureI_ok h
        simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hs, TabLe.refl _, Runs.pure _⟩
      rename_i hg
      simp only [hg, ↓reduceIte]
      obtain ⟨o, t⟩ := substConstAll_trC (n := c) hv hpr
      have hgM := hG ▸ hg
      have hhs : ∀ h ∈ hyps.map (InLean.substConst0 c annVal),
          OkS s₀ h = true ∧ (TrS s₀ h).looseBVarsBounded 0 = true := by
        intro h hm
        obtain ⟨h0, hm0, rfl⟩ := List.mem_map.1 hm
        refine ⟨OkS_substConst0 (OkS_of_okC s₀ hv) _ (hhO h0 hm0).2.1, ?_⟩
        rw [TrS_substConst0 c annVal (hhO h0 hm0).1, TrS_of_okC s₀ hv]
        exact lbb_substConst0 hvl _ (hhW h0 hm0).2
      have hV : VarsOk s₀ x y := ⟨hox, hoy, hx, hy⟩
      have hop := OkS_of_okC s₀ o
      obtain ⟨applied, s₁, ⟨hs₁, ht₁, hoA, hTA⟩, h⟩ : ∃ applied s₁,
          AppliedOk L s₀ s₁ (InLean.substConstAll c annVal proof)
            (hyps.map (InLean.substConst0 c annVal)) applied ∧
          (do
            let tp ← InLean.opInfer .verified fe 4 applied
            let l ← InLean.opDefeq .verified fe 4 tp (InLean.substConst0 c annVal eqE)
            if l = true then InLean.checkDivModCerts .verified fe c annVal x y srest prest
            else pure false : InLean.CheckCM Bool) s₁ = .ok (b, s') := by
        simp only [] at h
        generalize hHS : hyps.map (InLean.substConst0 c annVal) = HS at hhs h
        rcases HS with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
        · obtain ⟨ap, s₂, hP, h⟩ := bindI_ok h
          obtain ⟨rfl, rfl⟩ := pureI_ok hP
          exact ⟨_, _, applied0 hs hV hop (by simp) (by simp), h⟩
        · obtain ⟨a, s₂, hA, h⟩ := bindI_ok h
          obtain ⟨ap, s₃, hP, h⟩ := bindI_ok h
          obtain ⟨rfl, rfl⟩ := pureI_ok hP
          obtain ⟨o1, l1⟩ := hhs h1 (by simp)
          exact ⟨_, _, applied1 hs hV hop o1 l1 hA, h⟩
        · obtain ⟨a, s₂, hA, h⟩ := bindI_ok h
          obtain ⟨b', s₃, hB, h⟩ := bindI_ok h
          obtain ⟨ap, s₄, hP, h⟩ := bindI_ok h
          obtain ⟨rfl, rfl⟩ := pureI_ok hP
          obtain ⟨o1, l1⟩ := hhs h1 (by simp)
          obtain ⟨o2, l2⟩ := hhs h2 (by simp)
          exact ⟨_, _, applied2 hs hV hop o1 l1 o2 l2 hA hB, h⟩
        · obtain ⟨ap, s₂, hP, h⟩ := bindI_ok h
          obtain ⟨rfl, rfl⟩ := pureI_ok hP
          exact ⟨_, _, applied0 hs hV hop (by simp) (by simp), h⟩
      have hmapH : (hyps.map (InLean.substConst0 c annVal)).map (TrS s₀) =
          (hyps.map (TrS s₀)).map (ConLeche.Expr.substConst0 (toName c) (trC annVal)) := by
        simp only [List.map_map]
        refine List.map_congr_left fun h hm => ?_
        simp only [Function.comp]
        rw [TrS_substConst0 c annVal (hhO h hm).1, TrS_of_okC s₀ hv]
      rw [hmapH, TrS_of_okC s₀ o, t] at hTA
      have hwA := ConLeche.Cached.divModCertApplied_wscoped (trC_hasFvar annVal)
        (fun hyp hm => by
          obtain ⟨h0, hm0, rfl⟩ := List.mem_map.1 hm
          exact (hhW h0 hm0).1) hgM
      have hlA : (TrS s₁ applied).looseBVarsBounded 0 = true := by
        rw [hTA, divModCertApplied_lbb]
        unfold ConLeche.divModCertGuard at hgM
        simp only [Bool.and_eq_true] at hgM
        exact hgM.1.1.1.1.1
      obtain ⟨tp, s₂, hI, h⟩ := bindI_ok h
      obtain ⟨hs₂, ht₂, hotp, hRI, hwtp, hltp⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₁) (d := 4)
        hs₁ hoA (by rw [hTA]; exact hwA) hlA) tp s₂ hI
      rw [hTA] at hRI
      obtain ⟨b1, s₃, hD, h⟩ := bindI_ok h
      have ht₁₂ := ht₁.trans ht₂
      have hoe : OkS s₀ (InLean.substConst0 c annVal eqE) = true :=
        OkS_substConst0 (OkS_of_okC s₀ hv) _ heO.2.1
      have hTe : TrS s₂ (InLean.substConst0 c annVal eqE) =
          ConLeche.Expr.substConst0 (toName c) (trC annVal) (TrS s₀ eqE) := by
        rw [TrS_of_tabLe ht₁₂ hoe, TrS_substConst0 c annVal heO.1, TrS_of_okC s₀ hv]
      have hwE : ConLeche.Expr.WScoped 4 (TrS s₂ (InLean.substConst0 c annVal eqE)) := by
        rw [hTe]
        exact ConLeche.Expr.WScoped.mono (show 2 ≤ 4 by omega)
          (ConLeche.Expr.WScoped.of_wscopedB (ConLeche.wscopedB_substConst0 (trC_hasFvar _) _ heW.1))
      have hlE : (TrS s₂ (InLean.substConst0 c annVal eqE)).looseBVarsBounded 0 = true := by
        rw [hTe]; exact lbb_substConst0 hvl _ heW.2
      obtain ⟨hs₃, ht₃, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₂) (d := 4)
        hs₂ hotp (okS_of_tabLe ht₁₂ hoe) hwtp hwE hltp hlE) b1 s₃ hD
      rw [hTe] at hRD
      have ht₀₃ := ht₁₂.trans ht₃
      refine ⟨?_, ?_, Runs.bind hRI (Runs.bind hRD ?_)⟩ <;> cases b1
      all_goals simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      · exact (pureI_ok h).2 ▸ hs₃
      · exact (ih prest hs₃ (VarsOk.mono ⟨hox, hoy, hx, hy⟩ ht₀₃) hSrest
          (fun p hp => hPm p (List.mem_cons_of_mem _ hp)) h).1
      · exact (pureI_ok h).2 ▸ ht₀₃
      · exact ht₀₃.trans (ih prest hs₃ (VarsOk.mono ⟨hox, hoy, hx, hy⟩ ht₀₃) hSrest
          (fun p hp => hPm p (List.mem_cons_of_mem _ hp)) h).2.1
      · obtain ⟨rfl, -⟩ := pureI_ok h; exact Runs.pure _
      · have := (ih prest hs₃ (VarsOk.mono ⟨hox, hoy, hx, hy⟩ ht₀₃) hSrest
          (fun p hp => hPm p (List.mem_cons_of_mem _ hp)) h).2.2
        rwa [stmts_map_tabLe ht₀₃ hSrO] at this

/-- The facts a decoded variant's operation carries (`loadPinSets_okC`). -/
@[expose] def OpOk (op : InLean.PinOp) : Prop :=
  okC op.pin = true ∧ (∀ p ∈ op.proofs, okC p = true) ∧ ∀ t ∈ op.typePins, okC t.2 = true

theorem op?_mem {ps : InLean.PinSet} {c : Name} {op : InLean.PinOp} (h : ps.op? c = some op) :
    op ∈ ps.ops := Array.mem_of_find?_eq_some h

/-- What the pin guard gives about the pin and the type pins. -/
theorem pinGuard_lbb {fe : InLean.FEnv} {op : InLean.PinOp} (hD : OpOk op)
    (hg : InLean.divModPinGuard fe op = true) :
    (trC op.pin).looseBVarsBounded 0 = true ∧
      ∀ t ∈ op.typePins.toList, okC t.2 = true ∧ (trC t.2).looseBVarsBounded 0 = true := by
  unfold InLean.divModPinGuard at hg
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
  refine ⟨by rw [(flags_trC hD.1).1, hg.1.1.1.1]; rfl, fun t ht => ?_⟩
  have ht' := Array.mem_toList_iff.1 ht
  have h2 := Array.all_eq_true_iff_forall_mem.1 hg.2 t ht'
  obtain ⟨n, ty⟩ := t
  have hok := hD.2.2 _ ht'
  refine ⟨hok, ?_⟩
  simp only at h2
  split at h2
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
    rw [(flags_trC hok).1, h2.1.1.2]; rfl
  · exact absurd h2 (by simp)

/-- **One variant's attempt** (`checkDivModPinAt`: the type pins, the pin,
the certificates). -/
theorem checkDivModPinAt_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {c : Name} {value x y : Expr} {ps : InLean.PinSet} {op : InLean.PinOp}
    (hc : InLean.natDivModNames.contains c = true) (hop : ps.op? c = some op) (hD : OpOk op)
    (hv : okC value = true) (hvl : (trC value).looseBVarsBounded 0 = true)
    (hN : (L.find? ConLeche.natName).isSome = true) (hg : InLean.divModPinGuard fe op = true)
    {s₀ s' : InLean.CState} {b : Bool} (hs : CSOKI .verified false L s₀) (hV : VarsOk s₀ x y)
    (h : InLean.checkDivModPinAt .verified fe c value x y op s₀ = .ok (b, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.checkDivModPinAt (ConLeche.fueledOpsM .verified) L (toName c) (trC value)
        (trPinSet ps)) b := by
  obtain ⟨e1, e2, e3⟩ := trPinSet_fields ps hc
  obtain ⟨hpl, htl⟩ := pinGuard_lbb hD hg
  unfold InLean.checkDivModPinAt at h
  unfold ConLeche.checkDivModPinAt
  rw [e1, e2, e3]
  simp only [trOpPin, trOpProofs, trOpTypePins, hop]
  obtain ⟨b1, s₁, hT, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hRT⟩ := checkTypePins_sim hJ _ hs htl hT
  refine (?_ : _ ∧ _ ∧ _)
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs₁, ht₁, Runs.bind hRT (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _)⟩
  simp only [↓reduceIte] at h
  obtain ⟨b2, s₂, hD2, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₁) (d := 0)
    hs₁ (OkS_of_okC _ hv) (OkS_of_okC _ hD.1)
    (by rw [TrS_of_okC _ hv]; exact trC_wscoped _ _) (by rw [TrS_of_okC _ hD.1]; exact trC_wscoped _ _)
    (by rw [TrS_of_okC _ hv]; exact hvl) (by rw [TrS_of_okC _ hD.1]; exact hpl)) b2 s₂ hD2
  rw [TrS_of_okC _ hv, TrS_of_okC _ hD.1] at hRD
  have ht₀₂ := ht₁.trans ht₂
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs₂, ht₀₂, Runs.bind hRT (by
      simp only [↓reduceIte]
      exact Runs.bind hRD (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _))⟩
  simp only [↓reduceIte] at h
  have hV₂ := hV.mono ht₀₂
  obtain ⟨hs₃, ht₃, hRC⟩ := checkDivModCerts_sim hJ (c := c) hv hvl hN _ _ hs₂ hV₂
    (fun p hp => hp) (fun p hp => hD.2.1 p (Array.mem_toList_iff.1 hp)) h
  rw [divModCertStmts_tr hV₂.2.2.1 hV₂.2.2.2 hc] at hRC
  exact ⟨hs₃, ht₀₂.trans ht₃, Runs.bind hRT (by
    simp only [↓reduceIte]
    exact Runs.bind hRD (by simp only [↓reduceIte]; exact hRC))⟩

/-- **The variant loop** (`checkDivModPinLoop`), by induction over the
decoded variants: the guards agree both ways, so both loops try the same
variants. -/
theorem checkDivModPinLoop_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {c : Name} {value x y : Expr} (hc : InLean.natDivModNames.contains c = true)
    (hv : okC value = true) (hvl : (trC value).looseBVarsBounded 0 = true)
    (hN : (L.find? ConLeche.natName).isSome = true) :
    ∀ (l : List InLean.PinSet) (tI tM : List String) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → VarsOk s₀ x y → (∀ ps ∈ l, ∀ op ∈ ps.ops, OpOk op) →
      InLean.checkDivModPinLoop .verified fe c value x y l tI s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkDivModPinLoop (ConLeche.fueledOpsM .verified) L (toName c) (trC value)
          (l.map trPinSet) tM) () := by
  intro l
  induction l with
  | nil =>
    intro tI tM s₀ s' u _ _ _ h
    unfold InLean.checkDivModPinLoop at h
    exact (throwI_ok h).elim
  | cons ps rest ih =>
    intro tI tM s₀ s' u hs hV hD h
    have hDr : ∀ ps ∈ rest, ∀ op ∈ ps.ops, OpOk op := fun p hp => hD p (List.mem_cons_of_mem _ hp)
    unfold InLean.checkDivModPinLoop at h
    simp only [List.map_cons, ConLeche.checkDivModPinLoop]
    cases hop : ps.op? c with
    | none =>
      simp only [hop] at h
      rw [divModPinGuard_none hc hop, Bool.false_and]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih _ _ hs hV hDr h
    | some op =>
      simp only [hop] at h
      have hDo := hD ps (List.mem_cons_self ..) op (op?_mem hop)
      obtain ⟨hox, hoy, hx, hy⟩ := hV
      rw [divModPinGuard_eq hJ.pres hc hop hDo.1 hDo.2.2,
        divModCertsGuard_eq hJ.pres hox hoy hx hy hN hc hop hv hDo.2.1]
      split at h
      · rename_i hg
        simp only [hg, ↓reduceIte]
        simp only [Bool.and_eq_true] at hg
        obtain ⟨b, s₁, hA, h⟩ := bindI_ok h
        obtain ⟨hs₁, ht₁, hRA⟩ := checkDivModPinAt_sim hJ hc hop hDo hv hvl hN hg.1 hs
          ⟨hox, hoy, hx, hy⟩ hA
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨hs₂, ht₂, hR⟩ := ih _ (tM ++ [ConLeche.divModAttemptReason (trPinSet ps)]) hs₁
            (VarsOk.mono ⟨hox, hoy, hx, hy⟩ ht₁) hDr h
          exact ⟨hs₂, ht₁.trans ht₂, Runs.bind hRA (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hR)⟩
        · simp only [↓reduceIte] at h
          obtain ⟨-, rfl⟩ := pureI_ok h
          exact ⟨hs₁, ht₁, Runs.bind hRA (by simp only [↓reduceIte]; exact Runs.pure _)⟩
      · rename_i hg
        simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact ih _ _ hs ⟨hox, hoy, hx, hy⟩ hDr h

end InLeanProof
