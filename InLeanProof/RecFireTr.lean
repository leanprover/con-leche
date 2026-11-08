module

public import InLeanProof.BlockRecogRun
public import InLeanProof.Range

/-!
# A recursor's firing mode through the translation (task #451, lane P3r)

con-leche's install stores each generated recursor's rules with the firing
mode `recFire` reads off the recogniser's record (`.plain` when the major's
target is a member, `tgt < k`; else `.nested` at the major's container's
levels and parameters); InLean computes it at use, `recFireAt`, off the
stored `RecursorVal` (`.plain` when the major's head is in `rv.all`).
`recFire_tr`: the two are `FireRel`-related on a recognised block's
recursor whose `all` is the block's members (`genEntriesAgree`).

Both read the major's domain at `majorIdxOf` (`piBody?` against `stripPis`,
`piBody?_eq`), the head (`getAppFnT` against `getAppFn`), and drop the index
variables from the container's parameters (`dropVars_tr`: instantiation at
the closed `Sort 0`, `toExpr_instantiate1`).
-/

public section

namespace InLeanProof

open Lean InLean

theorem piBody?_eq : ∀ (n : Nat) (e : Expr), piBody? n e = (InLean.stripPis n e).map (·.2)
  | 0, e => by simp [piBody?, InLean.stripPis]
  | n + 1, .forallE _ _ b _ => by
    simp only [piBody?, InLean.stripPis, Option.map_map]
    rw [piBody?_eq n b]; rfl
  | n + 1, .mdata _ e => by simp only [piBody?, InLean.stripPis]; exact piBody?_eq (n + 1) e
  | _ + 1, .bvar _ | _ + 1, .fvar _ | _ + 1, .mvar _ | _ + 1, .sort _ | _ + 1, .const _ _
  | _ + 1, .app _ _ | _ + 1, .lam _ _ _ _ | _ + 1, .letE _ _ _ _ _ | _ + 1, .lit _
  | _ + 1, .proj _ _ _ => by simp [piBody?, InLean.stripPis]

/-! ## The spine through the closed translation -/

theorem trC_not_app_args {x : Expr} (h1 : ∀ f a, x ≠ .app f a) (h2 : ∀ m b, x ≠ .mdata m b) :
    (trC x).getAppArgs = [] := by
  cases x <;> simp_all [trC, trE, ConLeche.Expr.getAppArgs]

theorem getAppArgsT_go_tr : ∀ (e : Expr) (acc : List Expr),
    (Expr.getAppArgsT.go e acc).map trC = (trC e).getAppArgs ++ acc.map trC
  | .app f a, acc => by
    simp only [Expr.getAppArgsT.go, getAppArgsT_go_tr f (a :: acc), List.map_cons]
    simp [trC, trE, ConLeche.Expr.getAppArgs]
  | .mdata _ e, acc => by simp only [Expr.getAppArgsT.go]; exact getAppArgsT_go_tr e acc
  | .bvar _, acc | .fvar _, acc | .mvar _, acc | .sort _, acc | .const _ _, acc
  | .lam _ _ _ _, acc | .forallE _ _ _ _, acc | .letE _ _ _ _ _, acc | .lit _, acc
  | .proj _ _ _, acc => by
    simp only [Expr.getAppArgsT.go]
    rw [trC_not_app_args (by simp) (by simp)]; rfl

theorem getAppArgsT_tr (e : Expr) : (Expr.getAppArgsT e).toList.map trC = (trC e).getAppArgs := by
  simpa [Expr.getAppArgsT] using getAppArgsT_go_tr e []

theorem getAppArgsT_go_ok : ∀ (e : Expr) (acc : List Expr), okC e = true →
    (∀ a ∈ acc, okC a = true) → ∀ a ∈ Expr.getAppArgsT.go e acc, okC a = true
  | .app f x, acc, he, hacc => by
    simp only [okC, okE, Bool.and_eq_true] at he
    simp only [Expr.getAppArgsT.go]
    refine getAppArgsT_go_ok f (x :: acc) he.1 ?_
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact he.2
    · exact hacc a ha
  | .mdata _ e, acc, he, hacc => by
    simp only [Expr.getAppArgsT.go]; exact getAppArgsT_go_ok e acc he hacc
  | .bvar _, acc, _, hacc | .fvar _, acc, _, hacc | .mvar _, acc, _, hacc
  | .sort _, acc, _, hacc | .const _ _, acc, _, hacc | .lam _ _ _ _, acc, _, hacc
  | .forallE _ _ _ _, acc, _, hacc | .letE _ _ _ _ _, acc, _, hacc | .lit _, acc, _, hacc
  | .proj _ _ _, acc, _, hacc => by simpa [Expr.getAppArgsT.go] using hacc

theorem getAppArgsT_ok {e : Expr} (he : okC e = true) :
    ∀ a ∈ (Expr.getAppArgsT e).toList, okC a = true := by
  intro a ha
  exact getAppArgsT_go_ok e [] he (by simp) a (by simpa [Expr.getAppArgsT] using ha)

theorem getAppFnT_ok : ∀ {e : Expr}, okC e = true → okC (Expr.getAppFnT e) = true
  | .app f _, he => by
    simp only [okC, okE, Bool.and_eq_true] at he
    exact getAppFnT_ok (e := f) he.1
  | .mdata _ e, he => getAppFnT_ok (e := e) he
  | .bvar _, he | .fvar _, he | .mvar _, he | .sort _, he | .const _ _, he
  | .lam _ _ _ _, he | .forallE _ _ _ _, he | .letE _ _ _ _ _, he | .lit _, he
  | .proj _ _ _, he => he

theorem getAppFnT_not_app : ∀ (e : Expr) (f a : Expr), Expr.getAppFnT e ≠ .app f a
  | .app g _ => getAppFnT_not_app g
  | .mdata _ e => getAppFnT_not_app e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by intro f a h; cases h

theorem getAppFnT_not_mdata : ∀ (e : Expr) (m : MData) (b : Expr), Expr.getAppFnT e ≠ .mdata m b
  | .app g _ => getAppFnT_not_mdata g
  | .mdata _ e => getAppFnT_not_mdata e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by intro m b h; cases h

/-! ## Dropping the index variables -/

/-- **`dropVars` through the translation**: instantiation at the closed
`Sort 0` keeps a term in range and reads as con-leche's. -/
theorem dropVars_tr : ∀ (n : Nat) {e : Expr} {c : ConLeche.Expr}, Expr.RangeOk e →
    toExprC e = some c →
    Expr.RangeOk (InLean.dropVars n e) ∧ toExprC (InLean.dropVars n e) = some (ConLeche.Expr.dropVars n c)
  | 0, e, c, hr, h => ⟨hr, h⟩
  | n + 1, e, c, hr, h => by
    have hsr : Expr.RangeOk (Expr.sort Level.zero) := by simp [Expr.RangeOk, depthS]
    have hcl : (Expr.sort Level.zero).looseBVarRange = 0 := by
      rw [Expr.looseBVarRange_eq hsr]; rfl
    have hr' : Expr.RangeOk (EO.instantiate1 e (.sort .zero)) := instantiate1_eq e (.sort .zero) ▸
      RangeOk_instantiate hr (fun j hj => by
        have : j = 0 := by simp at hj; omega
        subst this; exact hsr) (fun j hj => by
        have : j = 0 := by simp at hj; omega
        subst this; exact hcl)
    have h' : toExprC (e.inst1I (.sort .zero)) = some (c.instantiate1 (.sort .zero) 0) :=
      toExpr_instantiate1 fvarsOnly_none hr hsr h rfl rfl
    simp only [InLean.dropVars, ConLeche.Expr.dropVars]
    exact dropVars_tr n hr' h'

theorem LRel_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ (l : List α), (∀ a ∈ l, R (f a) (g a)) → LRel R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a List.mem_cons_self) (LRel_map l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## The firing mode -/

theorem trC_not_forallE {x : Expr} (hx : ∀ n t b bi, x ≠ .forallE n t b bi)
    (hm : ∀ m b, x ≠ .mdata m b) : ∀ a b, trC x ≠ .forallE a b := by
  intro a b h
  cases x with
  | forallE n t b' bi => exact hx n t b' bi rfl
  | mdata m b' => exact hm m b' rfl
  | _ => simp [trC, trE] at h

theorem trC_not_const {x : Expr} (hx : ∀ n us, x ≠ .const n us)
    (hm : ∀ m b, x ≠ .mdata m b) : ∀ n us, trC x ≠ .const n us := by
  intro n us h
  cases x with
  | const n' us' => exact hx n' us' rfl
  | mdata m b' => exact hm m b' rfl
  | _ => simp [trC, trE] at h


/-- InLean's firing mode at the major's head `H` (`recFireAt`'s inner match). -/
@[expose] def fireAtHead (all : List Name) (nI : Nat) (dom : Expr) : Expr → RecRuleFire
  | .const T us =>
    if all.contains T then .plain
    else .nested us ((dom.getAppArgsT.toList.take (dom.getAppArgsT.toList.length - nI)).map
      (dropVars nI))
  | _ => .plain

/-- The recogniser's target at the major's head (`recTargetOf`'s inner match). -/
@[expose] def tgtAtHead (names : List Name) : Expr → Option Nat
  | .const n _ => names.findIdx? (· == n)
  | _ => none

/-- con-leche's firing mode at the major's head (`recFire`'s inner match). -/
@[expose] def cFireAtHead (nI : Nat) (cdom : ConLeche.Expr) : ConLeche.Expr → ConLeche.RecRuleFire
  | .const _ us => .nested us ((cdom.getAppArgs.take (cdom.getAppArgs.length - nI)).map
      (ConLeche.Expr.dropVars nI))
  | _ => .plain

theorem fire_head (names : List Name) (nI : Nat) {dom : Expr} (hokd : okC dom = true) :
    ∀ (H : Expr), okC H = true → (∀ m b, H ≠ .mdata m b) →
      FireRel (fireAtHead names nI dom H)
        (if (tgtAtHead names H).getD names.length < names.length then .plain
         else cFireAtHead nI (trC dom) (trC H))
  | .const T us, hHok, _ => by
    simp only [fireAtHead, tgtAtHead]
    by_cases hT : names.contains T = true
    · have hlt : (names.findIdx? (· == T)).getD names.length < names.length := by
        have hmem : T ∈ names := by simpa using hT
        obtain ⟨i, hi⟩ : ∃ i, names.findIdx? (· == T) = some i := by
          apply Option.isSome_iff_exists.1
          rw [List.findIdx?_isSome, List.any_eq_true]
          exact ⟨T, hmem, by simp⟩
        rw [hi]; exact List.findIdx?_eq_some_iff_getElem.1 hi |>.1
      simp only [hlt, ↓reduceIte, hT, FireRel]
    · have hnone : names.findIdx? (· == T) = none := by
        rw [List.findIdx?_eq_none_iff]
        intro a ha
        cases he : a == T
        · rfl
        · have : a = T := by simpa using he
          subst this
          exact absurd (by simpa using ha) hT
      have hT' : names.contains T = false := by simpa using hT
      simp only [hnone, Option.getD_none, Nat.lt_irrefl, ↓reduceIte, hT', Bool.false_eq_true,
        trC, trE, cFireAtHead]
      refine ⟨?_, rfl, ?_⟩
      · simpa [okC, okE] using hHok
      · rw [show trE (fun _ => none) dom = trC dom from rfl, ← getAppArgsT_tr dom,
          List.length_map, ← List.map_take, List.map_map]
        apply LRel_map
        intro a ha
        have haok := getAppArgsT_ok hokd a (List.mem_of_mem_take ha)
        obtain ⟨h1, h2⟩ := dropVars_tr nI (RangeOk_of_okE haok) (toExpr_of_okE _ haok)
        exact StoredT_of h1 h2
  | .mdata m b, _, hm => absurd rfl (hm m b)
  | .bvar _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .app _ _, _, _
  | .lam _ _ _ _, _, _ | .forallE _ _ _ _, _, _ | .letE _ _ _ _ _, _, _ | .lit _, _, _
  | .proj _ _ _, _, _ => by
    simp [fireAtHead, tgtAtHead, trC, trE, cFireAtHead, FireRel]

/-- **A recognised recursor's firing mode**: con-leche's `recFire` on the
record, at a block with the recursor's `all` as its members, against
InLean's `recFireAt` on the stored recursor. -/
theorem recFire_tr {P : ConLeche.BlockShape} {rc : InLean.RecShape} {rv : RecursorVal}
    {names : List Name} (hok : okC rv.type = true) (hall : rv.all = names)
    (hk : P.k = names.length) (hcv : rc.cvR = rv.toConstantVal) (hmI : rc.mI = majorIdxOf rv)
    (hrP : rc.rP = rulePrefixOf rv) (htgt : rc.tgt = recTargetOf names (majorIdxOf rv) rv.type) :
    FireRel (recFireAt rv false) (ConLeche.recFire P (trRec rc)) := by
  have hty : (trRec rc).cvR.type = trC rv.type := by simp [trRec, hcv]
  have hmI' : (trRec rc).mI = majorIdxOf rv := by simp [trRec, hmI]
  have hrP' : (trRec rc).rP = rulePrefixOf rv := by simp [trRec, hrP]
  have htgt' : (trRec rc).tgt = recTargetOf names (majorIdxOf rv) rv.type := by simp [trRec, htgt]
  unfold recFireAt ConLeche.recFire
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [htgt', hk, hty, hmI', hrP', piBody?_eq, stripPis_tr]
  unfold recTargetOf
  cases hs : InLean.stripPis (majorIdxOf rv) rv.type with
  | none => simp [FireRel]
  | some q =>
    obtain ⟨ds, r⟩ := q
    have hokr : okC (EO.stripTop r) = true := by rw [okC_stripTop]; exact stripPis_okC hok hs
    simp only [Option.map_some]
    rw [← trC_stripTop r]
    have hm := stripTop_ne_mdata' r
    generalize EO.stripTop r = x at hokr hm
    cases x with
    | forallE n dom b bi =>
      have hokd : okC dom = true := by
        simp only [okC, okE, Bool.and_eq_true] at hokr; exact hokr.1
      simp only [trC, trE]
      rw [show trE (fun _ => none) dom = trC dom from rfl, getAppFn_tr, ← hall]
      exact fire_head rv.all _ hokd _ (getAppFnT_ok hokd) (getAppFnT_not_mdata dom)
    | mdata m b => exact absurd rfl (hm m b)
    | _ => simp [trC, trE, FireRel]

end InLeanProof
