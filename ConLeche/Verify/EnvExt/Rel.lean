module

public import ConLeche.Verify.EnvExt.Reads

/-!
# A run does not see an extension of the environment: the reduction bodies (task #480)

`Rel P x₂ x₁`: two runs are the same run, and what it returns has `P`.  `KR` is that relation at
every slot of two knot records, on resolved terms.  Each body of `Kernel/Core.lean` used by
reduction, at two environments, is related here, given `KR` one level down.
-/

@[expose] public section

namespace ConLeche.Verify

open ConLeche

/-- Two runs are the same run, and what it returns has `P`. -/
def Rel {α : Type} (P : α → Prop) (x₂ x₁ : CheckM α) : Prop :=
  x₂ = x₁ ∧ ∀ y, x₁ = .ok y → P y

/-- No condition on what a run returns. -/
abbrev TT {α : Type} : α → Prop := fun _ => True

namespace Rel

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

theorem ok {a : α} (h : P a) : Rel P (.ok a) (.ok a) :=
  ⟨rfl, fun _ hy => by
    obtain rfl := Except.ok.inj hy
    exact h⟩

theorem err (e : CheckError) : Rel P (.error e) (.error e) :=
  ⟨rfl, fun _ hy => nomatch hy⟩

theorem triv {x : CheckM α} : Rel TT x x := ⟨rfl, fun _ _ => trivial⟩

theorem bind {x₂ x₁ : CheckM β} {k₂ k₁ : β → CheckM α} (h : Rel Q x₂ x₁)
    (hk : ∀ y, Q y → Rel P (k₂ y) (k₁ y)) : Rel P (x₂ >>= k₂) (x₁ >>= k₁) := by
  obtain ⟨rfl, hQ⟩ := h
  cases hx : x₂ with
  | error e => exact err e
  | ok y =>
    obtain ⟨he, hp⟩ := hk y (hQ y hx)
    exact ⟨he, hp⟩

theorem ite {c : Prop} [Decidable c] {a₂ a₁ b₂ b₁ : CheckM α}
    (h₁ : c → Rel P a₂ a₁) (h₂ : ¬c → Rel P b₂ b₁) :
    Rel P (if c then a₂ else b₂) (if c then a₁ else b₁) := by
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using h₁ hc
  · simpa only [hc, ↓reduceIte] using h₂ hc

/-- Branching on a returned verdict. -/
theorem iteB (b : Bool) {a₂ a₁ b₂ b₁ : CheckM α}
    (h₁ : b = true → Rel P a₂ a₁) (h₂ : b = false → Rel P b₂ b₁) :
    Rel P (if b = true then a₂ else b₂) (if b = true then a₁ else b₁) := by
  cases b
  · exact h₂ rfl
  · exact h₁ rfl

end Rel

/-- **The relation at every slot of two records**, on resolved terms. -/
structure KR (env₁ : Env) (r₂ r₁ : CoreFns CheckM) : Prop where
  whnfCore : ∀ c d {e}, Res env₁ e → Rel (Res env₁) (r₂.whnfCore c d e) (r₁.whnfCore c d e)
  whnf : ∀ d {e}, Res env₁ e → Rel (Res env₁) (r₂.whnf d e) (r₁.whnf d e)
  infer : ∀ d {e}, Res env₁ e → Rel (Res env₁) (r₂.infer d e) (r₁.infer d e)
  inferIO : ∀ d {e}, Res env₁ e → Rel (Res env₁) (r₂.inferIO d e) (r₁.inferIO d e)
  defeq : ∀ d {a b}, Res env₁ a → Res env₁ b → Rel TT (r₂.defeq d a b) (r₁.defeq d a b)
  defeqE : ∀ d {a b}, Res env₁ a → Res env₁ b → Rel TT (r₂.defeqE d a b) (r₁.defeqE d a b)

/-- The io view of two related records. -/
theorem KR.ioView {env₁ : Env} {r₂ r₁ : CoreFns CheckM} (K : KR env₁ r₂ r₁) :
    KR env₁ r₂.ioView r₁.ioView where
  whnfCore := K.whnfCore
  whnf := K.whnf
  infer := K.inferIO
  inferIO := K.inferIO
  defeq := K.defeq
  defeqE := K.defeqE

variable {env₁ env₂ : Env} {r₂ r₁ : CoreFns CheckM}

theorem res_take {l : List Expr} (h : ∀ a ∈ l, Res env₁ a) (n : Nat) :
    ∀ a ∈ l.take n, Res env₁ a :=
  fun a ha => h a (List.mem_of_mem_take ha)

theorem res_drop {l : List Expr} (h : ∀ a ∈ l, Res env₁ a) (n : Nat) :
    ∀ a ∈ l.drop n, Res env₁ a :=
  fun a ha => h a (List.mem_of_mem_drop ha)

theorem res_etaProjs {T : Name} {b : Expr} (hT : (env₁.find? T).isSome = true) (hb : Res env₁ b)
    (nF : Nat) : ∀ a ∈ etaProjs T b nF, Res env₁ a := by
  intro a ha
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
  exact res_proj.mpr ⟨hT, hb⟩

section Bodies

variable (K : KR env₁ r₂ r₁) (d : Nat)
include K

theorem defEqList_rel : ∀ (as bs : List Expr), (∀ a ∈ as, Res env₁ a) → (∀ b ∈ bs, Res env₁ b) →
    Rel TT (defEqList r₂ env₂ d as bs) (defEqList r₁ env₁ d as bs)
  | [], [], _, _ => Rel.ok trivial
  | [], _ :: _, _, _ | _ :: _, [], _, _ => Rel.ok trivial
  | a :: as, b :: bs, ha, hb => by
    simp only [defEqList]
    refine Rel.bind (K.defeq d (ha a List.mem_cons_self) (hb b List.mem_cons_self)) fun v _ => ?_
    refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
    exact defEqList_rel as bs (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))

theorem iotaCertsFull_rel : ∀ (ty : Expr) (args : List Expr), Res env₁ ty →
    (∀ a ∈ args, Res env₁ a) →
    Rel TT (iotaCertsFull r₂ env₂ d ty args) (iotaCertsFull r₁ env₁ d ty args)
  | _, [], _, _ => by
    simp only [iotaCertsFull]
    exact Rel.ok trivial
  | ty, arg :: rest, hty, ha => by
    cases ty with
    | forallE t b =>
      obtain ⟨ht, hb⟩ := res_forall.mp hty
      have harg := ha arg List.mem_cons_self
      simp only [iotaCertsFull]
      refine Rel.bind (K.infer d harg) fun ta hta => Rel.bind (K.defeq d hta ht) fun v _ => ?_
      refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
      exact iotaCertsFull_rel _ rest (res_instantiate1 harg b 0 hb)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ =>
      simp only [iotaCertsFull]
      exact Rel.ok trivial

omit K in
theorem res_piResidual : ∀ {t : Expr} {args : List Expr} {r : Expr}, Res env₁ t →
    (∀ a ∈ args, Res env₁ a) → piResidual t args = some r → Res env₁ r
  | t, [], r, ht, _, h => by
    simp only [piResidual, Option.some.injEq] at h
    exact h ▸ ht
  | t, a :: as, r, ht, ha, h => by
    cases t with
    | forallE _ b =>
      simp only [piResidual] at h
      exact res_piResidual (res_instantiate1 (ha a List.mem_cons_self) b 0 (res_forall.mp ht).2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h
    | _ => simp [piResidual] at h

theorem iotaIndexOk_rel (mI rP cnP : Nat) {tyCtor : Expr} {margs idx : List Expr}
    (ht : Res env₁ tyCtor) (hm : ∀ a ∈ margs, Res env₁ a) (hi : ∀ a ∈ idx, Res env₁ a) :
    Rel TT (iotaIndexOk r₂ env₂ d mI rP cnP tyCtor margs idx)
      (iotaIndexOk r₁ env₁ d mI rP cnP tyCtor margs idx) := by
  unfold iotaIndexOk
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  cases hp : piResidual tyCtor margs with
  | none => exact Rel.ok trivial
  | some residual =>
    exact defEqList_rel K d _ _
      (res_drop (res_getAppArgs (res_piResidual ht hm hp)) cnP) hi

theorem proofIrrel_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (proofIrrel r₂ d a b) (proofIrrel r₁ d a b) := by
  unfold proofIrrel
  refine Rel.bind (K.inferIO d ha) fun ta hta => Rel.bind (K.inferIO d hta) fun tt htt =>
    Rel.bind (K.whnf d htt) fun w _ => ?_
  cases w with
  | sort uT =>
    refine Rel.bind Rel.triv fun okA _ => Rel.bind (K.inferIO d hb) fun tb htb =>
      Rel.bind (K.inferIO d htb) fun tt' htt' => Rel.bind (K.whnf d htt') fun w' _ => ?_
    cases w' with
    | sort vT =>
      exact Rel.bind Rel.triv fun okB _ => Rel.ok trivial
    | _ => exact Rel.ok trivial
  | _ => exact Rel.ok trivial

theorem propIrrel_rel (hx : EnvExt env₁ env₂) {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (propIrrel r₂ env₂ d a b) (propIrrel r₁ env₁ d a b) := by
  unfold propIrrel
  rw [notProofFast_ext hx ha, notProofFast_ext hx hb, isProofFast_ext hx ha, isProofFast_ext hx hb]
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  refine Rel.bind (K.inferIO d ha) fun ta hta => Rel.bind (K.inferIO d hta) fun tt htt =>
    Rel.bind (K.whnf d htt) fun w _ => ?_
  cases w with
  | sort uT =>
    refine Rel.bind Rel.triv fun okA _ => Rel.bind (K.inferIO d hb) fun tb htb =>
      Rel.bind (K.inferIO d htb) fun tt' htt' => Rel.bind (K.whnf d htt') fun w' _ => ?_
    cases w' with
    | sort vT =>
      exact Rel.bind Rel.triv fun okB _ => Rel.ok trivial
    | _ => exact Rel.ok trivial
  | _ => exact Rel.ok trivial

theorem structEtaCertWith_rel (hx : EnvExt env₁ env₂) {a b wtb : Expr} (ha : Res env₁ a)
    (hb : Res env₁ b) (hw : Res env₁ wtb) :
    Rel TT (structEtaCertWith r₂ env₂ d a b wtb) (structEtaCertWith r₁ env₁ d a b wtb) := by
  unfold structEtaCertWith
  cases hfn : a.getAppFn with
  | const c us =>
    dsimp only
    rw [hx.find_of_isSome (res_head ha hfn)]
    cases env₁.find? c with
    | none => exact Rel.ok trivial
    | some ci =>
      cases ci with
      | ctorInfo cvc cnP cnF =>
        dsimp only
        refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
        cases hft : wtb.getAppFn with
        | const T us' =>
          dsimp only
          have hT := res_head hw hft
          rw [hx.find_of_isSome hT]
          cases env₁.find? T with
          | none => exact Rel.ok trivial
          | some ci' =>
            cases ci' with
            | indInfo cvT caps =>
              dsimp only
              rw [hx.table T hT]
              cases env₁.findTable? T with
              | none => exact Rel.ok trivial
              | some tbl =>
              dsimp only
              refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
              refine Rel.bind Rel.triv fun v _ => ?_
              refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
              have hargsA := res_getAppArgs ha
              refine Rel.bind (defEqList_rel K d _ _ (res_take hargsA _)
                (res_getAppArgs hw)) fun v' _ => ?_
              refine Rel.iteB v' (fun _ => ?_) fun _ => Rel.ok trivial
              exact defEqList_rel K d _ _ (res_drop hargsA _) (res_etaProjs hT hb _)
            | _ => exact Rel.ok trivial
        | _ => exact Rel.ok trivial
      | _ => exact Rel.ok trivial
  | _ => exact Rel.ok trivial

theorem structEtaFull_rel (hx : EnvExt env₁ env₂) {a b : Expr} (ha : Res env₁ a)
    (hb : Res env₁ b) :
    Rel TT (structEtaFull r₂ env₂ d a b) (structEtaFull r₁ env₁ d a b) := by
  unfold structEtaFull
  rw [etaCtorShape_ext hx ha]
  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
  exact Rel.bind (K.inferIO d hb) fun tb htb => Rel.bind (K.whnf d htb) fun w hw =>
    structEtaCertWith_rel K d hx ha hb hw

omit d in
theorem structEtaExpand_rel (hx : EnvExt env₁ env₂) :
    ∀ (k d : Nat) {a b t : Expr}, Res env₁ a → Res env₁ b → Res env₁ t →
      Rel TT (structEtaExpand r₂ env₂ k d a b t) (structEtaExpand r₁ env₁ k d a b t)
  | 0, d, _, _, _, ha, hb, _ => structEtaFull_rel K d hx ha hb
  | k + 1, d, a, b, t, ha, hb, ht => by
    cases t with
    | forallE dom body =>
      obtain ⟨hd, hbd⟩ := res_forall.mp ht
      have hv : Res env₁ (Expr.fvar d dom) := res_fvar.mpr hd
      exact structEtaExpand_rel hx k (d + 1) (res_app.mpr ⟨ha, hv⟩) (res_app.mpr ⟨hb, hv⟩)
        (res_open hd hbd)
    | _ => exact Rel.ok trivial

theorem structEtaCert_rel (hx : EnvExt env₁ env₂) {a b : Expr} (ha : Res env₁ a)
    (hb : Res env₁ b) :
    Rel TT (structEtaCert r₂ env₂ d a b) (structEtaCert r₁ env₁ d a b) := by
  unfold structEtaCert
  rw [etaCtorShape_ext hx ha, etaCtorPartial_ext hx ha]
  refine Rel.ite (fun _ => structEtaFull_rel K d hx ha hb) fun _ => ?_
  cases etaCtorPartial env₁ a with
  | none => exact Rel.ok trivial
  | some k =>
    dsimp only
    refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
    refine Rel.bind (K.inferIO d ha) fun ta hta => Rel.bind (K.inferIO d hb) fun tb htb => ?_
    refine Rel.bind (K.defeq d htb hta) fun v _ => ?_
    exact Rel.iteB v (fun _ => structEtaExpand_rel K hx k d ha hb hta) fun _ => Rel.ok trivial

theorem isPropType_rel {T : Expr} (hT : Res env₁ T) :
    Rel TT (isPropType r₂ d T) (isPropType r₁ d T) := by
  unfold isPropType
  refine Rel.bind (K.inferIO d hT) fun tt htt => Rel.bind (K.whnf d htt) fun w _ => ?_
  cases w with
  | sort u => exact Rel.triv
  | _ => exact Rel.ok trivial

omit d in
theorem unitLikeFields_rel {ul₂ ul₁ : Nat → Expr → CheckM Bool}
    (hul : ∀ d {e}, Res env₁ e → Rel TT (ul₂ d e) (ul₁ d e)) :
    ∀ (n d : Nat) {t : Expr}, Res env₁ t →
      Rel TT (unitLikeFields r₂ ul₂ n d t) (unitLikeFields r₁ ul₁ n d t)
  | 0, d, _, _ => Rel.ok trivial
  | n + 1, d, t, ht => by
    cases t with
    | forallE dom body =>
      obtain ⟨hd, hbd⟩ := res_forall.mp ht
      unfold unitLikeFields
      have hrest := unitLikeFields_rel hul n (d + 1) (res_open (d := d) hd hbd)
      refine Rel.bind (isPropType_rel K d hd) fun p _ => Rel.iteB p (fun _ => hrest) fun _ => ?_
      exact Rel.bind (hul d hd) fun u _ => Rel.iteB u (fun _ => hrest) fun _ => Rel.ok trivial
    | _ => exact Rel.ok trivial

theorem unitLikeStruct_rel (hx : EnvExt env₁ env₂) {ul₂ ul₁ : Nat → Expr → CheckM Bool}
    (hul : ∀ d {e}, Res env₁ e → Rel TT (ul₂ d e) (ul₁ d e)) {w : Expr} (hw : Res env₁ w) :
    Rel TT (unitLikeStruct r₂ ul₂ env₂ d w) (unitLikeStruct r₁ ul₁ env₁ d w) := by
  unfold unitLikeStruct
  rw [unitLikeShape_ext hx hw]
  cases hsh : unitLikeShape env₁ w with
  | none => exact Rel.ok trivial
  | some x =>
    obtain ⟨tele, n⟩ := x
    exact unitLikeFields_rel K hul n d (res_unitLikeShape hx hw hsh)

omit d in
theorem unitLikeLoop_rel (hx : EnvExt env₁ env₂) :
    ∀ (f d : Nat) {T : Expr}, Res env₁ T →
      Rel TT (unitLikeLoop r₂ env₂ f d T) (unitLikeLoop r₁ env₁ f d T)
  | 0, _, _, _ => Rel.ok trivial
  | f + 1, d, T, hT => by
    unfold unitLikeLoop
    refine Rel.bind (K.whnf d hT) fun w hw => ?_
    cases w with
    | forallE dom body =>
      obtain ⟨hd, hbd⟩ := res_forall.mp hw
      exact unitLikeLoop_rel hx f (d + 1) (res_open hd hbd)
    | _ =>
      exact unitLikeStruct_rel K d hx (fun d' _ he => unitLikeLoop_rel hx f d' he) hw

theorem structUnitCert_rel (hx : EnvExt env₁ env₂) {a b : Expr} (ha : Res env₁ a)
    (hb : Res env₁ b) :
    Rel TT (structUnitCert r₂ env₂ d a b) (structUnitCert r₁ env₁ d a b) := by
  unfold structUnitCert
  refine Rel.bind (K.inferIO d ha) fun ta hta => Rel.bind (K.whnf d hta) fun wta hwta => ?_
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  refine Rel.bind (unitLikeLoop_rel K hx unitLikeFuel d hwta) fun u _ => ?_
  refine Rel.iteB u (fun _ => ?_) fun _ => Rel.ok trivial
  refine Rel.bind (K.inferIO d hb) fun tb htb => Rel.bind (K.whnf d htb) fun wtb hwtb => ?_
  exact Rel.ite (fun _ => Rel.ok trivial) fun _ => K.defeq d hwta hwtb

theorem etaCert_rel (mode : CheckMode) {ty₁ body₁ b : Expr} (ht : Res env₁ ty₁)
    (hb₁ : Res env₁ body₁) (hb : Res env₁ b) :
    Rel TT (etaCert mode r₂ env₂ d ty₁ body₁ b) (etaCert mode r₁ env₁ d ty₁ body₁ b) := by
  unfold etaCert
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  refine Rel.bind (K.inferIO d hb) fun tb htb => Rel.bind (K.whnf d htb) fun w hw => ?_
  cases w with
  | forallE ty₂ cod₂ =>
    obtain ⟨ht₂, hc₂⟩ := res_forall.mp hw
    refine Rel.bind (K.defeq d ht₂ ht) fun v _ => ?_
    refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
    have ho : Res env₁ (body₁.instantiate1 (.fvar d ty₁)) := res_open ht hb₁
    have hv : Res env₁ (Expr.fvar d ty₁) := res_fvar.mpr ht
    refine Rel.bind (K.defeq (d + 1) ho (res_app.mpr ⟨hb, hv⟩)) fun v' _ => ?_
    cases v'
    · exact Rel.ok trivial
    · refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
      refine Rel.bind (K.infer (d + 1) ho) fun ti hti =>
        Rel.bind (K.defeq (d + 1) hti (res_open ht hc₂)) fun v'' _ => ?_
      exact Rel.iteB v'' (fun _ => Rel.ok trivial) fun _ => Rel.ok trivial
  | _ => exact Rel.ok trivial

theorem stuckIrrel_rel (hx : EnvExt env₁ env₂) {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (stuckIrrel r₂ env₂ d a b) (stuckIrrel r₁ env₁ d a b) := by
  unfold stuckIrrel
  refine Rel.bind (structEtaCert_rel K d hx ha hb) fun v _ => ?_
  refine Rel.iteB v (fun _ => Rel.ok trivial) fun _ => ?_
  refine Rel.bind (structEtaCert_rel K d hx hb ha) fun v' _ => ?_
  refine Rel.iteB v' (fun _ => Rel.ok trivial) fun _ => ?_
  refine Rel.bind (structUnitCert_rel K d hx ha hb) fun v'' _ => ?_
  exact Rel.iteB v'' (fun _ => Rel.ok trivial) fun _ => proofIrrel_rel K d ha hb

omit K in
theorem formerSortLoop_rel (K : KR env₁ r₂ r₁) : ∀ (n d : Nat) {e : Expr}, Res env₁ e →
    Rel TT (formerSortLoop r₂.whnf d n e) (formerSortLoop r₁.whnf d n e)
  | 0, d, e, he => by
    unfold formerSortLoop
    refine Rel.bind (K.whnf d he) fun w _ => ?_
    cases w <;> exact Rel.ok trivial
  | n + 1, d, e, he => by
    unfold formerSortLoop
    refine Rel.bind (K.whnf d he) fun w hw => ?_
    cases w with
    | forallE dom b =>
      obtain ⟨hd, hb⟩ := res_forall.mp hw
      exact formerSortLoop_rel K n (d + 1) (res_open hd hb)
    | _ => exact Rel.ok trivial

omit K d in
theorem formerNeverZeroAt_rel (K : KR env₁ r₂ r₁) {cvT : ConstantVal} {caps : IndCaps}
    {us : List Level} (hT : Res env₁ cvT.type) :
    Rel TT (formerNeverZeroAt r₂.whnf cvT caps us) (formerNeverZeroAt r₁.whnf cvT caps us) := by
  unfold formerNeverZeroAt
  split
  · exact Rel.ok trivial
  · refine Rel.bind (formerSortLoop_rel K _ 0 (res_inst _ _ hT)) fun w _ => ?_
    cases w <;> exact Rel.ok trivial

omit K d in
theorem iotaCase3At_rel (K : KR env₁ r₂ r₁) (hx : EnvExt env₁ env₂) (isK : Bool)
    {cvj : ConstantVal} (hty : Res env₁ cvj.type) (us : List Level) :
    Rel TT (iotaCase3At r₂.whnf env₂.find? isK cvj us)
      (iotaCase3At r₁.whnf env₁.find? isK cvj us) := by
  unfold iotaCase3At
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  have hfam : ctorFamily env₂.find? cvj = ctorFamily env₁.find? cvj := by
    unfold ctorFamily
    cases hfn : cvj.type.piResult.getAppFn with
    | const T us =>
      dsimp only
      rw [hx.find_of_isSome (res_head (res_piResult hty) hfn)]
    | _ => rfl
  rw [hfam]
  cases hf : ctorFamily env₁.find? cvj with
  | none => exact Rel.ok trivial
  | some fam =>
    obtain ⟨cvT, caps⟩ := fam
    have hTy : Res env₁ cvT.type := by
      unfold ctorFamily at hf
      cases hfn : cvj.type.piResult.getAppFn with
      | const T us =>
        rw [hfn] at hf
        dsimp only at hf
        cases hfT : env₁.find? T with
        | none => rw [hfT] at hf; exact nomatch hf
        | some ci =>
          rw [hfT] at hf
          cases ci with
          | indInfo cv' caps' =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, -⟩ := hf
            exact hx.facts.type hfT
          | _ => exact nomatch hf
      | _ => rw [hfn] at hf; exact nomatch hf
    dsimp only
    refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
    exact Rel.bind (formerNeverZeroAt_rel K hTy) fun _ _ => Rel.ok trivial


omit K d in
theorem familyNeverZeroAt_rel (K : KR env₁ r₂ r₁) {cvT : ConstantVal} {caps : IndCaps}
    {us : List Level} (hT : Res env₁ cvT.type) :
    Rel TT (familyNeverZeroAt r₂.whnf cvT caps us) (familyNeverZeroAt r₁.whnf cvT caps us) := by
  unfold familyNeverZeroAt
  split
  · exact Rel.ok trivial
  · exact formerNeverZeroAt_rel K hT

omit K d in
/-- The ι case split at the stored facts: the constructor's family is read at the extension as
below it. -/
theorem iotaCaseAt_rel (K : KR env₁ r₂ r₁) (hx : EnvExt env₁ env₂) (isK : Bool)
    {cvj : ConstantVal} (hty : Res env₁ cvj.type) (us : List Level) :
    Rel TT (iotaCaseAt r₂.whnf env₂.find? isK cvj us)
      (iotaCaseAt r₁.whnf env₁.find? isK cvj us) := by
  unfold iotaCaseAt
  have hfam : ctorFamily env₂.find? cvj = ctorFamily env₁.find? cvj := by
    unfold ctorFamily
    cases hfn : cvj.type.piResult.getAppFn with
    | const T us =>
      dsimp only
      rw [hx.find_of_isSome (res_head (res_piResult hty) hfn)]
    | _ => rfl
  have hnc : iotaNoCert env₂.find? isK cvj us.length = iotaNoCert env₁.find? isK cvj us.length := by
    unfold iotaNoCert; rw [hfam]
  rw [hnc]
  exact Rel.ite (fun _ => Rel.ok trivial) fun _ => iotaCase3At_rel K hx isK hty us
end Bodies

end ConLeche.Verify
