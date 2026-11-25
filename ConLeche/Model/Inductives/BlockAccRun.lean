module

import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Env.LfpAcc
public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Env.BlockLfpTup
import ConLeche.Verify.LooseBVar

public section

/-!
# Accessibility from the check's run

The producer side of (W) by accessibility: at a uniform block's
install every member constructor's field telescope is accessible along
the accessibility relation at the hole frame (`LfpDatum.accRel`), which
`LfpDatum.fitAcc_holeOp` turns into the hole fit's accessibility (at
every level, task #327), whence the operator's, (W) and monotonicity.

This file holds the pieces between the derivation's accessibility
(`memberCtorD_acc`, on the walked crest's reading) and the datum's
fields with holes (`d.absF`, the normal form's reading); the block
theorems are in `BlockAccRunCont.lean`:

* `teleAccP_of_piAccThen`: the walked fields' accessibility moves onto
  the datum's fields (they read alike at every satisfying frame, so the
  relations under them coincide), one bound per field;
* U4 on the opened normal form (`u4_nestOccAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level NestCtx NestHole ConstantVal BlockShape BlockShape)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The walked accessibility onto the datum's fields -/

/-- `TeleAccP` reads the bounds from field `l` on only. -/
theorem TeleAccP.congr {w : Nat} {Af Af' : Nat → (Nat → V) → V} :
    ∀ (Fs : List Term) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ l', l ≤ l' → l' < l + Fs.length → Af l' = Af' l') → TeleAccP w Af l Q R Fs →
        TeleAccP w Af' l Q R Fs
  | [], _, _, _, _, _ => trivial
  | F :: Fs, l, Q, R, h, ⟨h1, h2, h3, h4⟩ => by
    have hl : Af l = Af' l := h l (Nat.le_refl _) (by simp)
    refine ⟨hl ▸ h1, hl ▸ h2, h3, ?_⟩
    exact TeleAccP.congr Fs (l + 1) (shiftQ Q) (R.underBoth F)
      (fun l' hl' hl'' => h l' (by omega) (by simp at hl'' ⊢; omega)) h4

theorem shiftQ_congr {Q Q' : Nat → Nat → Prop} (h : ∀ i n, Q i n ↔ Q' i n) :
    ∀ i n, shiftQ Q i n ↔ shiftQ Q' i n
  | 0, _ => Iff.rfl
  | i + 1, n => h i n

/-- **The walked fields' accessibility moves onto the datum's fields**
(see the module docstring): one bound per field, reading only its walk
output's non-hole positions, and the walk's result fact at the relation
under the datum's fields. -/
theorem teleAccP_of_piAccThen {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {Qf : FrameRel V → Term → Prop} :
    ∀ (abD abN : List Term) (B : Term) (d l : Nat) (nds : List Expr)
      (Δ : List Term) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD) (abN) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → w ≠ 0 → FieldsBound w ρ (abN)) →
      (∀ i n, HoleQ ctx prog d i n ↔ Q i n) → ctx.hiAt prog.length ≤ d →
      PiAccThen w ctx prog Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP ctx.nP (ctx.hiAt prog.length) (d + i) nd) (Af (l + i))) ∧
        Qf (R.underBothTele (abN)) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    obtain ⟨h0, hrest⟩ := hE
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0⟩, hP'⟩ =>
      have hUE : R.underBoth x = R.underBoth y := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x σ σ₀ → w ≠ 0 →
          FieldsBound w σ (abN) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩ hw
        have hok0 := hok ρ ρ₀ hR hw
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, HoleQ ctx prog (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_holeQ hd i n]
        exact shiftQ_congr hQ i n
      obtain ⟨Af', htele', hinv', hQf⟩ :=
        teleAccP_of_piAccThen abD abN B (d + 1) (l + 1) nds' (x :: Δ) (R.underBoth x)
          (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · intro hw
          have hok0 := hok ρ ρ₀ hR hw
          exact mem_tg_of_mem_univ hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [ite_eq_right (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0.1
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [ite_eq_right (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · show Qf ((R.underBoth y).underBothTele (abN)) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

/-! ## The result indices -/

/-- **The result indices read alike** at two frames under a spine fitting
the fields at both, from the walk's result fact. -/
theorem resC_of_resultIdxConst {R : FrameRel V} {Fs : List Term} {h : Nat}
    {es : List Term}
    (hQ : ResultIdxConst (R.underBothTele Fs) (Term.mkAppN (.bvar h) es)) :
    ∀ ρ ρ', R ρ ρ' → ∀ fs, SpineFit ρ Fs fs → SpineFit ρ' Fs fs →
      ∀ e ∈ es, interp V (consList fs ρ) e = interp V (consList fs ρ') e := by
  obtain ⟨i, vs, heq, hvs⟩ := hQ
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  intro ρ ρ' hR fs hf hf' e he
  exact hvs e he _ _ (FrameRel.underBothTele_consList Fs fs hR hf hf')

/-! ## The relation at the walk's top -/

/-- **The admissible items at the walk's top are the member holes at
their full arity.** -/
theorem holeQ_top_iff {d : BlockData V} {ψ : Name → Nat} {ctx : NestCtx}
    (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k) (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0) :
    ∀ i n, HoleQ ctx [] (ctx.hiAt 0) i n ↔ d.toLfp.MemberQ ψ i n := by
  intro i n
  show _ ↔ ∃ t, t < d.k ∧ i = d.k - 1 - t ∧ n = (d.toLfp.ids t ψ).length
  constructor
  · rintro (⟨t, ht, hlt, rfl, rfl⟩ | ⟨j, hk, hj, -⟩)
    · rw [hcN] at ht
      exact ⟨t, ht, by rw [hhi, hcP]; omega, (har t ht).symm⟩
    · simp at hj
  · rintro ⟨t, ht, rfl, rfl⟩
    exact Or.inl ⟨t, by rw [hcN]; exact ht, by rw [hhi, hcP]; omega,
      by rw [hhi, hcP]; omega, har t ht⟩

private theorem defHoleFn_cons_list {r n : Nat} {g : List V → V} (hg : DefHoleFn (r + n) g) :
    ∀ (as : List V), as.length = r → DefHoleFn n fun vs => g (as ++ vs) := by
  induction r generalizing g with
  | zero =>
    intro as hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    rw [Nat.zero_add] at hg
    simpa only [List.nil_append] using hg
  | succ r ih =>
    intro as hlen
    cases as with
    | nil => simp at hlen
    | cons a as =>
      rw [Nat.succ_add] at hg
      exact ih (hg.cons a) as (by simpa using hlen)

private theorem defFun_mkTower_ofFn {k : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => Tower.mkTower (List.ofFn fun i => As i env)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [Tower.mkTower]
  | r + 1, As, hAs => by
    have hrest := defFun_mkTower_ofFn (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact (DefFun.spair_apply (hAs 0) hrest).congr fun env => by
      simp [List.ofFn_succ, Tower.mkTower]

private theorem defFun_tupW_ofFn (u : Nat) {k r : Nat}
    (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefFun k fun env => tupW u (List.ofFn fun i => As i env) := by
  by_cases hu : u = 0
  · subst hu
    exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn As hAs).congr fun _ => (tupW_pos hu _).symm

private theorem holeFam_congr_eq {Fs : List Term} {ρ ρ' : Nat → V} {g g' : List V → V}
    {hg : DefHoleFn Fs.length g} {hg' : DefHoleFn Fs.length g'}
    (hρ : ρ = ρ') (hg_eq : g = g') :
    holeFam ρ Fs g hg = holeFam ρ' Fs g' hg' := by
  subst hρ hg_eq
  rfl

private theorem defFun_holeFam_app_ofFn (u : Nat) (tail : Nat → V) :
    ∀ (Fs : List Term) {k m r : Nat}
      (Xs : Fin m → (Fin k → V) → V) (_ : ∀ i, DefFun k (Xs i))
      (Y : (Fin k → V) → V) (_ : DefFun k Y)
      (As : Fin r → (Fin k → V) → V) (_ : ∀ i, DefFun k (As i)),
      DefFun k fun env =>
        holeFam (Semantics.prepend (fun i => Xs i env) tail) Fs
          (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs)))
          (defHoleFn_cons_list (DefHoleFn.of_app_tupW (Y env) u (r + Fs.length))
            (List.ofFn fun i => As i env) List.length_ofFn)
  | [], k, m, r, Xs, hXs, Y, hY, As, hAs =>
    (DefFun.app_apply hY (defFun_tupW_ofFn u As hAs)).congr fun env => by
      rw [holeFam_nil, List.append_nil]
  | F :: Fs, k, m, r, Xs, hXs, Y, hY, As, hAs => by
    have hF : DefFun k fun env => interp V (Semantics.prepend (fun i => Xs i env) tail) F :=
      (interp_defFun_prepend tail m F).comp hXs
    let Xs' : Fin (m + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (k + 1) (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    let Y' : (Fin (k + 1) → V) → V := fun w => Y (ftail w)
    have hY' : DefFun (k + 1) Y' := hY.weaken
    let As' : Fin (r + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if hi : i.val < r then As ⟨i.val, hi⟩ (ftail w) else w 0
    have hAs' : ∀ i, DefFun (k + 1) (As' i) := fun ⟨i, hi⟩ => by
      dsimp only [As']
      split
      · exact (hAs _).weaken
      · exact DefFun.proj 0
    have hrec := defFun_holeFam_app_ofFn u tail Fs Xs' hXs' Y' hY' As' hAs'
    let hg_all : ∀ env, DefHoleFn (F :: Fs).length
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs))) := fun env =>
      defHoleFn_cons_list (DefHoleFn.of_app_tupW (Y env) u (r + (F :: Fs).length))
        (List.ofFn fun i => As i env) List.length_ofFn
    let F_lam : V → (Fin k → V) → V := fun x env =>
      holeFam (cons x (Semantics.prepend (fun i => Xs i env) tail)) Fs
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ x :: vs)))
        ((hg_all env).cons x)
    have hrec' : DefFun (k + 1) fun w => F_lam (w 0) (ftail w) := by
      refine hrec.congr fun w => ?_
      have hρ : Semantics.prepend (fun i => Xs' i w) tail =
          cons (w 0) (Semantics.prepend (fun i => Xs i (ftail w)) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs']
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      have hA_eq : List.ofFn (fun i => As' i w) =
          List.ofFn (fun i => As i (ftail w)) ++ [w 0] := by
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, As']
        by_cases hj : j < r
        · simp [hj, List.getElem_append_left]
        · have hjr : j = r := by omega
          subst hjr
          simp [List.getElem_append_right]
      have h_fn : (fun vs => app (Y' w) (tupW u (List.ofFn (fun i => As' i w) ++ vs))) =
          (fun vs => app (Y (ftail w)) (tupW u (List.ofFn (fun i => As i (ftail w)) ++ w 0 :: vs))) := by
        funext vs
        change app (Y (ftail w)) (tupW u (List.ofFn (fun i => As' i w) ++ vs)) = _
        rw [hA_eq, List.append_assoc, List.singleton_append]
      exact holeFam_congr_eq hρ h_fn
    have hGraph : ∀ env, HasGraph (interp V (Semantics.prepend (fun i => Xs i env) tail) F)
        (fun x => F_lam x env) := fun env =>
      holeFam_hasGraph (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)
    refine (DefFun.lamV_apply_curry (F := F_lam) (h := hGraph) hrec' hF).congr fun env => ?_
    exact (holeFam_cons (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)).symm

/-- **The accessibility relation at the hole frame is an accessibility
hole relation of the walk's context**: its frames satisfy the context,
agree off the member holes, are first-order finite-support definable,
`pt`-stable, and at a `Type`-valued block its member holes are rich. -/
theorem holeRelA_accRel {d : BlockData V} {ψ : Name → Nat} {ρp : Nat → V} {ctx : NestCtx}
    (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k)
    (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0)
    {Δa : List Term}
    (hsat : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      Sat V Δa (d.toLfp.frame ψ ρp X)) :
    HoleRelA m ψ (d.w ψ) ctx [] (ctx.hiAt 0) Δa (d.toLfp.accRel ψ ρp) where
  dom := by
    rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩
    exact ⟨hsat X hX, hsat Y hY⟩
  agree := by
    intro σ σ' hr i hi
    refine LfpDatum.accRel_agreeOff hr i ?_
    show d.k ≤ i
    refine Nat.le_of_not_lt fun hlt => hi ?_
    simp only [holeP, List.length_nil, hhi, hcP]
    omega
  dsScoped := fun _ _ h => by simp at h
  symm := LfpDatum.accRel_symm
  ptFree hw := PtFreeOn.congrQ (fun i n => (holeQ_top_iff hhi hcN hcP har i n).symm)
    (LfpDatum.accRel_ptFree (Nat.le_add_right _ _) hw)
  lrefl := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    exact LfpDatum.accRel_refl hX
  defRel := by
    have hk_eq : d.toLfp.k = d.k := rfl
    have hdk : d.toLfp.k ≤ ctx.hiAt 0 := by rw [hk_eq, hhi]; exact Nat.le_add_left _ _
    refine ⟨fun σ σ' hr j hj => LfpDatum.accRel_agreeOff hr j (Nat.le_trans hdk hj), fun tail => ?_⟩
    by_cases htail : ∀ j, ctx.hiAt 0 ≤ j → tail (j - ctx.hiAt 0) = ρp (j - d.toLfp.k)
    · have hSide : ∀ (slot : Fin d.toLfp.k → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V)
          (_ : ∀ t, DefFun (ctx.hiAt 0 + ctx.hiAt 0) (slot t))
          (pslot : Fin (ctx.hiAt 0) → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V)
          (_ : ∀ j, DefFun (ctx.hiAt 0 + ctx.hiAt 0) (pslot j)),
          DefRel (ctx.hiAt 0 + ctx.hiAt 0) fun v =>
            (∀ t : Fin d.toLfp.k, ∃ y : V,
              y ∈ˢ famSpace (d.toLfp.w ψ) (d.toLfp.idx ψ ρp t.val) ∧
              slot t v = d.toLfp.holeVal ψ ρp (fun _ => y) t.val) ∧
            (∀ j : Fin (ctx.hiAt 0), d.toLfp.k ≤ j.val → pslot j v = ρp (j.val - d.toLfp.k)) := by
        intro slot hslot pslot hpslot
        refine DefRel.and (DefRel.finForall fun t : Fin d.toLfp.k => ?_)
          (DefRel.finForall fun j : Fin (ctx.hiAt 0) => ?_)
        · refine DefRel.exists_curry (DefRel.and ?_ ?_)
          · exact DefRel.mem_apply (DefFun.proj 0)
              (DefFun.const (famSpace (d.toLfp.w ψ) (d.toLfp.idx ψ ρp t.val)))
          · have h_hole : DefFun ((ctx.hiAt 0 + ctx.hiAt 0) + 1) fun w =>
                d.toLfp.holeVal ψ ρp (fun _ => w 0) t.val := by
              have hb := defFun_holeFam_app_ofFn (d.toLfp.u t.val ψ) ρp (d.toLfp.ids t.val ψ)
                Fin.elim0 (fun i => Fin.elim0 i)
                (fun w : Fin ((ctx.hiAt 0 + ctx.hiAt 0) + 1) → V => w 0) (DefFun.proj 0)
                Fin.elim0 (fun i => Fin.elim0 i)
              refine hb.congr fun w => ?_
              unfold LfpDatum.holeVal
              refine holeFam_congr_eq (funext fun x => by simp [Semantics.prepend, Nat.not_lt_zero])
                (funext fun vs => by simp)
            exact (DefRel.eq_apply (hslot t).weaken h_hole).congr fun _ => Iff.rfl
        · by_cases hjk : d.toLfp.k ≤ j.val
          · exact (DefRel.eq_apply (hpslot j) (DefFun.const (ρp (j.val - d.toLfp.k)))).congr fun _ =>
              ⟨fun h _ => h, fun h => h hjk⟩
          · exact DefRel.true.congr fun _ =>
              ⟨fun _ h => absurd h hjk, fun _ => trivial⟩
      let slotL : Fin d.toLfp.k → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V :=
        fun t v => v ⟨d.toLfp.k - 1 - t.val, by omega⟩
      let slotR : Fin d.toLfp.k → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V :=
        fun t v => v ⟨ctx.hiAt 0 + (d.toLfp.k - 1 - t.val), by omega⟩
      let pslotL : Fin (ctx.hiAt 0) → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V :=
        fun j v => v ⟨j.val, by omega⟩
      let pslotR : Fin (ctx.hiAt 0) → (Fin (ctx.hiAt 0 + ctx.hiAt 0) → V) → V :=
        fun j v => v ⟨ctx.hiAt 0 + j.val, by omega⟩
      have hL := hSide slotL (fun _ => DefFun.proj _) pslotL (fun _ => DefFun.proj _)
      have hR := hSide slotR (fun _ => DefFun.proj _) pslotR (fun _ => DefFun.proj _)
      refine (DefRel.and hL hR).congr fun v => ?_
      have h_holeVal_pt : ∀ (Y : Nat → V) (mm : Nat),
          d.toLfp.holeVal ψ ρp Y mm = d.toLfp.holeVal ψ ρp (fun _ => Y mm) mm := fun _ _ => rfl
      constructor
      · rintro ⟨⟨hYL, hPL⟩, ⟨hYR, hPR⟩⟩
        let X : Nat → V := fun mm =>
          if hmm : mm < d.toLfp.k then Classical.choose (hYL ⟨mm, hmm⟩)
          else AccIter.emptyTup (d.toLfp.idx ψ ρp) mm
        let Y : Nat → V := fun mm =>
          if hmm : mm < d.toLfp.k then Classical.choose (hYR ⟨mm, hmm⟩)
          else AccIter.emptyTup (d.toLfp.idx ψ ρp) mm
        have hX : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X := by
          intro mm hmm
          dsimp only [X]
          split
          · next hmk => exact (Classical.choose_spec (hYL ⟨mm, hmk⟩)).1
          · exact AccIter.emptyTup_mem (w := d.toLfp.w ψ) (k := d.toLfp.N) (Is := d.toLfp.idx ψ ρp) mm hmm
        have hY : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) Y := by
          intro mm hmm
          dsimp only [Y]
          split
          · next hmk => exact (Classical.choose_spec (hYR ⟨mm, hmk⟩)).1
          · exact AccIter.emptyTup_mem (w := d.toLfp.w ψ) (k := d.toLfp.N) (Is := d.toLfp.idx ψ ρp) mm hmm
        refine ⟨X, Y, hX, hY, ?_, ?_⟩
        · funext i
          by_cases hik : i < d.toLfp.k
          · let t : Fin d.toLfp.k := ⟨d.toLfp.k - 1 - i, by omega⟩
            have hti : d.toLfp.k - 1 - t.val = i := by dsimp [t]; omega
            have hih : i < ctx.hiAt 0 := by omega
            simp only [Semantics.prepend, hih, ↓reduceDIte, ftake]
            have h_fin : (⟨d.toLfp.k - 1 - t.val, by omega⟩ : Fin (ctx.hiAt 0 + ctx.hiAt 0)) =
                ⟨i, by omega⟩ := Fin.ext hti
            have hspec : v ⟨i, by omega⟩ =
                d.toLfp.holeVal ψ ρp (fun _ => Classical.choose (hYL t)) t.val := by
              rw [← h_fin]
              exact (Classical.choose_spec (hYL t)).2
            rw [hspec, show i = d.toLfp.k - 1 - t.val by omega, LfpDatum.frame_hole t.isLt]
            have hXt : X t.val = Classical.choose (hYL t) := by
              dsimp only [X]; simp [t.isLt]
            rw [h_holeVal_pt X t.val, hXt]
          · have hge : d.toLfp.k ≤ i := by omega
            obtain ⟨m', rfl⟩ : ∃ m', i = m' + d.toLfp.k := ⟨i - d.toLfp.k, by omega⟩
            rw [LfpDatum.frame_param]
            by_cases hmi : m' + d.toLfp.k < ctx.hiAt 0
            · simp only [Semantics.prepend, hmi, ↓reduceDIte, ftake]
              simpa [pslotL, show m' + d.toLfp.k - d.toLfp.k = m' by omega] using hPL ⟨m' + d.toLfp.k, hmi⟩ hge
            · simp only [Semantics.prepend, hmi, ↓reduceDIte]
              simpa [show m' + d.toLfp.k - d.toLfp.k = m' by omega] using htail (m' + d.toLfp.k) (by omega)
        · funext i
          by_cases hik : i < d.toLfp.k
          · let t : Fin d.toLfp.k := ⟨d.toLfp.k - 1 - i, by omega⟩
            have hti : d.toLfp.k - 1 - t.val = i := by dsimp [t]; omega
            have hih : i < ctx.hiAt 0 := by omega
            simp only [Semantics.prepend, hih, ↓reduceDIte, fdrop]
            have h_fin : (⟨ctx.hiAt 0 + (d.toLfp.k - 1 - t.val), by omega⟩ : Fin (ctx.hiAt 0 + ctx.hiAt 0)) =
                ⟨ctx.hiAt 0 + i, by omega⟩ := Fin.ext (congrArg (ctx.hiAt 0 + ·) hti)
            have hspec : v ⟨ctx.hiAt 0 + i, by omega⟩ =
                d.toLfp.holeVal ψ ρp (fun _ => Classical.choose (hYR t)) t.val := by
              rw [← h_fin]
              exact (Classical.choose_spec (hYR t)).2
            rw [hspec, show i = d.toLfp.k - 1 - t.val by omega, LfpDatum.frame_hole t.isLt]
            have hYt : Y t.val = Classical.choose (hYR t) := by
              dsimp only [Y]; simp [t.isLt]
            rw [h_holeVal_pt Y t.val, hYt]
          · have hge : d.toLfp.k ≤ i := by omega
            obtain ⟨m', rfl⟩ : ∃ m', i = m' + d.toLfp.k := ⟨i - d.toLfp.k, by omega⟩
            rw [LfpDatum.frame_param]
            by_cases hmi : m' + d.toLfp.k < ctx.hiAt 0
            · simp only [Semantics.prepend, hmi, ↓reduceDIte, fdrop]
              simpa [pslotR, show m' + d.toLfp.k - d.toLfp.k = m' by omega] using hPR ⟨m' + d.toLfp.k, hmi⟩ hge
            · simp only [Semantics.prepend, hmi, ↓reduceDIte]
              simpa [show m' + d.toLfp.k - d.toLfp.k = m' by omega] using htail (m' + d.toLfp.k) (by omega)
      · rintro ⟨X, Y, hX, hY, h1, h2⟩
        have htN : ∀ t : Fin d.toLfp.k, t.val < d.toLfp.N := fun t =>
          Nat.lt_of_lt_of_le t.isLt (Nat.le_add_right _ _)
        refine ⟨⟨fun t => ?_, fun j hjk => ?_⟩, ⟨fun t => ?_, fun j hjk => ?_⟩⟩
        · refine ⟨X t.val, hX t.val (htN t), ?_⟩
          have hpos := congrFun h1 (d.toLfp.k - 1 - t.val)
          have hlt : d.toLfp.k - 1 - t.val < ctx.hiAt 0 := by omega
          simp only [Semantics.prepend, hlt, ↓reduceDIte, ftake] at hpos
          dsimp only [slotL]
          rw [hpos, LfpDatum.frame_hole t.isLt, h_holeVal_pt]
        · have hpos := congrFun h1 j.val
          simp only [Semantics.prepend, j.isLt, ↓reduceDIte, ftake] at hpos
          dsimp only [pslotL]
          rw [hpos, show j.val = (j.val - d.toLfp.k) + d.toLfp.k by omega, LfpDatum.frame_param]
          simp [show j.val - d.toLfp.k + d.toLfp.k - d.toLfp.k = j.val - d.toLfp.k by omega]
        · refine ⟨Y t.val, hY t.val (htN t), ?_⟩
          have hpos := congrFun h2 (d.toLfp.k - 1 - t.val)
          have hlt : d.toLfp.k - 1 - t.val < ctx.hiAt 0 := by omega
          simp only [Semantics.prepend, hlt, ↓reduceDIte, fdrop] at hpos
          dsimp only [slotR]
          rw [hpos, LfpDatum.frame_hole t.isLt, h_holeVal_pt]
        · have hpos := congrFun h2 j.val
          simp only [Semantics.prepend, j.isLt, ↓reduceDIte, fdrop] at hpos
          dsimp only [pslotR]
          rw [hpos, show j.val = (j.val - d.toLfp.k) + d.toLfp.k by omega, LfpDatum.frame_param]
          simp [show j.val - d.toLfp.k + d.toLfp.k - d.toLfp.k = j.val - d.toLfp.k by omega]
    · refine DefRel.false.congr fun _ => ⟨False.elim, ?_⟩
      rintro ⟨X, -, -, -, h1, -⟩
      apply htail
      intro j hj
      have hpos := congrFun h1 j
      have hnj : ¬ j < ctx.hiAt 0 := by omega
      simp only [Semantics.prepend, hnj, ↓reduceDIte] at hpos
      rw [hpos, show j = (j - d.toLfp.k) + d.toLfp.k by omega, LfpDatum.frame_param]
      simp [show j - d.toLfp.k + d.toLfp.k - d.toLfp.k = j - d.toLfp.k by omega]
  ptHit := FrameRel.PtHitStable.congrQ (fun i n => (holeQ_top_iff hhi hcN hcP har i n).symm)
    (LfpDatum.accRel_ptHitStable (Nat.le_add_right _ _))

/-! ## U4 on the normal form (syntactic) -/

section Syntax

open ConLeche (openPisAtFvars structUsedLater)

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses — at any base depth. -/
theorem u4_nestOccAt {b nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (b) = some (xs, rest))
    (hW : Expr.WScoped (b) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (b + j) (b + j + 1) = false := by
  obtain ⟨⟨bs, r⟩, hst⟩ := Option.isSome_iff_exists.mp
    (stripPis_of_openPis nF hop (j + 1) (by omega))
  have hfree : r.hasLooseBVar 0 = false := by
    unfold structUsedLater at hU
    rw [Nat.zero_add, hst] at hU
    simpa [Expr.hasLooseBVarB_eq] using hU
  obtain ⟨h1, -⟩ := openPisAtFvars_leaf_free nF j hop hj hst hfree fun z hz => by
    have := Expr.fvarLeaves_lt_of_wscoped hW z hz
    omega
  refine nestOcc_nil_of_leaves _ fun z hz => ?_
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF tyN (b) hop l x hx
  exact h1 l hjl _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses. -/
theorem u4_nestOcc {ctx : NestCtx} {nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1) = false :=
  u4_nestOccAt hop hW hU hj hjl hx

end Syntax

/-- NoBVar of a disjunction. -/
theorem noBVar_or {P₁ P₂ : Nat → Prop} {e : Term} (h₁ : NoBVar P₁ e) (h₂ : NoBVar P₂ e) :
    NoBVar (fun i => P₁ i ∨ P₂ i) e := by
  have := noBVar_exists' (α := Bool) (P := fun b i => if b then P₁ i else P₂ i) (e := e)
    fun b => by cases b <;> simpa
  refine NoBVar.mono (fun i hi => ?_) this
  rcases hi with h | h
  · exact ⟨true, by simpa using h⟩
  · exact ⟨false, by simpa using h⟩

end ConLeche.Model
