module

import ConLeche.Model.Claims
import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Model.IndPinGrade
public import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# Block library: the constructor's stage and the recursor's frame kit

The constructor's peel, frames and spine kit; the recursor's frame kit;
λ-towers folding to their body; the recursor rule's kit.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The constructor's peel -/


open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
@[expose] def paramBvars (nP nF : Nat) : List Term :=
  (List.range nP).map fun k => Term.bvar (nP + nF - 1 - k)

omit [SetTheory V] in
theorem consList_range_reverse :
    ∀ (n : Nat) (ρ : Nat → V),
      consList ((List.range n).reverse.map ρ) (fun j => ρ (j + n)) = ρ := by
  intro n
  induction n with
  | zero => intro ρ; funext j; simp
  | succ n ih =>
    intro ρ
    rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have hcons : cons (ρ n) (fun j => ρ (j + (n + 1))) = fun j => ρ (j + n) := by
      funext j
      cases j with
      | zero => rw [cons_zero, Nat.zero_add]
      | succ j => rw [cons_succ]; congr 1; omega
    rw [hcons]
    exact ih ρ

/-- The prefix and suffix of a peeled binder list, as the reversed
context's parts. -/
theorem reverse_map_take_drop (ds : List Term) (nP : Nat) :
    ds.reverse = (ds.drop nP).reverse ++ (ds.take nP).reverse := by
  rw [← List.reverse_append, List.take_append_drop]


/-!
## The constructor's frames

The opened record at a known peel, the field and parameter parts of
the reversed constructor context, and the field chain's universe bound
(`FieldsBound`), walked like its grading (`fieldsOkB_of_frame`).
-/


/-- An opened type whose reading is a known peel: the opened record
at the peel's reversed domains. -/
theorem opened_of_peel {m : EnvModel V env} {k : Nat} {e : Expr}
    {fvs : List Expr} {o : Expr} {pps : List Term} {b : Term}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (hread : denote m.acval env φ 0 e = some (mkPisAV pps b))
    (hlen : pps.length = k)
    (hok : ∀ ρ : Nat → V, WellDenoted V ρ (mkPisAV pps b)) :
    Opened m φ k e fvs o pps.reverse b := by
  obtain ⟨Γ, R, htele, hO⟩ := opened_of hop hcl hb hread hok
  have hst := stripPisAV_mkPisAV pps b
  rw [hlen] at hst
  obtain ⟨rfl, rfl⟩ := PiTeleAV.unique htele (piTeleAV_of_stripPisAV hst)
  exact hO

/-- The field entries of the reversed constructor context are the
peel's field domains. -/
theorem fieldsFrom_eq_drop {ds : List Term} {nP nF : Nat}
    (hlen : ds.length = nP + nF) :
    fieldsFrom ds.reverse (nP + nF) nP nF 0
      = ds.drop nP := by
  apply List.ext_getElem
  · simp [fieldsFrom, hlen]
  · intro t h1 h2
    simp only [fieldsFrom, List.getElem_map, List.getElem_range, List.getElem_drop]
    have ht : t < nF := by simpa [fieldsFrom] using h1
    rw [Nat.add_zero, getD_reverse_of_peel hlen (by omega)
      (List.getElem?_eq_getElem (by omega))]

/-- The reversed constructor context above the fields is the reversed
parameter context. -/
theorem drop_fields_eq {ds : List Term} {nP nF : Nat}
    (hlen : ds.length = nP + nF) (i : Nat) (hi : i ≤ nP) :
    ds.reverse.drop (nP + nF - i)
      = (ds.take nP).reverse.drop (nP - i) := by
  rw [reverse_map_take_drop ds nP, List.drop_append]
  have hl : (ds.drop nP).reverse.length = nF := by
    simp [hlen]
  rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, hl,
    show nP + nF - i - nF = nP - i from by omega]

/-- The field chain's universe bound, walked like its grading. -/
theorem fieldsBound_of_frame {Γ : List Term} {k nP nF w : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ w : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound w ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound w ρ (fieldsFrom Γ k nP nF j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    refine ⟨hbnd j hlt ρ hρ, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha


/-! ## Spines under a consed frame, and fits across equivalent contexts -/

omit [SetTheory V] in
theorem consN_eq_consList : ∀ (ts : List V) (ρ : Nat → V), consN ts ρ = consList ts ρ
  | [], _ => rfl
  | t :: ts, ρ => consN_eq_consList ts (cons t ρ)

omit [SetTheory V] in
/-- The reversed range under a consed spine recovers the spine. -/
theorem range_reverse_map_consList :
    ∀ (as : List V) (ρ : Nat → V),
      (List.range as.length).reverse.map (consList as ρ) = as
  | [], _ => rfl
  | a :: as, ρ => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have h0 : consList as (cons a ρ) as.length = a := by
      have := consList_apply_add as (cons a ρ) 0
      rw [Nat.zero_add] at this
      rw [this]; rfl
    rw [h0, range_reverse_map_consList as (cons a ρ)]

/-- Two domain lists whose reversed contexts have the same satisfying
valuations fit the same spines. -/
theorem spineFit_iff_of_sat_iff {Ds₁ Ds₂ : List Term}
    (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat V Ds₁.reverse ρ ↔ Sat V Ds₂.reverse ρ)
    (ρ : Nat → V) (as : List V) (hl : as.length = Ds₁.length) :
    SpineFit ρ Ds₁ as ↔ SpineFit ρ Ds₂ as := by
  have key : ∀ (Ds₁ Ds₂ : List Term), Ds₁.length = Ds₂.length →
      (∀ ρ : Nat → V, Sat V Ds₁.reverse ρ → Sat V Ds₂.reverse ρ) →
      ∀ (ρ : Nat → V) (as : List V), as.length = Ds₁.length →
      SpineFit ρ Ds₁ as → SpineFit ρ Ds₂ as := by
    intro Ds₁ Ds₂ hlen hsat ρ as hl h
    have h1 := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) h
    rw [List.append_nil] at h1
    have h2 := spineFit_of_sat (Δ₀ := []) (Ds := Ds₂)
      (by rw [List.append_nil]; exact hsat _ h1)
    have e1 : (fun j => consList as ρ (j + Ds₂.length)) = ρ := by
      funext j; rw [← hlen, ← hl, consList_apply_add]
    have e2 : ((List.range Ds₂.length).reverse.map (consList as ρ)) = as := by
      rw [← hlen, ← hl]; exact range_reverse_map_consList as ρ
    rw [e1, e2] at h2
    exact h2
  exact ⟨key Ds₁ Ds₂ hlen (fun ρ => (hiff ρ).mp) ρ as hl,
    key Ds₂ Ds₁ hlen.symm (fun ρ => (hiff ρ).mpr) ρ as (by rw [hl, hlen])⟩

/-- The reversed constructor context's parameter entries are the
reversed parameter context's. -/
theorem getD_reverse_take {ds : List Term} {nP nF : Nat}
    (hlen : ds.length = nP + nF) {i : Nat} (hi : i < nP) :
    ds.reverse.getD (nP + nF - 1 - i) default
      = (ds.take nP).reverse.getD (nP - 1 - i) default := by
  have hil : i < ds.length := by omega
  rw [getD_reverse_of_peel hlen (by omega) (List.getElem?_eq_getElem hil),
    getD_reverse_of_peel (List.length_take_of_le (by omega)) hi
      (by rw [List.getElem?_take_of_lt hi]; exact List.getElem?_eq_getElem hil)]


/-!
## The recursor's frame kit

Lifted Π-towers (`liftN_mkPisAV`: the tower of lifted domains), fits at
frames agreeing below the cut, and the parameter variables seen from
any depth above the parameters (`paramBvarsAt`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
 )


/-! ## Lifted Π-towers -/

theorem stripPisAV_mkPisAV_take
    (n : Nat) (ds : List Term) (b : Term) (h : n ≤ ds.length) :
    stripPisAV n (mkPisAV ds b) = some (ds.take n, mkPisAV (ds.drop n) b) := by
  have happ : ∀ (l₁ l₂ : List Term),
      mkPisAV (l₁ ++ l₂) b = mkPisAV l₁ (mkPisAV l₂ b) := by
    intro l₁ l₂
    induction l₁ with
    | nil => rfl
    | cons d l₁ ih => simp only [List.cons_append, mkPisAV, ih]
  have hst := stripPisAV_mkPisAV (ds.take n) (mkPisAV (ds.drop n) b)
  rw [← happ, List.take_append_drop, List.length_take, Nat.min_eq_left h] at hst
  exact hst

/-! ## Graded applications along a fit -/

/-- A fit of bounded domains reads the same at any frame agreeing
below the cut. -/
theorem spineFit_congr_below :
    ∀ {pds : List Term} {k : Nat} {ρ ρ' : Nat → V} {as : List V},
      DomsBelow k pds → (∀ i, i < k → ρ i = ρ' i) →
      SpineFit ρ pds as → SpineFit ρ' pds as
  | [], _, _, _, [], _, _, h => h
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | d :: pds, k, ρ, ρ', a :: as, hb, hρ, h => by
    simp only [SpineFit] at h ⊢
    refine ⟨?_, spineFit_congr_below hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp_congr_below V d k ρ ρ' hb.1 hρ]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hρ i (by omega)

/-! ## The family spine above the parameters -/

/-- The parameter variables as seen from depth `D` (`D ≥ nP`). -/
@[expose] def paramBvarsAt (nP D : Nat) : List Term :=
  (List.range nP).map fun k => .bvar (D - 1 - k)

theorem paramBvars_eq_paramBvarsAt (nP nF : Nat) :
    paramBvars nP nF = paramBvarsAt nP (nP + nF) := rfl

/-- A same-index `fvar` spine reads to the parameter variables. -/
theorem denoteSpine_fvars {acval : Name → (Name → Nat) → Term} (D : Nat) :
    ∀ (fvs : List Expr) (k₀ : Nat),
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (k₀ + k) ty) →
      DenoteSpine acval env φ D fvs
        ((List.range fvs.length).map fun k => .bvar (D - 1 - (k₀ + k)))
  | [], _, _ => .nil
  | x :: fvs, k₀, hidx => by
    obtain ⟨nm, ty, rfl⟩ := hidx 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denote_fvar, Nat.add_zero]) ?_
    have := denoteSpine_fvars (acval := acval) D fvs (k₀ + 1)
      (fun k y hy => by
        obtain ⟨ty', h⟩ := hidx (k + 1) y (by simpa using hy)
        exact ⟨ty', by rw [h]; congr 1; omega⟩)
    have hmapeq : (List.map ((fun k => Term.bvar (D - 1 - (k₀ + k))) ∘ Nat.succ)
          (List.range fvs.length))
        = (List.range fvs.length).map fun k => Term.bvar (D - 1 - (k₀ + 1 + k)) := by
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_def]
      congr 1
      omega
    rw [hmapeq]
    exact this

theorem map_paramBvarsAt_interp {nP e : Nat} {ρp σ : Nat → V}
    (hσ : ∀ j, σ (j + e) = ρp j) :
    (paramBvarsAt nP (nP + e)).map (interp V σ) = (List.range nP).reverse.map ρp := by
  apply List.ext_getElem
  · simp [paramBvarsAt]
  · intro i h1 h2
    simp only [paramBvarsAt, List.getElem_map, List.getElem_range, interp_bvar,
      List.getElem_reverse, List.length_range]
    rw [← hσ]
    congr 1
    have : i < nP := by simpa [paramBvarsAt] using h1
    omega

/-!
## The recursor's frame kit, continued

Openings at any depth, per-index scoping of an opening's variables,
frame shifts under a consed spine, list arithmetic, lifted domains.
-/


variable {V : Type w} [SetTheory V]

/-! ## Openings at any depth -/

theorem openPisAtFvars_of_stripPis_isSome :
    ∀ (n : Nat) {e : Expr} (d : Nat), (Expr.stripPis n e).isSome = true →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, e, _, _ => ⟨[], e, rfl⟩
  | n + 1, e, d, h => by
    match e, h with
    | .forallE dom body, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      obtain ⟨fvs, o, ho⟩ := openPisAtFvars_of_stripPis_isSome n (d + 1)
        (Expr.stripPis_instantiate1_isSome (v := .fvar d dom) n 0 h)
      exact ⟨.fvar d dom :: fvs, o, by simp only [openPisAtFvars, ho]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-! ## Per-index scoping -/

/-- Each opened variable's annotation is scoped at its own depth. -/
theorem openPisAtFvars_typeWScoped :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → Expr.WScoped d e →
      ∀ (i : Nat) (x : Expr), fvs[i]? = some x → Expr.WScoped (d + i) (Expr.fvarTypeD x)
  | 0, _, _, _, _, hop, _, i, x, hx => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, e, d, fvs, o, hop, hw, i, x, hx => by
    match e, hop with
    | .forallE dom body, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hw' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
          simpa only [Expr.WScoped] using hw
        cases i with
        | zero =>
          obtain rfl : Expr.fvar d dom = x := by simpa using hx
          show Expr.WScoped (d + 0) dom
          rw [Nat.add_zero]; exact hw'.1
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          have hb : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d dom)) :=
            Expr.WScoped.instantiate1_gen (v := .fvar d dom) (d := d + 1)
              (by simp only [Expr.WScoped]; exact ⟨by omega, hw'.1⟩) 0
              (Expr.WScoped.mono (by omega) hw'.2)
          have := openPisAtFvars_typeWScoped n hop' hb i x hx
          rw [show d + (i + 1) = d + 1 + i from by omega]
          exact this
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _, hop | .sort _, hop | .const _ _, hop | .app _ _, hop
    | .lam _ _, hop | .letE _ _ _, hop | .lit _, hop | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-! ## Frame shifts under a consed spine -/

/-! ## List arithmetic -/

theorem mkPisAV_append :
    ∀ (l₁ l₂ : List Term) (b : Term),
      mkPisAV (l₁ ++ l₂) b = mkPisAV l₁ (mkPisAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkPisAV, mkPisAV_append l₁ l₂ b]

/-! ## Lifted domains, field spines, and frame arithmetic -/

omit [SetTheory V] in
/-- A consed spine's entries below its length are the spine's, from the
top. -/
theorem consList_apply_lt :
    ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
      consList as σ k = (as[as.length - 1 - k]?).getD (σ 0)
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with h | h
    · rw [consList_apply_lt as (cons a σ) k h, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega), Option.getD_some,
        Option.getD_some]
    · obtain rfl : k = as.length := by simp at hk; omega
      have := consList_apply_add as (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, List.length_cons, show as.length + 1 - 1 - as.length = 0 from by omega,
        List.getElem?_cons_zero, Option.getD_some, cons_zero]


/-! ## Recursor-reading kit: opening variables, the constructor residual -/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  PropWhen)


variable {acval : Name → (Name → Nat) → Term}

/-! ## Syntactic bookkeeping -/

/-- The variables of an opening at any depth: one per binder, indexed
by position from the depth, closed. -/
theorem opening_vars_at {n d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o)) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (d + k) ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) :=
  ⟨openPisAtFvars_length n hop, openPisAtFvars_index n e d hop, fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e d hop q a hq
    rfl⟩

/-! ## The constructor telescope's residual -/

/-!
## λ-towers fold to their body

A **graded** λ-tower applied along a fitting spine computes its body
at the spine's frame: each layer steps by β on the domain (`app_lamV`).
This is what lets the recursor rule's law read the rule's right-hand
side with no correspondence between the rule's λ-tower and the
recursor's elimination level.
-/


/-- **A graded λ-tower folds to its body** along any fitting spine. -/
theorem mkLamsAV_fold_graded :
    ∀ {lds : List Term} {b : Term} {ρ : Nat → V} {as : List V},
      WellDenoted V ρ (mkLamsAV lds b) → SpineFit ρ lds as →
      as.foldl SetTheory.app (interp V ρ (mkLamsAV lds b))
        = interp V (consList as ρ) b
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, hsp => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp => by
    have hok' := hok
    simp only [mkLamsAV, WellDenoted_lam] at hok'
    obtain ⟨-, -, hrest, -⟩ := hok'
    rw [consList_cons, List.foldl_cons]
    simp only [mkLamsAV, interp_lam]
    rw [app_lamV hsp.1]
    exact mkLamsAV_fold_graded (hrest a hsp.1) hsp.2

/-- **A graded λ-tower applied along a fitting spine is graded**: each
step's Π-package is the layer's own (`lamV_mem` over the grading's
fibre family), or — once a layer has collapsed the value to the
point — the trivial one. -/
theorem mkAppN_wellDenoted_of_lam :
    ∀ {lds : List Term} {b f : Term} {args : List Term} {ρ σ : Nat → V},
      WellDenoted V ρ f → (∀ a ∈ args, WellDenoted V ρ a) →
      WellDenoted V σ (mkLamsAV lds b) →
      (interp V ρ f = (pt : V) ∨ interp V ρ f = interp V σ (mkLamsAV lds b)) →
      SpineFit σ lds (args.map (interp V ρ)) →
      WellDenoted V ρ (Term.mkAppN f args)
  | [], _, _, [], _, _, hf, _, _, _, _ => hf
  | [], _, _, _ :: _, _, _, _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, hf, _, _, _, _ => hf
  | d :: lds, b, f, a :: args, ρ, σ, hf, hargs, hok, hval, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, WellDenoted_lam] at hok'
    obtain ⟨-, hAty, hrest, B, hB, hBty⟩ := hok'
    have ha := hargs a List.mem_cons_self
    rw [Term.mkAppN_cons]
    -- the application's package
    have hokApp : WellDenoted V ρ (.app f a) := by
      rw [WellDenoted_app]
      rcases hval with hpt | heq
      · exact ⟨hf, ha, 0, interp V σ d, fun _ => unitSet,
          by rw [hpt, piR_zero]; exact pt_mem_truthVal fun x _ => ⟨pt, pt_mem_unitSet⟩,
          hsp.1, fun _ _ _ => mem_univZero.mpr (Subset.refl _), fun h => absurd rfl h⟩
      · refine ⟨hf, ha, propN (interp V σ d) B, interp V σ d, B, ?_, hsp.1,
          propN_eq_zero.mp, fun _ => hAty⟩
        rw [heq]
        simp only [mkLamsAV, interp_lam]
        exact lamV_mem hB hBty
    refine mkAppN_wellDenoted_of_lam hokApp (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))
      (hrest _ hsp.1) ?_ hsp.2
    -- the continuation's value
    rw [interp_app]
    rcases hval with hpt | heq
    · left; rw [hpt, app_pt]
    · rw [heq]
      simp only [mkLamsAV, interp_lam]
      right; rw [app_lamV hsp.1]


/-!
## The recursor rule's kit

Pieces of the recursor rule's law: a `TeleFitPA` fit's chain
memberships as a `SpineFit`, and the constructor's level assignment
agreeing with the recursor's on the block's parameters.
-/


/-! ## Fits as spines -/

/-- A fit's chain memberships are a `SpineFit` (the values read at the
fit's own frame `ρ`, the domains walked from `σ`). -/
theorem spineFit_of_chain' :
    ∀ {Ds : List Term} {ws : List Term} {σ ρ : Nat → V},
      ws.length = Ds.length →
      (∀ n, n < Ds.length →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (consN ((ws.take n).map (interp V ρ)) σ)
            (Ds.reverse.getD (Ds.length - 1 - n) default)) →
      SpineFit σ Ds (ws.map (interp V ρ))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | D :: Ds, w :: ws, σ, ρ, hlen, hmem => by
    simp only [List.map_cons, SpineFit]
    have h0 := hmem 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.length_cons,
      Nat.add_sub_cancel, Nat.sub_zero] at h0
    rw [List.getD_eq_getElem?_getD, List.reverse_cons, List.getElem?_append_right (by simp),
      List.length_reverse, Nat.sub_self] at h0
    refine ⟨h0, ?_⟩
    refine spineFit_of_chain' (by simpa using hlen) ?_
    intro n hn
    have := hmem (n + 1) (by simp; omega)
    simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.length_cons] at this
    rw [List.reverse_cons] at this
    rw [List.getD_eq_getElem?_getD (l := Ds.reverse ++ [D]),
      List.getElem?_append_left (by simp; omega),
      show Ds.length + 1 - 1 - (n + 1) = Ds.length - 1 - n from by omega,
      ← List.getD_eq_getElem?_getD] at this
    exact this

theorem spineFit_of_chain {Ds : List Term} {ws : List Term} {ρ : Nat → V}
    (hlen : ws.length = Ds.length)
    (hmem : ∀ n, n < Ds.length →
      interp V ρ (ws.getD n default)
        ∈ˢ interp V (chain V ρ (ws.take n)) (Ds.reverse.getD (Ds.length - 1 - n) default)) :
    SpineFit ρ Ds (ws.map (interp V ρ)) :=
  spineFit_of_chain' hlen hmem

/-! ## Level assignments -/

/-- The constructor's level assignment, fixed by the recursor's through
`recFireComparands`, agrees with the recursor's on the block's
parameters. -/
theorem substFn_agree_of_comparand {lps lpsR : List Name} {us usj : List Level}
    (hψ : Level.substFn φ lps usj
      = Level.substFn φ lps (lps.map fun q => Level.subst lpsR us (.param q))) :
    ∀ q ∈ lps, Level.substFn φ lps usj q = Level.substFn φ lpsR us q := by
  intro q hq
  rw [congrFun hψ q]
  have hmap : (lps.map fun q => Level.subst lpsR us (.param q))
      = (lps.map Level.param).map (Level.subst lpsR us) := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, Level.substFn_map_subst (by simp) hq, Level.substFn_map_param]

end ConLeche.Model
