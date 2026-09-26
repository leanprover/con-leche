module

import ConLeche.Model.Claims
import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Model.IndPinGrade
public import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitInst

public section

/-!
# Block library: the constructor's stage and the recursor's frame kit

The leaves' bit validity and P packages; the constructor's stage data,
frames and cons; the recursor's frame kit; the generated recursor read;
λ-towers folding to their body; the recursor rule's kit.
-/

/-!
## The direct-structure leaves' bit validity and P packages

`AnnotValid` for the three synthesized leaves, completing the
`WellDenotedV` currency (`WellDenoted` landed with the leaves themselves in
`SetBase/Tower{Leaf,Mk,Rec}.lean`).

The leaves contain **no `.pi` node** — λ, application, constants,
bound variables and the uniform `.proj` spelling only — so their bit
validity is pure hereditary plumbing: `AnnotValid`'s one genuine
clause (the `pi` codomain component) never fires, and every lemma
here is a walk with no semantic content beyond the λ-clause guards.
`UnderTowerValid` is the single hereditary premise shape, shared by
all three leaves (each IS a `mkLamsC` tower).

The `WellDenotedV` packages (`structTyAV_okP`/`structMkAV_okP`/
`structRecAV_okP`) pair the SetBase `_ok2` laws with the validity
walks — the `hAok`/`hAvalid` rows of `declStep_preserves_of_basis_cons`, per
leaf.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- Hereditary bit validity of a field chain. -/
@[expose] def FieldsValid (ρ : Nat → V) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => AnnotValid V ρ F ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsValid (cons a ρ) Fs

/-- The carrier body (graph regime) is bit-valid (no `pi` nodes;
hereditary). -/
theorem towerBodyAVPos_validV {w : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValid V ρ (towerBodyAVPos w Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValid V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAVPos w Fs)))
    rw [AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_app]
      exact ⟨trivial, hv.1⟩
    · rw [AnnotValid_lam]
      exact ⟨hv.1, fun a ha => towerBodyAVPos_validV (hv.2 a ha)⟩

/-- The carrier body (squash regime) is bit-valid: every `pi` node
carries bit `0` over a truth-value codomain (`piR 0`, or `Empty`). -/
theorem sqBodyAV_validV :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValid V ρ (sqBodyAV Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValid V ρ (negAV (.pi 0 0 F (negAV (sqBodyAV Fs))))
    unfold negAV
    rw [AnnotValid_pi]
    refine ⟨?_, fun _ _ => by simp, fun _ _ _ => ?_⟩
    · rw [AnnotValid_pi]
      refine ⟨hv.1, fun x hx => ?_, fun _ x _ => ?_⟩
      · rw [AnnotValid_pi]
        exact ⟨sqBodyAV_validV (hv.2 x hx), fun _ _ => by simp,
          fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
      · exact piR_zero_mem_univZero
    · rw [← univ_zero]; exact empty_mem_univ 0

/-- The carrier body is bit-valid, both regimes. -/
theorem towerBodyAV_validV {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (hv : FieldsValid ρ Fs) : AnnotValid V ρ (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_validV hv
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_validV hv

/-- Application spines are bit-valid from their parts. -/
theorem mkAppN_validV :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ f → (∀ a ∈ args, AnnotValid V σ a) →
      AnnotValid V σ (AnnotTerm.mkAppN f args)
  | [], _, _, hf, _ => hf
  | a :: args, f, σ, hf, hargs => by
    rw [AnnotTerm.mkAppN_cons]
    refine mkAppN_validV ?_ fun a' ha' => hargs a' (.tail _ ha')
    rw [AnnotValid_app]
    exact ⟨hf, hargs a (.head _)⟩

/-- The constructor tupler is bit-valid at a fitting frame — the one
walk that crosses the λ-frame lifts (`AnnotValid_liftN` +
`shiftE_consList`). -/
theorem mkTowerGoPos_validV {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsValid ρp Fs → FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      AnnotValid V (consList bs ρp) (mkTowerGoPos w Fs)
  | [], _, [], _, _, _ => trivial
  | [], _, _ :: _, _, _, hsp => hsp.elim
  | _ :: _, _, [], _, _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hv, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    show AnnotValid V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoPos w Fs))
    rw [AnnotValid_app]
    refine ⟨?_, mkTowerGoPos_validV hw (hv.2 b hsp.1) (hb.2 b hsp.1) hsp.2⟩
    rw [AnnotValid_app]
    refine ⟨?_, by rw [AnnotValid_bvar]; trivial⟩
    rw [AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_app]
      refine ⟨by rw [AnnotValid_const]; trivial, ?_⟩
      rw [AnnotValid_liftN, hshift]
      exact hv.1
    · rw [AnnotValid_lam]
      refine ⟨by rw [AnnotValid_liftN, hshift]; exact hv.1, ?_⟩
      intro x hx
      rw [hA] at hx
      rw [AnnotValid_liftN, ← cons_shiftE, hshift]
      exact towerBodyAV_validV (hv.2 x hx)

/-- The constructor tupler is bit-valid at a fitting frame, both
regimes. -/
theorem mkTowerGo_validV {w : Nat} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hv : FieldsValid ρp Fs)
    (hb : w ≠ 0 → FieldsBound w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_validV hw hv (hb hw) hsp

/-- The single hereditary validity premise of a `mkLamsC` leaf. -/
@[expose] def UnderTowerValid (ρ : Nat → V) (b : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => AnnotValid V ρ b
  | d :: ds => AnnotValid V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → UnderTowerValid (cons a ρ) b ds

/-- A constant-bit λ-tower is bit-valid from the hereditary premise
(the λ clause of `AnnotValid` carries no bit component). -/
theorem mkLamsC_validV {m : Nat} {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      UnderTowerValid ρ b ds → AnnotValid V ρ (mkLamsC m ds b)
  | [], _, h => h
  | d :: ds, ρ, h => by
    show AnnotValid V ρ (.lam m d.2.2 (mkLamsC m ds b))
    rw [AnnotValid_lam]
    exact ⟨h.1, fun a ha => mkLamsC_validV (h.2 a ha)⟩


/-!
## The constructor's stage data

`CtorData`: the constructor type's peeled reading — the binder data
`ds` (parameters then fields), whose codomain bits are zero exactly at
a squash instance, ending in the family applied to the parameter
variables — with its gradings, bounds and level dependence; derived
from the constructor's `checkConstantVal` run at the environment
holding the former (`ctorData_of`), crossed to later stages
(`CtorData.cross`).

`ctorFrames`: the field chain graded at the constructor's parameter
frame (from the field-sort runs), and the two parameter frames
identified (from the binder pins) — the semantic content the former's
real leaf and the constructor's leaf consume.
-/


open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
@[expose] def paramBvars (nP nF : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP + nF - 1 - k)

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
theorem reverse_map_take_drop (ds : List (Nat × Nat × AnnotTerm)) (nP : Nat) :
    ((ds.map (·.2.2)).reverse)
      = (((ds.drop nP).map (·.2.2)).reverse) ++ (((ds.take nP).map (·.2.2)).reverse) := by
  rw [← List.reverse_append, ← List.map_append, List.take_append_drop]


/-!
## The constructor's frames

`ctorFrames`: from the former's and the constructor's data at the
environment holding the former, the binder-domain pins identify the
two parameter frames (`paramFrames`), and the field-sort runs grade
the field chain at the constructor's parameter frame — `FieldsOkB`
(bounded by the result sort in the graph regime, O5), `FieldsValid`,
and `FieldsBound 0` at a propositional structure with the large
eliminator.  These are the premises the former's real leaf and the
constructor's leaf consume.
-/


/-! ## Kit -/

/-- An opened type whose reading is a known peel: the opened record
at the peel's reversed domains. -/
theorem opened_of_peel {m : EnvModel V env} {k : Nat} {e : Expr}
    {fvs : List Expr} {o : Expr} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (hread : denoteMeta m.acval env φ 0 e = some (mkPisAV pps b))
    (hlen : pps.length = k)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps b)) :
    Opened m φ k e fvs o ((pps.map (·.2.2)).reverse) b := by
  obtain ⟨Γ, R, htele, hO⟩ := opened_of hop hcl hb hread hok
  have hst := stripPisAV_mkPisAV pps b
  rw [hlen] at hst
  obtain ⟨rfl, rfl⟩ := PiTeleAV.unique htele (piTeleAV_of_stripPisAV hst)
  exact hO

/-- The field entries of the reversed constructor context are the
peel's field domains. -/
theorem fieldsFrom_eq_drop {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) :
    fieldsFrom ((ds.map (·.2.2)).reverse) (nP + nF) nP nF 0
      = (ds.drop nP).map (·.2.2) := by
  apply List.ext_getElem
  · simp [fieldsFrom, hlen]
  · intro t h1 h2
    simp only [fieldsFrom, List.getElem_map, List.getElem_range, List.getElem_drop]
    have ht : t < nF := by simpa [fieldsFrom] using h1
    rw [Nat.add_zero, getD_reverse_of_peel hlen (by omega)
      (List.getElem?_eq_getElem (by omega))]

/-- The reversed constructor context above the fields is the reversed
parameter context. -/
theorem drop_fields_eq {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) (i : Nat) (hi : i ≤ nP) :
    ((ds.map (·.2.2)).reverse).drop (nP + nF - i)
      = (((ds.take nP).map (·.2.2)).reverse).drop (nP - i) := by
  rw [reverse_map_take_drop ds nP, List.drop_append]
  have hl : (((ds.drop nP).map (·.2.2)).reverse).length = nF := by
    simp [hlen]
  rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, hl,
    show nP + nF - i - nF = nP - i from by omega]

/-- The field chain's validity, walked like its grading. -/
theorem fieldsValid_of_frame {Γ : List AnnotTerm} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) from
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
    refine ⟨(okΓ (nP + j) (by omega) ρ hρ).2, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha

/-- The field chain's universe bound, walked like its grading. -/
theorem fieldsBound_of_frame {Γ : List AnnotTerm} {k nP nF w : Nat}
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


/-!
## The constructor's cons

`stageCtor`: the P step at the constructor's cons.  The leaf is
`structMkAV (resSort.eval ψ) (ds ψ) (Fs ψ)` over the constructor
type's peel; its two hereditary premises (`MkPre`, `UnderTowerValid`)
walk the parameter frame and the full frame from the constructor's
data and frames; the family application at the bottom folds the
former's real leaf along the parameters (`formerFold`), the frames
identified.
-/


/-! ## Kit -/

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
theorem spineFit_iff_of_sat_iff {Ds₁ Ds₂ : List AnnotTerm}
    (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat V Ds₁.reverse ρ ↔ Sat V Ds₂.reverse ρ)
    (ρ : Nat → V) (as : List V) (hl : as.length = Ds₁.length) :
    SpineFit ρ Ds₁ as ↔ SpineFit ρ Ds₂ as := by
  have key : ∀ (Ds₁ Ds₂ : List AnnotTerm), Ds₁.length = Ds₂.length →
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
theorem getD_reverse_take {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) {i : Nat} (hi : i < nP) :
    ((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - i) default
      = (((ds.take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
  have hil : i < ds.length := by omega
  rw [getD_reverse_of_peel hlen (by omega) (List.getElem?_eq_getElem hil),
    getD_reverse_of_peel (List.length_take_of_le (by omega)) hi
      (by rw [List.getElem?_take_of_lt hi]; exact List.getElem?_eq_getElem hil)]


/-!
## The recursor's frame kit

The pieces the recursor's frames are assembled from:

* `piDomsSorts_of_infer` — the per-binder domain inference *and* sort
  runs of an inferred Π-type (`piDoms_of_infer` with the sort);
* `liftN_mkPisAV` — a lifted Π-tower is the tower of lifted domains;
* `instPisAt_openerRes` — the residual of an `instPisAt` run at an
  opener spine reads to the tower's core (`instPisAt_openerDoms`'s
  companion);
* `mkAppN_okP_of_spineFit` — a graded head inhabiting a Π-tower,
  applied along a fitting spine, is graded and lands in the core;
* `famSpine_read`/`famSpine_val` — the family spine `T p⃗` at any depth
  above the parameters: its reading, its grading, and its value (the
  instantiated carrier, by `formerFold`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta)


/-! ## Lifted Π-towers -/

/-- The binder data of a lifted Π-tower: each domain lifted at its own
depth. -/
@[expose] def liftDoms (n : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: ds => (d.1, d.2.1, d.2.2.liftN n k) :: liftDoms n (k + 1) ds

theorem liftDoms_length (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat), (liftDoms n k ds).length = ds.length
  | [], _ => rfl
  | _ :: ds, k => by simp [liftDoms, liftDoms_length n ds (k + 1)]

theorem liftDoms_getElem? (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k i : Nat),
      (liftDoms n k ds)[i]? = ds[i]?.map fun d => (d.1, d.2.1, d.2.2.liftN n (k + i))
  | [], _, _ => rfl
  | _ :: ds, k, 0 => by simp [liftDoms]
  | _ :: ds, k, i + 1 => by
    simp only [liftDoms, List.getElem?_cons_succ, liftDoms_getElem? n ds (k + 1) i]
    rw [show k + 1 + i = k + (i + 1) from by omega]

theorem liftN_mkPisAV (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (k : Nat),
      (mkPisAV ds b).liftN n k = mkPisAV (liftDoms n k ds) (b.liftN n (k + ds.length))
  | [], b, k => by simp [mkPisAV, liftDoms]
  | d :: ds, b, k => by
    simp only [mkPisAV, liftDoms, AnnotTerm.liftN_pi, liftN_mkPisAV n ds b (k + 1),
      List.length_cons]
    rw [show k + 1 + ds.length = k + (ds.length + 1) from by omega]

theorem stripPisAV_mkPisAV_take :
    ∀ (n : Nat) (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm), n ≤ ds.length →
      stripPisAV n (mkPisAV ds b) = some (ds.take n, mkPisAV (ds.drop n) b)
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => by simp at h
  | n + 1, d :: ds, b, h => by
    simp only [mkPisAV, stripPisAV, List.take_succ_cons, List.drop_succ_cons,
      stripPisAV_mkPisAV_take n ds b (by simpa using h), Option.map_some]

/-! ## Graded applications along a fit -/

/-- A fit of bounded domains reads the same at any frame agreeing
below the cut. -/
theorem spineFit_congr_below :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {k : Nat} {ρ ρ' : Nat → V} {as : List V},
      DomsBelow k pds → (∀ i, i < k → ρ i = ρ' i) →
      SpineFit ρ (pds.map (·.2.2)) as → SpineFit ρ' (pds.map (·.2.2)) as
  | [], _, _, _, [], _, _, h => h
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | d :: pds, k, ρ, ρ', a :: as, hb, hρ, h => by
    simp only [List.map_cons, SpineFit] at h ⊢
    refine ⟨?_, spineFit_congr_below hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp_congr_below V d.2.2 k ρ ρ' hb.1 hρ]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hρ i (by omega)

/-! ## The family spine above the parameters -/

/-- The parameter variables as seen from depth `D` (`D ≥ nP`). -/
@[expose] def paramBvarsAt (nP D : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => .bvar (D - 1 - k)

theorem paramBvars_eq_paramBvarsAt (nP nF : Nat) :
    paramBvars nP nF = paramBvarsAt nP (nP + nF) := rfl

/-- A same-index `fvar` spine reads to the parameter variables. -/
theorem denoteMetaSpine_fvars {acval : Name → (Name → Nat) → AnnotTerm} (D : Nat) :
    ∀ (fvs : List Expr) (k₀ : Nat),
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (k₀ + k) ty) →
      DenoteMetaSpine acval env φ D fvs
        ((List.range fvs.length).map fun k => .bvar (D - 1 - (k₀ + k)))
  | [], _, _ => .nil
  | x :: fvs, k₀, hidx => by
    obtain ⟨nm, ty, rfl⟩ := hidx 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteMeta_fvar, Nat.add_zero]) ?_
    have := denoteMetaSpine_fvars (acval := acval) D fvs (k₀ + 1)
      (fun k y hy => by
        obtain ⟨ty', h⟩ := hidx (k + 1) y (by simpa using hy)
        exact ⟨ty', by rw [h]; congr 1; omega⟩)
    have hmapeq : (List.map ((fun k => AnnotTerm.bvar (D - 1 - (k₀ + k))) ∘ Nat.succ)
          (List.range fvs.length))
        = (List.range fvs.length).map fun k => AnnotTerm.bvar (D - 1 - (k₀ + 1 + k)) := by
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

Openings at any depth, per-index scoping of an opening's variables and
of an `instPisAt` residual, frame shifts under a consed spine,
application scoping, the identification of two contexts from entry-wise
agreement (`frameIdent`), the minor space as a Π-tower reading
(`interp_minorSp_of_tele`), and list arithmetic.
-/


variable {V : Type w} [SetTheory V]

/-! ## Openings at any depth -/

theorem openPisAtFvars_of_stripPis_isSome :
    ∀ (n : Nat) {e : Expr} (d : Nat), (Expr.stripPis n e).isSome = true →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, e, _, _ => ⟨[], e, rfl⟩
  | n + 1, e, d, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      obtain ⟨fvs, o, ho⟩ := openPisAtFvars_of_stripPis_isSome n (d + 1)
        (Expr.stripPis_instantiate1_isSome (v := .fvar d dom) n 0 h)
      exact ⟨.fvar d dom :: fvs, o, by simp only [openPisAtFvars, ho]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
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
    | .forallE dom body mb, hop =>
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
    | .lam _ _ _, hop | .letE _ _ _, hop | .lit _, hop | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-! ## Frame shifts under a consed spine -/

omit [SetTheory V] in
theorem shiftE_cons_succ' (n k : Nat) (a : V) (σ : Nat → V) :
    shiftE n (k + 1) (cons a σ) = cons a (shiftE n k σ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ i =>
    simp only [shiftE, cons_succ]
    by_cases h : i < k
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, show i + 1 + n = i + n + 1 from by omega, cons_succ]

/-! ## List arithmetic -/

theorem mkPisAV_append :
    ∀ (l₁ l₂ : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      mkPisAV (l₁ ++ l₂) b = mkPisAV l₁ (mkPisAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkPisAV, mkPisAV_append l₁ l₂ b]

/-! ## Lifted domains, field spines, and frame arithmetic (from the retired
`StructRecMinorP`, task #175 S2) -/

theorem liftDoms_take (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k j : Nat),
      (liftDoms n k ds).take j = liftDoms n k (ds.take j)
  | [], _, _ => by simp [liftDoms]
  | _ :: ds, k, 0 => rfl
  | _ :: ds, k, j + 1 => by
    simp only [liftDoms, List.take_succ_cons, liftDoms_take n ds (k + 1) j]

/-- A fit of lifted domains is a fit of the domains at the shifted
frame. -/
theorem spineFit_liftDoms (n : Nat) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat} {σ : Nat → V} {as : List V},
      SpineFit σ ((liftDoms n k ds).map (·.2.2)) as ↔
        SpineFit (shiftE n k σ) (ds.map (·.2.2)) as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ds, k, σ, a :: as => by
    simp only [liftDoms, List.map_cons, SpineFit, interp_liftN]
    rw [← shiftE_cons_succ']
    exact and_congr Iff.rfl (spineFit_liftDoms n)

theorem spineFit_append_inv :
    ∀ {Ds₁ Ds₂ : List AnnotTerm} {ρ : Nat → V} {as : List V},
      SpineFit ρ (Ds₁ ++ Ds₂) as →
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂
  | [], _, ρ, as, h => ⟨[], as, rfl, trivial, h⟩
  | _ :: _, _, _, [], h => h.elim
  | D :: Ds₁, Ds₂, ρ, a :: as, h => by
    obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_inv (Ds₁ := Ds₁) h.2
    exact ⟨a :: as₁, as₂, rfl, ⟨h.1, h1⟩, h2⟩

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


/-!
## The generated recursor, read

The direct install stores the recursor it generates
(`structRecTy`/`structRecRhs`), so its reading is **syntactic**: the
generated type reads to the Π-tower

    mkPisAV (params (bit ℓ) ++ [motive, minor, major]) (motive t)

whose three special entries are spelled out (`motiveAV`, `minorAV`,
`majorAV`) over the type former's and the constructor's readings, and
the generated rule reads to the λ-tower over the same data
(`denoteP_structRecRhs`).  No frame pin is consumed: the recursor's
data (`recData_of`) comes from these readings, the fabricated type's
own inference run (its grading, `inferRow`) and the elimination datum
the generator wrote (its bits, `zeronessOf_sound`).

The two generic pieces are the readings of the binder walks
(`denoteMeta_replacePisPw`, `denoteMeta_pisToLamsPw`): a walk over an
opened telescope reads to the tower over the telescope's own domain
readings, bits reset, over the body instantiated at the opening's
variables.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta PropWhen)


variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Bits reset -/

/-- Binder data with every codomain bit reset to `b`. -/
@[expose] def rebit (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ds.map fun d => (d.1, b, d.2.2)

@[simp] theorem rebit_map_dom (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).map (·.2.2) = ds.map (·.2.2) := by simp [rebit]

theorem mem_rebit {b : Nat} {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm}
    (h : d ∈ rebit b ds) : d.2.1 = b := by
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp h
  rfl

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

/-- The reading of the constructor's residual, one under (the motive):
the field data lifted once. -/
theorem ctorResidual_read_lift {m : EnvModel V env} {ψ : Name → Nat} {nP nF : Nat}
    {crest : Expr} {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    (hread : denoteMeta m.acval env ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF) (e : Nat) :
    denoteMeta m.acval env ψ (nP + e) crest
      = some (mkPisAV (liftDoms e 0 (ds.drop nP)) (bodyC.liftN e nF)) := by
  rw [denoteMeta_lift m.acval_closed hw (nP + e) (by omega), hread, Option.map_some,
    show nP + e - nP = e from by omega, liftN_mkPisAV, Nat.zero_add]
  congr 3
  simp [hlenD]


/-!
## λ-towers fold to their body

A **graded** λ-tower applied along a fitting spine computes its body
at the spine's frame — whatever its bits.  A nonzero bit steps by
β (`app_lamR_pos`); a zero bit collapses the layer to the proof point,
but the grading's package puts the layer's body values in truth
values, so the body is the point too (`eq_pt_of_mem_univZero`), and the
fold of the point is the point.  This is what lets the recursor rule's
law read the rule's right-hand side without any bit correspondence
between the rule's λ-annotations and the recursor's elimination level.
-/


/-- A graded λ-tower whose value is the point has body value the point
along any fitting spine. -/
theorem mkLamsAV_pt_body :
    ∀ {lds : List (Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V} {as : List V},
      WellDenoted V ρ (mkLamsAV lds b) → SpineFit ρ (lds.map (·.2)) as →
      interp V ρ (mkLamsAV lds b) = (pt : V) →
      interp V (consList as ρ) b = (pt : V)
  | [], _, _, [], _, _, h => h
  | [], _, _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, _, [], _, hsp, _ => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp, hpt => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, WellDenoted_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    rw [consList_cons]
    refine mkLamsAV_pt_body (hrest a hsp.1) hsp.2 ?_
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · exact eq_pt_of_mem_univZero (hB0 h0 a hsp.1) (hB a hsp.1)
    · have := app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos)
        (A := interp V ρ d.2) (F := fun x => interp V (cons x ρ) (mkLamsAV lds b)) hsp.1
      simp only [mkLamsAV, interp_lam] at hpt
      rw [hpt, app_pt] at this
      exact this.symm

/-- **A graded λ-tower folds to its body** along any fitting spine. -/
theorem mkLamsAV_fold_graded :
    ∀ {lds : List (Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V} {as : List V},
      WellDenoted V ρ (mkLamsAV lds b) → SpineFit ρ (lds.map (·.2)) as →
      as.foldl SetTheory.app (interp V ρ (mkLamsAV lds b))
        = interp V (consList as ρ) b
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, hsp => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, WellDenoted_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    rw [consList_cons, List.foldl_cons]
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · -- a zero bit: the layer is the point, and so is the body
      have hpt : interp V ρ (mkLamsAV (d :: lds) b) = (pt : V) := by
        simp only [mkLamsAV, interp_lam]
        rw [h0]
        exact lamR_zero
      rw [hpt, app_pt, foldl_app_pt']
      exact (mkLamsAV_pt_body (hrest a hsp.1) hsp.2
        (eq_pt_of_mem_univZero (hB0 h0 a hsp.1) (hB a hsp.1))).symm
    · simp only [mkLamsAV, interp_lam]
      rw [app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos) hsp.1]
      exact mkLamsAV_fold_graded (hrest a hsp.1) hsp.2

/-- **A graded λ-tower applied along a fitting spine is graded**: each
step's Π-package is the layer's own (`lamR_mem` over the grading's
fibre family), or — once a zero layer has collapsed the value to the
point — the trivial one. -/
theorem mkAppN_wellDenotedV_of_lam :
    ∀ {lds : List (Nat × AnnotTerm)} {b f : AnnotTerm} {args : List AnnotTerm} {ρ σ : Nat → V},
      WellDenotedV V ρ f → (∀ a ∈ args, WellDenotedV V ρ a) →
      WellDenoted V σ (mkLamsAV lds b) →
      (interp V ρ f = (pt : V) ∨ interp V ρ f = interp V σ (mkLamsAV lds b)) →
      SpineFit σ (lds.map (·.2)) (args.map (interp V ρ)) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f args)
  | [], _, _, [], _, _, hf, _, _, _, _ => hf
  | [], _, _, _ :: _, _, _, _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, hf, _, _, _, _ => hf
  | d :: lds, b, f, a :: args, ρ, σ, hf, hargs, hok, hval, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, WellDenoted_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    have ha := hargs a List.mem_cons_self
    rw [AnnotTerm.mkAppN_cons]
    -- the application's package
    have hokApp : WellDenotedV V ρ (.app f a) := by
      refine ⟨?_, by rw [AnnotValid_app]; exact ⟨hf.2, ha.2⟩⟩
      rw [WellDenoted_app]
      rcases hval with hpt | heq
      · exact ⟨hf.1, ha.1, 0, interp V σ d.2, fun _ => unitSet,
          by rw [hpt, piR_zero]; exact pt_mem_truthVal fun x _ => ⟨pt, pt_mem_unitSet⟩,
          hsp.1, fun _ _ _ => mem_univZero.mpr (Subset.refl _)⟩
      · refine ⟨hf.1, ha.1, d.1, interp V σ d.2, B, ?_, hsp.1, fun h0 x hx => hB0 h0 x hx⟩
        rw [heq]
        simp only [mkLamsAV, interp_lam]
        exact lamR_mem hB
    refine mkAppN_wellDenotedV_of_lam hokApp (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))
      (hrest _ hsp.1) ?_ hsp.2
    -- the continuation's value
    rw [interp_app]
    rcases hval with hpt | heq
    · left; rw [hpt, app_pt]
    · rw [heq]
      simp only [mkLamsAV, interp_lam]
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · left; rw [h0, lamR_zero, app_pt]
      · right; rw [app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos) hsp.1]


/-!
## The recursor rule's kit

Syntactic and semantic pieces of the recursor rule's law: the
`checkDefEqList` pins indexed, the rule's λ-peel residual as the
body's instantiation sequence and its value (the minor applied to the
fields), a `TeleFitPA` fit's chain memberships as a `SpineFit`, the
constructor's level assignment agreeing with the recursor's on the
block's parameters, and the minor value at a zero elimination level.
-/


/-! ## Fits as spines -/

/-- A fit's chain memberships are a `SpineFit` (the values read at the
fit's own frame `ρ`, the domains walked from `σ`). -/
theorem spineFit_of_chain' :
    ∀ {Ds : List AnnotTerm} {ws : List AnnotTerm} {σ ρ : Nat → V},
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

theorem spineFit_of_chain {Ds : List AnnotTerm} {ws : List AnnotTerm} {ρ : Nat → V}
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
