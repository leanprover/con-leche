import Lech.SetP.DirectFix.FixRecReadDefsP
import Lech.Verify.Direct.FixRec

/-!
# The generated recursive recursor's readings (task #188)

`Lech/SetP/DirectSum/SumRecReadP.lean` with the inductive hypotheses:
the generated recursive recursor type reads to the Π-tower over
`fixRecDataAV` and rule `j` to the λ-tower over `fixRuleDataAV`
(`Lech/SetP/DirectFix/FixRecReadDefsP.lean`).

The one genuinely new reading is the `ih` binder's domain
`motive e⃗_i f_i`.  Its index expressions are read by the constructor
premise (`CtorReadR.eisRead`) at the constructor's OWN opening — the
parameters and the `i` earlier fields at indices `0 … nP + i - 1` —
while the recursor's frame puts the fields `o` slots higher (the
motive and the earlier minors sit between).  Moving between the two
frames is exactly `Expr.shiftFrom`, iterated `o` times
(`denoteP_instSeq_shift`), which lifts the reading by `o` at the cut
`d - nP`; taking `d` to be the frame depth `nP + nF + l` reached by
`denoteP_lift` first, the two lifts are precisely `ihIdxAt`'s.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Reading through an inserted block of variables -/

/-- **`denoteP_shiftFrom`, iterated**: inserting `o` fresh variable
slots at index `p` lifts the reading by `o` at the cut `d - p`. -/
theorem denoteP_shiftFromN {acval : Name → (Name → Nat) → AVExpr}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} :
    ∀ (o : Nat) {e : Expr} {d : Nat}, p ≤ d → Expr.WScoped d e →
      denoteP acval env φ (d + o) (Expr.shiftFromN p o e)
        = (denoteP acval env φ d e).map (AVExpr.liftN o · (d - p))
  | 0, e, d, _, _ => by
    show denoteP acval env φ (d + 0) e = _
    rw [Nat.add_zero]
    cases denoteP acval env φ d e with
    | none => rfl
    | some v => simp only [Option.map_some, AVExpr.liftN_zero]
  | o + 1, e, d, hpd, hw => by
    show denoteP acval env φ (d + (o + 1)) (Expr.shiftFrom p (Expr.shiftFromN p o e)) = _
    rw [show d + (o + 1) = d + o + 1 from by omega,
      denoteP_shiftFrom hacl _ (d + o) (by omega) (Expr.WScoped_shiftFromN o hw),
      denoteP_shiftFromN hacl o hpd hw]
    cases denoteP acval env φ d e with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      exact AVExprSubst.liftN_liftN_absorb v (by omega) (by omega) 1

/-- **A closed expression at a shifted opening.**  `A` opens it at the
variables `0 … A.length - 1`; `B` opens it at the same variables with
those at or above `p` moved `o` slots up.  The reading moves with
them: it is lifted by `o` at the cut `d - p`. -/
theorem denoteP_instSeq_shift {m : EnvS2Core V env} {ψ : Name → Nat} {p o d t : Nat}
    {e : Expr} (hef : e.hasFvar = false)
    {A B : List Expr} (hlen : A.length = B.length) (hpd : p ≤ d)
    (hAw : ∀ (k : Nat) (x : Expr), A[k]? = some x → Expr.WScoped d x)
    (hAB : ∀ (k : Nat) (a b : Expr), A[k]? = some a → B[k]? = some b →
      ∃ (ia : Nat) (nma nmb : Name) (tya tyb : Expr),
        a = Expr.fvar ia nma tya ∧ b = Expr.fvar (if ia < p then ia else ia + o) nmb tyb)
    {E : AVExpr}
    (hE : denoteP m.acval env ψ d (Expr.instSeq A t e) = some E) :
    denoteP m.acval env ψ (d + o) (Expr.instSeq B t e) = some (E.liftN o (d - p)) := by
  have hAcl : ∀ x ∈ A, Expr.WScoped d x := fun x hx => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    exact hAw q x hq
  have hw : Expr.WScoped d (Expr.instSeq A t e) :=
    Expr.instSeq_WScoped A t hAcl (Expr.WScoped.of_not_hasFvar hef)
  have hshift := denoteP_shiftFromN (acval := m.acval) (env := env) (φ := ψ)
    m.acval_closed (p := p) o hpd hw
  rw [hE, Option.map_some, Expr.shiftFromN_instSeq p o A t e,
    Expr.shiftFromN_eq_self_of_not_hasFvar o hef] at hshift
  have herased : Expr.ErasedEq (Expr.instSeq (A.map (Expr.shiftFromN p o)) t e)
      (Expr.instSeq B t e) := by
    refine Expr.instSeq_erasedEq_args _ _ t (Expr.ErasedEq.rfl e) ?_ (by simp [hlen])
    intro k a₁ a₂ ha₁ ha₂
    rw [List.getElem?_map] at ha₁
    cases hA : A[k]? with
    | none => rw [hA] at ha₁; exact nomatch ha₁
    | some a =>
      rw [hA, Option.map_some, Option.some.injEq] at ha₁
      obtain ⟨ia, nma, nmb, tya, tyb, rfl, hb⟩ := hAB k a a₂ hA ha₂
      obtain ⟨nm', ty', hsh⟩ := Expr.shiftFromN_fvar p o ia nma tya
      rw [← ha₁, hsh, hb]
      exact Eq.refl _
  rw [denoteP_erasedEq herased (d + o)] at hshift
  exact hshift

/-! ## Spine bookkeeping -/

/-- A read spine, re-read entry by entry at another frame. -/
theorem DenoteSpineP.map_map {acval : Name → (Name → Nat) → AVExpr} {d d' : Nat}
    {f g : Expr → Expr} {h : AVExpr → AVExpr} :
    ∀ {as : List Expr} {vs : List AVExpr},
      DenoteSpineP acval env φ d (as.map f) vs →
      (∀ (a : Expr) (v : AVExpr), a ∈ as → denoteP acval env φ d (f a) = some v →
        denoteP acval env φ d' (g a) = some (h v)) →
      DenoteSpineP acval env φ d' (as.map g) (vs.map h)
  | [], vs, hsp, _ => by
    cases hsp
    exact .nil
  | a :: as, vs, hsp, hfg => by
    rw [List.map_cons] at hsp
    cases hsp with
    | cons hd htl =>
      exact .cons (hfg a _ List.mem_cons_self hd)
        (DenoteSpineP.map_map htl fun x v hx hv => hfg x v (List.mem_cons_of_mem _ hx) hv)

/-! ## The `ih` binders' index expressions -/

/-- A field's index expressions inherit the constructor type's
closedness and its own frame's loose-bvar bound. -/
theorem directFieldIdx_props {cty : Expr} {nP nF i : Nat}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF) :
    ∀ e ∈ Lech.directFieldIdxOf cty nP nF i,
      e.hasFvar = false ∧ e.looseBVarsBounded (nP + i) = true := by
  intro e he
  obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
  have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
  obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i]? = some b :=
    ⟨cbs[nP + i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hbd : cbs.getD (nP + i) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  unfold Lech.directFieldIdxOf at he
  rw [hs] at he
  simp only at he
  rw [hbd] at he
  have hmem : e ∈ b.2.1.getAppArgs := List.mem_of_mem_drop he
  refine ⟨Lech.hasFvar_getAppArgs ?_ e hmem, Lech.looseBVarsBounded_getAppArgs ?_ e hmem⟩
  · exact (Lech.stripPis_not_hasFvar _ hs hCf).1 b (List.mem_of_getElem? hb)
  · have := Lech.stripPis_binder_bounded (nP + nF) hs hCb (nP + i) b hb
    rwa [Nat.zero_add] at this

set_option maxHeartbeats 1600000 in
/-- **A recursive field's index expressions at the recursor's frame.**
The constructor premise reads them at the constructor's own opening
(the parameters and the `i` earlier fields, at indices `0 … nP+i-1`);
the frame `p⃗ x⃗ f⃗ ih⃗` reads them at the same variables with the fields
`o` slots higher and `nF - i + l` binders below, which is `ihIdxAt`. -/
theorem denoteSpineP_ihIdx {m : EnvS2Core V env} {ψ : Name → Nat}
    {nP nF o l i : Nat} {cty : Expr} {Eis : List AVExpr}
    {fvs0 : List Expr} {crest : Expr}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    (heis : DenoteSpineP m.acval env ψ (nP + i)
      ((Lech.directFieldIdxOf cty nP nF i).map
        (Expr.instSeq (fvs0.take (nP + i)) (nP + i - 1))) Eis)
    (hi : i < nF)
    {P X F I : List Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty) :
    DenoteSpineP m.acval env ψ (nP + o + nF + l)
      ((Lech.directFieldIdxOf cty nP nF i).map
        (fun e => Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Lech.directIdxAt nF o i l e)))
      (Eis.map (ihIdxAt nF o i l)) := by
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxP q a hq
    rfl
  have hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxF q a hq
    rfl
  have htake : ∀ (k : Nat) (x : Expr),
      (fvs0.take (nP + i))[k]? = some x → fvs0[k]? = some x ∧ k < nP + i := by
    intro k x hx
    have hk : k < (fvs0.take (nP + i)).length := by
      rcases Nat.lt_or_ge k (fvs0.take (nP + i)).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx
        exact nomatch hx
    have hk' : k < nP + i := by
      have hle : (fvs0.take (nP + i)).length ≤ nP + i := by simp; omega
      omega
    rw [List.getElem?_eq_getElem hk] at hx
    refine ⟨?_, hk'⟩
    rw [List.getElem?_eq_getElem (show k < fvs0.length from by rw [hlen0]; omega), ← hx,
      List.getElem_take]
  have hlenAB : (fvs0.take (nP + i)).length = (P ++ F.take i).length := by
    simp [hlen0, hP, hF]
  refine DenoteSpineP.map_map heis ?_
  intro e E he hE
  obtain ⟨hef, heb⟩ := directFieldIdx_props hCf hCb hstripC hi e he
  have hwA : Expr.WScoped (nP + i) (Expr.instSeq (fvs0.take (nP + i)) (nP + i - 1) e) := by
    refine Expr.instSeq_WScoped _ _ ?_ (Expr.WScoped.of_not_hasFvar hef)
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨hq0, hqlt⟩ := htake q x hq
    exact (hw0 q x hq0).mono (by omega)
  have hE2 : denoteP m.acval env ψ (nP + nF + l)
      (Expr.instSeq (fvs0.take (nP + i)) (nP + i - 1) e) = some (E.liftN (nF - i + l) 0) := by
    rw [denoteP_lift m.acval_closed hwA (nP + nF + l) (by omega), hE, Option.map_some]
    congr 2
    omega
  have hshift := denoteP_instSeq_shift (m := m) (ψ := ψ) (p := nP) (o := o)
    (d := nP + nF + l) (t := nP + i - 1) hef hlenAB (by omega)
    (fun k x hx => by
      obtain ⟨hq0, hqlt⟩ := htake k x hx
      exact (hw0 k x hq0).mono (by omega))
    (fun k a b ha hb => by
      obtain ⟨ha0, halt⟩ := htake k a ha
      obtain ⟨nma, tya, rfl⟩ := hidx0 k a ha0
      by_cases hk : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at hb
        obtain ⟨nmb, tyb, rfl⟩ := hidxP k b hb
        exact ⟨k, nma, nmb, tya, tyb, rfl, by rw [if_pos hk]⟩
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at hb
        have hb' : F[k - nP]? = some b := by
          rw [← hb, List.getElem?_take, if_pos (show k - nP < i from by omega)]
        obtain ⟨nmb, tyb, rfl⟩ := hidxF (k - nP) b hb'
        refine ⟨k, nma, nmb, tya, tyb, rfl, ?_⟩
        rw [if_neg hk]
        congr 1
        omega)
    hE2
  rw [show nP + nF + l + o = nP + o + nF + l from by omega,
    show nP + nF + l - nP = nF + l from by omega] at hshift
  rw [Lech.instSeq_directIdxAt P X F I hP hX hF hI hclP hclF (by omega) heb]
  exact hshift

/-! ## The recursor's frame, variable by variable -/

/-- The frame `p⃗ x⃗ f⃗ ih⃗` is opened at the variables `0 … ` in order. -/
theorem frameIdx {P X F I : List Expr} {nP o nF : Nat}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + nF + k) nm ty) :
    ∀ (k : Nat) (x : Expr), (P ++ X ++ F ++ I)[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
  intro k x hx
  by_cases h1 : k < nP + o + nF
  · rw [List.getElem?_append_left (by simp [hP, hX, hF]; omega)] at hx
    by_cases h2 : k < nP + o
    · rw [List.getElem?_append_left (by simp [hP, hX]; omega)] at hx
      by_cases h3 : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at hx
        exact hidxP k x hx
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at hx
        obtain ⟨nm, ty, hy⟩ := hidxX (k - nP) x hx
        exact ⟨nm, ty, by rw [hy]; congr 1; omega⟩
    · rw [List.getElem?_append_right (by simp [hP, hX]; omega)] at hx
      simp only [List.length_append, hP, hX] at hx
      obtain ⟨nm, ty, hy⟩ := hidxF (k - (nP + o)) x hx
      exact ⟨nm, ty, by rw [hy]; congr 1; omega⟩
  · rw [List.getElem?_append_right (by simp [hP, hX, hF]; omega)] at hx
    simp only [List.length_append, hP, hX, hF] at hx
    obtain ⟨nm, ty, hy⟩ := hidxI (k - (nP + o + nF)) x hx
    exact ⟨nm, ty, by rw [hy]; congr 1; omega⟩

/-! ## The `ih` binders -/

set_option maxHeartbeats 1600000 in
/-- **The `ih` binders' `∀`-tower** reads to `ihPisAV`, the body read
under all of them. -/
theorem denoteP_ihPis {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF o : Nat} {pw : PropWhen}
    {cty : Expr} {Eiss : List (List AVExpr)} {fvs0 : List Expr} {crest : Expr}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (ho : 0 < o)
    {P X F : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty) :
    ∀ (is : List Nat) (l : Nat) (body : Expr) (I : List Expr),
      (∀ i ∈ is, i < nF) →
      (∀ i ∈ is, DenoteSpineP m.acval env ψ (nP + i)
        ((Lech.directFieldIdxOf cty nP nF i).map
          (Expr.instSeq (fvs0.take (nP + i)) (nP + i - 1))) (Eiss.getD i [])) →
      I.length = l →
      (∀ (k : Nat) (x : Expr), I[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + o + nF + k) nm ty) →
      ∃ I' : List Expr, I'.length = l + is.length ∧
        (∀ (k : Nat) (x : Expr), I'[k]? = some x →
          ∃ nm ty, x = Expr.fvar (nP + o + nF + k) nm ty) ∧
        denoteP m.acval env ψ (nP + o + nF + l)
            (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
              (Lech.directIhPis nF o pw (Lech.directFieldIdxOf cty nP nF) is l body))
          = (denoteP m.acval env ψ (nP + o + nF + l + is.length)
              (Expr.instSeq (P ++ X ++ F ++ I') (nP + o + nF + l + is.length - 1) body)).map
              (ihPisAV nF o (pwBit ψ pw) Eiss is l) := by
  intro is
  induction is with
  | nil =>
    intro l body I _ _ hlenI hidxI
    refine ⟨I, by simp [hlenI], hidxI, ?_⟩
    simp only [Lech.directIhPis, List.length_nil, Nat.add_zero, ihPisAV]
    cases denoteP m.acval env ψ (nP + o + nF + l)
      (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1) body) <;> rfl
  | cons i is ihs =>
    intro l body I hlt heis hlenI hidxI
    have hiF : i < nF := hlt i List.mem_cons_self
    have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
      simp [hP, hX, hF, hlenI]
      omega
    have hLidx := frameIdx hP hX hF hidxP hidxX hidxF hidxI
    have hclL : ∀ a ∈ P ++ X ++ F ++ I, a.looseBVarsBounded 0 = true := fun a ha => by
      obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, ty, rfl⟩ := hLidx q a hq
      rfl
    have hbvar : ∀ j : Nat, j < nP + o + nF + l →
        denoteP m.acval env ψ (nP + o + nF + l)
            (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1) (Expr.bvar j))
          = some (AVExpr.bvar j) := by
      intro j hj
      have hb := Expr.instSeq_bvar (P ++ X ++ F ++ I) (nP + o + nF + l - 1) j hclL
        (by omega) (by rw [hlenL]; omega)
      obtain ⟨nm, ty, hy⟩ := hLidx _ _ hb
      rw [hy, denoteP_fvar,
        show nP + o + nF + l - 1 - (nP + o + nF + l - 1 - j) = j from by omega]
    have hspI := denoteSpineP_ihIdx (m := m) (ψ := ψ) (l := l) hop0 hCf hCb hstripC
      (heis i List.mem_cons_self) hiF hP hX hF hlenI hidxP hidxF
    have hdom : denoteP m.acval env ψ (nP + o + nF + l)
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Expr.mkAppN (.bvar (nF + o - 1 + l))
            ((Lech.directFieldIdxOf cty nP nF i).map (Lech.directIdxAt nF o i l) ++
              [.bvar (nF - 1 - i + l)])))
        = some (ihDomAV nF o i l (Eiss.getD i [])) := by
      rw [Expr.instSeq_mkAppN, List.map_append, List.map_map]
      simp only [Function.comp_def, List.map_cons, List.map_nil]
      rw [denoteP_mkAppN (hspI.append (.cons (hbvar (nF - 1 - i + l) (by omega)) .nil))
        (hbvar (nF + o - 1 + l) (by omega))]
      rfl
    simp only [Lech.directIhPis]
    rw [Expr.instSeq_forallE (P ++ X ++ F ++ I) (nP + o + nF + l - 1) _ _ _ _
        (by rw [hlenL]; omega),
      show nP + o + nF + l - 1 + 1 = nP + o + nF + l from by omega,
      denoteP_forallE, hdom]
    generalize hfv : Expr.fvar (nP + o + nF + l) (Name.str .anonymous "ih")
      (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
        (Expr.mkAppN (.bvar (nF + o - 1 + l))
          ((Lech.directFieldIdxOf cty nP nF i).map (Lech.directIdxAt nF o i l) ++
            [.bvar (nF - 1 - i + l)]))) = ifv
    have hY : ∀ rest : Expr,
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l) rest).instantiate1 ifv 0
          = Expr.instSeq (P ++ X ++ F ++ (I ++ [ifv])) (nP + o + nF + l) rest := by
      intro rest
      rw [show P ++ X ++ F ++ (I ++ [ifv]) = (P ++ X ++ F ++ I) ++ [ifv] from by simp,
        Expr.instSeq_append (P ++ X ++ F ++ I) [ifv], hlenL, Nat.sub_self]
      rfl
    have hidxI' : ∀ (k : Nat) (x : Expr), (I ++ [ifv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + o + nF + k) nm ty := by
      intro k x hx
      by_cases hk : k < I.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxI k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - I.length = 0 := by
          rcases Nat.lt_or_ge (k - I.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have hkl : k = l := by omega
        subst hkl
        exact ⟨_, _, hfv.symm⟩
    obtain ⟨I', hlenI'', hidxI'', hread⟩ := ihs (l + 1) body (I ++ [ifv])
      (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi'))
      (fun i' hi' => heis i' (List.mem_cons_of_mem _ hi'))
      (by simp [hlenI]) hidxI'
    refine ⟨I', by rw [hlenI'']; simp; omega, hidxI'', ?_⟩
    rw [show nP + o + nF + (l + 1) - 1 = nP + o + nF + l from by omega,
      show nP + o + nF + (l + 1) + is.length = nP + o + nF + l + (i :: is).length from by
        simp; omega] at hread
    rw [hY, show nP + o + nF + l + 1 = nP + o + nF + (l + 1) from by omega, hread]
    cases denoteP m.acval env ψ (nP + o + nF + l + (i :: is).length)
      (Expr.instSeq (P ++ X ++ F ++ I') (nP + o + nF + l + (i :: is).length - 1) body) with
    | none => rfl
    | some v => rfl

/-! ## Reading at a deeper frame -/

/-- A closed expression opened at the variables `0 … L.length - 1`
reads the same at every deeper frame, up to the lift: the variables'
annotations do not matter (`denoteP_erasedEq`), so `denoteP_lift`
applies at the canonical opening. -/
theorem denoteP_instSeq_lift {m : EnvS2Core V env} {ψ : Name → Nat} {d d' t : Nat}
    {e : Expr} (hef : e.hasFvar = false) {L : List Expr}
    (hidxL : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hlenL : L.length ≤ d) (hdd : d ≤ d') {E : AVExpr}
    (hE : denoteP m.acval env ψ d (Expr.instSeq L t e) = some E) :
    denoteP m.acval env ψ d' (Expr.instSeq L t e) = some (E.liftN (d' - d) 0) := by
  obtain ⟨L₀, hlen₀, hidx₀⟩ : ∃ L₀ : List Expr, L₀.length = L.length ∧
      ∀ (k : Nat) (x : Expr), L₀[k]? = some x →
        x = Expr.fvar k Name.anonymous (.sort .zero) := by
    refine ⟨(List.range L.length).map fun k => Expr.fvar k Name.anonymous (.sort .zero),
      by simp, ?_⟩
    intro k x hx
    rcases Nat.lt_or_ge k L.length with hk | hk
    · rw [List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range L.length).length from by simp [hk]),
        List.getElem_range] at hx
      exact (Option.some.inj hx).symm
    · rw [List.getElem?_eq_none (by simp; omega)] at hx
      exact nomatch hx
  have herased : Expr.ErasedEq (Expr.instSeq L t e) (Expr.instSeq L₀ t e) := by
    refine Expr.instSeq_erasedEq_args _ _ t (Expr.ErasedEq.rfl e) ?_ (by rw [hlen₀])
    intro k a₁ a₂ ha₁ ha₂
    obtain ⟨nm, ty, rfl⟩ := hidxL k a₁ ha₁
    rw [hidx₀ k a₂ ha₂]
    exact Eq.refl _
  have hw : Expr.WScoped d (Expr.instSeq L₀ t e) := by
    refine Expr.instSeq_WScoped _ _ ?_ (Expr.WScoped.of_not_hasFvar hef)
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    have hq' : q < L.length := by
      rcases Nat.lt_or_ge q L.length with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlen₀]; omega)] at hq
        exact nomatch hq
    rw [hidx₀ q x hq]
    simp only [Expr.WScoped]
    exact ⟨by omega, trivial⟩
  rw [denoteP_erasedEq herased d] at hE
  rw [denoteP_erasedEq herased d', denoteP_lift m.acval_closed hw d' hdd, hE, Option.map_some]

/-! ## The recursive minor premise -/

set_option maxHeartbeats 3200000 in
/-- **The recursive minor premise at offset `o`**, instantiated at the
parameters and the `o` extras, reads to `minorAVAtR`: the sum route's
reading (`denoteP_minorAt`) with the `ih` binders (`denoteP_ihPis`)
between the fields and the conclusion, which is therefore read one
frame lower and lifted (`denoteP_instSeq_lift`). -/
theorem denoteP_minorAtR {m : EnvS2Core V env} {ψ : Name → Nat} {T C : Name} {lps : List Name}
    {ciT ci : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    (hfC : env.find? C = some ci) (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF nIdx : Nat} {pw : PropWhen} {cty mty : Expr} {extras : List Expr}
    {recIdx : List Nat} {Eiss : List (List AVExpr)}
    (hmin : Lech.directMinorTyR C lps nP nF extras.length pw cty recIdx = some mty)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hresid : ∃ (cbs : List (Name × Expr × BinderMeta)) (es : List Expr),
      cty.stripPis (nP + nF)
        = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es)) ∧
      es.length = nIdx)
    {ds : List (Nat × Nat × AVExpr)} {Es : List AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty
      = some (mkPisAV ds (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es))))
    (hlenD : ds.length = nP + nF) (hlenE : Es.length = nIdx)
    (hrecBnd : ∀ i ∈ recIdx, i < nF)
    (heisR : ∀ i ∈ recIdx, ∀ (fvs : List Expr) (rest : Expr),
      openPisAtFvars (nP + nF) cty 0 = some (fvs, rest) →
      DenoteSpineP m.acval env ψ (nP + i)
        ((Lech.directFieldIdxOf cty nP nF i).map
          (Expr.instSeq (fvs.take (nP + i)) (nP + i - 1))) (Eiss.getD i []))
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a)
    (ho : 0 < extras.length)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) :
    denoteP m.acval env ψ (nP + extras.length)
        (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty)
      = some (minorAVAtR m C ψ nP nF (pwBit ψ pw) extras.length ds Es recIdx Eiss) := by
  obtain ⟨cbs, fbs, crest0, res, hsC, hsF, hrep⟩ := Lech.directMinorTyR_unfold hmin
  obtain ⟨cbs', es, hsAll, hlenes⟩ := hresid
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := by rw [hsAll]; rfl
  have hres : res = Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es) := by
    have := (Lech.stripPis_append nP hsC hsF).symm.trans hsAll
    exact (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).2
  subst hres
  have hargs : ((Expr.mkAppN (.const T (lps.map .param))
      (Lech.directPsAt nF nP ++ es)).getAppArgs).drop nP = es := by
    rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' (by simp [Lech.directPsAt])]
  rw [hargs] at hrep
  have hesMem : ∀ e ∈ es, e ∈ (Expr.mkAppN (.const T (lps.map .param))
      (Lech.directPsAt nF nP ++ es)).getAppArgs := by
    intro e he
    rw [Expr.getAppArgs_mkAppN]
    exact List.mem_append_right _ (List.mem_append_right _ he)
  have hes : ∀ e ∈ es, e.looseBVarsBounded (nP + nF) = true := by
    intro e he
    have hb := Expr.stripPis_body_bounded (nP + nF) hsAll hCb
    rw [Nat.zero_add] at hb
    exact Lech.looseBVarsBounded_getAppArgs hb e (hesMem e he)
  have hesF : ∀ e ∈ es, e.hasFvar = false := fun e he =>
    Lech.hasFvar_getAppArgs (Lech.stripPis_not_hasFvar (nP + nF) hsAll hCf).2 e (hesMem e he)
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE q a hq
    rfl
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb
    rwa [Nat.zero_add] at this
  have hmin' := Lech.replacePisPw_instSeq (tfvs ++ extras) (nP + extras.length - 1)
    (by simp [hlenT]; omega) hrep
  rw [Lech.instSeq_minorTele tfvs extras hlenT hclT hcb0] at hmin'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + extras.length) hcstrip
  have hcreadO := ctorResidual_read_lift hcread hcw hlenD extras.length
  have hstX : stripPisAV nF (mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF))
      = some (liftDoms extras.length 0 (ds.drop nP),
          (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF) := by
    have := stripPisAV_mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcreadO hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mfv, hhead⟩ : ∃ mfv, extras[0]? = some mfv := ⟨_, List.getElem?_eq_getElem ho⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE 0 mfv hhead
  rw [Nat.add_zero] at hhead
  -- the frame, as one instantiation sequence
  have hcomb : ∀ Y : Expr,
      Expr.instSeq xFvs (nF - 1)
          (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF) Y)
        = Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + extras.length + nF - 1) Y := by
    intro Y
    rw [Expr.instSeq_append (tfvs ++ extras) xFvs,
      show (tfvs ++ extras).length = nP + extras.length from by simp [hlenT],
      show nP + extras.length + nF - 1 - (nP + extras.length) = nF - 1 from by omega,
      show nP + extras.length + nF - 1 = nP + extras.length - 1 + nF from by omega]
  rw [hcomb] at hminor
  have hidx3 : ∀ (k : Nat) (x : Expr), (tfvs ++ extras ++ xFvs)[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
    have h := frameIdx (I := ([] : List Expr)) hlenT rfl hlenX hidxT hidxE hidxX
      (by intro k x hx; simp at hx)
    simpa using h
  have hcl3 : ∀ a ∈ tfvs ++ extras ++ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidx3 q a hq
    rfl
  have hlen3 : (tfvs ++ extras ++ xFvs).length = nP + extras.length + nF := by
    simp [hlenT, hlenX]
    omega
  -- the conclusion, at the field frame
  have hcore : denoteP m.acval env ψ (nP + extras.length + nF)
      (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + extras.length + nF - 1)
        (Expr.mkAppN (.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++
            [Lech.directCtorSpineAt C lps extras.length nP nF])))
      = some (AVExpr.mkAppN (.bvar (nF + extras.length - 1))
          ((Es.map fun E => E.liftN extras.length nF) ++
            [AVExpr.mkAppN (m.acval C ψ)
              (paramBvarsAt nP (nP + extras.length + nF) ++ fieldBvars nF)])) := by
    rw [← hcomb, Lech.instSeq_minorBodyI_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead hes]
    have hspI := denoteSpineP_idxArgs_lift hfT hlpsT (o := extras.length) hsF hlenT hlenX hclT
      hidxX hcreadO hlenD hlenE hlenes
    have hspine := denoteP_famSpine_at (m := m) (ψ := ψ) hfC hlpsC (o := extras.length) hlenT
      hlenX hidxT hidxX
    rw [denoteP_mkAppN (hspI.append (.cons hspine .nil)) (by rw [denoteP_fvar]),
      show nP + extras.length + nF - 1 - nP = nF + extras.length - 1 from by omega]
  -- the conclusion is closed and bounded by the field frame
  have hcoreF : (Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [Lech.directCtorSpineAt C lps extras.length nP nF])).hasFvar = false := by
    refine Lech.hasFvar_mkAppN _ _ rfl ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      rw [Lech.hasFvar_liftLooseBVars]
      exact hesF e he
    · rw [List.mem_singleton] at h
      subst h
      refine Lech.hasFvar_mkAppN _ _ rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with h1 | h1
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h1
        rfl
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h1
        rfl
  have hcoreB : (Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [Lech.directCtorSpineAt C lps extras.length nP nF])).looseBVarsBounded
      (nP + extras.length + nF) = true := by
    refine Lech.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]; omega) ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      have hb := Expr.looseBVarsBounded_liftLooseBVars extras.length e (b := nP + nF)
        (c := nF) (hes e he)
      exact Expr.looseBVarsBounded_mono (by omega) hb
    · rw [List.mem_singleton] at h
      subst h
      unfold Lech.directCtorSpineAt
      refine Lech.looseBVarsBounded_mkAppN rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with h1 | h1
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
        have : k < nP := by simpa [Lech.directPsAt] using hk
        simp [Expr.looseBVarsBounded]
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
        have : k < nF := by simpa using hk
        simp [Expr.looseBVarsBounded]
        omega
  -- the `ih` binders
  obtain ⟨fvs0, crest00, hop0⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  obtain ⟨I', hlenI', hidxI', hIH⟩ := denoteP_ihPis (m := m) (ψ := ψ) (pw := pw) (Eiss := Eiss)
    hop0 hCf hCb hstripC ho hlenT rfl hlenX hidxT hidxE hidxX recIdx 0
    ((Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [Lech.directCtorSpineAt C lps extras.length nP nF])).liftLooseBVars recIdx.length 0)
    [] hrecBnd (fun i hi => heisR i hi fvs0 crest00 hop0) rfl
    (by intro k x hx; simp at hx)
  simp only [List.append_nil, Nat.add_zero, Nat.zero_add] at hIH hlenI'
  -- the conclusion, under the `ih` binders
  have hcoreR : denoteP m.acval env ψ (nP + extras.length + nF + recIdx.length)
      (Expr.instSeq (tfvs ++ extras ++ xFvs ++ I') (nP + extras.length + nF + recIdx.length - 1)
        ((Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++
            [Lech.directCtorSpineAt C lps extras.length nP nF])).liftLooseBVars
          recIdx.length 0))
      = some ((AVExpr.mkAppN (.bvar (nF + extras.length - 1))
          ((Es.map fun E => E.liftN extras.length nF) ++
            [AVExpr.mkAppN (m.acval C ψ)
              (paramBvarsAt nP (nP + extras.length + nF) ++ fieldBvars nF)])).liftN
          recIdx.length 0) := by
    have hmid := Lech.instSeq_liftLooseBVars_mid (tfvs ++ extras ++ xFvs) I' (c := 0) hcl3
      (by rw [hlen3, Nat.add_zero]; exact hcoreB)
    rw [hlen3, hlenI', Nat.add_zero, Nat.add_zero] at hmid
    rw [hmid]
    have hlift := denoteP_instSeq_lift (m := m) (ψ := ψ) hcoreF hidx3 (Nat.le_of_eq hlen3)
      (show nP + extras.length + nF ≤ nP + extras.length + nF + recIdx.length from by omega) hcore
    rw [show nP + extras.length + nF + recIdx.length - (nP + extras.length + nF)
      = recIdx.length from by omega] at hlift
    exact hlift
  rw [hminor, hIH, hcoreR, Option.map_some, Option.map_some]
  rfl

/-! ## The minors' telescopes -/

set_option maxHeartbeats 1600000 in
/-- **The `∀`-telescope of recursive minors** reads to the Π-tower over
`fixMinorsData`, the body read under the motive and all minors. -/
theorem denoteP_minorsPisR {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
      {body mins : Expr} {extras : List Expr},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      Lech.directMinorsPisR lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkPisAV (fixMinorsData m ψ nP (pwBit ψ pw) cds extras.length))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Lech.directMinorsPisR_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsData]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty, recIdx) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es, recIdx', Eiss⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    have hrI : recIdx' = recIdx := hc.recIdx
    subst hC' hnF' hrI
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Lech.directMinorsPisR_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_forallE,
      denoteP_minorAtR hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hc.recIdxBnd hc.eisRead hlenT hidxT hspW ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length) (Lech.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Lech.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Lech.directMinorsPisR lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsPisR hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **The `λ`-telescope of recursive minors** reads to the λ-tower over
`fixMinorsData`'s domains, the body read under the motive and all
minors. -/
theorem denoteP_minorsLamsR {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
      {body mins : Expr} {extras : List Expr},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      Lech.directMinorsLamsR lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkLamsAV ((fixMinorsData m ψ nP (pwBit ψ pw) cds extras.length).map
                fun d => (d.2.1, d.2.2)))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Lech.directMinorsLamsR_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsData, List.map_nil]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty, recIdx) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es, recIdx', Eiss⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    have hrI : recIdx' = recIdx := hc.recIdx
    subst hC' hnF' hrI
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Lech.directMinorsLamsR_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Lech.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_lam,
      denoteP_minorAtR hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hc.recIdxBnd hc.eisRead hlenT hidxT hspW ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length) (Lech.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Lech.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Lech.directMinorsLamsR lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsLamsR hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

/-! ## The generated type -/

set_option maxHeartbeats 3200000 in
/-- **The generated recursive recursor type reads to the Π-tower over
`fixRecDataAV`** with the core `motive ı⃗ t`. -/
theorem denoteP_directRecTyR {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
    (hcr : CtorReadsR m ψ T lps nP nIdx ctors cds)
    {tty recTy : Expr}
    (hgen : Lech.directRecTyR T lps elim large nP nIdx tty ctors = some recTy)
    (hTf : tty.hasFvar = false) (hTb : tty.looseBVarsBounded 0 = true)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx) :
    denoteP m.acval env ψ 0 recTy
      = some (mkPisAV (fixRecDataAV m T ψ nP nIdx (Lech.directElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds)
          (recConcAV cds.length nIdx)) := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hsT, hmot, hmaj, hmin, hrec⟩ :=
    Lech.directRecTyR_unfold hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  generalize hn : ctors.length = n at hmaj hmin hlenC
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hrec hmaj hmin hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hrec hmaj hmin ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteP_replacePisPw nP hrec hopT hTread hst, Nat.zero_add]
  -- the motive binder, instantiated at the parameters
  rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteP_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteP_forallE, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Lech.directMinorsPisR lps nP pw ctors [mfv].length major = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsPisR hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the index telescope, under the motive and the minors
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras', a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE' a h
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  obtain ⟨mfv', hhead⟩ : ∃ x, extras'[0]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE' 0 mfv' hhead
  rw [Nat.add_zero] at hhead
  have htb0 : itele.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsT hTb; rwa [Nat.zero_add] at this
  have hmaj' := Lech.replacePisPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hmaj
  have hres := Lech.instSeq_minorTele tfvs extras' hlenT hclT htb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hmaj'
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx (nP + 1 + n) htstrip
  have htreadN : denoteP m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) itele)
      = some (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w)) := by
    have := ctorResidual_read_lift htread htw hlenP (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega, AVExpr.liftN_sort] at this
  have hstI : stripPisAV nIdx (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w))
      = some (liftDoms (n + 1) 0 (ppsAll.drop nP), .sort w) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (AVExpr.sort w)
    rwa [liftDoms_length, List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmajR := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmaj' hopI
    htreadN hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the major and the conclusion, instantiated
  have hnilI : ifvs = [] ∨ nIdx - 1 + 1 = nIdx := by
    rcases Nat.eq_zero_or_pos nIdx with h0 | hpos
    · left; rw [h0] at hlenI; exact List.eq_nil_of_length_eq_zero hlenI
    · right; omega
  have hdom1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (Lech.directFamI T lps nP nIdx (n + 1) 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold Lech.directFamI
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + 1 + n - 1 + nIdx = (0 + (n + 1) + nIdx) + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt (tfvs ++ extras') (0 + (n + 1) + nIdx) nP hclTE
        (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      directPsAt_zero, Lech.map_instSeq_fieldBvars_above (tfvs ++ extras') _ nIdx
        (by rw [hlenTE]; omega)]
  have hcod1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
      (Expr.mkAppN (.bvar (nIdx + n + 1)) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP nmM tyM) (Lech.directPsAt 1 nIdx ++ [.bvar 0]) := by
    have hhead' : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
        (.bvar (nIdx + n + 1)) = Expr.fvar nP nmM tyM := by
      have := Expr.instSeq_bvar (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1) (nIdx + n + 1)
        hclTE (by omega) (by rw [hlenTE]; omega)
      rw [show nP + 1 + n - 1 + nIdx + 1 - (nIdx + n + 1) = nP from by omega,
        List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
      exact (Option.some.inj this).symm
    rw [Expr.instSeq_mkAppN, hhead', List.map_append]
    congr 2
    · refine (List.map_congr_left ?_).trans (List.map_id _)
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact Lech.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)
    · simp only [List.map_cons, List.map_nil]
      rw [Lech.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      Lech.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hcod2 : Expr.instSeq ifvs (nIdx - 1 + 1)
      (Expr.mkAppN (.fvar nP nmM tyM) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0]) := by
    rw [instSeq_idx_congr (sp := ifvs) (t := nIdx - 1 + 1) (t' := nIdx) _ hnilI,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.fvar nP nmM tyM) rfl,
      List.map_append, map_instSeq_directPsAt_one ifvs nIdx hclI hlenI]
    simp only [List.map_cons, List.map_nil]
    rw [Lech.instSeq_bvar_lt ifvs _ 0 (by omega)]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (.forallE (.str .anonymous "t") (Lech.directFamI T lps nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
        ⟨.default, pw⟩))
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
          (Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])) ⟨.default, pw⟩ := by
    rw [Expr.instSeq_forallE (tfvs ++ extras') (nP + 1 + n - 1 + nIdx) _ _ _ _
        (by rw [hlenTE]; omega), hdom1, hcod1,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ _ (by omega), hdom2, hcod2]
  rw [hbody] at hmajR
  -- the major's reading
  have hspine := denoteP_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := 1 + n) hlenT hlenI hidxT
    (fun k x hx => by rw [show nP + (1 + n) + k = nP + 1 + n + k from by omega]; exact hidxI k x hx)
  rw [show nP + (1 + n) + nIdx = nP + 1 + n + nIdx from by omega] at hspine
  have hconc : denoteP m.acval env ψ (nP + 1 + n + nIdx + 1)
      ((Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])).instantiate1
        (.fvar (nP + 1 + n + nIdx) (.str .anonymous "t")
          (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))) 0)
      = some (recConcAV n nIdx) := by
    rw [Expr.mkAppN_instantiate1, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instantiate1_eq_self (e := Expr.fvar nP nmM tyM) rfl,
      map_instantiate1_closed hclI]
    simp +decide only [Expr.instantiate1, ↓reduceIte]
    have hspI : DenoteSpineP m.acval env ψ (nP + 1 + n + nIdx + 1) ifvs (idxVarsAV nIdx 1) := by
      have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nIdx + 1)
        ifvs (nP + 1 + n) hidxI
      rw [hlenI] at this
      have he : ((List.range nIdx).map fun k =>
          AVExpr.bvar (nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + k))) = idxVarsAV nIdx 1 := by
        unfold idxVarsAV
        apply List.map_congr_left
        intro k _
        congr 1
        omega
      rwa [he] at this
    rw [denoteP_mkAppN (hspI.append (.cons (denoteP_fvar _ _ _ _ _) .nil)) (denoteP_fvar _ _ _ _ _),
      show nP + 1 + n + nIdx + 1 - 1 - nP = 1 + nIdx + n from by omega,
      show nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + nIdx) = 0 from by omega,
      AVExpr.mkAppN_append_one]
    rfl
  have hpi : denoteP m.acval env ψ (nP + 1 + n + nIdx)
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
        (Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])) ⟨.default, pw⟩)
      = some (.pi 0 (pwBit ψ pw) (majorAVAt m T ψ nP nIdx n) (recConcAV n nIdx)) := by
    rw [denoteP_forallE, hspine, hconc]
    rfl
  rw [hpi, Option.map_some] at hmajR
  rw [hmajR]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold fixRecDataAV majorAVAt
  rw [mkPisAV_append, mkPisAV_append, mkPisAV_append, mkPisAV_append, hlenC]
  rfl

/-! ## The rule's core -/

/-- The recursor's leading spine `p⃗ motive m⃗` in a rule, as one
`bvar` list: the parameters, the motive and the minors are the frame's
first `nP + n + 1` variables. -/
theorem recPrefixBvars_eq (nP n nF : Nat) :
    recPrefixBvars nP n nF
      = (List.range (nP + n + 1)).map fun k => AVExpr.bvar (nP + n + nF - k) := by
  have hlA : (paramBvarsAt nP (nP + nF + n + 1)).length = nP := by simp [paramBvarsAt]
  have hlAB : (paramBvarsAt nP (nP + nF + n + 1) ++ [AVExpr.bvar (nF + n)]).length = nP + 1 := by
    simp [paramBvarsAt]
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  by_cases hk : k < nP + n + 1
  · rw [List.getElem?_eq_getElem (show k < (List.range (nP + n + 1)).length from by simp; omega),
      List.getElem_range, Option.map_some]
    unfold recPrefixBvars
    by_cases hkp : k < nP
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [paramBvarsAt, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range nP).length from by simp; omega),
        List.getElem_range, Option.map_some, Option.some.injEq]
      congr 1
      omega
    · by_cases hkm : k = nP
      · subst hkm
        rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hlA,
          Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), hlAB]
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem
            (show k - (nP + 1) < (List.range n).length from by simp; omega),
          List.getElem_range, Option.map_some, Option.some.injEq]
        congr 1
        omega
  · have hlR : (recPrefixBvars nP n nF).length = nP + n + 1 := by
      simp only [recPrefixBvars, paramBvarsAt, List.length_append, List.length_map,
        List.length_range, List.length_singleton]
      omega
    rw [List.getElem?_eq_none (by rw [hlR]; omega),
      List.getElem?_eq_none (show (List.range (nP + n + 1)).length ≤ k from by simp; omega)]
    rfl

/-- A pointwise-read mapped spine. -/
theorem DenoteSpineP.of_map {α : Type} {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {f : α → Expr} {g : α → AVExpr} :
    ∀ (l : List α), (∀ a ∈ l, denoteP acval env φ d (f a) = some (g a)) →
      DenoteSpineP acval env φ d (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h =>
    .cons (h a List.mem_cons_self)
      (DenoteSpineP.of_map l fun x hx => h x (List.mem_cons_of_mem _ hx))

set_option maxHeartbeats 3200000 in
/-- **Rule `j`'s core at a recursive block**: minor `j` at the field
variables and the inductive hypotheses, read at the full frame under
the motive and `n` minors. -/
theorem denoteP_ruleCoreR {m : EnvS2Core V env} {ψ : Name → Nat}
    {recC : Name} {rlps : List Name} {ciR : ConstantInfo}
    (hfR : env.find? recC = some ciR) (hlpsR : ciR.toConstantVal.levelParams = rlps)
    {nP nF n j : Nat} {cty : Expr} {recIdx : List Nat} {Eiss : List (List AVExpr)}
    {fvs0 : List Expr} {crest00 : Expr}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest00))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    (hrecBnd : ∀ i ∈ recIdx, i < nF)
    (heisR : ∀ i ∈ recIdx, DenoteSpineP m.acval env ψ (nP + i)
      ((Lech.directFieldIdxOf cty nP nF i).map
        (Expr.instSeq (fvs0.take (nP + i)) (nP + i - 1))) (Eiss.getD i []))
    {tfvs extras xFvs : List Expr}
    (hlenT : tfvs.length = nP) (hlenE : extras.length = n + 1) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + 1 + n + k) nm ty)
    (hj : j < n) :
    denoteP m.acval env ψ (nP + 1 + n + nF)
        (Expr.instSeq xFvs (nF - 1) (Expr.instSeq (tfvs ++ extras) (nP + n + nF)
          (Lech.directRuleBodyR recC (rlps.map .param) nP n nF j recIdx
            (Lech.directFieldIdxOf cty nP nF))))
      = some (fixRuleCoreAV (m.acval recC ψ) nP nF n j recIdx Eiss) := by
  have hidxX' : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + (n + 1) + k) nm ty := by
    intro k x hx
    obtain ⟨nm, ty, hy⟩ := hidxX k x hx
    exact ⟨nm, ty, by rw [hy]; congr 1; omega⟩
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE q a hq
    rfl
  have hlenTE : (tfvs ++ extras).length = nP + (n + 1) := by simp [hlenT, hlenE]
  have hcombR : ∀ Y : Expr,
      Expr.instSeq xFvs (nF - 1) (Expr.instSeq (tfvs ++ extras) (nP + n + nF) Y)
        = Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF) Y := by
    intro Y
    rw [Expr.instSeq_append (tfvs ++ extras) xFvs, hlenTE,
      show nP + n + nF - (nP + (n + 1)) = nF - 1 from by omega]
  have hLidx : ∀ (k : Nat) (x : Expr), (tfvs ++ extras ++ xFvs)[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
    have h := frameIdx (I := ([] : List Expr)) hlenT hlenE hlenX hidxT hidxE hidxX'
      (by intro k x hx; simp at hx)
    simpa using h
  have hclL : ∀ a ∈ tfvs ++ extras ++ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hLidx q a hq
    rfl
  have hlenL : (tfvs ++ extras ++ xFvs).length = nP + 1 + n + nF := by
    simp [hlenT, hlenE, hlenX]
    omega
  have hbvar : ∀ q : Nat, q < nP + 1 + n + nF →
      denoteP m.acval env ψ (nP + 1 + n + nF)
          (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF) (Expr.bvar q))
        = some (AVExpr.bvar q) := by
    intro q hq
    have hb := Expr.instSeq_bvar (tfvs ++ extras ++ xFvs) (nP + n + nF) q hclL
      (by omega) (by rw [hlenL]; omega)
    obtain ⟨nm, ty, hy⟩ := hLidx _ _ hb
    rw [hy, denoteP_fvar,
      show nP + 1 + n + nF - 1 - (nP + n + nF - q) = q from by omega]
  have hpremap : (Lech.directRecPrefixAt nP n nF 0).map
      (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF)) = tfvs ++ extras := by
    rw [show (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF))
        = (fun a => Expr.instSeq xFvs (nF - 1)
            (Expr.instSeq (tfvs ++ extras) (nP + n + nF) a)) from by
      funext a; rw [hcombR]]
    exact Lech.map_instSeq_directRecPrefixAt tfvs extras xFvs hlenT hlenE hlenX hclT hclE
  have hpre : DenoteSpineP m.acval env ψ (nP + 1 + n + nF) (tfvs ++ extras)
      (recPrefixBvars nP n nF) := by
    have h := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nF)
      (tfvs ++ extras) 0 (fun k x hx => by
        have hklt : k < (tfvs ++ extras).length := by
          rcases Nat.lt_or_ge k (tfvs ++ extras).length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx
            exact nomatch hx
        obtain ⟨nm, ty, hy⟩ := hLidx k x (by
          rw [List.getElem?_append_left hklt]
          exact hx)
        exact ⟨nm, ty, by rw [hy, Nat.zero_add]⟩)
    have he : ((List.range (tfvs ++ extras).length).map fun k =>
        AVExpr.bvar (nP + 1 + n + nF - 1 - (0 + k))) = recPrefixBvars nP n nF := by
      rw [recPrefixBvars_eq, hlenTE,
        show nP + (n + 1) = nP + n + 1 from by omega]
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at h
  have hihApp : ∀ i ∈ recIdx,
      denoteP m.acval env ψ (nP + 1 + n + nF)
          (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF)
            (Lech.directIhApp recC (rlps.map .param) nP n nF i
              (Lech.directFieldIdxOf cty nP nF i)))
        = some (ihAppAV (m.acval recC ψ) nP n nF i (Eiss.getD i [])) := by
    intro i hi
    have hiF : i < nF := hrecBnd i hi
    have hspI := denoteSpineP_ihIdx (m := m) (ψ := ψ) (o := n + 1) (l := 0)
      (I := ([] : List Expr)) hop0 hCf hCb hstripC (heisR i hi) hiF hlenT hlenE hlenX rfl
      hidxT hidxX'
    rw [show nP + (n + 1) + nF + 0 - 1 = nP + n + nF from by omega,
      show nP + (n + 1) + nF + 0 = nP + 1 + n + nF from by omega, List.append_nil] at hspI
    unfold Lech.directIhApp ihAppAV
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (e := Expr.const recC (rlps.map .param)) rfl,
      List.map_append, List.map_append, hpremap, List.map_map, List.map_cons, List.map_nil]
    simp only [Function.comp_def]
    rw [denoteP_mkAppN ((hpre.append hspI).append
      (.cons (hbvar (nF - 1 - i) (by omega)) .nil))
      (by rw [denoteP_const hfR (by rw [hlpsR]; simp), hlpsR, Level.substFn_param_self])]
  rw [hcombR]
  unfold Lech.directRuleBodyR fixRuleCoreAV
  rw [Expr.instSeq_mkAppN, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [denoteP_mkAppN
    ((DenoteSpineP.of_map (List.range nF)
        (fun k _ => hbvar (nF - 1 - k) (by omega))).append
      (DenoteSpineP.of_map recIdx (fun i hi => hihApp i hi)))
    (hbvar (nF + n - 1 - j) (by omega))]
  rfl

/-! ## The generated rule -/

set_option maxHeartbeats 3200000 in
/-- **Rule `j` reads to the λ-tower over `fixRuleDataAV`** at
constructor `j`'s data, with the core `minor_j f⃗ ih⃗`. -/
theorem denoteP_directRecRhsR {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx j : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
    (hcr : CtorReadsR m ψ T lps nP nIdx ctors cds)
    {recC : Name} {rlps : List Name} {ciR : ConstantInfo}
    (hfR : env.find? recC = some ciR) (hlpsR : ciR.toConstantVal.levelParams = rlps)
    {tty rhs : Expr}
    (hgen : Lech.directRecRhsR T lps elim large nP nIdx tty ctors recC (rlps.map .param) j
      = some rhs)
    (hTf : tty.hasFvar = false)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {C : Name} {nF : Nat} {ds : List (Nat × Nat × AVExpr)} {Es : List AVExpr}
    {recIdx : List Nat} {Eiss : List (List AVExpr)}
    (hjd : cds[j]? = some (C, nF, ds, Es, recIdx, Eiss)) :
    denoteP m.acval env ψ 0 rhs
      = some (mkLamsAV (fixRuleDataAV m T ψ nP nIdx (Lech.directElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds ds)
          (fixRuleCoreAV (m.acval recC ψ) nP nF cds.length j recIdx Eiss)) := by
  obtain ⟨C₀, nF₀, cty, recIdx₀, tbs, cbs, itele, motiveTy, crest0, inner, minors, hj, hsT,
    hmot, hsC, hinner, hmin, hr⟩ := Lech.directRecRhsR_unfold hgen
  obtain ⟨cd, hjd', hc⟩ := hcr.getElem? hj
  obtain ⟨rfl⟩ := Option.some.inj (hjd'.symm.trans hjd)
  have hC0 : C = C₀ := hc.name
  have hnF0 : nF = nF₀ := hc.nF
  have hrI0 : recIdx = recIdx₀ := hc.recIdx
  subst hC0 hnF0 hrI0
  have hCread := hc.read
  have hlenD : ds.length = nP + nF := hc.len
  have hCb : cty.looseBVarsBounded 0 = true := hc.bounded
  have hCf : cty.hasFvar = false := hc.hasFvar
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := by
    obtain ⟨cbs0, es0, hs0, -⟩ := hc.resid
    rw [hs0]
    rfl
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  have hjn : j < ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  generalize hn : ctors.length = n at hinner hlenC hjn
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hr hmin hinner hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hr hmin hinner ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteP_pisToLamsPw nP hr hopT hTread hst, Nat.zero_add]
  rw [Lech.instSeq_lam tfvs (nP - 1) _ _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteP_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteP_lam, hmotive]
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Lech.directMinorsLamsR lps nP pw ctors [mfv].length inner = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsLamsR hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb
    rwa [Nat.zero_add] at this
  have hinner' := Lech.pisToLamsPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hinner
  have hres := Lech.instSeq_minorTele tfvs extras' hlenT hclT hcb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hinner'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1 + n) hcstrip
  have hcreadN : denoteP m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
          ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)) := by
    have := ctorResidual_read_lift hcread hcw hlenD (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega] at this
  have hstX : stripPisAV nF (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF))
      = some (liftDoms (n + 1) 0 (ds.drop nP),
          (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hinnerR := denoteP_pisToLamsPw (acval := m.acval) (env := env) (φ := ψ) nF hinner' hopX
    hcreadN hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨fvs0, crest00, hop0⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  rw [show nP + 1 + n - 1 + nF = nP + n + nF from by omega,
    denoteP_ruleCoreR hfR hlpsR hop0 hCf hCb hstripC hc.recIdxBnd
      (fun i hi => hc.eisRead i hi fvs0 crest00 hop0) hlenT hlenE' hlenX hidxT hidxE' hidxX hjn,
    Option.map_some] at hinnerR
  rw [hinnerR]
  subst hpw
  rw [← hlenC]
  unfold fixRuleDataAV
  rw [List.map_append, List.map_append, List.map_append, mkLamsAV_append, mkLamsAV_append,
    mkLamsAV_append, rebit_map_lam, rebit_map_lam, hlenC]
  rfl

end Lech.SetP
