module

public import ConLeche.Model.Inductives.ClassGenStep
public import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.ErasureKit
import ConLeche.Verify.Inductives.ScopeKit
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Semantics.DeclRun
import ConLeche.Verify.Abstract
import ConLeche.Semantics.Kit
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Semantics.Tower.SumTower

public section

/-!
# The minor premise's own typing, from the generator (`hminor`, G1-syn)

`genHstep` (`ClassGenStep.lean`) proves the step's typing at the
generated family from the MINOR PREMISE's typing, stated semantically
(`hminor`): a minor applied to fields fitting the rule frame's field
domains and to `ih` values of the `ih` binders' types
(`genIhDomAV`) lands in the motive at the constructor.  Here that
statement is DERIVED from the generator, and so are the rule frame's
components themselves — the field domains, the `ih` data, the
conclusion's index spine and constructor term — as the pieces of the
minor premise's domain in the generated type's reading (finding 3 of
CLASSCHECK / G1-SYN).

The minor sits in the shared prefix at position `mp = nP + s`, so its
domain is read at depth `mp`; the rule frame is at depth `rP` (the whole
prefix).  The reading is peeled at `mp`, where the generator's own
`closeTelescope` lives (so the opened pieces are the annotated raw
pieces, up to erasure), and moved to `rP` by the de Bruijn lift over the
`rP - mp` later prefix binders (`denoteMeta_lift` on the model side is
free: `stripPisAV` of a lifted reading is the lifted pieces).  Three
readings of openings at different depths meet:

* a FIELD domain `k` is read at `mp + k` and lifted at cutoff `k`;
* an `ih` domain `l` is read at `mp + nF + l`, under the `l` earlier
  `ih` binders — but it names no `ih` variable (the generator closes the
  `ih`'s own telescope again, `ClassGen.minorTy_spec`), so its reading is
  the lift by `l` of its reading at `mp + nF`, which is then lifted to
  `rP + nF`: that is `genIhDomAV (rP + nF) mt q` for the `ih` datum `q`
  read off it;
* the CONCLUSION is read at `mp + nF + nIh`, again the lift of its
  reading at `mp + nF` (it names no `ih` variable either).

The binders' bits are never inspected: the generated type's reading is
bit-VALID (`AnnotValid`, the inference claim's currency), and validity
descends the prefix to the minor's domain, whose Π-tower then applies
(`foldl_app_mem_mkPisAV`).  What the components are asked to be for the
chain independence rows (`genHchI_of_readings`, `ihDatumBelow_of_readings`)
is only their `bvarsBelow` bound; the lifted readings have it (they are
not themselves readings of a scoped term at `rP`: the opened pieces at
`rP` are the generator's pieces RENAMED, which the proof never needs).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ClassGen ClassGenScoped ClassCtor ScB closeTelescope
  classGenRecTy classBinder)

universe w

/-! ## De Bruijn bookkeeping on readings -/

/-- **Peeling a lifted reading** peels the reading and lifts the pieces. -/
theorem stripPisAV_liftN_inv (n : Nat) :
    ∀ (m k : Nat) {A : AnnotTerm} {ps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      stripPisAV m (A.liftN n k) = some (ps, b) →
      ∃ ps0 b0, stripPisAV m A = some (ps0, b0) ∧ ps = liftDoms n k ps0 ∧
        b = b0.liftN n (k + m)
  | 0, k, A, ps, b, h => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], A, rfl, rfl, by simp⟩
  | m + 1, k, A, ps, b, h => by
    cases A with
    | pi u v A B =>
      simp only [AnnotTerm.liftN_pi, stripPisAV] at h
      cases hB : stripPisAV m (B.liftN n (k + 1)) with
      | none => rw [hB] at h; exact nomatch h
      | some pb =>
        rw [hB] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨ps', b'⟩ := pb
        obtain ⟨ps0, b0, hs, rfl, rfl⟩ := stripPisAV_liftN_inv n m (k + 1) hB
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨(u, v, A) :: ps0, b0, by simp [stripPisAV, hs], by simp [liftDoms], ?_⟩
        rw [show k + 1 + m = k + (m + 1) by omega]
    | bvar i =>
      simp only [AnnotTerm.liftN_bvar, stripPisAV] at h; exact nomatch h
    | sort u => simp [stripPisAV] at h
    | const c us => simp [stripPisAV] at h
    | app f a => simp [stripPisAV] at h
    | lam v A b => simp [stripPisAV] at h
    | eqE a b => simp [stripPisAV] at h
    | fst e => simp [stripPisAV] at h
    | snd e => simp [stripPisAV] at h
    | prf => simp [stripPisAV] at h

/-- A lifted spine is the lift of a spine. -/
theorem liftN_mkAppN_inv (n k : Nat) :
    ∀ (as : List AnnotTerm) {h b0 : AnnotTerm}, b0.liftN n k = AnnotTerm.mkAppN h as →
      ∃ h0 as0, b0 = AnnotTerm.mkAppN h0 as0 ∧ h0.liftN n k = h ∧
        as = as0.map fun a => a.liftN n k
  | [], h, b0, hb => ⟨b0, [], rfl, hb, rfl⟩
  | a :: as, h, b0, hb => by
    obtain ⟨h1, as0, rfl, hh1, rfl⟩ := liftN_mkAppN_inv n k as (h := .app h a) hb
    cases h1 with
    | app f0 a0 =>
      simp only [AnnotTerm.liftN_app, AnnotTerm.app.injEq] at hh1
      obtain ⟨rfl, rfl⟩ := hh1
      exact ⟨f0, a0 :: as0, rfl, rfl, rfl⟩
    | bvar i => simp at hh1
    | sort u => simp at hh1
    | const c us => simp at hh1
    | lam v A b => simp at hh1
    | pi u v A B => simp at hh1
    | eqE a b => simp at hh1
    | fst e => simp at hh1
    | snd e => simp at hh1
    | prf => simp at hh1

/-- A lifted variable spine above the cutoff is the lift of one. -/
theorem liftN_mkAppN_bvar_inv {n k j : Nat} {as : List AnnotTerm} {b0 : AnnotTerm}
    (hb : b0.liftN n k = AnnotTerm.mkAppN (.bvar j) as) (hj : k + n ≤ j) :
    ∃ as0, b0 = AnnotTerm.mkAppN (.bvar (j - n)) as0 ∧ as = as0.map fun a => a.liftN n k := by
  obtain ⟨h0, as0, rfl, hh, rfl⟩ := liftN_mkAppN_inv n k as hb
  cases h0 with
  | bvar i =>
    simp only [AnnotTerm.liftN_bvar, AnnotTerm.bvar.injEq] at hh
    split at hh
    · omega
    · exact ⟨as0, by rw [show j - n = i by omega], rfl⟩
  | sort u => simp at hh
  | const c us => simp at hh
  | app f a => simp at hh
  | lam v A b => simp at hh
  | pi u v A B => simp at hh
  | eqE a b => simp at hh
  | fst e => simp at hh
  | snd e => simp at hh
  | prf => simp at hh

/-! ## Frames -/

section Frames

variable {V : Type w} [SetTheory V]

/-- **Lifting over the top of the outer spine**: the frame
`ys` over `zs` read through a lift by `n` at `|ys|` is the frame `ys`
over `zs` without its last `n` values. -/
theorem shiftE_consList {n k : Nat} {ys zs : List V} {ρ : Nat → V} (hk : ys.length = k)
    (hn : n ≤ zs.length) :
    shiftE n k (consList ys (consList zs ρ))
      = consList ys (consList (zs.take (zs.length - n)) ρ) := by
  funext i
  simp only [shiftE]
  split
  · rw [consList_getD_of_lt ys _ i (by omega), consList_getD_of_lt ys _ i (by omega)]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + k := ⟨i - k, by omega⟩
    subst hk
    rw [show j + ys.length + n = (j + n) + ys.length by omega, consList_apply_add,
      consList_apply_add]
    have hdl : (zs.drop (zs.length - n)).length = n := by simp; omega
    rw [show consList zs ρ = consList (zs.drop (zs.length - n)) (consList (zs.take (zs.length - n)) ρ)
      by rw [← consList_append, List.take_append_drop]]
    have := consList_apply_add (zs.drop (zs.length - n)) (consList (zs.take (zs.length - n)) ρ) j
    rw [hdl] at this
    exact this

omit [SetTheory V] in
/-- Lifting over a whole spine forgets it. -/
theorem shiftE_zero_consList {n : Nat} {ys : List V} {σ : Nat → V} (hn : ys.length = n) :
    shiftE n 0 (consList ys σ) = σ := by
  funext i
  subst hn
  simp only [shiftE, Nat.not_lt_zero, if_false]
  exact consList_apply_add ys σ i

omit [SetTheory V] in
theorem take_append_of_le {xs ys : List V} {n : Nat} (h : n ≤ xs.length) :
    (xs ++ ys).take n = xs.take n := by
  rw [List.take_append_of_le_length h]

end Frames

/-! ## Validity along a Π-tower -/

section Valid

variable {V : Type w} [SetTheory V]

/-- A valid Π-tower's domains are valid at a fitting spine's prefixes. -/
theorem annotValid_piDom_at {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V},
      AnnotValid V ρ (mkPisAV tl B) → SpineFit ρ (tl.map (·.2.2)) bs →
      ∀ l, l < tl.length →
        AnnotValid V (consList (bs.take l) ρ) ((tl.map (·.2.2)).getD l default)
  | [], _, _, _, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, _, [], _, h, _, _ => h.elim
  | d :: tl, ρ, b :: bs, hv, h, l, hl => by
    have hv' : AnnotValid V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv
    rw [AnnotValid_pi] at hv'
    cases l with
    | zero => simpa using hv'.1
    | succ l =>
      simp only [List.map_cons, List.getD_cons_succ, List.take_succ_cons, consList_cons]
      exact annotValid_piDom_at (hv'.2.1 b h.1) h.2 l (by simpa using hl)

end Valid

/-! ## Bounds of lifted pieces -/

theorem domsBelow_of_getElem? {k : Nat} :
    ∀ {ps : List (Nat × Nat × AnnotTerm)},
      (∀ (i : Nat) (p : Nat × Nat × AnnotTerm), ps[i]? = some p →
        Term.bvarsBelow (k + i) p.2.2.erase) → DomsBelow k ps
  | [], _ => trivial
  | p :: ps, h => by
    refine ⟨by simpa using h 0 p rfl, domsBelow_of_getElem? (k := k + 1) fun i p' hp => ?_⟩
    have := h (i + 1) p' (by simpa using hp)
    rwa [show k + (i + 1) = k + 1 + i by omega] at this

/-- A bounded Π-tower's domains, lifted by `δ`, are bounded `δ` higher. -/
theorem fieldsBelow_liftDoms (δ : Nat) :
    ∀ {k c : Nat} {ps : List (Nat × Nat × AnnotTerm)}, DomsBelow k ps →
      FieldsBelow (k + δ) ((liftDoms δ c ps).map (·.2.2))
  | _, _, [], _ => trivial
  | k, c, p :: ps, h => by
    refine ⟨bvarsBelow_liftN_add h.1 (Nat.le_refl _) c, ?_⟩
    have := fieldsBelow_liftDoms δ (k := k + 1) (c := c + 1) h.2
    rwa [show k + 1 + δ = k + δ + 1 by omega] at this

theorem liftDoms_fst (δ : Nat) :
    ∀ {c : Nat} {ps : List (Nat × Nat × AnnotTerm)}, (∀ p ∈ ps, p.1 = 0) →
      ∀ p ∈ liftDoms δ c ps, p.1 = 0
  | _, [], _, p, hp => nomatch hp
  | c, q :: ps, h, p, hp => by
    simp only [liftDoms, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h q List.mem_cons_self
    · exact liftDoms_fst δ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')) p hp

/-! ## Readings of a variable spine -/

theorem denoteMeta_mkAppN_len {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ (as : List Expr) {f : Expr} {r : AnnotTerm},
      denoteMeta acval env φ d (Expr.mkAppN f as) = some r →
      ∃ fr rs, denoteMeta acval env φ d f = some fr ∧ r = AnnotTerm.mkAppN fr rs ∧
        rs.length = as.length
  | [], f, r, h => ⟨r, [], h, rfl, rfl⟩
  | a :: as, f, r, h => by
    obtain ⟨g, rs, hg, rfl, hl⟩ := denoteMeta_mkAppN_len as (f := .app f a) h
    rw [denoteMeta_app] at hg
    cases hf : denoteMeta acval env φ d f with
    | none => simp [hf] at hg
    | some fr =>
      cases ha : denoteMeta acval env φ d a with
      | none => simp [hf, ha] at hg
      | some ar =>
        simp only [hf, ha, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hg
        subst hg
        exact ⟨fr, ar :: rs, rfl, rfl, by simp [hl]⟩

/-- The reading of a variable applied to a spine. -/
theorem denoteMeta_mkAppN_fvar_inv {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d i : Nat} {T : Expr} {as : List Expr} {r : AnnotTerm}
    (h : denoteMeta acval env φ d (Expr.mkAppN (.fvar i T) as) = some r) :
    ∃ rs, r = AnnotTerm.mkAppN (.bvar (d - 1 - i)) rs ∧ rs.length = as.length := by
  obtain ⟨fr, rs, hfr, rfl, hl⟩ := denoteMeta_mkAppN_len as h
  rw [denoteMeta_fvar] at hfr
  obtain rfl := (Option.some.inj hfr).symm
  exact ⟨rs, rfl, hl⟩

/-- A term erasure-equal to a variable applied to a spine is one. -/
theorem erasedEq_mkAppN_fvar_inv {i : Nat} {T e : Expr} {as : List Expr}
    (h : Expr.ErasedEq e (Expr.mkAppN (.fvar i T) as)) :
    ∃ T' as', e = Expr.mkAppN (.fvar i T') as' ∧ as'.length = as.length := by
  obtain ⟨f', as', rfl, hf', hl⟩ := erasedEq_mkAppN_inv as h
  match f', hf' with
  | .fvar j T', hf => exact ⟨T', as', by rw [show j = i from hf], hl⟩

/-! ## One `ih` domain, and the conclusion -/

section Pieces

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env envK : Env}

set_option maxHeartbeats 1600000 in
/-- **An `ih` binder's domain, read.**  The `l`-th `ih` domain of a minor
premise sits at depth `lo + l` (`lo = mp + nF`: the minor's slot and its
fields), under the `l` earlier `ih` binders, but names no `ih` variable:
its reading is the lift by `l` of a reading `A0` at `lo`.  Lifted by `δ`
over the prefix binders after the minor (cutoff `c` = the fields), `A0`
is the generated `ih` binder type `genIhDomAV (lo + δ) mt q` of an `ih`
datum `q` bounded at the rule's depth. -/
theorem classGenIh_read (m : EnvModel V env) {φ : Name → Nat} {F lo l c δ mt t : Nat}
    {TB : List (Expr × ConLeche.BinderMeta)} {bargs : List Expr} {Y N : Expr} {A : AnnotTerm}
    (hmt : mt + c < lo) (hbne : bargs ≠ [])
    (hTB : ∀ (k : Nat) (nd : Expr × ConLeche.BinderMeta), TB[k]? = some nd →
      ScB (lo + l + k) nd.1)
    (hbody : ScB (lo + l + TB.length) (Expr.mkAppN (.fvar mt (.sort .zero)) bargs))
    (hbelow : Expr.fvarsBelow lo
      (closeTelescope TB (lo + l) (Expr.mkAppN (.fvar mt (.sort .zero)) bargs)))
    (hY : Expr.ErasedEq Y
      (closeTelescope TB (lo + l) (Expr.mkAppN (.fvar mt (.sort .zero)) bargs)))
    (hwY : Expr.WScoped (lo + l) Y)
    (hann : ConLeche.annotateCore μ envK F (lo + l) Y = .ok N)
    (hA : denoteMeta m.acval env φ (lo + l) N = some A) :
    ∃ (A0 : AnnotTerm) (q : IhDatum), A = A0.liftN l 0 ∧ q.1 = t ∧
      genIhDomAV (lo + δ) mt q = A0.liftN δ c ∧ IhDatumBelow (lo + δ) q := by
  have hraw : ScB (lo + l)
      (closeTelescope TB (lo + l) (Expr.mkAppN (.fvar mt (.sort .zero)) bargs)) :=
    ScB.of_closeTelescope hTB hbody
  have hYb : Y.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hY hraw.2
  have hYlo : Expr.WScoped lo Y :=
    ConLeche.WScoped.of_fvarsBelow hwY (erasedEq_fvarsBelow _ _ (ConLeche.Expr.ErasedEq.symm hY)
      hbelow)
  have hwN : Expr.WScoped lo N := ConLeche.annotateCore_WScoped_below hann hwY hYb hYlo
  have hNb : N.looseBVarsBounded 0 = true := ConLeche.annotateCore_looseBVars F Y hann hYb
  -- the reading at `lo`, lifted by `l`
  have hlift := denoteMeta_lift (env := env) (φ := φ) m.acval_closed hwN (lo + l) (by omega)
  rw [hA, show lo + l - lo = l by omega] at hlift
  obtain ⟨A0, hA0, rfl⟩ : ∃ A0, denoteMeta m.acval env φ lo N = some A0 ∧ A = A0.liftN l 0 := by
    cases h0 : denoteMeta m.acval env φ lo N with
    | none => rw [h0] at hlift; exact nomatch hlift
    | some A0 => rw [h0] at hlift; exact ⟨A0, rfl, Option.some.inj hlift⟩
  -- the annotated telescope
  have hTBb : ∀ p ∈ TB, p.1.looseBVarsBounded 0 = true := fun p hp => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    exact (hTB k _ (List.getElem?_eq_getElem hk)).2
  obtain ⟨ndsT, BT', hlT, heN, ⟨BT₀, FT, hBT₀, -, hannBT⟩, hdomsT⟩ :=
    ConLeche.annotateCore_closeTelescope_gen TB hTBb hbody.2 hY hwY hann
  have hndsTb : ∀ p ∈ ndsT, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, F', nd, hnd, hX, -, hann'⟩ := hdomsT k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hTBb nd (List.mem_of_getElem? hnd)))
  have hBT₀b : BT₀.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hBT₀ hbody.2
  have hBT'b : BT'.looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars FT BT₀ hannBT hBT₀b
  obtain ⟨Ts, restT, hopT, hrestT, -⟩ :=
    open_of_erasedEq_closeTelescope ndsT (lo + l) BT' N hndsTb hBT'b heN
  obtain ⟨pps_t, b_t, hst_t, hb_t, -, hpp_t⟩ := denoteMeta_openPis _ hopT hA
  rw [hlT] at hst_t hb_t
  -- the body: the callee's motive variable, applied
  obtain ⟨T₀, as₀, rfl, hl₀⟩ := erasedEq_mkAppN_fvar_inv hBT₀
  obtain ⟨as', rfl, hl'⟩ := ConLeche.annotateCore_mkAppN_fvar hannBT
  rw [denoteMeta_erasedEq hrestT] at hb_t
  obtain ⟨rs, rfl, hlrs⟩ := denoteMeta_mkAppN_fvar_inv hb_t
  -- peel the lift
  obtain ⟨ps0, b0, hs0, rfl, hb0⟩ := stripPisAV_liftN_inv l TB.length 0 hst_t
  obtain ⟨as0, rfl, rfl⟩ := liftN_mkAppN_bvar_inv (n := l) (k := 0 + TB.length) hb0.symm
    (by omega)
  obtain ⟨rfl, hps0l⟩ := stripPisAV_eq_mkPis hs0
  have has0l : as0.length = bargs.length := by simp at hlrs; omega
  -- the domain-sort numerals are `0`
  have hTl : Ts.length = ndsT.length := ConLeche.Verify.openPisAtFvars_length _ hopT
  have hps0z : ∀ p ∈ ps0, p.1 = 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨p', hp', hp'1, -⟩ := hpp_t i (Ts[i]'(by omega)) (List.getElem?_eq_getElem _)
    rw [liftDoms_getElem?, List.getElem?_eq_getElem hi, Option.map_some,
      Option.some.injEq] at hp'
    rw [← hp'] at hp'1
    exact hp'1
  -- bounds
  have hA0B := bvarsBelow_of_reading (m := m) hwN hNb hA0
  obtain ⟨hdoms0, hbody0⟩ := bvarsBelow_mkPisAV_inv hA0B
  rw [AnnotTerm.erase_mkAppN] at hbody0
  obtain ⟨-, has0⟩ := bvarsBelow_mkAppN_inv hbody0
  -- the datum
  obtain ⟨init, last, hil⟩ : ∃ init last,
      as0.map (fun a => a.liftN δ (c + ps0.length)) = init ++ [last] := by
    rcases List.eq_nil_or_concat (as0.map fun a => a.liftN δ (c + ps0.length)) with h | h
    · exfalso
      rw [List.map_eq_nil_iff] at h
      subst h
      exact hbne (List.eq_nil_of_length_eq_zero (by simpa using has0l.symm))
    · obtain ⟨L, b, h⟩ := h
      exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  refine ⟨mkPisAV ps0 (AnnotTerm.mkAppN (.bvar (lo + l + TB.length - 1 - mt - l)) as0),
    (t, (liftDoms δ c ps0).map (fun p => (p.2.1, p.2.2)), init, last), rfl, rfl, ?_, ?_⟩
  · -- the generated `ih` binder type is the lifted reading
    have hmap : ((liftDoms δ c ps0).map (fun p => (p.2.1, p.2.2))).map
        (fun p => ((0 : Nat), p.1, p.2)) = liftDoms δ c ps0 := by
      rw [List.map_map]
      refine (List.map_congr_left fun p hp => ?_).trans (List.map_id _)
      have := liftDoms_fst δ hps0z p hp
      obtain ⟨u, v, A⟩ := p
      simp only at this
      subst this
      rfl
    simp only [genIhDomAV]
    rw [hmap, liftN_mkPisAV δ ps0 _ c, liftN_mkAppN, ← hil, List.length_map, liftDoms_length,
      AnnotTerm.liftN_bvar, if_neg (by omega)]
    congr 2
    rw [hps0l, show lo + δ + TB.length - 1 - mt = lo + l + TB.length - 1 - mt - l + δ by omega]
  · refine ⟨?_, fun e he => ?_⟩
    · rw [List.map_map]
      have := fieldsBelow_liftDoms δ (c := c) hdoms0
      exact this
    · rw [← hil] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      have hb := has0 a.erase (List.mem_map_of_mem ha)
      rw [List.length_map, liftDoms_length]
      exact bvarsBelow_liftN_add hb (by omega) _

set_option maxHeartbeats 800000 in
/-- **The conclusion, read.**  A minor premise's conclusion sits at depth
`lo + n` (`lo = mp + nF`, under the `n` `ih` binders) but names no `ih`
variable: its reading is the lift by `n` of the motive's variable
applied to a nonempty spine of readings bounded at `lo`. -/
theorem classGenConcl_read (m : EnvModel V env) {φ : Name → Nat} {F lo n mc : Nat}
    {cargs : List Expr} {B₀ B' : Expr} {b : AnnotTerm} (hcne : cargs ≠ [])
    (hraw : ScB lo (Expr.mkAppN (.fvar mc (.sort .zero)) cargs))
    (hB₀ : Expr.ErasedEq B₀ (Expr.mkAppN (.fvar mc (.sort .zero)) cargs))
    (hwB₀ : Expr.WScoped (lo + n) B₀)
    (hann : ConLeche.annotateCore μ envK F (lo + n) B₀ = .ok B')
    (hb : denoteMeta m.acval env φ (lo + n) B' = some b) :
    ∃ rs : List AnnotTerm, b = (AnnotTerm.mkAppN (.bvar (lo - 1 - mc)) rs).liftN n 0 ∧
      rs ≠ [] ∧ ∀ a ∈ rs, Term.bvarsBelow lo a.erase := by
  have hB₀b : B₀.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hB₀ hraw.2
  have hB₀lo : Expr.WScoped lo B₀ :=
    ConLeche.WScoped.of_fvarsBelow hwB₀ (erasedEq_fvarsBelow _ _
      (ConLeche.Expr.ErasedEq.symm hB₀) hraw.1.fvarsBelow)
  have hwB' : Expr.WScoped lo B' := ConLeche.annotateCore_WScoped_below hann hwB₀ hB₀b hB₀lo
  have hB'b : B'.looseBVarsBounded 0 = true := ConLeche.annotateCore_looseBVars F B₀ hann hB₀b
  have hlift := denoteMeta_lift (env := env) (φ := φ) m.acval_closed hwB' (lo + n) (by omega)
  rw [hb, show lo + n - lo = n by omega] at hlift
  obtain ⟨bD, hbD, rfl⟩ : ∃ bD, denoteMeta m.acval env φ lo B' = some bD ∧ b = bD.liftN n 0 := by
    cases h0 : denoteMeta m.acval env φ lo B' with
    | none => rw [h0] at hlift; exact nomatch hlift
    | some bD => rw [h0] at hlift; exact ⟨bD, rfl, Option.some.inj hlift⟩
  have hbB := bvarsBelow_of_reading (m := m) hwB' hB'b hbD
  obtain ⟨T₀, as₀, rfl, hl₀⟩ := erasedEq_mkAppN_fvar_inv hB₀
  obtain ⟨as', rfl, hl'⟩ := ConLeche.annotateCore_mkAppN_fvar hann
  obtain ⟨rs, rfl, hlrs⟩ := denoteMeta_mkAppN_fvar_inv hbD
  rw [AnnotTerm.erase_mkAppN] at hbB
  obtain ⟨-, hrs⟩ := bvarsBelow_mkAppN_inv hbB
  refine ⟨rs, rfl, fun h => hcne ?_, fun a ha => hrs a.erase (List.mem_map_of_mem ha)⟩
  subst h
  exact List.eq_nil_of_length_eq_zero (by simp at hlrs; omega)

end Pieces

/-! ## The prefix's bound -/

theorem fieldsBelow_take_of_domsBelow :
    ∀ (n : Nat) {k : Nat} {ps : List (Nat × Nat × AnnotTerm)}, DomsBelow k ps →
      FieldsBelow k ((ps.take n).map (·.2.2))
  | 0, _, _, _ => by simp [FieldsBelow]
  | _ + 1, _, [], _ => by simp [FieldsBelow]
  | n + 1, k, p :: ps, h => ⟨h.1, fieldsBelow_take_of_domsBelow n h.2⟩

section Prefix

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env envK : Env}

/-- **The shared prefix's domains are bounded at their positions** (the
`hP` rows of `genHchI_of_below`): the generated type is closed, so its
reading names no variable, and neither does any of its domains beyond
the binders before it. -/
theorem classGenRecTy_prefix_below (m : EnvModel V env) {φ : Name → Nat} {g : ClassGen}
    (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {F : Nat}
    {gty gtyA : Expr} {ea : AnnotTerm}
    (hgty : classGenRecTy g c = some gty)
    (hann : ConLeche.annotateCore μ envK F 0 gty = .ok gtyA)
    (hread : denoteMeta m.acval env φ 0 gtyA = some ea)
    {n : Nat} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    (hst : stripPisAV n ea = some (pps, b)) (k : Nat) :
    FieldsBelow 0 ((pps.take k).map (·.2.2)) := by
  have hclosed := ConLeche.classGenRecTy_closed hg hm hgty
  have hgA := annotate_syntax hann hclosed.1 hclosed.2
  have hB := bvarsBelow_of_reading (m := m) (Expr.WScoped.of_not_hasFvar hgA.1) hgA.2 hread
  rw [(stripPisAV_eq_mkPis hst).1] at hB
  exact fieldsBelow_take_of_domsBelow k (bvarsBelow_mkPisAV_inv hB).1

end Prefix

/-! ## The minor premise's typing -/

/-- The prefix position of class `t`'s motive. -/
@[expose] def classMotPos (g : ClassGen) (t : Nat) : Nat :=
  g.nP + (ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ t).getD 0

section Minor

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env envK : Env}

set_option maxHeartbeats 6400000 in
/-- **`hminor`, from the generator.**  Read the generated recursor type
of any class `c` (annotated, read, peeled to its binder data `pps`); the
minor premise at slot `sm` (class `cm`, constructor `x`) sits in the
shared prefix at `mp = nP + sm`.  Its domain's pieces, moved to the rule
frame's depth `rP` (the whole prefix), are the rule frame's components:
the field domains `fd`, the `ih` data `ihd` (callees the constructor's
recursive fields' classes), the conclusion's index spine `es` and
constructor term `mk` — each bounded at its depth (the chain
independence rows' premises), and the minor premise's own typing holds
over them in exactly the form `genHstep` consumes: at every prefix
spine fitting the shared prefix, fields fitting `fd` and `ih` values of
the generated `ih` binder types, the minor applied to the fields and the
`ih` values lands in the motive of `cm` at `es` and `mk`.  The one
semantic premise is the reading's bit validity (`hval`, the inference
claim's `AnnotValid` half). -/
theorem classGenMinor_read (m : EnvModel V env) {φ : Name → Nat} {g : ClassGen}
    (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {F : Nat}
    {gty gtyA : Expr} {ea : AnnotTerm}
    (hgty : classGenRecTy g c = some gty)
    (hann : ConLeche.annotateCore μ envK F 0 gty = .ok gtyA)
    (hread : denoteMeta m.acval env φ 0 gtyA = some ea)
    {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    (hst : stripPisAV (g.pre.length + (g.cls.getD c default).nIdx + 1) ea = some (pps, b))
    (hval : ∀ ρ : Nat → V, AnnotValid V ρ ea)
    {sm cm : Nat} {C : Name} {ihs0 : List (Nat × Nat)}
    (hsl : g.slots[sm]? = some (.minor cm C ihs0)) :
    ∃ (x : ClassCtor) (fd : List AnnotTerm) (ihd : List IhDatum) (es : List AnnotTerm)
      (mk : AnnotTerm),
      (g.ctors.getD cm []).find? (·.cv.name == C) = some x ∧
      fd.length = x.nF ∧ ihd.length = x.recs.length ∧
      classMotPos g cm < g.nP + sm ∧
      (∀ (l : Nat) (q : IhDatum), ihd[l]? = some q →
        (∃ i tele, x.recs.getD l default = (i, q.1, tele)) ∧ classMotPos g q.1 < g.nP + sm) ∧
      FieldsBelow g.pre.length fd ∧
      (∀ e ∈ es, Term.bvarsBelow (g.pre.length + x.nF) e.erase) ∧
      Term.bvarsBelow (g.pre.length + x.nF) mk.erase ∧
      (∀ q ∈ ihd, IhDatumBelow (g.pre.length + x.nF) q) ∧
      ∀ (ρ : Nat → V) (xs : List V), SpineFit ρ ((pps.take g.pre.length).map (·.2.2)) xs →
      ∀ fs : List V, SpineFit (consList xs ρ) fd fs →
      ∀ hs : List V, hs.length = ihd.length →
      (∀ (l : Nat) (q : IhDatum) (h : V), ihd[l]? = some q → hs[l]? = some h →
        h ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV (g.pre.length + fd.length) (classMotPos g q.1) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + sm) pt)
        ∈ˢ (es.map (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ) mk]).foldl SetTheory.app
            (xs.getD (classMotPos g cm) pt) := by
  obtain ⟨hpl, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  obtain ⟨x, T, hxf, hT, hpreT⟩ := ConLeche.ClassGen.prefixBinders_minor hg hsl
  have hxm := List.mem_of_find?_eq_some hxf
  have hxC : x.cv.name = C := by simpa using List.find?_some hxf
  obtain ⟨FB, IB, cargs, sc, rfl, hFBl, hIBl, hscB, hmc, hsc, hcne, hconclS, hih⟩ :=
    ConLeche.ClassGen.minorTy_spec hg hsl hxm hxC hT
  have hslen : sm < g.slots.length := (List.getElem?_eq_some_iff.mp hsl).1
  have hmcP : classMotPos g cm = g.nP + sc := by simp [classMotPos, hmc]
  -- the generated type, annotated and opened
  have hclosed := ConLeche.classGenRecTy_closed hg hm hgty
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  generalize hnds : g.pre ++ ifs.map classBinder ++ [(maj, (default : ConLeche.BinderMeta))]
    = nds at hann hcl hclosed
  generalize hbody : Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])
    = body at hann hbb hclosed
  have hn : nds.length = g.pre.length + (g.cls.getD c default).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_append, List.length_map, List.length_singleton, hifl]
  have hw0 : Expr.WScoped 0 (closeTelescope nds 0 body) :=
    Expr.WScoped.of_not_hasFvar hclosed.1
  obtain ⟨nds', B', hl', he', ⟨B₀g, F₀g, hB₀g, -, hannBg⟩, hdoms⟩ :=
    ConLeche.annotateCore_closeTelescope_gen nds hcl hbb (ConLeche.Expr.ErasedEq.rfl _) hw0 hann
  have hcl' : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, F', nd, hnd, hX, -, hann'⟩ := hdoms k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hcl nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F₀g B₀g hannBg (looseBVarsBounded_of_erasedEq hB₀g hbb)
  obtain ⟨fvs, o, hop, -, hxs⟩ := open_of_erasedEq_closeTelescope nds' 0 B' gtyA hcl' hB'b he'
  rw [hl', hn] at hop
  obtain ⟨pps', b', hst', -, -, hpp'⟩ := denoteMeta_openPis _ hop hread
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hst'))
  have hgA := annotate_syntax hann hclosed.1 hclosed.2
  obtain ⟨hfvl, hfvs, -⟩ := ScB.openPis hop ⟨Expr.WScoped.of_not_hasFvar hgA.1, hgA.2⟩
  -- the minor's slot
  have hmpP : g.nP + sm < g.pre.length := by omega
  have hndmp : nds[g.nP + sm]? = some (closeTelescope (FB ++ IB) (g.nP + sm)
      (Expr.mkAppN (.fvar (g.nP + sc) (.sort .zero)) cargs), default) := by
    rw [← hnds, List.append_assoc, List.getElem?_append_left hmpP]; exact hpreT
  have hk' : g.nP + sm < nds'.length := by rw [hl', hn]; omega
  obtain ⟨X, FX, nd, hnd, hX, hwX, hannX⟩ := hdoms (g.nP + sm) _ (List.getElem?_eq_getElem hk')
  rw [hndmp] at hnd
  obtain rfl := (Option.some.inj hnd).symm
  simp only [Nat.zero_add] at hX hwX hannX
  have hfmp : g.nP + sm < fvs.length := by omega
  obtain ⟨tyM, hfe, hScM⟩ := hfvs (g.nP + sm) _ (List.getElem?_eq_getElem hfmp)
  obtain ⟨pM, hpM, -, hMm⟩ := hpp' (g.nP + sm) _ (List.getElem?_eq_getElem hfmp)
  have hMoE : Expr.ErasedEq fvs[g.nP + sm].fvarTypeD nds'[g.nP + sm].1 :=
    hxs (g.nP + sm) _ _ (List.getElem?_eq_getElem hfmp) (by simp [List.getElem?_eq_getElem hk'])
  rw [hfe] at hMoE hMm
  simp only [Expr.fvarTypeD, Nat.zero_add] at hMoE hMm hScM
  -- the minor's domain, annotated: the telescope of the annotated pieces
  have hFIb : ∀ p ∈ FB ++ IB, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    exact (hscB k _ (List.getElem?_eq_getElem hk)).2
  obtain ⟨nds'', B'', hl'', he'', ⟨B₀, F₀, hB₀, hwB₀, hannB⟩, hdoms''⟩ :=
    ConLeche.annotateCore_closeTelescope_gen (FB ++ IB) hFIb hconclS.2 hX hwX hannX
  have hcl'' : ∀ p ∈ nds'', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X', F', nd, hnd, hX', -, hann'⟩ := hdoms'' k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars F' X' hann'
      (looseBVarsBounded_of_erasedEq hX' (hFIb nd (List.mem_of_getElem? hnd)))
  have hB''b : B''.looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F₀ B₀ hannB (looseBVarsBounded_of_erasedEq hB₀ hconclS.2)
  obtain ⟨Zs, rest, hopM, hrest, hZs⟩ :=
    open_of_erasedEq_closeTelescope nds'' (g.nP + sm) B'' tyM hcl'' hB''b (hMoE.trans he'')
  rw [hl''] at hopM
  obtain ⟨pm, bm, hstm, hbm, hlm, hppm⟩ := denoteMeta_openPis _ hopM hMm
  obtain ⟨hZl, hZs', -⟩ := ScB.openPis hopM hScM
  -- abbreviations
  have hnF : FB.length = x.nF := hFBl
  generalize hmpd : g.nP + sm = mp at *
  generalize hrPd : g.pre.length = rP at *
  generalize hδ : rP - mp = δ
  have hFIl : (FB ++ IB).length = x.nF + IB.length := by simp [hFBl]
  -- the conclusion
  rw [denoteMeta_erasedEq hrest, hFIl, ← Nat.add_assoc] at hbm
  rw [hFIl, ← Nat.add_assoc] at hwB₀ hannB
  obtain ⟨rs, rfl, hrsne, hrsB⟩ := classGenConcl_read m (lo := mp + x.nF) (n := IB.length) hcne
    hconclS hB₀ hwB₀ hannB hbm
  obtain ⟨esL, mkT, hesmk⟩ : ∃ esL mkT,
      rs.map (fun a => a.liftN δ x.nF) = esL ++ [mkT] := by
    rcases List.eq_nil_or_concat (rs.map fun a => a.liftN δ x.nF) with h | h
    · exact absurd (List.map_eq_nil_iff.mp h) hrsne
    · obtain ⟨L, b, h⟩ := h
      exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  -- the `ih` domains
  have hihR : ∀ l, ∃ (q : IhDatum) (A0 : AnnotTerm), l < IB.length →
      (pm[x.nF + l]?).map (·.2.2) = some (A0.liftN l 0) ∧
      (∃ i tele, x.recs.getD l default = (i, q.1, tele)) ∧ classMotPos g q.1 < mp ∧
      genIhDomAV (mp + x.nF + δ) (classMotPos g q.1) q = A0.liftN δ x.nF ∧
      IhDatumBelow (mp + x.nF + δ) q := by
    intro l
    by_cases hl : l < IB.length
    · obtain ⟨i, t, tele, st, TB, bargs, hrec, hmt, hst, hbne, hIB, hTB, hbodyT, hbelowT⟩ :=
        hih l hl
      have hkl : x.nF + l < nds''.length := by rw [hl'']; simp [hFBl]; omega
      obtain ⟨Y, FY, ndY, hndY, hYE, hwY, hannY⟩ :=
        hdoms'' (x.nF + l) _ (List.getElem?_eq_getElem hkl)
      rw [List.getElem?_append_right (by omega), hFBl, Nat.add_sub_cancel_left, hIB] at hndY
      obtain rfl := (Option.some.inj hndY).symm
      have hZk : x.nF + l < Zs.length := by rw [hZl]; simp [hFBl]; omega
      obtain ⟨p, hp, -, hpd⟩ := hppm (x.nF + l) _ (List.getElem?_eq_getElem hZk)
      rw [denoteMeta_erasedEq (hZs _ _ nds''[x.nF + l].1 (List.getElem?_eq_getElem hZk)
        (by simp [List.getElem?_eq_getElem hkl]))] at hpd
      rw [← Nat.add_assoc] at hpd hwY hannY
      obtain ⟨A0, q, hA0, hq1, hgen, hqb⟩ := classGenIh_read m (lo := mp + x.nF) (l := l)
        (c := x.nF) (δ := δ) (mt := g.nP + st) (t := t) (by omega) hbne hTB hbodyT hbelowT hYE hwY
        hannY hpd
      have hmtP : classMotPos g t = g.nP + st := by simp [classMotPos, hmt]
      refine ⟨q, A0, fun _ => ⟨by rw [hp, Option.map_some, hA0], ⟨i, tele, by rw [hq1]; exact hrec⟩,
        by rw [hq1, hmtP]; omega, by rw [hq1, hmtP]; exact hgen, hqb⟩⟩
    · exact ⟨default, default, fun h => absurd h hl⟩
  obtain ⟨fq, hfq⟩ : ∃ fq : Nat → IhDatum × AnnotTerm, ∀ l, l < IB.length →
      (pm[x.nF + l]?).map (·.2.2) = some ((fq l).2.liftN l 0) ∧
      (∃ i tele, x.recs.getD l default = (i, (fq l).1.1, tele)) ∧
      classMotPos g (fq l).1.1 < mp ∧
      genIhDomAV (mp + x.nF + δ) (classMotPos g (fq l).1.1) (fq l).1 = (fq l).2.liftN δ x.nF ∧
      IhDatumBelow (mp + x.nF + δ) (fq l).1 :=
    ⟨fun l => (Classical.choose (hihR l), Classical.choose (Classical.choose_spec (hihR l))),
      fun l => Classical.choose_spec (Classical.choose_spec (hihR l))⟩
  -- the field domains
  have hfdB : ∀ (i : Nat) (p : Nat × Nat × AnnotTerm), (pm.take x.nF)[i]? = some p →
      Term.bvarsBelow (mp + i) p.2.2.erase := by
    intro i p hp
    rw [List.getElem?_take] at hp
    split at hp
    · have hiZ : i < Zs.length := by
        have := (List.getElem?_eq_some_iff.mp hp).1
        rw [hlm] at this; rw [hZl]; exact this
      obtain ⟨p', hp', -, hpd⟩ := hppm i _ (List.getElem?_eq_getElem hiZ)
      rw [hp] at hp'
      obtain rfl := Option.some.inj hp'
      obtain ⟨ty, hze, hty⟩ := hZs' i _ (List.getElem?_eq_getElem hiZ)
      rw [hze] at hpd
      simp only [Expr.fvarTypeD] at hpd
      exact bvarsBelow_of_reading (m := m) hty.1 hty.2 hpd
    · exact nomatch hp
  have hpmL : pm.length = x.nF + IB.length := by rw [hlm, hFIl]
  have hmpr : mp ≤ rP := by omega
  refine ⟨x, (liftDoms δ 0 (pm.take x.nF)).map (·.2.2),
    (List.range IB.length).map fun l => (fq l).1, esL, mkT, hxf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [liftDoms_length, hpmL]
  · simp [hIBl]
  · rw [hmcP, ← hmpd]; omega
  · intro l q hq
    simp only [List.getElem?_map] at hq
    by_cases hl : l < IB.length
    · rw [List.getElem?_range hl, Option.map_some, Option.some.injEq] at hq
      subst hq
      obtain ⟨-, hrec, hmot, -, -⟩ := hfq l hl
      exact ⟨hrec, hmot⟩
    · rw [List.getElem?_eq_none (by simpa using hl)] at hq
      exact nomatch hq
  · have := fieldsBelow_liftDoms δ (k := mp) (c := 0) (domsBelow_of_getElem? hfdB)
    rwa [show mp + δ = rP by omega] at this
  · intro e he
    have he' : e ∈ rs.map fun a => a.liftN δ x.nF := by
      rw [hesmk]; exact List.mem_append_left _ he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he'
    exact bvarsBelow_liftN_add (hrsB a ha) (by omega) _
  · have he' : mkT ∈ rs.map fun a => a.liftN δ x.nF := by
      rw [hesmk]; exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨a, ha, he⟩ := List.mem_map.mp he'
    rw [← he]
    exact bvarsBelow_liftN_add (hrsB a ha) (by omega) _
  · intro q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    have := (hfq l (List.mem_range.mp hl)).2.2.2.2
    rwa [show mp + x.nF + δ = rP + x.nF by omega] at this
  · intro ρ xs hxs fs hfs hs hhl hhs
    have hppsl : pps.length = rP + (g.cls.getD c default).nIdx + 1 :=
      (stripPisAV_eq_mkPis hst).2
    have hxl : xs.length = rP := by
      rw [hxs.length_eq, List.length_map, List.length_take]; omega
    have hfl : fs.length = x.nF := by
      rw [hfs.length_eq, List.length_map, liftDoms_length, List.length_take]; omega
    have hfdl : ((liftDoms δ 0 (pm.take x.nF)).map (·.2.2)).length = x.nF := by
      rw [List.length_map, liftDoms_length, List.length_take]; omega
    have hhl' : hs.length = IB.length := by rw [hhl]; simp
    -- the frames
    have hsh : ∀ ys : List V, shiftE δ ys.length (consList ys (consList xs ρ))
        = consList ys (consList (xs.take mp) ρ) := by
      intro ys
      rw [shiftE_consList rfl (by omega), show xs.length - δ = mp by omega]
    -- the minor's value lies in its domain, which is valid there
    have hmpl : mp < ((pps.take rP).map (·.2.2)).length := by
      simp only [List.length_map, List.length_take]; omega
    have hgetM : ((pps.take rP).map (·.2.2)).getD mp default = pM.2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, if_pos (by omega),
        hpM]
      rfl
    have hmem := FixKI.spineFit_getD_mem' hxs hmpl
    rw [hgetM] at hmem
    have hea := (stripPisAV_eq_mkPis hst).1
    have hv := hval ρ
    rw [hea, ← List.take_append_drop rP pps, mkPisAV_append'] at hv
    have hvM := annotValid_piDom_at hv hxs mp (by simpa using hmpl)
    rw [hgetM] at hvM
    obtain ⟨hMeq, -⟩ := stripPisAV_eq_mkPis hstm
    rw [hMeq] at hmem hvM
    -- the fields and the `ih` values fit the minor's domain
    have hfit : SpineFit (consList (xs.take mp) ρ) (pm.map (·.2.2)) (fs ++ hs) := by
      refine spineFit_of_getD (by simp [hfl, hhl', hpmL]) fun r hr => ?_
      rw [List.length_map] at hr
      rcases Nat.lt_or_ge r x.nF with hrF | hrF
      · -- a field
        have hfr := FixKI.spineFit_getD_mem' hfs (l := r) (by rw [hfdl]; exact hrF)
        have hpr : r < pm.length := by omega
        have hfdr : ((liftDoms δ 0 (pm.take x.nF)).map (·.2.2)).getD r default
            = (pm[r].2.2).liftN δ r := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, liftDoms_getElem?,
            List.getElem?_take, if_pos hrF, List.getElem?_eq_getElem hpr]
          simp
        have hsh' : shiftE δ r (consList (fs.take r) (consList xs ρ))
            = consList (fs.take r) (consList (xs.take mp) ρ) := by
          have := hsh (fs.take r)
          rwa [List.length_take, Nat.min_eq_left (by omega)] at this
        rw [hfdr, interp_liftN, hsh'] at hfr
        have hL : (fs ++ hs).getD r pt = fs.getD r pt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD]
        have hD : (pm.map (·.2.2)).getD r default = pm[r].2.2 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hpr]; rfl
        rw [hL, take_append_of_le (by omega), hD]
        exact hfr
      · -- an `ih` value
        obtain ⟨l, rfl⟩ : ∃ l, r = x.nF + l := ⟨r - x.nF, by omega⟩
        have hl : l < IB.length := by omega
        obtain ⟨hpmr, -, -, hgen, -⟩ := hfq l hl
        have hq : ((List.range IB.length).map fun l => (fq l).1)[l]? = some (fq l).1 := by
          simp [hl]
        have hhsl : hs[l]? = some (hs.getD l pt) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        have hh := hhs l _ _ hq hhsl
        rw [hfdl, show rP + x.nF = mp + x.nF + δ by omega, hgen, consList_append,
          interp_liftN, ← hfl, hsh] at hh
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hfl,
          Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
        rw [List.take_append, List.take_of_length_le (by omega), hfl,
          Nat.add_sub_cancel_left, consList_append]
        have hget : (pm.map (·.2.2)).getD (x.nF + l) default = (fq l).2.liftN l 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hpmr]; rfl
        rw [hget, interp_liftN, shiftE_zero_consList (by simp; omega)]
        exact hh
    have happ := foldl_app_mem_mkPisAV hvM hfit hmem
    -- the conclusion
    rw [interp_liftN, consList_append, shiftE_zero_consList hhl', interp_mkAppN,
      ← List.foldl_map (f := interp V (consList fs (consList (xs.take mp) ρ)))
        (g := SetTheory.app)] at happ
    have hhd : interp V (consList fs (consList (xs.take mp) ρ))
        (.bvar (mp + x.nF - 1 - (g.nP + sc))) = xs.getD (classMotPos g cm) pt := by
      show consList fs (consList (xs.take mp) ρ) _ = _
      have hmcl : g.nP + sc < (xs.take mp).length := by simp; omega
      rw [← consList_append, show mp + x.nF - 1 - (g.nP + sc)
        = fs.length + (xs.take mp).length - 1 - (g.nP + sc) by simp; omega,
        consList_prefix_getD hmcl, hmcP, List.getD_eq_getElem?_getD, List.getElem?_take,
        if_pos (by omega), ← List.getD_eq_getElem?_getD]
    have hargs : rs.map (interp V (consList fs (consList (xs.take mp) ρ)))
        = (esL ++ [mkT]).map (interp V (consList (xs ++ fs) ρ)) := by
      rw [← hesmk, List.map_map]
      refine List.map_congr_left fun a _ => ?_
      simp only [Function.comp]
      rw [consList_append, interp_liftN, ← hfl, hsh]
    rw [hhd, hargs, List.map_append] at happ
    simpa using happ
end Minor

end ConLeche.Model
