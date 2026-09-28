module

public import ConLeche.Model.Inductives.ClassGenStep
public import ConLeche.Model.Inductives.ClassGenRead
public import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Model.Inductives.NestPosOut
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
import ConLeche.Verify.Leaves
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

end ConLeche.Model
