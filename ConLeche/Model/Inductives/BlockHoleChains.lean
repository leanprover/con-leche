module

import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.BlockHoleValid
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.StructFrameKit

public section

/-!
# The hole chains, closed below the operator's frame

The walk-free half of the grading facts (the positivity run's half —
`blockHoleGrade_of_run`, `blockRunLink` — is `BlockHoleGrade.lean`):
hereditary facts from per-prefix ones
(`fieldsOkB_of_prefix`, `fieldsValid_of_prefix`), a Π-tower's domains
graded along it (`wellDenotedV_mkPisAV_dom`), the hole chains closed
below the operator's frame (`blockHoleChains_facts`) and their
congruences, and a graded closed telescope's prefix (`teleTake_ok`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  BlockParts BlockShape instPisWith nestAbstract nestHoles openPisAtFvars fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Hereditary facts from per-prefix ones -/

/-- A field list is hereditarily graded (`FieldsOkB`) when each field
is graded, and bounded at a nonzero universe, at every fitting prefix. -/
theorem fieldsOkB_of_prefix {w : Nat} :
    ∀ (Fs : List AnnotTerm) (σ : Nat → V),
      (∀ i, i < Fs.length → ∀ as : List V, SpineFit σ (Fs.take i) as →
        WellDenoted V (consList as σ) (Fs.getD i default) ∧
        (w ≠ 0 → interp V (consList as σ) (Fs.getD i default) ∈ˢ (univ w : V))) →
      FieldsOkB w σ Fs
  | [], _, _ => trivial
  | F :: Fs, σ, h => by
    have h0 := h 0 (by simp) [] trivial
    refine ⟨h0.1, h0.2, fun a ha => fieldsOkB_of_prefix Fs (cons a σ) fun i hi as has => ?_⟩
    exact h (i + 1) (by simp; omega) (a :: as) ⟨ha, has⟩

/-- A field list is hereditarily bit-valid when each field is, at every
fitting prefix. -/
theorem fieldsValid_of_prefix :
    ∀ (Fs : List AnnotTerm) (σ : Nat → V),
      (∀ i, i < Fs.length → ∀ as : List V, SpineFit σ (Fs.take i) as →
        AnnotValid V (consList as σ) (Fs.getD i default)) →
      FieldsValid σ Fs
  | [], _, _ => trivial
  | F :: Fs, σ, h => by
    refine ⟨h 0 (by simp) [] trivial, fun a ha => fieldsValid_of_prefix Fs (cons a σ)
      fun i hi as has => ?_⟩
    exact h (i + 1) (by simp; omega) (a :: as) ⟨ha, has⟩

/-- A Π-tower's domains are graded along it. -/
theorem wellDenotedV_mkPisAV_dom :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {Δa : List AnnotTerm} {B : AnnotTerm},
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (mkPisAV ab B)) →
      ∀ (i : Nat) (x : Nat × Nat × AnnotTerm), ab[i]? = some x →
      ∀ ρ : Nat → V, Sat V (((ab.take i).map (·.2.2)).reverse ++ Δa) ρ →
        WellDenotedV V ρ x.2.2
  | [], _, _, _, i, x, hx, _, _ => by simp at hx
  | y :: ab, Δa, B, h, 0, x, hx, ρ, hρ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact (Rules.WellDenotedV.hoist_pi (V := V) h).1 ρ (by simpa using hρ)
  | y :: ab, Δa, B, h, i + 1, x, hx, ρ, hρ => by
    simp only [List.getElem?_cons_succ] at hx
    refine wellDenotedV_mkPisAV_dom (Rules.WellDenotedV.hoist_pi (V := V) h).2 i x hx ρ ?_
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ

/-! ## The hole chains are closed below the operator's frame -/

omit [SetTheory V] in
/-- A parallel substitution at the cut `k` keeps a term below `k + b`
when it was below `k + n` and every substituted term is below `b`. -/
theorem bvarsBelow_substAV (τ : Nat → AnnotTerm) {n b : Nat}
    (hτ : ∀ j, j < n → Term.bvarsBelow b (τ j).erase) :
    ∀ (e : AnnotTerm) (k : Nat), Term.bvarsBelow (k + n) e.erase →
      Term.bvarsBelow (k + b) (AnnotTerm.substAV τ e k).erase := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [AnnotTerm.substAV, AnnotTerm.erase_bvar, Term.bvarsBelow] at h ⊢
    split
    · simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN k (τ (i - k)).erase b 0 (hτ _ (by omega))
      rwa [Nat.add_comm b k] at this
  | sort u => intro _ _; trivial
  | const c us => intro _ _; trivial
  | prf => intro _ _; trivial
  | app f a ihf iha =>
    intro k h
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam u A b' ihA ihb =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have := ihb (k + 1) (by rw [show k + 1 + n = k + n + 1 by omega]; exact h.2)
    rwa [show k + 1 + b = k + b + 1 by omega] at this
  | pi u v A B ihA ihB =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have := ihB (k + 1) (by rw [show k + 1 + n = k + n + 1 by omega]; exact h.2)
    rwa [show k + 1 + b = k + b + 1 by omega] at this
  | eqE a b' iha ihb =>
    intro k h
    exact ⟨iha k h.1, ihb k h.2⟩
  | fst e ih => intro k h; exact ih k h
  | snd e ih => intro k h; exact ih k h

omit [SetTheory V] in
/-- The hole substitution sends the holes and the parameters below the
operator's frame `(t, Y, parameters)`. -/
theorem holeTau_below {k nP : Nat} {H : Nat → AnnotTerm}
    (hH : ∀ m, m < k → Term.bvarsBelow (nP + 2) (H m).erase) :
    ∀ j, j < k + nP → Term.bvarsBelow (nP + 2) (holeTau k H j).erase := by
  intro j hj
  unfold holeTau
  split
  · exact hH _ (by omega)
  · simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega

omit [SetTheory V] in
/-- A constructor's fields with holes, as chain entries, are closed below
the operator's frame. -/
theorem fieldsBelow_holeEntsAV {k nP : Nat} {H : Nat → AnnotTerm}
    (hH : ∀ m, m < k → Term.bvarsBelow (nP + 2) (H m).erase) :
    ∀ (Fs : List AnnotTerm) (i : Nat), FieldsBelow (i + (k + nP)) Fs →
      FieldsBelow (nP + 2 + i) (holeEntsAV k H i Fs)
  | [], _, _ => trivial
  | F :: Fs, i, hF => by
    refine ⟨?_, ?_⟩
    · have := bvarsBelow_substAV (holeTau k H) (holeTau_below hH) F i hF.1
      rwa [Nat.add_comm i (nP + 2)] at this
    · have := fieldsBelow_holeEntsAV hH Fs (i + 1)
        (by rw [show i + 1 + (k + nP) = i + (k + nP) + 1 by omega]; exact hF.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 by omega] at this

omit [SetTheory V] in
/-- A field chain gives λ-domains at any annotation. -/
theorem lamDomsBelow_map {v : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs → LamDomsBelow k (Fs.map (v, ·))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, lamDomsBelow_map h.2⟩

omit [SetTheory V] in
/-- **A member's hole term is closed below the operator's frame**, from
its parameter telescope closed and its index telescope below the
parameters. -/
theorem holeTmAV_below {u m nP : Nat} {Ps Is : List AnnotTerm} (hPlen : Ps.length = nP)
    (hP : FieldsBelow 0 Ps) (hI : FieldsBelow nP Is) :
    Term.bvarsBelow (nP + 2) (holeTmAV u m Ps Is).erase := by
  subst hPlen
  unfold holeTmAV
  have hP' : FieldsBelow (Ps.length + 2) (liftFields (Ps.length + 2) 0 Ps) := by
    have := FieldsBelow_liftFields (n := Ps.length + 2) (Nat.le_refl 0) hP
    rwa [Nat.zero_add] at this
  have hI' : FieldsBelow (Ps.length + 2 + Ps.length) (liftFields (Ps.length + 2) 0 Is) := by
    have := FieldsBelow_liftFields (n := Ps.length + 2) (Nat.zero_le Ps.length) hI
    rwa [show Ps.length + (Ps.length + 2) = Ps.length + 2 + Ps.length by omega] at this
  refine mkLamsAV_below (lamDomsBelow_map (fieldsBelow_append hP' ?_)) ?_
  · rw [liftFields_length]; exact hI'
  · simp only [List.length_map, List.length_append, liftFields_length,
      AnnotTerm.erase_app, Term.bvarsBelow]
    refine ⟨projAV_below (by simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega), ?_⟩
    have := mkTowerGo_below (w := u) hI'
    rw [liftFields_length] at this
    rwa [show Ps.length + 2 + Ps.length + Is.length = Ps.length + 2 + (Ps.length + Is.length)
      by omega] at this

namespace LfpDatum

variable {D : LfpDatum V}

omit [SetTheory V] in
/-- **The hole chains are closed below the operator's frame** — every
chain of every member, when the members' telescopes are, the fields with
holes are below the parameters and the holes, and the result index
readings below them and the fields. -/
theorem holeChains_below {ψ : Name → Nat} {nP : Nat}
    (hP : ∀ m, m < D.k → (D.pars m ψ).length = nP ∧ FieldsBelow 0 (D.pars m ψ))
    (hI : ∀ m, m < D.k → FieldsBelow nP (D.ids m ψ))
    {c : Nat} (hF : ∀ j, j < D.nctors c → FieldsBelow (nP + D.k) (D.fields ψ c j) ∧
      (∀ e ∈ D.resIdx ψ c j, Term.bvarsBelow (nP + D.k + (D.fields ψ c j).length) e.erase) ∧
      (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    ∀ chain ∈ D.holeChains ψ c, FieldsBelow (nP + 2) chain := by
  have hH : ∀ m, m < D.k → Term.bvarsBelow (nP + 2) (D.holeTm ψ m).erase :=
    fun m hm => holeTmAV_below (hP m hm).1 (hP m hm).2 (hI m hm)
  intro chain hch
  unfold holeChains holeChs termChs at hch
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hch
  simp only [List.length_map, List.length_range] at hj
  have hj' : j < D.nctors c := List.mem_range.mp hj
  have hgF : (((List.range (D.nctors c)).map (D.fields ψ c)).map
      (holeEntsAV D.k (D.holeTm ψ) 0)).getD j []
        = holeEntsAV D.k (D.holeTm ψ) 0 (D.fields ψ c j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hj']
    rfl
  have hgE : ((List.range ((List.range (D.nctors c)).map (D.fields ψ c)).length).map fun j =>
      holeEqsAV D.k (D.holeTm ψ) (D.ids c ψ).length
        (((List.range (D.nctors c)).map (D.fields ψ c)).getD j []).length
        (((List.range (D.nctors c)).map (D.resIdx ψ c)).getD j [])).getD j []
      = holeEqsAV D.k (D.holeTm ψ) (D.ids c ψ).length (D.fields ψ c j).length
          (D.resIdx ψ c j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hj')]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj',
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj']
    rfl
  rw [hgF, hgE]
  obtain ⟨hFb, hEb, hElen⟩ := hF j hj'
  have hents := fieldsBelow_holeEntsAV hH (D.fields ψ c j) 0
    (by rw [Nat.zero_add, Nat.add_comm]; exact hFb)
  rw [Nat.add_zero] at hents
  refine FieldsBelow_append_idxEq hents fun e he => ?_
  unfold holeEqsAV at he
  obtain ⟨l, hlr, rfl⟩ := List.mem_map.mp he
  rw [holeEntsAV_length]
  refine ⟨?_, projAV_below (by simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega)⟩
  have hl : l < (D.resIdx ψ c j).length := by rw [hElen]; exact List.mem_range.mp hlr
  have hmem : (D.resIdx ψ c j).getD l default ∈ D.resIdx ψ c j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; exact List.getElem_mem _
  have := bvarsBelow_substAV (holeTau D.k (D.holeTm ψ)) (holeTau_below hH) _
    (D.fields ψ c j).length
    (by rw [show (D.fields ψ c j).length + (D.k + nP) = nP + D.k + (D.fields ψ c j).length
          by omega]; exact hEb _ hmem)
  rwa [Nat.add_comm (D.fields ψ c j).length (nP + 2)] at this

end LfpDatum

/-! ## The block's hole chains, well-formed -/

/-- **The block's hole chains are graded, bit-valid and closed** — the
three facts a member's former leaf on them needs (`blockTyG_wellDenoted`,
its currency, its closedness) — from the per-constructor facts
`blockHoleGrade_of_run` gives and the members' telescopes. -/
theorem blockHoleChains_facts {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} (hH : BlockHoleFacts m d lps) (ψ : Name → Nat)
    (hIdx : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp → ∀ c, c < d.N →
      IdxOk (d.uM c ψ) ρp (d.IdsM c ψ) ∧ FieldsValid ρp (d.IdsM c ψ))
    (hPars : ∀ mm, mm < d.k → FieldsBelow 0 (d.toLfp.pars mm ψ) ∧ ∀ σ : Nat → V,
      FieldsOkB 0 σ (d.toLfp.pars mm ψ) ∧ FieldsValid σ (d.toLfp.pars mm ψ))
    (hIdsB : ∀ c, c < d.k → FieldsBelow d.nP (d.IdsM c ψ))
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      (FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
        ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase) ∧
      ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X : Nat → V, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
      FieldsValid (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
      ∀ fs : List V, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
        ∀ e ∈ d.absE ψ c j, WellDenotedV V (consList fs (d.toLfp.frame ψ ρp X)) e) :
    (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      BlockChainsOkG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)) ∧
    (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      ∀ Y, Y ∈ˢ famsSpaceB d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) →
      ∀ c, c < d.N → ∀ t : V, SumFieldsValid (cons t (cons Y ρp)) (d.toLfp.holeChains ψ c)) ∧
    (∀ c, c < d.N → ∀ chain ∈ d.toLfp.holeChains ψ c, FieldsBelow (d.nP + 2) chain) := by
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hres : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro c hc j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  have happ : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun c hc j hj => blockHolesApplied hH ψ hc hj
  have hok : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp → d.toLfp.HoleTmOk ψ ρp :=
    fun ρp hs mm hmm =>
      ⟨⟨(hH.parsLen ψ mm hmm).trans (hH.lenP ψ).symm, hH.parsSat ψ mm hmm ρp hs⟩,
        fun _ => (hIdx ρp hs mm (Nat.lt_of_lt_of_le hmm hkN)).1.2⟩
  refine ⟨fun ρp hs => ?_, fun ρp hs Y hY c hc t => ?_, fun c hc => ?_⟩
  · exact LfpDatum.holeChains_ok (hok ρp hs) hkN (fun c hc => (hIdx ρp hs c hc).1)
      (fun mm hmm => ((hPars mm hmm).2 _).1) happ hres
      (fun X hX c hc j hj => ⟨((hG c hc j hj).2 ρp hs X hX).1,
        fun fs hfs e he => (((hG c hc j hj).2 ρp hs X hX).2.2 fs hfs e he).1⟩)
  · exact LfpDatum.holeChains_valid (hok ρp hs) (fun mm hmm => ((hPars mm hmm).2 _).2)
      (fun mm hmm => (hIdx ρp hs mm (Nat.lt_of_lt_of_le hmm hkN)).2) happ
      (fun X hX c hc j hj => ⟨((hG c hc j hj).2 ρp hs X hX).2.1,
        fun fs hfs e he => (((hG c hc j hj).2 ρp hs X hX).2.2 fs hfs e he).2⟩) hY t hc
  · refine LfpDatum.holeChains_below (D := d.toLfp) (nP := d.nP)
      (fun mm hmm => ⟨hH.parsLen ψ mm hmm, (hPars mm hmm).1⟩) hIdsB (fun j hj => ?_)
    obtain ⟨⟨hFb, hEb⟩, -⟩ := hG c hc j hj
    exact ⟨hFb, hEb, hres c hc j hj⟩

/-! ## Congruences of the hole form -/

omit [SetTheory V] in
/-- The result index readings with holes are congruent in the readings. -/
theorem BlockData.absE_congr {d d' : BlockData V} {ψ ψ' : Name → Nat} {c j : Nat}
    (hk : d.k = d'.k) (hes : (d.Ess c ψ).getD j [] = (d'.Ess c ψ').getD j [])
    (hlen : ((d.Fss c ψ).getD j []).length = ((d'.Fss c ψ').getD j []).length) :
    d.absE ψ c j = d'.absE ψ' c j := by
  unfold BlockData.absE
  rw [hes, hlen, hk]

omit [SetTheory V] in
/-- **The hole chains are congruent** in the lfp datum's readings. -/
theorem LfpDatum.holeChains_congr {D D' : LfpDatum V} {ψ ψ' : Name → Nat} (hk : D.k = D'.k)
    (hu : ∀ m, D.u m ψ = D'.u m ψ') (hp : ∀ m, D.pars m ψ = D'.pars m ψ')
    (hi : ∀ c, D.ids c ψ = D'.ids c ψ') (hn : ∀ c, D.nctors c = D'.nctors c)
    (hf : ∀ c j, D.fields ψ c j = D'.fields ψ' c j)
    (he : ∀ c j, D.resIdx ψ c j = D'.resIdx ψ' c j) :
    D.holeChains ψ = D'.holeChains ψ' := by
  have hf' : ∀ c, D.fields ψ c = D'.fields ψ' c := fun c => funext (hf c)
  have he' : ∀ c, D.resIdx ψ c = D'.resIdx ψ' c := fun c => funext (he c)
  unfold LfpDatum.holeChains LfpDatum.holeTm
  simp only [hk, hu, hp, hi, hn, hf', he']

/-! ## A closed telescope's prefix -/

omit [SetTheory V] in
theorem fieldsBelow_take : ∀ {Fs : List AnnotTerm} {k : Nat} (n : Nat),
    FieldsBelow k Fs → FieldsBelow k (Fs.take n)
  | [], _, _, _ => by simp; trivial
  | _ :: _, _, 0, _ => trivial
  | _ :: Fs, _, n + 1, h => ⟨h.1, fieldsBelow_take (Fs := Fs) n h.2⟩

/-- **A graded closed telescope's first `n` domains** are closed and
hereditarily graded and bit-valid at every frame — a member's parameter
telescope, read off its former's type. -/
theorem teleTake_ok {pps : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm} (n : Nat)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps B)) (hb : DomsBelow 0 pps) :
    FieldsBelow 0 ((pps.take n).map (·.2.2)) ∧ ∀ σ : Nat → V,
      FieldsOkB 0 σ ((pps.take n).map (·.2.2)) ∧ FieldsValid σ ((pps.take n).map (·.2.2)) := by
  have hdom : ∀ σ : Nat → V, ∀ i, i < ((pps.take n).map (·.2.2)).length → ∀ as : List V,
      SpineFit σ (((pps.take n).map (·.2.2)).take i) as →
      WellDenotedV V (consList as σ) (((pps.take n).map (·.2.2)).getD i default) := by
    intro σ i hi as has
    have hi' : i < pps.length := by simp at hi; omega
    have hin : i < n := by simp at hi; omega
    have hget : ((pps.take n).map (·.2.2)).getD i default = (pps[i]'hi').2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hin,
        List.getElem?_eq_getElem hi']
      rfl
    rw [hget]
    refine wellDenotedV_mkPisAV_dom (Δa := []) (fun ρ _ => hok ρ) i _
      (List.getElem?_eq_getElem hi') _ ?_
    have h1 : ((pps.take n).map (·.2.2)).take i = (pps.take i).map (·.2.2) := by
      rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hin)]
    rw [h1] at has
    simpa using sat_of_spineFit (Sat_nil V σ) has
  have hb' := hb.fields
  refine ⟨by rw [List.map_take]; exact fieldsBelow_take n hb', fun σ =>
    ⟨fieldsOkB_of_prefix _ σ fun i hi as has => ⟨(hdom σ i hi as has).1, fun h => absurd rfl h⟩,
      fieldsValid_of_prefix _ σ fun i hi as has => (hdom σ i hi as has).2⟩⟩

end ConLeche.Model
