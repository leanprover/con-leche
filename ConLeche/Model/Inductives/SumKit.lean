module

public import ConLeche.Model.Inductives.StructRecKit
public import ConLeche.Semantics.Tower.SumWire
public import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.IndPointKit

public section

/-!
# Block library: constructor lists over an indexed family

The single-constructor library at a constructor list over an indexed
family: the sum leaves' bit validity; the generated recursor's
readings; the constructors' data and frames; the recursor's data and
frames; the former's and a constructor's cons; the install assembled
(`declSumP`).
-/

/-!
## The sum leaves' bit validity and P packages

`AnnotValid` for the three sum leaves at an indexed family.  The
case split and the injection carry no `.pi` node (hereditary
plumbing); the squash carrier's, the index equation's and the
recursor's motive `.pi` nodes carry the genuine clause — a zero
codomain bit over a truth value — discharged from
`piR_zero_mem_univZero` (the squash carrier, the equation chain) and
from the motive's own applications being truth values at a zero
elimination level (the recursor, `RecHypS.hM0`).  The restricted
chains (`rChain`) are bit-valid from the fields' validity at the
shifted frame and the index readings' validity at fitting field
frames (`rChain_validV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Kit -/

theorem AnnotValid.mkAppN_inv {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, AnnotValid V ρ (AnnotTerm.mkAppN f args) →
      AnnotValid V ρ f ∧ ∀ a ∈ args, AnnotValid V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := AnnotValid.mkAppN_inv h
    rw [AnnotValid_app] at hfa
    exact ⟨hfa.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hfa.2
      · exact hall a' ha'⟩

theorem numeralAV_validV (i : Nat) (σ : Nat → V) : AnnotValid V σ (numeralAV i) := by
  induction i with
  | zero => trivial
  | succ i ih =>
    show AnnotValid V σ (.app (.const .natSucc []) (numeralAV i))
    rw [AnnotValid_app]
    exact ⟨trivial, ih⟩

theorem natRecAV_validV {u : Nat} {M z s kx : AnnotTerm} {σ : Nat → V}
    (hM : AnnotValid V σ M) (hz : AnnotValid V σ z) (hs : AnnotValid V σ s)
    (hk : AnnotValid V σ kx) : AnnotValid V σ (natRecAV u M z s kx) := by
  show AnnotValid V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) kx)
  simp only [AnnotValid_app, AnnotValid_const]
  exact ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

theorem natSortMotiveAV_validV (w : Nat) (σ : Nat → V) :
    AnnotValid V σ (natSortMotiveAV w) := by
  show AnnotValid V σ (.lam (w + 1) natAV (.sort w))
  rw [AnnotValid_lam]
  exact ⟨trivial, fun _ _ => trivial⟩

/-- The selector is bit-valid from the spellings' validity at the
retracted environment (hereditary; no `.pi` node). -/
theorem caseAVAt_validV {w : Nat} :
    ∀ {Ts : List AnnotTerm} {d : Nat} {kx : AnnotTerm} {σ : Nat → V},
      (∀ T ∈ Ts, AnnotValid V (shiftE d 0 σ) T) → AnnotValid V σ kx →
      AnnotValid V σ (caseAVAt w Ts d kx)
  | [], _, _, _, _, _ => trivial
  | T :: Ts, d, kx, σ, hT, hk => by
    refine natRecAV_validV (natSortMotiveAV_validV w σ) ?_ ?_ hk
    · rw [AnnotValid_liftN]; exact hT T List.mem_cons_self
    · rw [AnnotValid_lam]
      refine ⟨trivial, fun b _ => ?_⟩
      rw [AnnotValid_lam]
      refine ⟨trivial, fun a _ => ?_⟩
      refine caseAVAt_validV (Ts := Ts) (d := d + 2) (kx := .bvar 1) (σ := cons a (cons b σ))
        ?_ trivial
      rw [shiftE_step]
      exact fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')

/-! ## The index equation -/

/-- The equation chain is a truth value (every node is a
`Prop`-product). -/
theorem eqChainAV_mem_univZero : ∀ (eqs : List (AnnotTerm × AnnotTerm)) (ρ : Nat → V),
    interp V ρ (eqChainAV eqs) ∈ˢ (univZero : V)
  | [], _ => by
    show (empty : V) ∈ˢ univZero
    rw [← univ_zero]; exact empty_mem_univ 0
  | (_, _) :: _, _ => piR_zero_mem_univZero

theorem eqChainAV_validV :
    ∀ {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V},
      (∀ e ∈ eqs, AnnotValid V ρ e.1 ∧ AnnotValid V ρ e.2) →
      AnnotValid V ρ (eqChainAV eqs)
  | [], _, _ => trivial
  | (a, b) :: r, ρ, h => by
    show AnnotValid V ρ (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0))
    rw [AnnotValid_pi, AnnotValid_eqE]
    refine ⟨h (a, b) List.mem_cons_self, fun x _ => ?_, fun _ x _ => ?_⟩
    · rw [AnnotValid_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_validV fun e he => h e (List.mem_cons_of_mem _ he)
    · rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_mem_univZero r ρ

/-- The index equation is bit-valid from its sides' validity. -/
theorem idxEqAV_validV {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V}
    (h : ∀ e ∈ eqs, AnnotValid V ρ e.1 ∧ AnnotValid V ρ e.2) :
    AnnotValid V ρ (idxEqAV eqs) := by
  show AnnotValid V ρ (.pi 0 0 (eqChainAV eqs) (.const .empty [0]))
  rw [AnnotValid_pi]
  exact ⟨eqChainAV_validV h, fun _ _ => trivial,
    fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩

theorem idxEqAV_nil_validV (ρ : Nat → V) : AnnotValid V ρ (idxEqAV []) :=
  idxEqAV_validV fun _ h => nomatch h

/-- A chain extended by one field valid at every fitting frame. -/
theorem FieldsValid_append_one {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → AnnotValid V (consList bs ρ) E) →
      FieldsValid ρ (Fs ++ [E])
  | [], ρ, _, hE => ⟨by simpa [consList] using hE [] trivial, fun _ _ => trivial⟩
  | F :: Fs, ρ, hv, hE => by
    refine ⟨hv.1, fun a ha => ?_⟩
    refine FieldsValid_append_one (hv.2 a ha) fun bs hsp => ?_
    have := hE (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- Per-constructor hereditary validity. -/
@[expose] def SumFieldsValid (ρ : Nat → V) (Fss : List (List AnnotTerm)) : Prop :=
  ∀ Fs ∈ Fss, FieldsValid ρ Fs

/-- The unit-restricted chains are bit-valid. -/
theorem uChains_validV {ρ : Nat → V} {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρ Fss) :
    SumFieldsValid ρ (uChains Fss) := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsValid_append_one (hv Fs hFs) fun _ _ => idxEqAV_nil_validV _

/-! ## The carrier -/

theorem towers_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : ∀ T ∈ Fss.map (towerBodyAV w), AnnotValid V ρ T := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_validV (hv Fs hFs)

theorem case_validV_at {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρp Fss) (k : V) :
    AnnotValid V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)) := by
  refine caseAVAt_validV ?_ trivial
  rw [shiftE_succ_cons, hsh]
  exact towers_validV hv

theorem sumBodyAVPos_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sumBodyAVPos w Fss) := by
  unfold sumBodyAVPos
  rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
  exact ⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at (shiftE_zero_zero ρ) hv k⟩

theorem sqSumBodyAV_validV {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sqSumBodyAV Fss) := by
  unfold sqSumBodyAV negAV
  rw [AnnotValid_pi]
  refine ⟨?_, fun _ _ => by simp, fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
  rw [AnnotValid_pi]
  refine ⟨trivial, fun k _ => ?_, fun _ k _ => piR_zero_mem_univZero⟩
  rw [AnnotValid_pi]
  exact ⟨case_validV_at (shiftE_zero_zero ρ) hv k, fun _ _ => by simp,
    fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩

theorem sumBodyAV_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sumBodyAV w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_validV hv
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_validV hv

/-- The type-former leaf's P currency. -/
theorem sumTyAV_wellDenotedV {w : Nat} {Fss : List (List AnnotTerm)}
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkS w ρ Fss pps)
    (hval : UnderTowerValid ρ (sumBodyAV w Fss) pps) :
    WellDenotedV V ρ (sumTyAV w pps Fss) :=
  ⟨sumTyAV_wellDenoted hok, mkLamsC_validV hval⟩

/-! ## The constructor -/

theorem sumInjAtAV_validV {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρp Fss) {tag payload : AnnotTerm}
    (ht : AnnotValid V σ tag) (hp : AnnotValid V σ payload) :
    AnnotValid V σ (sumInjAtAV w Fss d tag payload) := by
  show AnnotValid V σ (.app (.app (.app (.app (.const .psigmaMk [w, w]) natAV)
    (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))) tag) payload)
  simp only [AnnotValid_app, AnnotValid_const, AnnotValid_lam]
  exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at hsh hv k⟩, ht⟩, hp⟩

/-- The proof-field-terminated tupler is bit-valid at a fitting frame
(graph regime). -/
theorem mkTowerGoUPos_validV {w : Nat} {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsValid ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      AnnotValid V (consList bs ρp) (mkTowerGoUPos w E Fs)
  | [], ρp, [], hv, _ => by
    show AnnotValid V ρp (.app (.app (.app (.app (.const .psigmaMk [w, w]) E)
        (.lam (w + 1) E (.const .punit [w + 1]))) .prf) (.const .punitUnit []))
    simp only [AnnotValid_app, AnnotValid_const, AnnotValid_lam, AnnotValid_prf]
    exact ⟨⟨⟨⟨trivial, hv.1⟩, hv.1, fun _ _ => trivial⟩, trivial⟩, trivial⟩
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hv, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    rw [List.cons_append] at hv
    show AnnotValid V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoUPos w E Fs))
    rw [AnnotValid_app]
    refine ⟨?_, mkTowerGoUPos_validV (hv.2 b hsp.1) hsp.2⟩
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

/-- The tupler is bit-valid at a fitting frame, both regimes. -/
theorem mkTowerGoU_validV {w : Nat} {E : AnnotTerm} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hv : FieldsValid ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp) (mkTowerGoU w Fs E) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; trivial
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_validV hv hsp

/-- The constructor's body is bit-valid at a fitting field frame. -/
theorem sumInj_validV_at_fields {w j : Nat} {ρp : Nat → V} {Fs : List AnnotTerm}
    {Fss : List (List AnnotTerm)} {bs : List V}
    (hv : SumFieldsValid ρp Fss) (hvF : FieldsValid ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp)
      (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) := by
  have hlen : bs.length = Fs.length := hsp.length_eq
  have hsh : shiftE Fs.length 0 (consList bs ρp) = ρp := by rw [← hlen]; exact shiftE_consList bs ρp
  exact sumInjAtAV_validV hsh hv (numeralAV_validV j _)
    (mkTowerGoU_validV (FieldsValid_append_one hvF fun _ _ => idxEqAV_nil_validV _) hsp)

/-- The constructor leaf's P currency. -/
theorem sumMkAV_wellDenotedV {w j : Nat} {bodyC : AnnotTerm} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} {pds fds : List (Nat × Nat × AnnotTerm)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPreS w j ρ (fds.map (·.2.2)) Fss bodyC pds)
    (hval : UnderTowerValid ρ
      (sumInjAtAV w Fss (fds.map (·.2.2)).length (numeralAV j)
        (mkTowerGoU w (fds.map (·.2.2)) (idxEqAV [])))
      (pds ++ fds)) :
    WellDenotedV V ρ (sumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss) :=
  ⟨sumMkAV_wellDenoted hz hpre, mkLamsC_validV hval⟩


/-!
## The generated sum recursor's readings

`ConLeche/Model/Inductives/StructRecKit.lean` at a constructor list over
an indexed family: the generated recursor type reads to the Π-tower
over `sumRecDataAV` (parameters, motive over the index telescope, one
minor per constructor, the index telescope again, major), with the
core `motive ı⃗ t`, and rule `j` reads to the λ-tower over
`sumRuleDataAV` at constructor `j`'s field data, with the core
`minor_j f⃗`.  The minor entries are read by one induction over the
constructor list (`denoteP_minorsPis` / `denoteP_minorsLams`), the
accumulated variables (the motive first, then the earlier minors)
threaded as `extras`.

The one genuinely new reading is the minor's conclusion
`motive e⃗ (C p⃗ f⃗)`: the constructor's index expressions, spelled at
the recursor frame (under the extras), read to the constructor's own
index readings lifted above the fields
(`denoteMetaSpine_idxArgs_lift`) — obtained by reading the whole opened
residual `T p⃗ e⃗` at that frame and inverting the application spine.
-/


open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `AnnotTerm` bookkeeping -/

theorem liftN_mkAppN (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, liftN_mkAppN n k as, AnnotTerm.liftN_app]

theorem DenoteMetaSpine.unique {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → DenoteMetaSpine acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteMetaSpine.unique h h']

/-! ## The entries -/

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm


/-!
## The direct sum's constructor data and frames

`CtorDataI`: `CtorData` at an indexed family — the constructor's type
reads to the Π-tower over its field data ending in the family at the
parameter variables and the **index readings** `Es` (the readings of
the residual's index expressions at the constructor's own frame), and
the field **sources** `srcs` (per field: the index position the field
literally is, or none — the squash-regime recursor body applies its
minor to the sources; a field without a source at a large-eliminating
`Prop` family is propositional, `FieldsBoundSrc`).  `sumCtorData_of`
reads them off `checkSumCtor`'s run (the residual `T p⃗ e⃗` at
the opened frame, its spine inverted), and `sumCtorFrames` gives the
constructor's frames: the parameter frames identified, the field
chain graded, the index expressions graded and **fitting the former's
index telescope** — read off the residual's own grading
(`spineFit_of_wellDenoted_lams`: an application spine graded against a
λ-tower fits the tower's domains, since a graph determines its
domain).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta)


/-! ## Kit -/

/-- The arguments of a bounded spine are bounded. -/
theorem bvarsBelow_mkAppN_inv {k : Nat} :
    ∀ {as : List Term} {f : Term}, Term.bvarsBelow k (Term.mkAppN f as) →
      Term.bvarsBelow k f ∧ ∀ a ∈ as, Term.bvarsBelow k a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hf, hall⟩ := bvarsBelow_mkAppN_inv (as := as) (f := .app f a) h
    exact ⟨hf.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hf.2
      · exact hall a' ha'⟩

/-- The head and the arguments of a graded spine are graded. -/
theorem WellDenoted.mkAppN_inv {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      WellDenoted V ρ f ∧ ∀ a ∈ args, WellDenoted V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := WellDenoted.mkAppN_inv h
    rw [WellDenoted_app] at hfa
    exact ⟨hfa.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hfa.2.1
      · exact hall a' ha'⟩

/-- Equal graphs have equal domains. -/
theorem graph_eq_dom {F G : V → V} {A D : V} (h : graph F A = graph G D) : A = D := by
  apply SetTheory.ext
  intro x
  constructor
  · intro hx
    have : kpair x (F x) ∈ˢ graph G D := h ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'
  · intro hx
    have : kpair x (G x) ∈ˢ graph F A := h.symm ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'

/-- A graph-regime abstraction in a product has the product's
domain. -/
theorem lamR_mem_piR_dom {u v : Nat} (hu : u ≠ 0) {A D : V} {F B : V → V}
    (h : lamR u D F ∈ˢ piR v A B) : A = D := by
  by_cases hv : v = 0
  · subst hv
    rw [piR_zero] at h
    exact absurd (eq_pt_of_mem_truthVal h) (lamR_ne_pt hu)
  · have h1 := (mem_piR_pos hv h).1
    rw [lamR_pos hu] at h1
    exact graph_eq_dom h1

/-- **A spine graded against a constant-bit λ-tower fits its
domains** (graph regime): each application node's product has the
abstraction's domain. -/
theorem spineFit_of_wellDenoted_lams {u : Nat} (hu : u ≠ 0) {b : AnnotTerm} :
    ∀ {args : List AnnotTerm} {ds : List (Nat × Nat × AnnotTerm)} {σ ρ : Nat → V} {f : AnnotTerm},
      args.length ≤ ds.length →
      WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = interp V σ (mkLamsC u ds b) →
      SpineFit σ ((ds.take args.length).map (·.2.2)) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | a :: args, d :: ds, σ, ρ, f, hlen, hok, hf => by
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hf' : interp V ρ f
        = lamR u (interp V σ d.2.2) fun x => interp V (cons x σ) (mkLamsC u ds b) := by
      rw [hf]; rfl
    rw [hf'] at hfm
    have hA : A = interp V σ d.2.2 := lamR_mem_piR_dom hu hfm
    rw [hA] at ham
    have happ : interp V ρ (.app f a) = interp V (cons (interp V ρ a) σ) (mkLamsC u ds b) := by
      rw [interp_app, hf', app_lamR_pos hu ham]
    have ih := spineFit_of_wellDenoted_lams hu (args := args) (ds := ds) (σ := cons (interp V ρ a) σ)
      (ρ := ρ) (f := .app f a) (by simpa using hlen) hok happ
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    exact ⟨ham, ih⟩

/-- A read spine crosses a cons its terms do not mention. -/
theorem DenoteMetaSpine.cons_mono {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? c₀.name = none)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) {ψ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ a ∈ as, ConstsBound env a) →
      DenoteMetaSpine acval env ψ d as vs →
      DenoteMetaSpine (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hcb, .cons ha htl =>
    .cons (denoteMeta_cons_mono hfresh (hat a) ψ d (hcb a List.mem_cons_self) ha)
      (DenoteMetaSpine.cons_mono hfresh hat (fun a' ha' => hcb a' (List.mem_cons_of_mem _ ha')) htl)

omit [SetTheory V] in
/-- A valuation agreeing with the parameters below `nP`. -/
theorem consList_params_apply {nP : Nat} (ρ X : Nat → V) {i : Nat} (hi : i < nP) :
    consList ((List.range nP).reverse.map ρ) X i = ρ i := by
  have hlt : ((List.range nP).reverse.map ρ).length - 1 - i < ((List.range nP).reverse.map ρ).length := by
    simp; omega
  have h1 := consList_apply_lt ((List.range nP).reverse.map ρ) X i (by simpa using hi)
  have h2 := consList_apply_lt ((List.range nP).reverse.map ρ) (fun j => ρ (j + nP)) i
    (by simpa using hi)
  rw [consList_range_reverse] at h2
  rw [List.getElem?_eq_getElem hlt, Option.getD_some] at h1 h2
  rw [h1, h2]

/-! ## The field sources -/

/-- The first position of an expression in a list. -/
def firstIdx (x : Expr) : List Expr → Option Nat
  | [] => none
  | a :: as => if a = x then some 0 else (firstIdx x as).map (· + 1)

theorem firstIdx_some : ∀ {l : List Expr} {x : Expr} {i : Nat},
    firstIdx x l = some i → l[i]? = some x
  | [], _, _, h => by simp [firstIdx] at h
  | a :: as, x, i, h => by
    simp only [firstIdx] at h
    split at h
    · next hax =>
      obtain rfl := Option.some.inj h
      simp [hax]
    · obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using firstIdx_some hi'

theorem firstIdx_of_mem : ∀ {l : List Expr} {x : Expr}, x ∈ l → ∃ i, firstIdx x l = some i
  | [], _, h => nomatch h
  | a :: as, x, h => by
    simp only [firstIdx]
    by_cases hax : a = x
    · exact ⟨0, by rw [if_pos hax]⟩
    · rw [if_neg hax]
      obtain ⟨i, hi⟩ := firstIdx_of_mem (l := as) (x := x)
        (by rcases List.mem_cons.mp h with rfl | h'; exact absurd rfl hax; exact h')
      exact ⟨i + 1, by rw [hi]; rfl⟩

/-- The sources of the fields: a field whose sort is `Prop` is a proof
(`none`); otherwise the first index position the field variable
occupies. -/
def srcsOf (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map fun j =>
    if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
    else firstIdx (xFvs.getD j default) idxArgs

theorem srcsOf_length (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) :
    (srcsOf xFvs idxArgs sorts nF).length = nF := by simp [srcsOf]

theorem srcsOf_getElem? (xFvs idxArgs : List Expr) (sorts : List Level) (nF j : Nat) (hj : j < nF) :
    (srcsOf xFvs idxArgs sorts nF)[j]?
      = some (if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
          else firstIdx (xFvs.getD j default) idxArgs) := by
  simp [srcsOf, hj]

/-- The fields not sourced by an index are propositions: each such
field's domain is a truth value, hereditarily. -/
@[expose] def FieldsBoundSrc (ρ : Nat → V) : List AnnotTerm → List (Option Nat) → Prop
  | [], _ => True
  | _ :: _, [] => True
  | F :: Fs, s :: ss => (s = none → interp V ρ F ∈ˢ (univ 0 : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBoundSrc (cons a ρ) Fs ss

/-- `fieldsBound_of_frame` at the sourced fields. -/
theorem fieldsBoundSrc_of_frame {Γ : List AnnotTerm} {k nP nF : Nat} {srcs : List (Option Nat)}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → srcs[j]? = some none → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ 0 : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) from
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
    cases hs : srcs.drop j with
    | nil => trivial
    | cons s ss =>
      have hsj : srcs[j]? = some s := by
        have := congrArg (·[0]?) hs
        simpa [List.getElem?_drop] using this
      have hss : srcs.drop (j + 1) = ss := by
        rw [← List.drop_drop, hs]
        rfl
      refine ⟨fun hsn => hbnd j hlt (hsn ▸ hsj) ρ hρ, fun a ha => ?_⟩
      rw [← hss]
      refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
      rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
      have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
        rw [List.getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
      exact Sat_cons V hρ ha

/-! ## The constructor's data -/

/-- The family at the parameter variables and the index readings,
read at the constructor's full frame. -/
@[expose] def ctorBodyAVI {env : Env} (m : EnvModel V env) (T : Name) (nP nF : Nat)
    (ψ : Name → Nat) (Es : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)

/-- **A constructor's data at an indexed family**: its stored type
reads to the Π-tower over `ds ψ` ending in the family at the
parameters and the index readings `Es ψ`; the index readings read the
residual's index expressions `idxArgs` at the constructor's frame; the
sources `srcs` name, per field, the index it literally is, and at a
large-eliminating `Prop` family the other fields are
propositional. -/
structure CtorDataI {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name)
    (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) : Prop where
  resid : ∃ (cbs : List (Expr × BinderMeta)) (es : List Expr),
    cvC.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
    es.length = nIdx
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  lenE : ∀ ψ : Name → Nat, (Es ψ).length = nIdx
  idxLen : idxArgs.length = nIdx
  idxRead : ∀ ψ : Name → Nat, DenoteMetaSpine m.acval env ψ (nP + nF) idxArgs (Es ψ)
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ ds ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  belowE : ∀ ψ : Name → Nat, ∀ E ∈ Es ψ, Term.bvarsBelow (nP + nF) E.erase
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) →
    ds ψ₁ = ds ψ₂ ∧ Es ψ₁ = Es ψ₂
  srcLen : srcs.length = nF
  srcBnd : ∀ s ∈ srcs, ∀ l, s = some l → l < nIdx
  srcIdx : ∀ j l, srcs[j]? = some (some l) → ∀ ψ : Name → Nat,
    (Es ψ)[l]? = some (AnnotTerm.bvar (nF - 1 - j))
  srcProp : large = true → ∀ ψ : Name → Nat, resSort.eval ψ = 0 → ∀ ρ : Nat → V,
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    FieldsBoundSrc ρ (((ds ψ).drop nP).map (·.2.2)) srcs

/-- The data crosses a cons whose head is neither the former nor
mentioned. -/
theorem CtorDataI.cross {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m₂ T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ
    unfold ctorBodyAVI
    rw [hac, acvalWith_ne hT]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hac, hbody]
    exact denoteMeta_cons_mono hfresh (hat _) ψ 0 hcb (h.read ψ)
  · rw [hac]
    exact DenoteMetaSpine.cons_mono hfresh hat hcbI (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ


/-- The constructor's data, from its stage run at the environment
holding the former. -/
theorem sumCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {bs : List (Expr × ConLeche.BinderMeta)}
    {sorts : List Level} {sT : Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hsT : ∀ ψ : Name → Nat, sT.eval ψ = resSort.eval ψ)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT)) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat)),
      (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        idxArgs = xrest.getAppArgs.drop nP) ∧
      CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  obtain ⟨⟨_, hccv⟩, hresid, fvsP, crest, tfvs, trest, xFvs, idxArgs, hopC, -, -, hopX, hlenI,
    -, hres, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', -, hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hopC hresid
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP type' 0 hopC
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ idxArgs) hib
  obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : ConLeche.inferTypeCore μ env F' (nP + nF)
      (.const T (lps.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ idxArgs) htfT
    (by rw [List.length_append, hlenP, hlenI]; exact hstripT) hib
  have hvb := ensureSortCore_sort_eq hensb
  rw [hvb] at hbits
  -- the per-assignment reading
  have hper : ∀ ψ : Name → Nat, ∃ (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type'
        = some (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es)) ∧
      ds.length = nP + nF ∧ Es.length = nIdx ∧
      DenoteMetaSpine mp.base2.acval env ψ (nP + nF) idxArgs Es ∧
      (∀ d ∈ ds, (resSort.eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es))) ∧
      DomsBelow 0 ds ∧ (∀ E ∈ Es, Term.bvarsBelow (nP + nF) E.erase) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hopAll htf' hbt' hTa hokT'
    -- the residual's spine, inverted
    obtain ⟨fa, vs, hfa, hsp, hR⟩ := denoteMeta_mkAppN_inv hop'.body
    have hfa' : fa = mp.base2.acval T ψ := by
      have hconst := denoteMeta_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := nP + nF) hfT
        (show (lps.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (lps.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (lps.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (lps.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hconst, hsubst] at hfa
      exact (Option.some.inj hfa).symm
    subst hfa'
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
    have hvs₁ : vs₁ = paramBvars nP nF := by
      have := DenoteMetaSpine.unique hsp₁
        (denoteMetaSpine_fvars (acval := mp.base2.acval) (env := env) (φ := ψ) (nP + nF)
          fvsP 0 hidx)
      rw [this, hlenP]
      unfold paramBvars
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    subst hvs₁
    have hR' : R = ctorBodyAVI mp.base2 T nP nF ψ vs₂ := hR
    subst hR'
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    have hbelowAll := stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)
    refine ⟨ds, vs₂, hTa, hlen, by rw [← hsp₂.length, hlenI], hsp₂, ?_, hokT', hbelowAll.1, ?_⟩
    · intro d hd
      rw [← hsT ψ]
      exact (stripPisAV_bits (nP + nF) (hbits ψ) hTa hst' d hd).symm
    · intro E hE
      have hb := hbelowAll.2
      rw [Nat.zero_add] at hb
      unfold ctorBodyAVI at hb
      rw [AnnotTerm.erase_mkAppN] at hb
      exact (bvarsBelow_mkAppN_inv hb).2 _
        (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
  -- the sources
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hspec : ∀ ψ, _ := fun ψ => Classical.choose_spec (Classical.choose_spec (hper ψ))
  refine ⟨idxArgs, fun ψ => Classical.choose (hper ψ),
    fun ψ => Classical.choose (Classical.choose_spec (hper ψ)),
    srcsOf xFvs idxArgs sorts nF, hres, ⟨fvsP, crest, xFvs, _, hopC, hopX, ?_⟩, ?_⟩
  · rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' hlenP]
  refine ⟨hresid, fun ψ => (hspec ψ).1, fun ψ => (hspec ψ).2.1, fun ψ => (hspec ψ).2.2.1,
    hlenI, fun ψ => (hspec ψ).2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.2.2, ?_,
    srcsOf_length _ _ _ _, ?_, ?_, ?_⟩
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have h2 := (hspec ψ₂).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAVI mp.base2 T nP nF ψ₁ (Classical.choose (Classical.choose_spec (hper ψ₁))))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 type' htp']
      exact (hspec ψ₁).1
    obtain ⟨hds, hbody⟩ := mkPisAV_inj
      (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1]) (Option.some.inj (h1.symm.trans h2))
    refine ⟨hds, ?_⟩
    obtain ⟨-, hargs⟩ := AnnotTerm.mkAppN_inj (f := mp.base2.acval T ψ₁) (g := mp.base2.acval T ψ₂) hbody
      (by rw [List.length_append, List.length_append, (hspec ψ₁).2.2.1, (hspec ψ₂).2.2.1])
    exact List.append_cancel_left hargs
  · -- the sources are index positions
    intro s hs l hsl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hj
    have hj' := Option.some.inj hj
    rw [hsl] at hj'
    split at hj'
    · exact nomatch hj'
    · have := firstIdx_some hj'
      rw [← hlenI]
      exact (List.getElem?_eq_some_iff.mp this).1
  · -- an index source reads to the field variable
    intro j l hjl ψ
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hjl).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hjl
    have hjl' := Option.some.inj hjl
    split at hjl'
    · exact nomatch hjl'
    · have hidxl := firstIdx_some hjl'
      obtain ⟨fv, hfv⟩ : ∃ fv, xFvs[j]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := hidxX j fv hfv
      rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some] at hidxl
      obtain ⟨v, hv, hread⟩ := denoteMetaSpine_getElem?' ((hspec ψ).2.2.2.1) _ _ hidxl
      rw [denoteMeta_fvar, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega] at hread
      rw [hv, Option.some.inj hread]
  · -- the unsourced fields are propositional at a large-eliminating
    -- family instantiated at `Prop`
    intro hl ψ hw0 ρ hρ
    have hc := claimsAt_of hμ mp ψ F
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs))
        (((Classical.choose (hper ψ)).map (·.2.2)).reverse)
        (ctorBodyAVI mp.base2 T nP nF ψ (Classical.choose (Classical.choose_spec (hper ψ)))) :=
      opened_of_peel hopAll htf' hbt' (hspec ψ).1 (hspec ψ).2.1 (hspec ψ).2.2.2.2.2.1
    have hlenDs : (Classical.choose (hper ψ)).length = nP + nF := (hspec ψ).2.1
    have hΓlen : ((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).length = nP + nF := by
      rw [List.length_reverse, List.length_map, hlenDs]
    have hρ' : Sat V (((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := Classical.choose (hper ψ)) (nP := nP) (nF := nF) hlenDs
    rw [← hFsEq]
    have h := fieldsBoundSrc_of_frame (Γ := ((Classical.choose (hper ψ)).map (·.2.2)).reverse)
      (srcs := srcsOf xFvs idxArgs sorts nF) rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
    · rw [List.drop_zero] at h; exact h
    intro j hj hsj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
    have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
    have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hC.doms (nP + j) fv hfvA
    have hmem := (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    -- the source is `none`: the sort evaluates to `0`
    have hu0 : u.eval ψ = 0 := by
      cases hp : isProp with
      | false =>
        have hle := Level.leq_sound (hleq hp) ψ
        omega
      | true =>
        rw [srcsOf_getElem? _ _ _ _ _ hj] at hsj
        have hsj' := Option.some.inj hsj
        have hsu : sorts.getD j .zero = u := by
          rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
        rw [hsu] at hsj'
        split at hsj'
        · next hequ => exact Level.isEquiv_sound (beq_iff_eq.mp hequ) ψ
        · rcases hz hp hl with h | h
          · exact Level.isEquiv_sound (beq_iff_eq.mp h) ψ
          · exfalso
            have hfvx : xFvs.getD j default = fv := by
              rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some]
            rw [hfvx] at hsj'
            obtain ⟨i, hi'⟩ := firstIdx_of_mem (List.contains_iff_mem.mp h)
            rw [hi'] at hsj'
            exact nomatch hsj'
    rw [hu0] at hmem
    exact hmem

/-! ## The constructor's frames -/

/-- **The constructor's frames**: the parameter frames identified, and
under the parameters the field chain graded (at the block's level),
bit-valid, bounded when the family is not `Prop`, and the index
expressions graded and fitting the former's index telescope at every
fitting field spine. -/
theorem ctorFramesGen (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
    -- the fields' sorts, as the stage read them (task #210 Part A: the
    -- projection table's guard levels at a structure-like block): one
    -- per field, each bounded by the result sort at a non-`Prop` family,
    -- and the field's reading along a fitting prefix a member of its
    -- sort's universe
    (sorts.length = nF ∧
      (∀ j, j < nF → isProp = false → Level.leq (sorts.getD j .zero) resSort = some true) ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
  obtain ⟨⟨_, hccv⟩, -, fvsP, crest, tfvs, trest, xFvs, idxArgs', hopC, hopT, hdoms, hopX,
    -, -, -, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopC hsorts
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hpins := ConLeche.checkStructDomsAt_inv hdoms
  have hlenX : xFvs.length = nF := openPisAtFvars_length _ hopX
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    -- the former, opened at the parameters
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hopT hTf hTb (hFD.read ψ) (hFD.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take nP (ppsAll ψ) (AnnotTerm.sort (resSort.eval ψ))
      (by rw [hFD.len ψ]; omega)
    obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
    subst hΓt
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs'))
        ((ds ψ).map (·.2.2)).reverse (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
      opened_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hlenF : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
    have hiff : ∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ := by
      intro ρ
      have := (hpf nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    have hrow : ∀ j, j < nF → ∃ u, sorts[j]? = some u ∧
        (isProp = false → Level.leq u resSort = some true) ∧
        ∀ ρ : Nat → V,
          Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + j))) ρ →
          interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD
            (nP + nF - 1 - (nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, -⟩ := hfields j hj
      refine ⟨u, hu, hleq, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
      have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
      have hread := hC.doms (nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hsortsPart : ∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) := by
      intro ρ hρ j hj as hsp
      obtain ⟨u, hu, -, hmem⟩ := hrow j hj
      have hsat := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
      have hdropj : ((((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - (nP + j))
          = ((((ds ψ).drop nP).map (·.2.2)).take j).reverse ++
            (((ds ψ).take nP).map (·.2.2)).reverse := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - (nP + j) = nF - j from by omega,
          List.drop_append_of_le_length (by rw [List.length_reverse, hlenF]; exact Nat.sub_le _ _),
          List.drop_reverse, hlenF, show nF - (nF - j) = j from by omega]
      have hentj : ((((ds ψ).map (·.2.2)).reverse)).getD (nP + nF - 1 - (nP + j)) default
          = (((ds ψ).drop nP).map (·.2.2)).getD j default := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_reverse, hlenF]; omega),
          List.getElem?_reverse (by rw [hlenF]; omega), hlenF,
          show nF - 1 - (nF - 1 - j) = j from by omega, ← List.getD_eq_getElem?_getD]
      have := hmem (consList as ρ) (by rw [hdropj]; exact hsat)
      rw [hentj] at this
      rw [List.getD_eq_getElem?_getD (l := sorts), hu]
      exact this
    refine ⟨hiff, fun ρ hρ => ?_, hsortsPart⟩
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by
      simp [hlenDs]
    have hρ' : Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      by_cases hnp : isProp = true
      · exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · rw [← hFsEq]
      exact fieldsValid_of_frame rfl hΓlen hC.okΓ 0 (Nat.zero_le _) ρ hρ'
    · intro hnp
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      have hle := Level.leq_sound (hleq hnp) ψ
      exact univ_mono hle _ (hmem ρ hρ)
    · -- the index expressions at a fitting field spine
      intro bs hsp
      have hlenB : bs.length = nF := by rw [hsp.length_eq, hlenF]
      have hsat : Sat V (((ds ψ).map (·.2.2)).reverse) (consList bs ρ) := by
        have := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
        rwa [← reverse_map_take_drop] at this
      have hokRP := hC.okR _ hsat
      unfold ctorBodyAVI at hokRP
      have hokR := hokRP.1
      obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokR
      obtain ⟨-, hargsV⟩ := AnnotValid.mkAppN_inv hokRP.2
      refine ⟨fun E hE => ⟨hargs E (List.mem_append_right _ hE),
        hargsV E (List.mem_append_right _ hE)⟩, ?_⟩
      -- the spine fits the former's leaf
      obtain ⟨B, hB⟩ := hleafT ψ
      have hfit := spineFit_of_wellDenoted_lams (u := resSort.eval ψ + 1) (Nat.succ_ne_zero _)
        (b := B) (args := paramBvars nP nF ++ Es ψ)
        (ds := ppsAll ψ) (σ := consList bs ρ) (ρ := consList bs ρ) (f := mp.base2.acval T ψ)
        (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]) hokR (by rw [hB])
      rw [List.take_of_length_le (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]),
        ← List.take_append_drop nP (ppsAll ψ), List.map_append, List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = nP := by
        rw [h1.length_eq, List.length_map, List.length_take, hFD.len ψ]; omega
      have hps : (paramBvars nP nF).map (interp V (consList bs ρ))
          = (List.range nP).reverse.map ρ := by
        rw [paramBvars_eq_paramBvarsAt]
        exact map_paramBvarsAt_interp (fun j => by rw [← hlenB]; exact consList_apply_add bs ρ j)
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvars])
      rw [hps] at h2
      show SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) ((Es ψ).map (interp V (consList bs ρ)))
      refine spineFit_congr_below (DomsBelow.drop nP (hFD.below ψ)) ?_ h2
      intro i hi
      rw [Nat.zero_add] at hi
      exact consList_params_apply ρ _ hi
  refine ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2.1, hlenS, ?_, fun ψ => (hframes ψ).2.2⟩
  intro j hj hnp
  obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hfields j hj
  rw [List.getD_eq_getElem?_getD, hu]
  exact hleq hnp


/-!
## The sum recursor's data

`SumRecData`: the generated sum recursor type's reading, peeled — the
`RecData` of the single-constructor route with `n` minor entries, the
index telescope re-emitted after the minors, and the core
`motive ı⃗ t`; read off the generated type by `sumRecData_of`, and
rule `j`'s reading and grading by `sumRuleData_of`.  The constructors'
data (field data, index readings, sources) is carried as functions of
the position (`ctorDataList`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)


variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The constructors' data, positionally -/

/-- The constructor data list from position-indexed data functions. -/
@[expose] def ctorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatum
  | [], _ => []
  | c :: cs, j => (c.1.name, c.2, dsF j ψ, esF j ψ) :: ctorDataList dsF esF ψ cs (j + 1)

theorem ctorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (ctorDataList dsF esF ψ cs j)[i]? = cs[i]?.map fun c => (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ)
  | [], _, _ => by simp [ctorDataList]
  | c :: cs, j, 0 => by simp [ctorDataList]
  | c :: cs, j, i + 1 => by
    simp only [ctorDataList, List.getElem?_cons_succ]
    rw [ctorDataList_getElem? dsF esF ψ cs (j + 1) i, show j + 1 + i = j + (i + 1) from by omega]

theorem ctorDataList_params {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ₁ ψ₂ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {j : Nat},
      (∀ i, i < cs.length → dsF (j + i) ψ₁ = dsF (j + i) ψ₂ ∧ esF (j + i) ψ₁ = esF (j + i) ψ₂) →
      ctorDataList dsF esF ψ₁ cs j = ctorDataList dsF esF ψ₂ cs j
  | [], _, _ => rfl
  | _ :: cs, j, h => by
    simp only [ctorDataList]
    obtain ⟨h0d, h0e⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h0d h0e
    rw [h0d, h0e]
    congr 1
    exact ctorDataList_params fun i hi => by
      rw [show j + 1 + i = j + (i + 1) from by omega]
      exact h (i + 1) (by simpa using hi)

/-- What the readings need of every constructor at its position:
stored, at the block's level parameters, and its data. -/
@[expose] def CtorFactsAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j) (srcsF j)


/-!
## The sum former's cons

`stageSumFormer`: the P step at the sum's type former, for a given
list of field chains `Fss` (one per constructor, scoped at the
parameter-and-index frame — the restricted chains `rChains` at an
indexed family) — `stageFormer` with the sum leaf `sumTyAV`
and the per-constructor grading `SumFieldsOkB`.  The former is stored
with the empty capability record, so the block's own capability laws
are vacuous.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)


/-- **The sum former leaf's two hereditary premises**, from the former's
data and the chains' grading at the parameter frame. -/
theorem formerWalksS {m : EnvModel V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT nP resSort pps)
    {Fss : (Name → Nat) → List (List AnnotTerm)}
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkS (resSort.eval ψ) ρ (Fss ψ) (pps ψ) ∧
      UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP := by
    simp [hFD.len ψ]
  have hent : ∀ i, i < nP → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkS (resSort.eval ψ) ρ (Fss ψ) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hFssOk ψ ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => sumBodyAV_validV (hFssOk ψ ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw


/-!
## A sum constructor's cons

`stageSumCtor`: the P step at constructor `j`'s cons — onto the
environment holding the former and the earlier constructors — with
the leaf `sumMkAV (resSort.eval ψ) j (ds ψ) Fs_j (uChains Fss)`.
The constructor's run was taken at the former's environment
(`checkSumCtor`) and its data crossed to the cons's environment
(`CtorDataI.cross`); the family application at the bottom — the
family at the parameters and the constructor's index expressions —
folds the former's leaf along the parameters and the index values
(`sumFormerFold`), landing in the fibre at the constructor's own index
tuple, where the point-terminated tuple lives by the index equation
(`restricted_member_intro`).  The capability laws are vacuous (the
block claims no eta or unit law).
-/


/-! ## Kit -/

omit [SetTheory V] in
/-- The frame's index tuple at a consed index spine. -/
theorem frameIdx_consList {nIdx : Nat} {is : List V} (hlen : is.length = nIdx) (X : Nat → V) :
    frameIdx nIdx (consList is X) = is := by
  apply List.ext_getElem
  · simp [frameIdx, hlen]
  · intro l h1 h2
    have hl : l < nIdx := by simpa [frameIdx] using h1
    simp only [frameIdx, List.getElem_map, List.getElem_range]
    rw [consList_apply_lt _ _ _ (by omega), hlen,
      show nIdx - 1 - (nIdx - 1 - l) = l from by omega, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- **The constructor leaf's hereditary premises**: `MkPreS` along
the parameters and `UnderTowerValid` along the whole frame. -/
theorem ctorWalksGen {m : EnvModel V env} {T : Name} {lps : List Name} {cvT cvC : ConstantVal}
    {nP nF nIdx j : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List AnnotTerm)}
    (_hFD : FormerData m cvT (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI m T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (_hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))
    (ψ : Name → Nat) (ρ : Nat → V) :
    MkPreS (resSort.eval ψ) j ρ (((ds ψ).drop nP).map (·.2.2)) (uChains (Fss ψ))
        (ctorBodyAVI m T nP nF ψ (Es ψ)) ((ds ψ).take nP) ∧
      UnderTowerValid ρ
        (sumInjAtAV (resSort.eval ψ) (uChains (Fss ψ)) (((ds ψ).drop nP).map (·.2.2)).length
          (numeralAV j) (mkTowerGoU (resSort.eval ψ) (((ds ψ).drop nP).map (·.2.2)) (idxEqAV [])))
        ((ds ψ).take nP ++ (ds ψ).drop nP) := by
  have hlenDs := hCD.len ψ
  have hlenP : ((ds ψ).take nP).length = nP := List.length_take_of_le (by omega)
  let Fs : List AnnotTerm := ((ds ψ).drop nP).map (·.2.2)
  have hlenFs : Fs.length = nF := by simp [Fs, hlenDs]
  have hst := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ))
  rw [hlenDs] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hCD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hlenDs]
  have hΓplen : ((((ds ψ).take nP).map (·.2.2)).reverse).length = nP := by
    rw [List.length_reverse, List.length_map, hlenP]
  have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
      Sat V (((((ds ψ).take nP).map (·.2.2)).reverse).drop (nP - i)) ρ →
      WellDenotedV V ρ (((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
    intro i hi ρ hρ
    rw [← getD_reverse_take hlenDs hi]
    refine okΓ i (by omega) ρ ?_
    rw [drop_fields_eq hlenDs i (by omega)]
    exact hρ
  have hentP : ∀ i, i < nP → ∃ q, ((ds ψ).take nP)[i]? = some q ∧
      q.2.2 = ((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < ((ds ψ).take nP).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
  have hent : ∀ i, i < nP + nF → ∃ q, (ds ψ)[i]? = some q ∧
      q.2.2 = (((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - i) default := by
    intro i hi
    have hil : i < (ds ψ).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenDs hi (List.getElem?_eq_getElem hil)]⟩
  have hchain : (rChains nIdx nIdx (Fss ψ) (Ess ψ))[j]? = some (rChain nIdx nIdx Fs (Es ψ)) := by
    rw [rChains_getElem?, hFsj ψ, hEsj ψ]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds => MkPreS (resSort.eval ψ) j ρ Fs (uChains (Fss ψ))
        (ctorBodyAVI m T nP nF ψ (Es ψ)) pds)
      hΓplen hlenP hentP okΓp
      (fun ρ hρ => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat_nil V ρ)
    · rw [List.drop_zero] at hw; exact hw
    -- the base: at the parameter frame
    have hρt : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ := (hiff ψ ρ).mpr hρ
    have hokFss := (hFssOkP ψ ρ hρ).1
    refine ⟨SumFieldsOkB_uChains hokFss, by rw [uChains_getElem?, hFsj ψ]; rfl, fun bs hsp => ?_⟩
    have hlenI : (idxValsAt ρ (Es ψ) bs).length = nIdx := by
      simp [idxValsAt, hCD.lenE ψ]
    refine ⟨sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
      (rChains nIdx nIdx (Fss ψ) (Ess ψ)), ?_, ?_⟩
    · exact hfold ψ ρ hρt bs hsp
    · -- the point-terminated tuple lives in the fibre at the index tuple
      rw [sumFibre_of_getElem? hchain]
      have hshift : shiftE nIdx 0 (consList (idxValsAt ρ (Es ψ) bs) ρ) = ρ := by
        rw [← hlenI]; exact shiftE_consList _ _
      refine restricted_member_intro (Fs := liftFields nIdx 0 Fs) ?_ ?_
      · rw [spineFit_liftFields, hshift]
        exact hsp
      · rw [EqAll_idxEqsAt (hCD.lenE ψ) hsp.length_eq, hshift, frameIdx_consList hlenI]
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ
        (sumInjAtAV (resSort.eval ψ) (uChains (Fss ψ)) Fs.length (numeralAV j)
          (mkTowerGoU (resSort.eval ψ) Fs (idxEqAV []))) ds')
      hΓlen hlenDs hent okΓ
      (fun ρ' hρ' => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat_nil V ρ)
    · rw [List.take_append_drop]
      rw [List.drop_zero] at hw
      exact hw
    rw [reverse_map_take_drop (ds ψ) nP] at hρ'
    have hspF := spineFit_of_sat (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((ds ψ).drop nP).map (·.2.2)) hρ'
    rw [hlenFs] at hspF
    have hρp : Sat V (((ds ψ).take nP).map (·.2.2)).reverse (fun j => ρ' (j + nF)) := by
      have := Sat_drop hρ' nF
      rw [List.drop_append_of_le_length (by simp [hlenDs]),
        List.drop_eq_nil_of_le (by simp [hlenDs]), List.nil_append] at this
      exact this
    obtain ⟨-, hvAll⟩ := hFssOkP ψ _ hρp
    have hvF : FieldsValid (fun j => ρ' (j + nF)) Fs :=
      hvAll _ (List.mem_of_getElem? (hFsj ψ))
    have := sumInj_validV_at_fields (w := resSort.eval ψ) (j := j) (uChains_validV hvAll) hvF hspF
    rwa [consList_range_reverse] at this

/-- **The P step at a sum-shaped constructor's cons**, for a given fibre fold. -/
theorem stageCtorGen {T : Name}
    {F : Nat} {lps : List Name} {nP nF nIdx j : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    -- **the other stored families' η constructors are not this one**
    -- (`capsOk_cons_native`'s `hother`): at ONE family it is closure
    -- (`etaCtor_ne_of_closed`); at a BLOCK a still-pending member's η
    -- constructor is one of ITS OWN constructors, which the block's
    -- distinct names refute
    (hE : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      env.find? T' = some (.indInfo cvT' caps') → T' ≠ T →
      ConLeche.reservedBasisNames.contains T' = false → caps'.eta = true →
      ConLeche.EtaFamilyStored ⟨.ctorInfo cvCa nP nF :: env.consts⟩ T' caps' →
      caps'.etaCtor ≠ cvCa.name)
    (mp : EnvModelM V μ env)
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env₁ T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    -- the constructor is fresh at the cons's environment and its type
    -- resolves there
    (hfresh : env.find? cvCa.name = none)
    (htr : cvCa.type.constsResolve env = true)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hlpsC : cvCa.levelParams = lps)
    {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List AnnotTerm)}
    -- the block's own capability laws at the cons (task #210 Parts A
    -- and B), at any carrier agreeing with this one off the
    -- constructor's name and storing the constructor's leaf there
    (hTlaws : ∀ m₂ : EnvModel V ⟨.ctorInfo cvCa nP nF :: env.consts⟩,
      (∀ n, n ≠ cvCa.name → m₂.acval n = mp.base2.acval n) →
      (∀ ψ, m₂.acval cvCa.name ψ
        = sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP).map (·.2.2)) (uChains (Fss ψ))) →
      CapsLawsAt m₂ T cvTa caps)
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ lps, ψ₁ q = ψ₂ q) → Fss ψ₁ = Fss ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ Fss ψ, FieldsBelow nP Fs)
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvCa nP nF :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvCa.name
        (fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP).map (·.2.2))
          (uChains (Fss ψ))) := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, hnres, hpshape, -, hlbt, hitf, type', -, -, hann', htp, -, -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  have hCname : cvCa.name = cvC.name := by rw [hty]
  have hcb : ConstsBound env cvCa.type := constsBound_of_constsResolve _ htr
  have hTC : T ≠ cvCa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvCa nP nF :: env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF ?_ ?_ (Expr.constsResolve_mono htr) ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · show cvCa.type.hasFvar = false; rw [hty]; exact htf'
    · show cvCa.type.allLevelParamsDefined cvCa.levelParams = true; rw [hty]; exact htp
    · show cvCa.type.looseBVarsBounded 0 = true; rw [hty]; exact hbt'
  let Fs : (Name → Nat) → List AnnotTerm := fun ψ => ((ds ψ).drop nP).map (·.2.2)
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (Fs ψ) (uChains (Fss ψ))
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    sumMkAV_below (hCD.below ψ)
      ((DomsBelow.drop nP (hCD.below ψ)).fields)
      (by rw [Nat.zero_add]; exact uChains_below (hFssBelow ψ))
      (by show nP + (((ds ψ).drop nP).map (·.2.2)).length = (ds ψ).length
          simp [hCD.len ψ])
  have hwalks := ctorWalksGen hFD hCD hfold hFsj hEsj hiff hFssOkP hIdx
  have hz : ∀ ψ, ∀ d ∈ (ds ψ).take nP ++ (ds ψ).drop nP,
      (resSort.eval ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    rw [List.take_append_drop] at hd
    exact hCD.bits ψ d hd
  have hreadC : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvCa.name A)
        ⟨.ctorInfo cvCa nP nF :: env.consts⟩ ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .ctorInfo cvCa nP nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa nP nF).name = false := by
    show ConLeche.reservedBasisNames.contains cvCa.name = false
    rw [hCname]; exact hnres
  have hpshapeC : (ConstantInfo.ctorInfo cvCa nP nF).name.isProjFnShape = false := by
    show cvCa.name.isProjFnShape = false
    rw [hCname]; exact hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvCa nP nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHead.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    have hφT : ∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q := by rw [hlpsT, ← hlpsC]; exact hφ
    obtain ⟨-, hw⟩ := hFD.params ψ₁ ψ₂ hφT
    show sumMkAV _ j (ds ψ₁) (((ds ψ₁).drop nP).map (·.2.2)) (uChains (Fss ψ₁))
      = sumMkAV _ j (ds ψ₂) (((ds ψ₂).drop nP).map (·.2.2)) (uChains (Fss ψ₂))
    rw [hw, (hCD.params ψ₁ ψ₂ hφ).1, hFssParams ψ₁ ψ₂ (by rw [← hlpsC]; exact hφ)]
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.1
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.2
  · exact fun ψ => ⟨_, hreadC ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hCD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    have := sumMkAV_mem (V := V) (hz ψ) (hwalks ψ ρ).1
    rw [List.take_append_drop] at this
    exact this
  · -- `caps_ok`: nothing is claimed by the block's family
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvCa nP nF) (A := A)
      (T := T) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape hfam
      exact hE T' cvT' caps' hf hne hres hcape hfam
    · intro cvT caps' hf _
      have hfT' : (⟨.ctorInfo cvCa nP nF :: env.consts⟩ : Env).find? T
          = some (.indInfo cvTa caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun h => hTC h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      refine hTlaws m₂ (fun n hn => ?_) (fun ψ => ?_)
      · rw [hac]
        exact acvalWith_ne hn
      · rw [hac]
        exact congrFun acvalWith_self ψ


/-!
## The sum recursor's frames

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the nested product over the former's index telescope into
the family at each index tuple, minor entry `j` (at the frame under
the motive and the earlier minors) to constructor `j`'s minor space
`minorSpI` (its conclusion at the constructor's own index values),
the index entries to the former's index telescope, the major entry
to the family at the frame's index tuple — and the K-frame's two
hypothesis records (`RecHypS`, `SqHypS`).  The walk: down the minor
chain (`sumMinorsTail`), then down the index chain (`sumIdxTail`),
the frame kept as an explicit `consList`.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta)


/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
@[expose] def fssOf (nP : Nat) (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The index readings of the constructor data. -/
@[expose] def essOf (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => cd.2.2.2

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]


/-!
## The direct sum's install, assembled

`declSumP`: the P carrier survives the direct sum install's run
(`DeclSumRun`).  The stages: the former (twice — first with the
empty chain list, to read the constructors' field data and index
readings at a carrier storing the former; then with the restricted
chains `rChains` read off that data, the readings identified by
`denoteP_openPis_agree` (field domains) and `CtorDataI.Es_eq` (index
readings) since neither mentions the former), the constructors in
order (`sumCtorsLoop`, every earlier constructor's data and leaf
crossing each later cons; the pending constructors staying fresh by
the distinct-names guard), and the recursor (`stageSumRec`).
-/


variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- Distinct names, positionally. -/
theorem names_ne_of_nodup {ctorsA : List (ConstantVal × Nat)}
    (hnd : (ctorsA.map (·.1.name)).Nodup) {i j : Nat} {cAi cAj : ConstantVal × Nat}
    (hi : ctorsA[i]? = some cAi) (hj : ctorsA[j]? = some cAj) (hne : i ≠ j) :
    cAi.1.name ≠ cAj.1.name := by
  have hil : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp := List.pairwise_iff_getElem.mp hnd
  have hi' : ctorsA[i] = cAi := by
    have := List.getElem?_eq_getElem hil; rw [hi] at this; exact (Option.some.inj this).symm
  have hj' : ctorsA[j] = cAj := by
    have := List.getElem?_eq_getElem hjl; rw [hj] at this; exact (Option.some.inj this).symm
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := hp i j (by simpa using hil) (by simpa using hjl) hlt
    simp only [List.getElem_map, hi', hj'] at this
    exact this
  · have := hp j i (by simpa using hjl) (by simpa using hil) hgt
    simp only [List.getElem_map, hi', hj'] at this
    exact fun h => this h.symm

/-! ## The constructors' loop -/

/-- The facts about the pending constructors at an environment. -/
@[expose] def PendingAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, k ≤ i → ctorsA[i]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF i) (dsF i) (esF i) (srcsF i)

/-- The facts about the consed constructors at an environment. -/
@[expose] def ConsedAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, i < k → ctorsA[i]? = some cA →
    CtorFactsAt m T lps nP nIdx resSort isProp large idxF dsF esF srcsF i cA ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV (resSort.eval ψ) i (dsF i ψ) (((dsF i ψ).drop nP).map (·.2.2))
          (uChains (fssOf nP (ctorDataList dsF esF ψ ctorsA 0)))

end ConLeche.Model
