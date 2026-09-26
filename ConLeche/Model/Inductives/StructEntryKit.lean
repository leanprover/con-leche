module

public import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Verify.Inductives.DirectGen
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# Block library: the projection entries and the projection table

The projection entry's kit (Π-peels along spines, fits, gradings as a
congruence below a bound, the entry residual's chain frame); unused
fields are invariant; the projection body's frame; the projection
table's cons.
-/

/-!
## The projection entry's kit

Semantic and syntactic pieces of a tower entry's install:

* the syntactic Π-peel of a tower along a spine is the body's
  instantiation sequence (`peelPis_of_piTeleAV`, the fit-free spine of
  `teleFitPA_of_tower`), and a `mkPisAV` tower is a `PiTeleAV`;
* a graded application of a nonzero-bit λ-tower **fits** the tower
  (`spineFit_of_wellDenotedV_mkAppN_lam`): the application clause's package
  pins each argument to the layer's domain (a graph's domain is
  rigid, `graph_dom_of_mem_piSet`) — the converse of
  `mkAppN_wellDenotedV_of_lam`;
* the projection spelling is graded at a tower member in the graph
  regime (`wellDenoted_projAV_tower`, the pair chain's Σ packages) and at
  the point in the squash regime (`wellDenoted_projAV_pt`);
* the coarse guard level's content (`eval_foldl_max_zero_iff`), and
  the squash prefix: a fitting spine over proof fields is the point
  spine (`spineFit_eq_replicate_pt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The peel -/

/-- A `mkPisAV` tower is a `PiTeleAV` over its reversed domains. -/
theorem piTeleAV_mkPisAV :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      PiTeleAV ds.length (mkPisAV ds b) ((ds.map (·.2.2)).reverse) b
  | [], _ => PiTeleAV.nil
  | d :: ds, b => by
    simp only [List.length_cons, mkPisAV, List.map_cons, List.reverse_cons]
    exact PiTeleAV.cons (piTeleAV_mkPisAV ds b)

/-- **The fit-free peel**: the syntactic Π-peel of a tower along a
spine of the tower's length is the body's instantiation sequence
(`teleFitPA_of_tower`'s spine, memberships dropped). -/
theorem peelPis_of_piTeleAV :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ws : List AnnotTerm}, ws.length = k →
      ConLeche.Model.AnnotTerm.peelPis T ws
        = some (ConLeche.Model.AnnotTerm.instSeq ws (k - 1) R) := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws hlen
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    rfl
  | succ k ihk =>
    intro T Γ R h ws hlen
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hinst := htail.inst w 0
    have := ihk hinst hlen'
    rw [show ConLeche.Model.AnnotTerm.instSeq (w :: ws') (k + 1 - 1) R
        = ConLeche.Model.AnnotTerm.instSeq ws' (k - 1) (R.inst w k) from by
      rw [AnnotTerm.instSeq_cons]
      simp only [Nat.add_sub_cancel]]
    rw [show (0 : Nat) + k = k from Nat.zero_add k] at this
    exact this

/-- The instantiation sequence of a `.pi` is a `.pi` over the
sequence of its domain. -/
theorem instSeq_pi_dom :
    ∀ (ws : List AnnotTerm) (t u v : Nat) (A B : AnnotTerm),
      ∃ B', ConLeche.Model.AnnotTerm.instSeq ws t (.pi u v A B)
        = .pi u v (ConLeche.Model.AnnotTerm.instSeq ws t A) B'
  | [], _, _, _, _, B => ⟨B, rfl⟩
  | w :: ws, t, u, v, A, B => by
    rw [AnnotTerm.instSeq_cons, AnnotTerm.instSeq_cons, AnnotTerm.inst_pi]
    exact instSeq_pi_dom ws (t - 1) u v (A.inst w t) (B.inst w (t + 1))

/-! ## Fits from gradings -/

/-- **A graded application of a nonzero-bit λ-tower fits the tower**:
each application clause's package puts the argument in a domain the
layer's graph inhabits as a function, and a graph's domain is rigid
(`mkAppN_wellDenotedV_of_lam`'s converse). -/
theorem spineFit_of_wellDenotedV_mkAppN_lam :
    ∀ {lds : List (Nat × AnnotTerm)} {b f : AnnotTerm} {args : List AnnotTerm} {ρ σ : Nat → V},
      (∀ d ∈ lds, d.1 ≠ 0) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = interp V σ (mkLamsAV lds b) →
      args.length = lds.length →
      SpineFit σ (lds.map (·.2)) (args.map (interp V ρ))
  | [], _, _, [], _, _, _, _, _, _ => trivial
  | [], _, _, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, _, _, [], _, _, _, _, _, hlen => by simp at hlen
  | d :: lds, b, f, a :: args, ρ, σ, hnz, hok, hval, hlen => by
    simp only [List.map_cons, SpineFit]
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokApp := Rules.mkAppN_head args hok
    obtain ⟨-, -, v, A, B, hf, ha, -⟩ := (WellDenoted_app V ρ f a) ▸ hokApp.1
    have hd : d.1 ≠ 0 := hnz d List.mem_cons_self
    rw [hval] at hf
    simp only [mkLamsAV, interp_lam] at hf
    rw [lamR_pos hd] at hf
    -- the package's codomain bit is nonzero: a graph is not the point
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0, piR_zero] at hf
      exact graph_ne_pt (eq_pt_of_mem_truthVal hf)
    rw [piR_pos hv] at hf
    have hmem : interp V ρ a ∈ˢ interp V σ d.2 := graph_dom_of_mem_piSet hf _ ha
    refine ⟨hmem, ?_⟩
    refine spineFit_of_wellDenotedV_mkAppN_lam (b := b) (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd'))
      hok ?_ (by simpa using hlen)
    rw [interp_app, hval]
    simp only [mkLamsAV, interp_lam]
    rw [app_lamR_pos hd hmem]

/-! ## The projection spelling's grading -/

omit [SetTheory V] in
theorem nat_max_self (w : Nat) : Nat.max w w = w := by simp [Nat.max]

/-- At the point (the squash regime's every member) the projection
spelling is graded through the trivial Σ package. -/
theorem wellDenoted_projAV_pt :
    ∀ {i : Nat} {e : AnnotTerm} {ρ : Nat → V},
      WellDenoted V ρ e → interp V ρ e = (pt : V) → WellDenoted V ρ (projAV i e)
  | 0, e, ρ, hok, hpt => by
    show WellDenoted V ρ (.fst e)
    rw [WellDenoted_fst]
    refine ⟨hok, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
      fun _ _ => unitSet_mem_univ 0⟩
    rw [hpt, nat_max_self]
    exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet
  | i + 1, e, ρ, hok, hpt => by
    show WellDenoted V ρ (projAV i (.snd e))
    refine wellDenoted_projAV_pt (i := i) ?_ ?_
    · rw [WellDenoted_snd]
      refine ⟨hok, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
        fun _ _ => unitSet_mem_univ 0⟩
      rw [hpt, nat_max_self]
      exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet
    · rw [interp_snd, hpt, ssnd_pt]

/-- At a tower member in the graph regime the projection spelling is
graded: each pair step's Σ package is the tower's own level, with the
tail in the fibre (`ssnd_mem_gen`). -/
theorem wellDenoted_projAV_tower {w : Nat} :
    ∀ {i : Nat} {Fs : List AnnotTerm} {ρ' : Nat → V} {x : V} {e : AnnotTerm} {ρ : Nat → V},
      FieldsBound w ρ' Fs → x ∈ˢ towerSet w (teleOfFields ρ' Fs) →
      WellDenoted V ρ e → interp V ρ e = x → i < Fs.length →
      WellDenoted V ρ (projAV i e) := by
  intro i
  induction i with
  | zero =>
    intro Fs ρ' x e ρ hb hx hok hval hi
    match Fs, hb, hx, hi with
    | F :: Fs', hb, hx, _ =>
      show WellDenoted V ρ (.fst e)
      rw [WellDenoted_fst]
      refine ⟨hok, w, w, interp V ρ' F,
        fun a => towerSet w (teleOfFields (cons a ρ') Fs'), ?_, hb.1,
        fun a ha => towerSet_univ_teleOfFields (hb.2 a ha)⟩
      rw [hval, nat_max_self]
      exact hx
  | succ i ih =>
    intro Fs ρ' x e ρ hb hx hok hval hi
    match Fs, hb, hx, hi with
    | F :: Fs', hb, hx, hi =>
      show WellDenoted V ρ (projAV i (.snd e))
      have hx' : x ∈ˢ sigmaSet (Nat.max w w) (interp V ρ' F)
          (fun a => towerSet w (teleOfFields (cons a ρ') Fs')) := by
        rw [nat_max_self]; exact hx
      have hA : interp V ρ' F ∈ˢ (univ w : V) := hb.1
      have hB : ∀ a, a ∈ˢ interp V ρ' F →
          towerSet w (teleOfFields (cons a ρ') Fs') ∈ˢ (univ w : V) :=
        fun a ha => towerSet_univ_teleOfFields (hb.2 a ha)
      have hfst := sfst_mem_gen V hA hx'
      have hsnd := ssnd_mem_gen V hA hB hx'
      refine ih (Fs := Fs') (ρ' := cons (sfst x) ρ') (x := ssnd x) (hb.2 _ hfst) hsnd ?_ ?_
        (by simpa using hi)
      · rw [WellDenoted_snd]
        refine ⟨hok, w, w, interp V ρ' F,
          fun a => towerSet w (teleOfFields (cons a ρ') Fs'), ?_, hA, hB⟩
        rw [hval]; exact hx'
      · rw [interp_snd, hval]

/-! ## The squash prefix -/

/-- The prefix of a fitting spine fits the prefix, and the next field
is inhabited at it. -/
theorem spineFit_prefix_next {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i < Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) ∧
      (as.getD i pt) ∈ˢ interp V (consList (as.take i) ρ) (Fs.getD i default) := by
  have hsplit : Fs = Fs.take i ++ Fs.drop i := (List.take_append_drop i Fs).symm
  rw [hsplit] at h
  obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_inv h
  have hl1 : as₁.length = i := by rw [h1.length_eq, List.length_take]; omega
  have htake : (as₁ ++ as₂).take i = as₁ := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [htake]
  refine ⟨h1, ?_⟩
  rw [List.drop_eq_getElem_cons hi] at h2
  match as₂, h2 with
  | b :: as₂, h2 =>
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl1, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h2.1

/-! ## Application values -/

theorem interp_mkAppN_foldl (ρ : Nat → V) (as : List AnnotTerm) (f : AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as)
      = (as.map (interp V ρ)).foldl SetTheory.app (interp V ρ f) := by
  rw [interp_mkAppN, List.foldl_map]


/-!
## The projection entry's kit, continued

* the grading is a congruence below a variable bound
  (`WellDenotedV_congr_below`, `interp_congr_below`'s twin for the two
  truthfulness halves);
* the field chain's per-field grading at a fitting prefix
  (`fieldsOkB_getD`, `fieldsValid_getD`);
* the entry residual's chain frame: the readings of the opened
  parameters and the earlier projections, and their value chain
  against the subject's projection spine (`chain_entry_agree`).
-/


/-! ## Grading below a bound -/

omit [SetTheory V] in
theorem cons_agree_below {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i < k → ρ i = ρ' i)
    (x : V) : ∀ i, i < k + 1 → cons x ρ i = cons x ρ' i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)

theorem WellDenoted_congr_below :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (WellDenoted V ρ e ↔ WellDenoted V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | prf => intros; simp
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_app, WellDenoted_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag,
      interp_congr_below V f k ρ ρ' hb.1 hag, interp_congr_below V a k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_lam, WellDenoted_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [← interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_pi, WellDenoted_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_eqE, WellDenoted_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_fst, WellDenoted_fst, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_snd, WellDenoted_snd, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]

theorem AnnotValid_congr_below :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (AnnotValid V ρ e ↔ AnnotValid V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp [AnnotValid]
  | sort u => intros; simp [AnnotValid]
  | const c us => intros; simp [AnnotValid]
  | prf => intros; simp [AnnotValid]
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_app, AnnotValid_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_lam, AnnotValid_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_pi, AnnotValid_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [← interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_eqE, AnnotValid_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_fst, AnnotValid_fst, ihe k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_snd, AnnotValid_snd, ihe k ρ ρ' hb hag]

theorem WellDenotedV_congr_below (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V)
    (hb : Term.bvarsBelow k e.erase) (hag : ∀ i, i < k → ρ i = ρ' i) :
    WellDenotedV V ρ e ↔ WellDenotedV V ρ' e := by
  unfold WellDenotedV
  rw [WellDenoted_congr_below e k ρ ρ' hb hag, AnnotValid_congr_below e k ρ ρ' hb hag]

/-! ## The field chain, indexed -/

theorem fieldsValid_drop :
    ∀ {Fs₁ : List AnnotTerm} {as : List V} {Fs₂ : List AnnotTerm} {ρ : Nat → V},
      FieldsValid ρ (Fs₁ ++ Fs₂) → SpineFit ρ Fs₁ as →
      FieldsValid (consList as ρ) Fs₂
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | F :: Fs₁, a :: as, Fs₂, ρ, h, hsp => by
    rw [consList_cons]
    exact fieldsValid_drop (h.2 a hsp.1) hsp.2

/-- Field `j`'s domain is graded at every fitting prefix. -/
theorem fieldsOkB_getD {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (h : FieldsOkB w ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    WellDenoted V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := FieldsOkB.drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

theorem fieldsValid_getD {Fs : List AnnotTerm} {ρ : Nat → V}
    (h : FieldsValid ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    AnnotValid V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := fieldsValid_drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

/-! ## The residual's chain frame -/

/-- The readings of the opened parameters at the entry's full depth. -/
@[expose] def entryParamBvars (nP : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP - k)

/-- The readings of the earlier projections of the subject, at the
table's projection offset `off` (task #210 Part A: `projS (j + off)`
is field `j` of a carrier whose tuple tower sits below `off` leading
pair components). -/
@[expose] def entryProjAVs (off i : Nat) : List AnnotTerm :=
  (List.range i).map fun j => projAV (j + off) (.bvar 0)

omit [SetTheory V] in
theorem entryParamBvars_length (nP : Nat) : (entryParamBvars nP).length = nP := by
  simp [entryParamBvars]

omit [SetTheory V] in
theorem entryProjAVs_length (off i : Nat) : (entryProjAVs off i).length = i := by
  simp [entryProjAVs]

/-- The opened parameters read to `entryParamBvars` at depth `nP + 1`. -/
theorem denoteMetaSpine_entryParams {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP : Nat} {fvsP : List Expr}
    (hidx : ∀ (k : Nat) (x : Expr), fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hlen : fvsP.length = nP) :
    DenoteMetaSpine acval env φ (nP + 1) fvsP (entryParamBvars nP) := by
  have h := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) (nP + 1) fvsP 0
    (fun k x hx => by obtain ⟨ty, rfl⟩ := hidx k x hx; exact ⟨ty, by rw [Nat.zero_add]⟩)
  rw [hlen] at h
  have e : ((List.range nP).map fun k => AnnotTerm.bvar (nP + 1 - 1 - (0 + k)))
      = entryParamBvars nP := by
    unfold entryParamBvars
    apply List.map_congr_left
    intro k _
    congr 1
    omega
  rw [e] at h
  exact h

/-- The earlier projections of the subject read to `entryProjAVs` at
depth `nP + 1`, through the stored tower entries. -/
theorem denoteMetaSpine_entryProjs {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP off : Nat} {T : Name} {sdom : Expr}
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry ∧ entry.off = off) :
    DenoteMetaSpine acval env φ (nP + 1)
      ((List.range i).map fun j => Expr.proj T j (.fvar nP sdom)) (entryProjAVs off i) := by
  unfold entryProjAVs
  suffices ∀ (l : List Nat), (∀ j ∈ l, j < i) →
      DenoteMetaSpine acval env φ (nP + 1)
        (l.map fun j => Expr.proj T j (.fvar nP sdom))
        (l.map fun j => projAV (j + off) (.bvar 0)) from
    this (List.range i) (fun j hj => List.mem_range.mp hj)
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons j l ih =>
    intro hl
    obtain ⟨entry, hfe, hoff⟩ := hprev j (hl j List.mem_cons_self)
    simp only [List.map_cons]
    refine .cons ?_ (ih fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
    rw [denoteMeta_proj_tower hfe (denoteMeta_fvar acval (nP + 1) nP sdom),
      show nP + 1 - 1 - nP = 0 from by omega, hoff]

/-- **The chain frame agrees with the projection spine's frame** below
the field's depth: the parameter readings pick the frame's parameter
values, the projection readings the subject's projections. -/
theorem chain_entry_agree (nP off i : Nat) (ρ : Nat → V) :
    ∀ n, n < nP + i →
      chain V ρ (entryParamBvars nP ++ entryProjAVs off i) n
        = consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)) n := by
  intro n hn
  have hlen : (entryParamBvars nP ++ entryProjAVs off i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  rw [chain_lt (by rw [hlen]; exact hn), hlen]
  rcases Nat.lt_or_ge n i with hni | hni
  · -- a projection slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entryParamBvars_length]; omega), entryParamBvars_length]
    unfold entryProjAVs
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, projAV_interp, interp_bvar]
    rw [consList_apply_lt _ _ _ (by rw [projList_length]; exact hni), projList_length,
      projList_eq_map_range, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [projS_add_dropS, show nP + i - 1 - n - nP = i - 1 - n from by omega]
  · -- a parameter slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (by rw [entryParamBvars_length]; omega)]
    unfold entryParamBvars
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, interp_bvar]
    have := consList_apply_add (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)) (n - i)
    rw [projList_length, show n - i + i = n from by omega] at this
    rw [this]
    congr 1
    omega


/-!
## Unused fields are invariant

The official `infer_proj` guard joins only the earlier fields *a
later field uses* (`structUsedLater`: the field's variable occurs in
the constructor telescope after its binder).  At a squash instance
the structure's members are one point and every earlier projection
reads as the point, so the projection law needs the field's type at
the **point prefix**; the guard makes the used earlier fields proof
fields (their fitting values are the point), and an unused one must
not matter.  This module carries that: an unused binder's variable is
absent from the opened telescope's later annotations
(`openPisAtFvars_leaf_free`), a leaf-free reading is a lift at the
leaf's index (`denoteMeta_liftN_of_leaf_free`), and interpretation and
grading are invariant under a lift's index (`interp_congr_lifts`,
`wellDenotedV_congr_lifts`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta)


/-! ## The syntax: an unused binder -/

omit [SetTheory V] in
/-- Instantiating a variable-free term above an index leaves the
lower indices' occurrences alone. -/
theorem hasLooseBVar_instantiate1_lt {v : Expr} (hv : ∀ i, v.hasLooseBVar i = false) :
    ∀ (e : Expr) (i k : Nat), i < k →
      (e.instantiate1 v k).hasLooseBVar i = e.hasLooseBVar i := by
  intro e
  induction e with
  | bvar j =>
    intro i k hik
    simp only [Expr.instantiate1]
    split
    · next hj =>
      subst hj
      rw [hv]
      simp only [Expr.hasLooseBVar]
      exact (beq_eq_false_iff_ne.mpr (by omega)).symm
    · split
      · next hj hj' =>
        simp only [Expr.hasLooseBVar]
        rw [beq_eq_false_iff_ne.mpr (show i ≠ j - 1 from by omega),
          beq_eq_false_iff_ne.mpr (show i ≠ j from by omega)]
      · rfl
  | fvar _ _ => intros; rfl
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | lit _ => intros; rfl
  | app f a ihf iha =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihf i k hik, iha i k hik]
  | lam ty b _ ihty ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihty i k hik, ihb (i + 1) (k + 1) (by omega)]
  | forallE ty b _ ihty ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihty i k hik, ihb (i + 1) (k + 1) (by omega)]
  | letE t v' b iht ihv ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, iht i k hik, ihv i k hik,
      ihb (i + 1) (k + 1) (by omega)]
  | proj _ _ e ihe =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihe i k hik]

omit [SetTheory V] in
/-- Instantiating an absent variable introduces no leaf. -/
theorem fvarLeaves_instantiate1_of_not_hasLooseBVar :
    ∀ (e v : Expr) (k : Nat), e.hasLooseBVar k = false →
      ∀ l, l ∈ (e.instantiate1 v k).fvarLeaves → l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | bvar j =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq] at hk
    simp only [Expr.instantiate1] at hl
    rw [if_neg (Ne.symm hk)] at hl
    split at hl <;> simp [Expr.fvarLeaves] at hl
  | fvar _ _ => intro v k _ l hl; exact hl
  | sort _ => intro v k _ l hl; exact hl
  | const _ _ => intro v k _ l hl; exact hl
  | lit _ => intro v k _ l hl; exact hl
  | app f a ihf iha =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihf v k hk.1 l hl)
    · exact Or.inr (iha v k hk.2 l hl)
  | lam ty b _ ihty ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty v k hk.1 l hl)
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | forallE ty b _ ihty ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty v k hk.1 l hl)
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | letE t v' b iht ihv ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · exact Or.inl (Or.inl (iht v k hk.1.1 l hl))
    · exact Or.inl (Or.inr (ihv v k hk.1.2 l hl))
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | proj _ _ e ihe =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves] at hl ⊢
    exact ihe v k hk l hl

omit [SetTheory V] in
theorem fvar_hasLooseBVar (idx : Nat) (ty : Expr) (i : Nat) :
    (Expr.fvar idx ty).hasLooseBVar i = false := rfl

omit [SetTheory V] in
/-- **An unused binder is absent from the opening.**  If the telescope
after binder `m` does not mention it, no later opener's annotation and
not the opened body carries the `m`-th opener as a leaf. -/
theorem openPisAtFvars_leaf_free :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr} (m : Nat)
      {bs : List (Expr × BinderMeta)} {rest : Expr},
      openPisAtFvars n e d = some (fvs, o) → m < n →
      e.stripPis (m + 1) = some (bs, rest) → rest.hasLooseBVar 0 = false →
      (∀ l ∈ e.fvarLeaves, l.1 ≠ d + m) →
      (∀ k, m < k → ∀ x, fvs[k]? = some x → ∀ l ∈ x.fvarLeaves, l.1 ≠ d + m) ∧
      (∀ l ∈ o.fvarLeaves, l.1 ≠ d + m)
  | 0, _, _, _, _, m, _, _, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero m)
  | n + 1, e, d, fvs, o, m, bs, rest, hop, hm, hst, hfree, hleaves => by
    match e, hop, hst with
    | .forallE dom body mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        -- the openers' leaves are the term's or openers
        have hopen := openPisAtFvars_leaves n hop'
        have hidx := openPisAtFvars_index n _ (d + 1) hop'
        cases m with
        | zero =>
          -- `rest` is the body: the opener at `d` is never substituted
          simp only [Expr.stripPis, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨-, rfl⟩ := hst
          have hsub : ∀ l, l ∈ (body.instantiate1 (.fvar d dom)).fvarLeaves →
              l ∈ body.fvarLeaves :=
            fun l hl => fvarLeaves_instantiate1_of_not_hasLooseBVar body _ 0 hfree l hl
          have hbody : ∀ l ∈ body.fvarLeaves, l.1 ≠ d + 0 := by
            intro l hl
            exact hleaves l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl)
          have key : ∀ l, (l ∈ o'.fvarLeaves ∨ ∃ x ∈ fvs', l ∈ x.fvarLeaves) → l.1 ≠ d + 0 := by
            intro l hl
            rcases hopen l hl with h | h
            · exact hbody l (hsub l h)
            · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
              obtain ⟨ty', heq⟩ := hidx q _ hq
              have : l.1 = d + 1 + q := by
                have := congrArg (fun e => match e with | .fvar i _ => i | _ => 0) heq
                simpa using this
              omega
          refine ⟨?_, fun l hl => key l (Or.inl hl)⟩
          intro k hk x hx l hl
          cases k with
          | zero => exact absurd hk (Nat.lt_irrefl _)
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx
            exact key l (Or.inr ⟨x, List.mem_of_getElem? hx, hl⟩)
        | succ m =>
          -- `rest` is below the head binder: strip it off the instantiated body
          simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
          obtain ⟨⟨bs', rest'⟩, hst', heq⟩ := hst
          simp only [Prod.mk.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          have hsome := Expr.stripPis_instantiate1_isSome (v := .fvar d dom) (m + 1) (e := body) 0
            (by rw [hst']; rfl)
          obtain ⟨⟨bs'', rest''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨hr, -⟩ := Expr.stripPis_instantiate1_eq (v := .fvar d dom) (m + 1) 0 hst' hst''
          rw [Nat.zero_add] at hr
          have hfree' : rest''.hasLooseBVar 0 = false := by
            rw [hr, hasLooseBVar_instantiate1_lt (fvar_hasLooseBVar d dom) rest' 0 (m + 1)
              (by omega)]
            exact hfree
          have hleaves' : ∀ l ∈ (body.instantiate1 (.fvar d dom)).fvarLeaves,
              l.1 ≠ d + 1 + m := by
            intro l hl
            rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl | hl
            · exact fun h => hleaves l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl)
                (by rw [h]; omega)
            · simp only [Expr.fvarLeaves, List.mem_cons] at hl
              rcases hl with rfl | hl
              · omega
              · exact fun h => hleaves l
                  (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl) (by rw [h]; omega)
          obtain ⟨h1, h2⟩ := openPisAtFvars_leaf_free n m hop' (by omega) hst'' hfree' hleaves'
          refine ⟨?_, fun l hl => by have := h2 l hl; omega⟩
          intro k hk x hx l hl
          cases k with
          | zero => exact absurd hk (Nat.not_lt_zero _)
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx
            have := h1 k (by omega) x hx l hl
            omega
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _ | .const _ _, hop, _
    | .app _ _, hop, _ | .lam _ _ _, hop, _ | .letE _ _ _, hop, _ | .lit _, hop, _
    | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The reading: a leaf-free term reads as a lift -/

/-- **A leaf-free reading is a lift at the leaf's index.**  A term
without the `q`-th variable as a leaf reads, at depth `d`, as a
reading lifted over index `d - 1 - q` — the slot that variable would
read as. -/
theorem denoteMeta_liftN_of_leaf_free {env : Env} (m : EnvModel V env) {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      ∀ {q : Nat}, q < d → (∀ l ∈ e.fvarLeaves, l.1 ≠ q) →
      ∀ {ea : AnnotTerm}, denoteMeta m.acval env φ d e = some ea →
      ∃ X : AnnotTerm, ea = X.liftN 1 (d - 1 - q) := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro _ q _ _ ea h
    rw [denoteMeta] at h
    exact ⟨ea, by rw [← Option.some.inj h]; rfl⟩
  | case2 d idx ty =>
    intro hw q hq hl ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    simp only [Expr.WScoped] at hw
    have hne : idx ≠ q := hl (idx, ty) (by simp [Expr.fvarLeaves])
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨.bvar (d - 2 - idx), ?_⟩
      rw [AnnotTerm.liftN_bvar, if_neg (by omega)]
      congr 1
      omega
    · refine ⟨.bvar (d - 1 - idx), ?_⟩
      rw [AnnotTerm.liftN_bvar, if_pos (by omega)]
  | case3 d n us ci hf hlen =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    exact ⟨_, (m.acval_closed _ _ _).symm⟩
  | case4 d n us ci hf hlen =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro hw q hq hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xt, rfl⟩ := ihty hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    obtain ⟨Xb, rfl⟩ := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (q := q) (by omega) (by
      intro l hl'
      rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
      · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact fun h => by simp at h; omega
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    refine ⟨.pi 0 (pwBit φ mb.pw) Xt Xb, ?_⟩
    rw [AnnotTerm.liftN_pi, show d + 1 - 1 - q = d - 1 - q + 1 from by omega]
  | case7 d ty body mb ihty ihbody =>
    intro hw q hq hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xt, rfl⟩ := ihty hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    obtain ⟨Xb, rfl⟩ := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (q := q) (by omega) (by
      intro l hl'
      rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
      · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact fun h => by simp at h; omega
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    refine ⟨.lam (pwBit φ mb.pw) Xt Xb, ?_⟩
    rw [AnnotTerm.liftN_lam, show d + 1 - 1 - q = d - 1 - q + 1 from by omega]
  | case8 d f a ihf iha =>
    intro hw q hq hl ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xf, rfl⟩ := ihf hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hfa
    obtain ⟨Xa, rfl⟩ := iha hw.2 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')) haa
    exact ⟨.app Xf Xa, by rw [AnnotTerm.liftN_app]⟩
  | case9 d ty val body =>
    intro _ q hq hl ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hw q hq hl ea h
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xe, rfl⟩ := ihe hw hq (fun l hl' => hl l (by simpa [Expr.fvarLeaves] using hl')) hia
    rcases hcase with ⟨entry, -, rfl⟩ | ⟨-, hdec⟩
    · exact ⟨projAV (i + entry.off) Xe, by rw [projAV_liftN]⟩
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · exact ⟨.fst Xe, by rw [AnnotTerm.liftN_fst]⟩
      · exact ⟨.snd Xe, by rw [AnnotTerm.liftN_snd]⟩
  | case11 d n hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    exact ⟨_, (natLitAV_liftN (m.acval_closed _ _ _) (m.acval_closed _ _ _) n).symm⟩
  | case12 d n hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ q _ _ ea h
    -- the string literal's reading is closed: its own reading at depth `0`
    have h0 : denoteMeta m.acval env φ 0 (.lit (.strVal s)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    have hcl := bvarsBelow_of_reading (m := m) (d := 0) (e := .lit (.strVal s))
      (Expr.WScoped.of_not_hasFvar rfl) rfl h0
    exact ⟨ea, (AnnotTerm.liftN_eq_self ea (Term.bvarsBelow.mono (Nat.zero_le _) hcl) 1).symm⟩
  | case14 d s hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ q _ _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## Invariance under a lift's index -/

omit [SetTheory V] in
theorem shiftE_congr_off {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i ≠ k → ρ i = ρ' i) :
    shiftE 1 k ρ = shiftE 1 k ρ' := by
  funext i
  unfold shiftE
  split
  · exact hag i (by omega)
  · exact hag (i + 1) (by omega)

theorem interp_congr_lift {e X : AnnotTerm} {k : Nat} (h : e = X.liftN 1 k) {ρ ρ' : Nat → V}
    (hag : ∀ i, i ≠ k → ρ i = ρ' i) : interp V ρ e = interp V ρ' e := by
  subst h
  rw [interp_liftN, interp_liftN, shiftE_congr_off hag]

theorem wellDenotedV_congr_lift {e X : AnnotTerm} {k : Nat} (h : e = X.liftN 1 k) {ρ ρ' : Nat → V}
    (hag : ∀ i, i ≠ k → ρ i = ρ' i) : WellDenotedV V ρ e ↔ WellDenotedV V ρ' e := by
  subst h
  unfold WellDenotedV
  rw [WellDenoted_liftN, WellDenoted_liftN, AnnotValid_liftN, AnnotValid_liftN, shiftE_congr_off hag]

/-- **Invariance under the free indices**: two valuations that differ
only below `N`, and only at indices the term is a lift over, interpret
the term alike. -/
theorem interp_congr_lifts :
    ∀ (N : Nat) {e : AnnotTerm} {ρ ρ' : Nat → V},
      (∀ i, i < N → ρ i ≠ ρ' i → ∃ X : AnnotTerm, e = X.liftN 1 i) →
      (∀ i, N ≤ i → ρ i = ρ' i) →
      interp V ρ e = interp V ρ' e := by
  intro N
  induction N with
  | zero =>
    intro e ρ ρ' _ hag
    have : ρ = ρ' := funext fun i => hag i (Nat.zero_le i)
    rw [this]
  | succ N ih =>
    intro e ρ ρ' hfree hag
    let ρ'' : Nat → V := fun i => if i = N then ρ' N else ρ i
    have h1 : interp V ρ e = interp V ρ'' e := by
      by_cases hN : ρ N = ρ' N
      · have : ρ'' = ρ := by
          funext i
          show (if i = N then ρ' N else ρ i) = ρ i
          split
          · next h => rw [h, hN]
          · rfl
        rw [this]
      · obtain ⟨X, hX⟩ := hfree N (Nat.lt_succ_self N) hN
        exact interp_congr_lift hX fun i hi => by
          show ρ i = (if i = N then ρ' N else ρ i)
          rw [if_neg hi]
    rw [h1]
    refine ih ?_ ?_
    · intro i hi hne
      have hiN : i ≠ N := by omega
      refine hfree i (by omega) ?_
      show ρ i ≠ ρ' i
      have : ρ'' i = ρ i := by show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg hiN]
      rw [this] at hne
      exact hne
    · intro i hi
      rcases Nat.lt_or_ge i (N + 1) with hlt | hge
      · have : i = N := by omega
        subst this
        show (if i = i then ρ' i else ρ i) = ρ' i
        rw [if_pos rfl]
      · have : ρ'' i = ρ i := by
          show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg (by omega)]
        rw [this]
        exact hag i hge

theorem wellDenotedV_congr_lifts :
    ∀ (N : Nat) {e : AnnotTerm} {ρ ρ' : Nat → V},
      (∀ i, i < N → ρ i ≠ ρ' i → ∃ X : AnnotTerm, e = X.liftN 1 i) →
      (∀ i, N ≤ i → ρ i = ρ' i) →
      (WellDenotedV V ρ e ↔ WellDenotedV V ρ' e) := by
  intro N
  induction N with
  | zero =>
    intro e ρ ρ' _ hag
    have : ρ = ρ' := funext fun i => hag i (Nat.zero_le i)
    rw [this]
  | succ N ih =>
    intro e ρ ρ' hfree hag
    let ρ'' : Nat → V := fun i => if i = N then ρ' N else ρ i
    have h1 : WellDenotedV V ρ e ↔ WellDenotedV V ρ'' e := by
      by_cases hN : ρ N = ρ' N
      · have : ρ'' = ρ := by
          funext i
          show (if i = N then ρ' N else ρ i) = ρ i
          split
          · next h => rw [h, hN]
          · rfl
        rw [this]
      · obtain ⟨X, hX⟩ := hfree N (Nat.lt_succ_self N) hN
        exact wellDenotedV_congr_lift hX fun i hi => by
          show ρ i = (if i = N then ρ' N else ρ i)
          rw [if_neg hi]
    rw [h1]
    refine ih ?_ ?_
    · intro i hi hne
      have hiN : i ≠ N := by omega
      refine hfree i (by omega) ?_
      show ρ i ≠ ρ' i
      have : ρ'' i = ρ i := by show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg hiN]
      rw [this] at hne
      exact hne
    · intro i hi
      rcases Nat.lt_or_ge i (N + 1) with hlt | hge
      · have : i = N := by omega
        subst this
        show (if i = i then ρ' i else ρ i) = ρ' i
        rw [if_pos rfl]
      · have : ρ'' i = ρ i := by
          show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg (by omega)]
        rw [this]
        exact hag i hge

/-! ## The point prefix against a fitting prefix -/

/-- The point prefix and a fitting prefix differ only at the slots
whose fitting value is not the point; below the prefix both frames
are the parameters'. -/
theorem consList_prefix_agree {i : Nat} {as : List V} (hlen : as.length = i) (ρ' : Nat → V) :
    (∀ k, k < i → consList (List.replicate i pt) ρ' k ≠ consList as ρ' k →
      as.getD (i - 1 - k) pt ≠ pt) ∧
    (∀ k, i ≤ k → consList (List.replicate i pt) ρ' k = consList as ρ' k) := by
  constructor
  · intro k hk hne
    rw [consList_apply_lt _ _ _ (by rw [List.length_replicate]; exact hk),
      consList_apply_lt _ _ _ (by rw [hlen]; exact hk), List.length_replicate, hlen] at hne
    rw [List.getElem?_replicate, if_pos (by omega), List.getElem?_eq_getElem (by omega)] at hne
    simp only [Option.getD_some] at hne
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    exact fun h => hne h.symm
  · intro k hk
    have h1 := consList_apply_add (List.replicate i pt) ρ' (k - i)
    have h2 := consList_apply_add as ρ' (k - i)
    rw [List.length_replicate, show k - i + i = k from by omega] at h1
    rw [hlen, show k - i + i = k from by omega] at h2
    rw [h1, h2]

/-- **A differing slot is unused**: where the point prefix and a fitting
prefix differ, the fitting value is not the point, so that field is
not a proposition there, so (under the guard) no later field uses it,
so the projected field is a lift over that slot. -/
theorem free_of_diff {nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {sorts : List Level}
    {ψ : Name → Nat} {ρ' : Nat → V} {used : Nat → Bool}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ j, j < nF → ∀ as : List V,
      SpineFit ρ' (((ds.drop nP).map (·.2.2)).take j) as →
      interp V (consList as ρ') (((ds.drop nP).map (·.2.2)).getD j default)
        ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hguard : ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    {as' : List V} (hspAs : SpineFit ρ' ((ds.drop nP).map (·.2.2)) as') :
    ∀ k, k < i → consList (List.replicate i pt) ρ' k ≠ consList (as'.take i) ρ' k →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 k := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenTake : (as'.take i).length = i := by
    rw [List.length_take, hspAs.length_eq, hlenFs]; omega
  intro k hk hne
  have hne' := (consList_prefix_agree hlenTake ρ').1 k hk hne
  have hun : used (i - 1 - k) = false := by
    cases hu : used (i - 1 - k)
    · rfl
    · exfalso
      apply hne'
      obtain ⟨hpre, hnext⟩ :=
        spineFit_prefix_next hspAs (i := i - 1 - k) (by rw [hlenFs]; omega)
      have hs := hsorts (i - 1 - k) (by omega) _ hpre
      rw [hguard (i - 1 - k) (by omega) hu] at hs
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
        ← List.getD_eq_getElem?_getD]
      exact mem_univ_zero hs hnext
  obtain ⟨X, hX⟩ := hfree (i - 1 - k) (by omega) hun
  rw [show i - 1 - (i - 1 - k) = k from by omega] at hX
  exact ⟨X, hX⟩

/-- The prefix of a fitting spine has the prefix's length. -/
theorem spineFit_take_length {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) : (as.take i).length = i := by
  rw [List.length_take, h.length_eq]; omega

/-! ## The official guard's spelling -/

omit [SetTheory V] in
/-- The evaluated join over the used slots is zero exactly when the
base and every used joined level are. -/
theorem eval_foldl_max_if_zero_iff (ψ : Name → Nat) (used : Nat → Bool) (s : Nat → Level) :
    ∀ (l : List Nat) (s0 : Level),
      Level.eval ψ (l.foldl (fun acc j => if used j then Level.max acc (s j) else acc) s0) = 0 ↔
        Level.eval ψ s0 = 0 ∧ ∀ j ∈ l, used j = true → Level.eval ψ (s j) = 0
  | [], s0 => by simp
  | a :: l, s0 => by
    rw [List.foldl_cons, eval_foldl_max_if_zero_iff ψ used s l]
    cases hu : used a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, forall_eq_or_imp, hu,
        false_implies, true_and]
    · simp only [↓reduceIte, Level.eval, Nat.max_eq_zero_iff, List.mem_cons, forall_eq_or_imp,
        hu, forall_const]
      constructor
      · rintro ⟨⟨h0, ha⟩, hl⟩; exact ⟨h0, ha, hl⟩
      · rintro ⟨h0, ha, hl⟩; exact ⟨⟨h0, ha⟩, hl⟩


/-!
## The projection body's frame

The table stores, per field, a **body** `F_i[p⃗ ↦ bvars, f_j ↦ .proj T
j (bvar 0)]` (`structProjBodies`), and the tower law (A) reads it
through the dummy telescope `projTele (nP + 1) body`
(`ConLeche/Verify/ProjTele.lean`).  Two facts make the reading what the
law needs:

* **the telescope's reading is the opened body's** (`denoteMeta_projTele`):
  `denoteMeta` opens the `nP + 1` dummy binders at fresh variables, so
  the telescope reads to `mkPisAV` over `nP + 1` dummy `Sort 0` binder
  data with the body instantiated at the variables as its residual;
* **the opened body is the constructor's field domain at the frame**
  (`bodyFrames`): by `structProjBody_open` the opened body *is* the
  head domain of the constructor telescope peeled at the variables and
  the subject's earlier projections, so its reading is the field
  domain's instantiation sequence along the readings of those
  arguments (`Rules.denoteMeta_instPisAt_peel`), which at the frame — the
  subject a member of the family at the parameters — agrees with the
  field domain read at the subject's projection spine
  (`chain_entry_agree`) and is graded there (the graph regime by the
  projections' fit, the squash regime by the point spine's agreement
  with a fitting prefix at every used slot, `free_of_diff`).

No annotation, inference or definitional-equality run is consumed:
the body is a substitution instance of the stored constructor type,
and the reading is a homomorphism for substitution.
-/


/-! ## The telescope's reading -/

/-- **The dummy telescope reads to the opened body**: `k` dummy
binders at depth `d` open at the variables `d, …, d + k - 1`, and the
residual is the body's instantiation sequence at them. -/
theorem denoteMeta_projTele {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (k d : Nat) (body : Expr) {RA : AnnotTerm},
      denoteMeta acval env φ (d + k)
        (Expr.instSeq ((List.range k).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k - 1) body) = some RA →
      denoteMeta acval env φ d (ConLeche.projTele k body)
        = some (mkPisAV (List.replicate k (0, 1, .sort 0)) RA)
  | 0, d, body, RA, h => by
    simpa [ConLeche.projTele, Expr.instSeq, mkPisAV] using h
  | k + 1, d, body, RA, h => by
    have hspine : Expr.instSeq ((List.range (k + 1)).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k + 1 - 1) body
        = Expr.instSeq ((List.range k).map fun j =>
            Expr.fvar (d + 1 + j) (.sort .zero)) (k - 1)
            (body.instantiate1 (Expr.fvar d (.sort .zero)) k) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
      show Expr.instSeq _ (k - 1) (body.instantiate1 _ k) = _
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [show d + (j + 1) = d + 1 + j from by omega]
    rw [hspine, show d + (k + 1) = d + 1 + k from by omega] at h
    have ih := denoteMeta_projTele k (d + 1)
      (body.instantiate1 (Expr.fvar d (.sort .zero)) k) h
    rw [ConLeche.projTele, denoteMeta_forallE, denoteMeta_sort, ConLeche.projTele_instantiate1,
      Nat.zero_add, ih]
    rfl

/-- The telescope over the parameters and the subject, at depth `0`:
the residual is the body at the direct install's own variable
spelling (`fvsD`/`tfvD`). -/
theorem denoteMeta_projTele_zero {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP : Nat} {body : Expr} {RA : AnnotTerm}
    (h : denoteMeta acval env φ (nP + 1)
      (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) = some RA) :
    denoteMeta acval env φ 0 (ConLeche.projTele (nP + 1) body)
      = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) RA) := by
  refine denoteMeta_projTele (nP + 1) 0 body ?_
  rw [Nat.zero_add, Nat.add_sub_cancel]
  rw [Expr.instSpine_eq_instSeq] at h
  have e : ((List.range (nP + 1)).map fun j => Expr.fvar (0 + j) (.sort .zero))
      = ConLeche.fvsD nP ++ [ConLeche.tfvD nP] := by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    simp only [ConLeche.fvsD, ConLeche.tfvD, Nat.zero_add]
  rw [e]
  exact h

/-! ## The frame -/

omit [SetTheory V] in
theorem DomsBelow.getD_below {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} (j : Nat), DomsBelow k ds → j < ds.length →
      Term.bvarsBelow (k + j) (ds.getD j default).2.2.erase
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d :: ds, 0, h, _ => by simpa using h.1
  | d :: ds, j + 1, h, hj => by
    rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.getD_below j h.2 (by simpa using hj)

/-- **The opened body's frame.**  At the frame (the subject a member of
the family at the parameters — `ρ 0` in the tower over the field chain
at `ρ ∘ succ`, which satisfies the constructor's parameter context)
the opened body reads to a graded term whose value is the field
domain at the subject's projection spine.  The grading in the squash
regime rides the official guard's content (`hguard`) and the unused
earlier fields' invariance (`hfree`). -/
theorem bodyFrames {env : Env} (m : EnvModel V env)
    {nP nF i off : Nat} {T : Name} {cty : Expr} {cds : List Expr}
    {bodyC : Expr} {mbC : BinderMeta} {body : Expr}
    (hcf : Expr.instPisAt (ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP) cty
      = some (cds, .forallE
          (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) bodyC mbC))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    -- the earlier fields' entries, at the table's projection offset
    -- (task #210 Part A: the tagged tower of the fixpoint route reads
    -- its fields at offset `1`)
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry ∧ entry.off = off)
    (hi : i < nF)
    {ds : List (Nat × Nat × AnnotTerm)} {bodyA : AnnotTerm} {ψ : Name → Nat} {w : Nat}
    (hlenDs : ds.length = nP + nF) (hbelow : DomsBelow 0 ds)
    (hctyRead0 : denoteMeta m.acval env ψ 0 cty = some (mkPisAV ds bodyA))
    {sorts : List Level}
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)) ∧ FieldsValid ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    -- THE SUBJECT'S FRAME, abstractly (task #210 Part A): whatever
    -- carrier the subject `ρ 0` lives in, at a squash instance it is
    -- the point and the fields admit a fitting spine; in the graph
    -- regime the subject's projection tuple (below the offset) fits
    -- the fields; and the subject's projection readings are graded
    (Frame : (Nat → V) → Prop)
    (hsq : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) → w = 0 →
      ρ 0 = pt ∧ ∃ as' : List V, SpineFit (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2)) as')
    (hgr : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) → w ≠ 0 →
      SpineFit (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2)) (projList nF (dropS off (ρ 0))))
    (hokProj : ∀ ρ : Nat → V, Frame ρ →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      ∀ j, j < nF → WellDenoted V ρ (projAV (j + off) (.bvar 0))) :
    ∃ fdomA : AnnotTerm,
      denoteMeta m.acval env ψ (nP + 1)
        (Expr.instSpine (ConLeche.fvsD nP ++ [ConLeche.tfvD nP]) nP body) = some fdomA ∧
      ((w = 0 → ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0) →
        ∀ ρ : Nat → V, Frame ρ →
          Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
          WellDenotedV V ρ fdomA) ∧
      (∀ ρ : Nat → V, Frame ρ →
        Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
        interp V ρ fdomA
          = interp V (consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)))
              (((ds.drop nP).map (·.2.2)).getD i default)) := by
  -- the constructor type's reading at the body's depth
  have hctyRead : denoteMeta m.acval env ψ (nP + 1) cty = some (mkPisAV ds bodyA) :=
    denoteMeta_depth_of_closed m.acval_closed hCf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hCf hCb hctyRead0 1 k)
      hctyRead0 (nP + 1)
  -- the arguments' scoping
  have hlenP : (ConLeche.fvsD nP).length = nP := ConLeche.fvsD_length nP
  have hfvsDidx : ∀ (k : Nat) (x : Expr), (ConLeche.fvsD nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1; rwa [hlenP] at this
    rw [ConLeche.fvsD_getElem? nP k hk] at hx
    exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
  have hargs : ∀ a ∈ ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP,
      Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hk
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, and_true]
      omega
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, ConLeche.tfvD, and_true]
      omega
  have hctyW : Expr.WScoped (nP + 1) cty := Expr.WScoped.of_not_hasFvar hCf
  -- the arguments' readings: the parameters and the earlier projections
  have hspP := denoteMetaSpine_entryParams (acval := m.acval) (env := env) (φ := ψ)
    hfvsDidx hlenP
  have hspX := denoteMetaSpine_entryProjs (acval := m.acval) (env := env) (φ := ψ)
    (nP := nP) (sdom := .sort .zero) hprev
  have hsp : DenoteMetaSpine m.acval env ψ (nP + 1) (ConLeche.fvsD nP ++ ConLeche.projArgsD T i nP)
      (entryParamBvars nP ++ entryProjAVs off i) :=
    DenoteMetaSpine.append hspP hspX
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denoteMeta_instPisAt_peel m.acval_closed
    (acval_inst_self m) _ hcf hctyW hargs hctyRead hsp
  obtain ⟨fdomA, ba, hfdA, -, rfl⟩ := denoteMeta_forallE_inv hrest
  -- the peel is the instantiation sequence of the field domain
  have hlenVs : (entryParamBvars nP ++ entryProjAVs off i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  have hsplitDs : ds = ds.take (nP + i) ++ ds.drop (nP + i) :=
    (List.take_append_drop _ _).symm
  have htele : PiTeleAV (nP + i) (mkPisAV ds bodyA)
      (((ds.take (nP + i)).map (·.2.2)).reverse)
      (mkPisAV (ds.drop (nP + i)) bodyA) := by
    have h := piTeleAV_mkPisAV (ds.take (nP + i)) (mkPisAV (ds.drop (nP + i)) bodyA)
    rw [← mkPisAV_append, ← hsplitDs, List.length_take, hlenDs,
      show min (nP + i) (nP + nF) = nP + i from by omega] at h
    exact h
  have hpeel' := peelPis_of_piTeleAV (nP + i) htele hlenVs
  rw [hpeel] at hpeel'
  have hdropDs : ds.drop (nP + i) = ds.getD (nP + i) default :: ds.drop (nP + i + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hdropDs] at hpeel'
  simp only [mkPisAV] at hpeel'
  obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ entryProjAVs off i) (nP + i - 1)
    (ds.getD (nP + i) default).1 (ds.getD (nP + i) default).2.1
    (ds.getD (nP + i) default).2.2
    (mkPisAV (ds.drop (nP + i + 1)) bodyA)
  rw [hB'] at hpeel'
  obtain ⟨-, -, hfdomA, -⟩ := AnnotTerm.pi.inj (Option.some.inj hpeel')
  -- the field's domain, named
  have hFi : ((ds.drop nP).map (·.2.2)).getD i default = (ds.getD (nP + i) default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hFiBelow : Term.bvarsBelow (nP + i) (ds.getD (nP + i) default).2.2.erase := by
    have := DomsBelow.getD_below (nP + i) hbelow (by omega)
    rwa [Nat.zero_add] at this
  have hlenFs : ((ds.drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
  have hlen' : (entryParamBvars nP ++ entryProjAVs off i).length - 1 = nP + i - 1 := by
    rw [hlenVs]
  refine ⟨fdomA, hfdA, ?_, ?_⟩
  · -- the grading at the frame
    intro hguard ρ hx hsat
    -- the field's grading at the subject's projection spine: in the
    -- graph regime the projections fit; at a squash instance they are
    -- the point spine, which differs from a fitting prefix only at
    -- unused slots, where the field is a lift
    have hokPre : WellDenotedV V (consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)))
        (((ds.drop nP).map (·.2.2)).getD i default) := by
      by_cases hw : w = 0
      · obtain ⟨hpt, as', hspAs⟩ := hsq ρ hx hsat hw
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
        rw [hpt, dropS_pt, projList_pt]
        have hlenTake : (as'.take i).length = i :=
          spineFit_take_length hspAs (by rw [hlenFs]; omega)
        rw [wellDenotedV_congr_lifts i
          (free_of_diff hlenDs hi (hsorts _ hsat) (hguard hw) hfree hspAs)
          (consList_prefix_agree hlenTake _).2]
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
      · have hspAll := hgr ρ hx hsat hw
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAll (by rw [hlenFs]; exact hi)
        rw [projList_take nF i _ (Nat.le_of_lt hi)] at hpre
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
    -- the readings' gradings at the frame
    have hokArgs : ∀ w' ∈ entryParamBvars nP ++ entryProjAVs off i, WellDenotedV V ρ w' := by
      intro w' hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw'
        exact ⟨trivial, trivial⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw'
        have hj' : j < i := List.mem_range.mp hj
        exact ⟨hokProj ρ hx hsat j (by omega), projAV_validV trivial⟩
    rw [hfdomA, ← hlen']
    refine wellDenotedV_instSeq _ hokArgs ?_
    rw [(WellDenotedV_congr_below _ (nP + i) _ _ hFiBelow (chain_entry_agree nP off i ρ))]
    rw [← hFi]
    exact hokPre
  · -- the value at the frame
    intro ρ _ _
    rw [hfdomA, ← hlen', interp_instSeq, hFi]
    exact interp_congr_below V _ (nP + i) _ _ hFiBelow (chain_entry_agree nP off i ρ)


/-!
## The projection table's cons

`stageTable`: the P step at the direct install's last stage — the
structure's projection **table**, one constant holding every field's
body (`checkStructProjTable`).  The table's leaf is `Sort 0` (a
member of its dummy type's reading; a table is not a term), and what
the cons owes is the tower law at every field
(`declStep_preserves_of_tower_cons`):

* **(A)** the typing law reads body `i` through the dummy telescope
  (`denoteMeta_projTele_zero`); the opened body is the constructor's
  field domain at the variables (`structProjBody_open`), whose frame
  facts are `bodyFrames`, and `entryTypingCore` closes;
* **(B)** the iota law and **(C)** the η law are the block's own
  (`entryIotaCore`/`entryIotaCoreZero`, `entryEtaCore`), as before.

The squash regime's guard content (`structProjGuards_getD` over the
field-sort run) and the unused earlier fields' invariance
(`openPisAtFvars_leaf_free`) are derived here per field, as the
retired per-slot fold derived them per slot.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta ProjEntry ProjTable projTableName)


variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The table name has the reserved shape. -/
theorem projTableName_isProjFnShape (T : Name) :
    (projTableName T).isProjFnShape = true := rfl

end ConLeche.Model
