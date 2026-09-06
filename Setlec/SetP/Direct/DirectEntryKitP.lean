import Setlec.SetP.Direct.DirectStageRecP

/-!
# The projection entry's kit (task #175 W4c, P3 module 7, part 1)

Semantic and syntactic pieces of a tower entry's install:

* the syntactic Π-peel of a tower along a spine is the body's
  instantiation sequence (`peelPis_of_piTeleP`, the fit-free spine of
  `teleFitPA_of_tower`), and a `mkPisAV` tower is a `PiTeleP`;
* a graded application of a nonzero-bit λ-tower **fits** the tower
  (`spineFit_of_okP_mkAppN_lam`): the application clause's package
  pins each argument to the layer's domain (a graph's domain is
  rigid, `graph_dom_of_mem_piSet`) — the converse of
  `mkAppN_okP_of_lam`;
* the projection spelling is graded at a tower member in the graph
  regime (`annotOk2_projAV_tower`, the pair chain's Σ packages) and at
  the point in the squash regime (`annotOk2_projAV_pt`);
* the coarse guard level's content (`eval_foldl_max_zero_iff`), and
  the squash prefix: a fitting spine over proof fields is the point
  spine (`spineFit_eq_replicate_pt`).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The peel -/

/-- A `mkPisAV` tower is a `PiTeleP` over its reversed domains. -/
theorem piTeleP_mkPisAV :
    ∀ (ds : List (Nat × Nat × AVExpr)) (b : AVExpr),
      PiTeleP ds.length (mkPisAV ds b) ((ds.map (·.2.2)).reverse) b
  | [], _ => PiTeleP.nil
  | d :: ds, b => by
    simp only [List.length_cons, mkPisAV, List.map_cons, List.reverse_cons]
    exact PiTeleP.cons (piTeleP_mkPisAV ds b)

/-- **The fit-free peel**: the syntactic Π-peel of a tower along a
spine of the tower's length is the body's instantiation sequence
(`teleFitPA_of_tower`'s spine, memberships dropped). -/
theorem peelPis_of_piTeleP :
    ∀ (k : Nat) {T : AVExpr} {Γ : List AVExpr} {R : AVExpr},
      PiTeleP k T Γ R → ∀ {ws : List AVExpr}, ws.length = k →
      Setlec.SetP.AVExpr.peelPis T ws
        = some (Setlec.SetP.AVExpr.instSeq ws (k - 1) R) := by
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
    rw [show Setlec.SetP.AVExpr.instSeq (w :: ws') (k + 1 - 1) R
        = Setlec.SetP.AVExpr.instSeq ws' (k - 1) (R.inst w k) from by
      rw [AVExpr.instSeq_cons]
      simp only [Nat.add_sub_cancel]]
    rw [show (0 : Nat) + k = k from Nat.zero_add k] at this
    exact this

/-- The instantiation sequence of a `.pi` is a `.pi` over the
sequence of its domain. -/
theorem instSeq_pi_dom :
    ∀ (ws : List AVExpr) (t u v : Nat) (A B : AVExpr),
      ∃ B', Setlec.SetP.AVExpr.instSeq ws t (.pi u v A B)
        = .pi u v (Setlec.SetP.AVExpr.instSeq ws t A) B'
  | [], _, _, _, _, B => ⟨B, rfl⟩
  | w :: ws, t, u, v, A, B => by
    rw [AVExpr.instSeq_cons, AVExpr.instSeq_cons, AVExpr.inst_pi]
    exact instSeq_pi_dom ws (t - 1) u v (A.inst w t) (B.inst w (t + 1))

/-! ## Fits from gradings -/

/-- **A graded application of a nonzero-bit λ-tower fits the tower**:
each application clause's package puts the argument in a domain the
layer's graph inhabits as a function, and a graph's domain is rigid
(`mkAppN_okP_of_lam`'s converse). -/
theorem spineFit_of_okP_mkAppN_lam :
    ∀ {lds : List (Nat × AVExpr)} {b f : AVExpr} {args : List AVExpr} {ρ σ : Nat → V},
      (∀ d ∈ lds, d.1 ≠ 0) →
      AnnotOkP V ρ (AVExpr.mkAppN f args) →
      interp2 V ρ f = interp2 V σ (mkLamsAV lds b) →
      args.length = lds.length →
      SpineFit σ (lds.map (·.2)) (args.map (interp2 V ρ))
  | [], _, _, [], _, _, _, _, _, _ => trivial
  | [], _, _, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, _, _, [], _, _, _, _, _, hlen => by simp at hlen
  | d :: lds, b, f, a :: args, ρ, σ, hnz, hok, hval, hlen => by
    simp only [List.map_cons, SpineFit]
    rw [AVExpr.mkAppN_cons] at hok
    have hokApp := AnnotOkP_mkAppN_head args hok
    obtain ⟨-, -, v, A, B, hf, ha, -⟩ := (AnnotOk2_app V ρ f a) ▸ hokApp.1
    have hd : d.1 ≠ 0 := hnz d List.mem_cons_self
    rw [hval] at hf
    simp only [mkLamsAV, interp2_lam] at hf
    rw [lamR_pos hd] at hf
    -- the package's codomain bit is nonzero: a graph is not the point
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0, piR_zero] at hf
      exact graph_ne_pt (eq_pt_of_mem_truthVal hf)
    rw [piR_pos hv] at hf
    have hmem : interp2 V ρ a ∈ˢ interp2 V σ d.2 := graph_dom_of_mem_piSet hf _ ha
    refine ⟨hmem, ?_⟩
    refine spineFit_of_okP_mkAppN_lam (b := b) (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd'))
      hok ?_ (by simpa using hlen)
    rw [interp2_app, hval]
    simp only [mkLamsAV, interp2_lam]
    rw [app_lamR_pos hd hmem]

/-! ## The projection spelling's grading -/

omit [SetTheory V] in
theorem nat_max_self (w : Nat) : Nat.max w w = w := by simp [Nat.max]

/-- At the point (the squash regime's every member) the projection
spelling is graded through the trivial Σ package. -/
theorem annotOk2_projAV_pt :
    ∀ {i : Nat} {e : AVExpr} {ρ : Nat → V},
      AnnotOk2 V ρ e → interp2 V ρ e = (pt : V) → AnnotOk2 V ρ (projAV i e)
  | 0, e, ρ, hok, hpt => by
    show AnnotOk2 V ρ (.proj 0 e)
    rw [AnnotOk2_proj]
    refine ⟨hok, by decide, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
      fun _ _ => unitSet_mem_univ 0⟩
    rw [hpt, nat_max_self]
    exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet
  | i + 1, e, ρ, hok, hpt => by
    show AnnotOk2 V ρ (projAV i (.proj 1 e))
    refine annotOk2_projAV_pt (i := i) ?_ ?_
    · rw [AnnotOk2_proj]
      refine ⟨hok, by decide, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
        fun _ _ => unitSet_mem_univ 0⟩
      rw [hpt, nat_max_self]
      exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet
    · rw [interp2_proj, if_neg (by decide), hpt, ssnd_pt]

/-- At a tower member in the graph regime the projection spelling is
graded: each pair step's Σ package is the tower's own level, with the
tail in the fibre (`ssnd_mem_gen`). -/
theorem annotOk2_projAV_tower {w : Nat} :
    ∀ {i : Nat} {Fs : List AVExpr} {ρ' : Nat → V} {x : V} {e : AVExpr} {ρ : Nat → V},
      FieldsBound w ρ' Fs → x ∈ˢ towerSet w (teleOfFields ρ' Fs) →
      AnnotOk2 V ρ e → interp2 V ρ e = x → i < Fs.length →
      AnnotOk2 V ρ (projAV i e) := by
  intro i
  induction i with
  | zero =>
    intro Fs ρ' x e ρ hb hx hok hval hi
    match Fs, hb, hx, hi with
    | F :: Fs', hb, hx, _ =>
      show AnnotOk2 V ρ (.proj 0 e)
      rw [AnnotOk2_proj]
      refine ⟨hok, by decide, w, w, interp2 V ρ' F,
        fun a => towerSet w (teleOfFields (cons a ρ') Fs'), ?_, hb.1,
        fun a ha => towerSet_univ_teleOfFields (hb.2 a ha)⟩
      rw [hval, nat_max_self]
      exact hx
  | succ i ih =>
    intro Fs ρ' x e ρ hb hx hok hval hi
    match Fs, hb, hx, hi with
    | F :: Fs', hb, hx, hi =>
      show AnnotOk2 V ρ (projAV i (.proj 1 e))
      have hx' : x ∈ˢ sigmaSet (Nat.max w w) (interp2 V ρ' F)
          (fun a => towerSet w (teleOfFields (cons a ρ') Fs')) := by
        rw [nat_max_self]; exact hx
      have hA : interp2 V ρ' F ∈ˢ (univ w : V) := hb.1
      have hB : ∀ a, a ∈ˢ interp2 V ρ' F →
          towerSet w (teleOfFields (cons a ρ') Fs') ∈ˢ (univ w : V) :=
        fun a ha => towerSet_univ_teleOfFields (hb.2 a ha)
      have hfst := sfst_mem_gen V hA hx'
      have hsnd := ssnd_mem_gen V hA hB hx'
      refine ih (Fs := Fs') (ρ' := cons (sfst x) ρ') (x := ssnd x) (hb.2 _ hfst) hsnd ?_ ?_
        (by simpa using hi)
      · rw [AnnotOk2_proj]
        refine ⟨hok, by decide, w, w, interp2 V ρ' F,
          fun a => towerSet w (teleOfFields (cons a ρ') Fs'), ?_, hA, hB⟩
        rw [hval]; exact hx'
      · rw [interp2_proj, if_neg (by decide), hval]

/-! ## The coarse guard -/

/-- The evaluated join over a list is zero exactly when every joined
level is. -/
theorem eval_foldl_max_zero_iff (ψ : Name → Nat) (s : Nat → Level) :
    ∀ (l : List Nat) (s0 : Level),
      Level.eval ψ (l.foldl (fun acc j => Level.max acc (s j)) s0) = 0 ↔
        Level.eval ψ s0 = 0 ∧ ∀ j ∈ l, Level.eval ψ (s j) = 0
  | [], s0 => by simp
  | a :: l, s0 => by
    rw [List.foldl_cons, eval_foldl_max_zero_iff ψ s l]
    simp only [Level.eval, Nat.max_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h0, ha⟩, hl⟩; exact ⟨h0, ha, hl⟩
    · rintro ⟨h0, ha, hl⟩; exact ⟨⟨h0, ha⟩, hl⟩

/-! ## The squash prefix -/

/-- A spine fitting a chain of truth values (each domain lands in
`univ 0` at every fitting prefix) is the point spine. -/
theorem spineFit_eq_replicate_pt :
    ∀ {Fs : List AVExpr} {ρ : Nat → V} {as : List V},
      SpineFit ρ Fs as →
      (∀ j, j < Fs.length → ∀ bs : List V, SpineFit ρ (Fs.take j) bs →
        interp2 V (consList bs ρ) (Fs.getD j default) ∈ˢ (univ 0 : V)) →
      as = List.replicate Fs.length pt
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, h, _ => h.elim
  | _ :: _, _, [], h, _ => h.elim
  | F :: Fs, ρ, a :: as, h, hz => by
    have h0 := hz 0 (by simp) [] trivial
    simp only [consList_nil, List.getD_cons_zero] at h0
    have ha : a = pt := mem_univ_zero h0 h.1
    subst ha
    rw [List.length_cons, List.replicate_succ]
    congr 1
    refine spineFit_eq_replicate_pt (ρ := cons pt ρ) h.2 ?_
    intro j hj bs hbs
    have := hz (j + 1) (by simp; omega) (pt :: bs) ⟨h.1, hbs⟩
    simpa using this

/-- The prefix of a fitting spine fits the prefix, and the next field
is inhabited at it. -/
theorem spineFit_prefix_next {Fs : List AVExpr} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i < Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) ∧
      (as.getD i pt) ∈ˢ interp2 V (consList (as.take i) ρ) (Fs.getD i default) := by
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

theorem interp2_mkAppN_foldl (ρ : Nat → V) (as : List AVExpr) (f : AVExpr) :
    interp2 V ρ (AVExpr.mkAppN f as)
      = (as.map (interp2 V ρ)).foldl SetTheory.app (interp2 V ρ f) := by
  rw [interp2_mkAppN, List.foldl_map]

end Setlec.SetP
