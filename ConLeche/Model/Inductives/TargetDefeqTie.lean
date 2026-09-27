module

public import ConLeche.Model.Inductives.TargetRecRead
public import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.TargetFlatCall
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope

public section

/-!
# The defeq tie: parameters defeq with holes ⇒ the same fits (PRIMREC / NESTKN)

The liberal matching ruling (2026-09-27) matches a recursor class
against a positivity-check node, and a call's callee against the called
field, UP TO DEFEQ with the holes abstracted.  At a `Prop`-valued class
the class induction reads DECODINGS — the hole fits `LfpDatum.HFits`
(a constructor index and a field spine fitting the container's recorded
field readings at the class's parameter FRAME) — not merely readings of
types: every inhabited `Prop` reads `{pt}`, so two classes whose majors
read alike need not share a frame (`P Nat` and `P Bool` for
`P (α : Type) : Prop | mk : α → P α`: both `{pt}`, their decodings
`mk n` / `mk b` disjoint).  So "the major reads like the node's key"
does NOT give the node's fits.

What does: the match compared PER COMPONENT — one head constant, levels
evaluating alike, and every PARAMETER defeq at the hole context.  Then
the kernel's defeq soundness (`Rules.defeq_sound`) makes every
parameter read alike at every valuation of the holes (`params_read_eq`),
so the key frames agree (`keyFrame_eq_of_params`), and the fits, the
carriers and the index sets — functions of the datum, the level
assignment and the frame alone — agree literally (`hfits_iff_of_frame`,
`tie_fits`).  That is the lemma the nested recursor route consumes; the
kernel side is a per-parameter comparison (official's majors are the
field's classes verbatim, K.53, so it moves no official verdict).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Fits are functions of the frame -/

/-- **The hole fit, the carrier and the index set depend on the frame's
values only.** -/
theorem hfits_iff_of_frame (D : LfpDatum V) (ψ : Name → Nat) {ρ₁ ρ₂ : Nat → V}
    (h : ∀ q, ρ₁ q = ρ₂ q) (X : Nat → V) (t : V) (c j : Nat) (fs : List V) :
    D.HFits ψ ρ₁ X t c j fs ↔ D.HFits ψ ρ₂ X t c j fs := by
  rw [show ρ₁ = ρ₂ from funext h]

theorem carrier_eq_of_frame (D : LfpDatum V) (ψ : Name → Nat) {ρ₁ ρ₂ : Nat → V}
    (h : ∀ q, ρ₁ q = ρ₂ q) : D.carrier ψ ρ₁ = D.carrier ψ ρ₂ := by
  rw [show ρ₁ = ρ₂ from funext h]

theorem idx_eq_of_frame (D : LfpDatum V) (ψ : Name → Nat) {ρ₁ ρ₂ : Nat → V}
    (h : ∀ q, ρ₁ q = ρ₂ q) : D.idx ψ ρ₁ = D.idx ψ ρ₂ := by
  rw [show ρ₁ = ρ₂ from funext h]

/-- Key frames of spines reading alike agree. -/
theorem keyFrame_eq_of_params {dsa₁ dsa₂ : List AnnotTerm} {hi : Nat} {ρ : Nat → V}
    (h : dsa₁.map (interp V ρ) = dsa₂.map (interp V ρ)) :
    keyFrame dsa₁ hi ρ = keyFrame dsa₂ hi ρ := by
  unfold keyFrame; rw [h]

/-! ## Defeq with holes ⇒ equal readings at every valuation of the holes -/

section Walk

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

set_option maxHeartbeats 4000000 in
/-- **One parameter**: two terms over the walk's context (its free
variables — the holes among them — entries of the frame list `L`), each
inferred, and defeq there, read alike at the context's valuation — at
EVERY valuation satisfying the context, the holes' included. -/
theorem param_read_eq (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F D : Nat} {L : List Expr} (h2 : FvarList D L)
    {ρ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ D ρ Δ L)
    {a b ta tb : Expr}
    (ha : ConLeche.inferTypeCore μ envT F D a = .ok ta)
    (hb : ConLeche.inferTypeCore μ envT F D b = .ok tb)
    (hd : ConLeche.isDefEqCore μ envT F D a b = .ok true)
    (haL : ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hbL : ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) :
    ∃ aa ba, denoteMeta mT.acval envT φ D a = some aa ∧
      denoteMeta mT.acval envT φ D b = some ba ∧ interp V ρ aa = interp V ρ ba := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  have hWS0 := hW.2.2.2.2.1
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge ha)
  obtain ⟨aa, haa⟩ := acceptedReads_of mT φ ha (wscoped_of_leaves_mem h2 _ haL) hAb
    (fun l hl => hWS0 _ (haL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin h2 hW haL hAb haa
    ⟨_, Rules.inferTypeCore_bridge ha⟩
  have hBb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hb)
  obtain ⟨ba, hba⟩ := acceptedReads_of mT φ hb (wscoped_of_leaves_mem h2 _ hbL) hBb
    (fun l hl => hWS0 _ (hbL l hl))
  obtain ⟨hFrB, hCB, hGB⟩ := WalkCtx.subjOkL hacl1 hin h2 hW hbL hBb hba
    ⟨_, Rules.inferTypeCore_bridge hb⟩
  exact ⟨aa, ba, haa, hba,
    Rules.defeq_sound hin (Rules.isDefEqCore_bridge hd) hFrA hFrB hCA hCB haa hba hGA hGB _
      hW.2.1⟩

/-- **Every parameter**: two parameter spines compared pairwise by the
kernel's defeq at the hole context read alike at every valuation of it
— the spines' readings, mapped, agree. -/
theorem params_read_eq (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F D : Nat} {L : List Expr} (h2 : FvarList D L)
    {ρ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ D ρ Δ L) :
    ∀ {ds₁ ds₂ : List Expr}, ds₁.length = ds₂.length →
      (∀ (i : Nat) (a b : Expr), ds₁[i]? = some a → ds₂[i]? = some b →
        (∃ ta, ConLeche.inferTypeCore μ envT F D a = .ok ta) ∧
        (∃ tb, ConLeche.inferTypeCore μ envT F D b = .ok tb) ∧
        ConLeche.isDefEqCore μ envT F D a b = .ok true ∧
        (∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) ∧
        (∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)) →
      ∃ dsa₁ dsa₂, (ds₁.mapM (denoteMeta mT.acval envT φ D)) = some dsa₁ ∧
        (ds₂.mapM (denoteMeta mT.acval envT φ D)) = some dsa₂ ∧
        dsa₁.map (interp V ρ) = dsa₂.map (interp V ρ)
  | [], [], _, _ => ⟨[], [], rfl, rfl, rfl⟩
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a :: ds₁, b :: ds₂, hl, hp => by
    obtain ⟨⟨ta, ha⟩, ⟨tb, hb⟩, hd, haL, hbL⟩ := hp 0 a b rfl rfl
    obtain ⟨aa, ba, haa, hba, heq⟩ := param_read_eq hμ hacl hin h2 hW ha hb hd haL hbL
    obtain ⟨dsa₁, dsa₂, h1, h2', hm⟩ := params_read_eq hμ hacl hin h2 hW
      (Nat.succ.inj hl) (fun i a' b' ha' hb' => hp (i + 1) a' b' ha' hb')
    refine ⟨aa :: dsa₁, ba :: dsa₂, ?_, ?_, ?_⟩
    · simp [List.mapM_cons, haa, h1]
    · simp [List.mapM_cons, hba, h2']
    · simp [heq, hm]

/-- **THE TIE** (see the module docstring): a class and a node of ONE
container datum `D`, at one level assignment, whose parameters the
kernel found pairwise defeq at the hole context, have — at every
valuation of that context — one key frame, hence the same hole fits,
carrier and index set.  The frames are the parameters' readings over the
frame below the key's depth (`keyFrame`). -/
theorem tie_fits (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F Dd : Nat} {L : List Expr} (h2 : FvarList Dd L)
    {ρ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ Dd ρ Δ L)
    {ds₁ ds₂ : List Expr} (hl : ds₁.length = ds₂.length)
    (hp : ∀ (i : Nat) (a b : Expr), ds₁[i]? = some a → ds₂[i]? = some b →
        (∃ ta, ConLeche.inferTypeCore μ envT F Dd a = .ok ta) ∧
        (∃ tb, ConLeche.inferTypeCore μ envT F Dd b = .ok tb) ∧
        ConLeche.isDefEqCore μ envT F Dd a b = .ok true ∧
        (∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) ∧
        (∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2 ∈ L))
    (D : LfpDatum V) (ψ : Name → Nat) (hi : Nat) :
    ∃ dsa₁ dsa₂, (ds₁.mapM (denoteMeta mT.acval envT φ Dd)) = some dsa₁ ∧
      (ds₂.mapM (denoteMeta mT.acval envT φ Dd)) = some dsa₂ ∧
      keyFrame dsa₁ hi ρ = keyFrame dsa₂ hi ρ ∧
      D.carrier ψ (keyFrame dsa₁ hi ρ) = D.carrier ψ (keyFrame dsa₂ hi ρ) ∧
      D.idx ψ (keyFrame dsa₁ hi ρ) = D.idx ψ (keyFrame dsa₂ hi ρ) ∧
      ∀ X t c j fs, D.HFits ψ (keyFrame dsa₁ hi ρ) X t c j fs ↔
        D.HFits ψ (keyFrame dsa₂ hi ρ) X t c j fs := by
  obtain ⟨dsa₁, dsa₂, h1, h2', hm⟩ := params_read_eq hμ hacl hin h2 hW hl hp
  have hk := keyFrame_eq_of_params (hi := hi) hm
  refine ⟨dsa₁, dsa₂, h1, h2', hk, by rw [hk], by rw [hk], fun X t c j fs => ?_⟩
  rw [hk]

end Walk

end ConLeche.Model
