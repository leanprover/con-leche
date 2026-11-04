module

public import ConLeche.Model.CtxOkKit
public import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.Depth

public section

/-!
# An opened constructor telescope, read

A closed `∀`-telescope opened at its own variables: each variable's
annotation reads to the telescope's domain at its depth, and correlates
with the earlier domains (`CtxOk`).  What the install's frames and a
projection's guard at its use read.  Below the rules tier: nothing here
looks at a derivation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
theorem cons_eta (ρ : Nat → V) : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
  funext i
  cases i <;> rfl

theorem Sat_cons_inv {Δ : List Term} {A : Term} {ρ : Nat → V}
    (h : Sat V (A :: Δ) ρ) :
    ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) A ∧
      Sat V Δ (fun j => ρ (j + 1)) :=
  ⟨by have := h 0 A rfl; simpa using this, Sat_tail h⟩

theorem stripPisAV_mkPisAV :
    ∀ (pps : List Term) (b : Term),
      stripPisAV pps.length (mkPisAV pps b) = some (pps, b)
  | [], _ => rfl
  | d :: pps, b => by
    simp only [List.length_cons, mkPisAV, stripPisAV, stripPisAV_mkPisAV pps b,
      Option.map_some]

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem WellDenoted_pi_dom {ρ : Nat → V} {A B : Term}
    (h : WellDenoted V ρ (.pi A B)) : WellDenoted V ρ A :=
  (cast (WellDenoted_pi V ρ A B) h).1

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem WellDenoted_pi_body {ρ : Nat → V} {A B : Term}
    (h : WellDenoted V ρ (.pi A B)) {x : V}
    (hx : x ∈ˢ interp V ρ A) : WellDenoted V (cons x ρ) B :=
  (cast (WellDenoted_pi V ρ A B) h).2.2.1 x hx


/-- **`CtxOk` at the opened frame**: a context whose entries at the touched indices are the
frame's own-depth annotation readings correlates with a kit expression;
padding slots are never consulted. -/
theorem ctxOk_of_openers {env : Env} {m : EnvModel V env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {k : Nat} {fvs : List Expr} {Aa : Nat → Term} {Δa : List Term}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < n → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedTy V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i)) :
    CtxOk m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2⟩ : l.1 = pos ∧ l.2 = ty := by
    injection hx with a b
    exact ⟨a, b⟩
  subst h1 h2
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2 := by
    simpa [Expr.WScoped] using hw
  refine ⟨hwty.1, hwty.2.fvarsBelow, (Aa l.1).liftN (k - l.1) 0, Aa l.1,
    ?_, hent l.1 hlt, ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hpos
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2) = l.2 from rfl]
      at hd1
    rw [denote_lift hacl hwty.2 k (by omega), hd1]
    rfl
  · -- the equation: `interp_liftN`'s `shiftE` against the entry's own
    -- context environment; both are `fun j => ρ (j + (k - l.1))`
    intro ρ _
    rw [interp_liftN]
    congr 1
    funext j
    show (if j < 0 then ρ j else ρ (j + (k - l.1))) = ρ (j + (k - 1 - l.1) + 1)
    rw [ite_eq_right (Nat.not_lt_zero j)]
    congr 1
    omega
  · -- the grading: the entry's, transported across the same lift
    intro ρ hρ
    refine (WellDenotedTy_liftN (k - l.1) (Aa l.1) 0 ρ).mpr ?_
    have h := hokA l.1 hlt ρ hρ
    have henv : shiftE (k - l.1) 0 ρ = fun j => ρ (j + (k - 1 - l.1) + 1) := by
      funext j
      show (if j < 0 then ρ j else ρ (j + (k - l.1))) = _
      rw [ite_eq_right (Nat.not_lt_zero j)]
      congr 1
      omega
    rw [henv]
    exact h


/-- **The peel.**  A Π-prefix opened at `fvar`s reads to a
`stripPisAV`-strippable reading whose domains are the opened
variables' annotation readings at their own depths, and whose residual is
the opened body's reading at the full depth. -/
theorem denote_openPis {acval : Name → (Name → Nat) → Term} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
      {ea : Term},
      openPisAtFvars n e d = some (fvs, o) →
      denote acval env φ d e = some ea →
      ∃ (pps : List Term) (b : Term),
        stripPisAV n ea = some (pps, b) ∧
        denote acval env φ (d + n) o = some b ∧
        pps.length = n ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          ∃ p, pps[i]? = some p ∧
            denote acval env φ (d + i) x.fvarTypeD = some p
  | 0, d, e, fvs, o, ea, hop, hden => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨[], ea, rfl, by simpa using hden, rfl,
      fun i x hx => by simp at hx⟩
  | n + 1, d, e, fvs, o, ea, hop, hden => by
    match e, hop with
    | .forallE dom body, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv hden
        obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denote_openPis n hop' hba
        refine ⟨ta :: pps, b, ?_, ?_, ?_, ?_⟩
        · simp only [stripPisAV, hst, Option.map_some]
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hb
        · simp [hlen]
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            subst hx
            exact ⟨ta, rfl,
              by rw [Nat.add_zero]; exact hta⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨p, hp, hpd⟩ := hbind i x hx
            exact ⟨p, by simpa using hp,
              by rw [show d + (i + 1) = d + 1 + i from by omega]; exact hpd⟩
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _, hop | .sort _, hop | .const _ _, hop
    | .app _ _, hop | .lam _ _, hop | .letE _ _ _, hop | .lit _, hop
    | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop


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


/-- The peel's entries, read off the reversed context. -/
theorem getD_reverse_of_peel {pps : List Term} {k : Nat}
    (hlen : pps.length = k) {i : Nat} (hi : i < k) {p : Term}
    (hp : pps[i]? = some p) :
    (pps.reverse).getD (k - 1 - i) default = p := by
  rw [List.getD, List.getElem?_reverse (by omega), hlen,
    show k - 1 - (k - 1 - i) = i from by omega, hp]
  rfl


/-- **`CtxOk` at an opening's frame**: a term well-scoped at depth
`i ≤ k` over the opening's variables correlates with the reading's
context at that depth (`Γ.drop (k - i)` — the earlier domains,
innermost first). -/
theorem ctxOk_opened {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    {Γ : List Term} (hΓ : Γ.length = k)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote m.acval env φ i (Expr.fvarTypeD x)
        = some (Γ.getD (k - 1 - i) default))
    (hokΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedTy V ρ (Γ.getD (k - 1 - i) default))
    {i : Nat} (hik : i ≤ k) {x : Expr} (hwx : Expr.WScoped i x)
    (hleaf : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    CtxOk m φ i (Γ.drop (k - i)) x := by
  have hidx := openPisAtFvars_index k e 0 hop
  have hlenF : fvs.length = k := openPisAtFvars_length k hop
  have hws := (openPisAtFvars_WScoped k e 0 hop
    (Expr.WScoped.of_not_hasFvar hcl)).1
  -- the positions of the variables a leaf can be
  have hpos : ∀ l ∈ x.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty, hx⟩ := hidx p _ hp
    rw [Nat.zero_add] at hx
    obtain ⟨rfl, -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hx with a b
      exact ⟨a, b⟩
    exact hp
  refine ctxOk_of_openers m.acval_closed (fvs := fvs.take i)
    (Aa := fun j => Γ.getD (k - 1 - j) default) (Δa := Γ.drop (k - i))
    (by rw [List.length_drop]; omega) ?_ ?_ ?_ (e := x) (n := i) ?_
    (Expr.fvarLeaves_lt_of_wscoped hwx) ?_ ?_
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    obtain ⟨ty, hx⟩ := hidx j y hy
    exact ⟨ty, by rw [hx, Nat.zero_add]⟩
  · intro y hy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
    have hji : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hji] at hj
    obtain ⟨ty, rfl⟩ := hidx j y hj
    have hw := hws _ (List.mem_of_getElem? hj)
    rw [Nat.zero_add] at hw ⊢
    simp only [Expr.WScoped, Nat.zero_add] at hw ⊢
    exact ⟨hji, hw.2⟩
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    exact hdoms j y hy
  · intro l hl
    have hlt := Expr.fvarLeaves_lt_of_wscoped hwx l hl
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hpos l hl)
  · intro j hj
    rw [List.getElem?_drop, show k - i + (i - 1 - j) = k - 1 - j from by omega]
    have hjl : k - 1 - j < Γ.length := by omega
    rw [List.getD, List.getElem?_eq_getElem hjl]
    rfl
  · intro j hj ρ hρ
    have hd := Sat_drop hρ (i - j)
    rw [List.drop_drop, show k - i + (i - j) = k - j from by omega] at hd
    have e : (fun l => ρ (l + (i - 1 - j) + 1)) = fun l => ρ (l + (i - j)) := by
      funext l; congr 1; omega
    rw [e]
    exact hokΓ j (by omega) _ hd



/-- **The domains of a graded `∀`-telescope are graded types** under the
earlier ones. -/
theorem mkPisAV_doms_graded {b : Term} :
    ∀ (ds : List Term) {Δ₀ : List Term},
      (∀ ρ : Nat → V, Sat V Δ₀ ρ → WellDenoted V ρ (mkPisAV ds b)) →
      ∀ i, i < ds.length → ∀ ρ : Nat → V, Sat V ((ds.take i).reverse ++ Δ₀) ρ →
        WellDenotedTy V ρ (ds.getD i default)
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | A :: ds, Δ₀, hT, i, hi, ρ, hρ => by
    cases i with
    | zero =>
      have h := hT ρ (by simpa using hρ)
      exact ⟨WellDenoted_pi_dom h, (cast (WellDenoted_pi V ρ _ _) h).2.1⟩
    | succ i =>
      have hB : ∀ ρ : Nat → V, Sat V (A :: Δ₀) ρ → WellDenoted V ρ (mkPisAV ds b) := by
        intro ρ hρ
        obtain ⟨h0, htl⟩ := Sat_cons_inv hρ
        have := WellDenoted_pi_body (hT _ htl) h0
        rwa [cons_eta] at this
      have := mkPisAV_doms_graded ds hB i (by simpa using hi) ρ (by
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ)
      simpa using this

end ConLeche.Model
