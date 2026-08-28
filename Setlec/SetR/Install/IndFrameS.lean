import Setlec.SetR.Install.IndBottomS
import Setlec.Verify.Denote.TeleOpen
import Setlec.Verify.Denote.IndFrame

/-!
# The [set] frame toolkit for the modeled-iota bottoms (task #148, T5)

The value-side machinery the bottoms' proofs consume — the [set]
counterparts of `IndBottom.lean`'s context/spine tier, collapsed by
the design's central saving: *evaluation is instantiation*.  Where the
TT lane instantiates open `Deq`s syntactically (`Deq.instCtx` over
`VExpr.instSeq`), this lane evaluates open interp-equalities at a
**value chain** (`chainE`), and the whole substitution apparatus is
one lemma (`interp_instSeq`).

The padding trick transposes with `empty` in place of `dummyPropT`:
an untouched inner context slot is `.sort 0`, its chain value is
`empty ∈ˢ univ 0`, so a partially-fitted chain satisfies a full-depth
context with no strengthening lemma (`sat_padded`).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The value chain -/

/-- The chain fold, with the value environment split from the base:
values are always interpreted at `ρval`, the fold conses onto
`ρbase`. -/
noncomputable def chainFrom (V : Type w) [SetTheory V] (ρval : Nat → V)
    (ρbase : Nat → V) (ws : List VExpr) : Nat → V :=
  ws.foldl (fun ρ' w => cons V (interp V ρval w) ρ') ρbase

/-- The value chain of a fired spine (outermost first): the [set]
shadow of `VExpr.instSeq` — `bvar 0` is the innermost (last) value,
indices past the spine read the ambient environment. -/
noncomputable def chainE (V : Type w) [SetTheory V] (ρ : Nat → V) (ws : List VExpr) :
    Nat → V :=
  chainFrom V ρ ρ ws

@[simp] theorem chainFrom_nil (ρval ρbase : Nat → V) :
    chainFrom V ρval ρbase [] = ρbase := rfl

theorem chainFrom_cons (ρval ρbase : Nat → V) (w : VExpr)
    (ws : List VExpr) :
    chainFrom V ρval ρbase (w :: ws)
      = chainFrom V ρval (cons V (interp V ρval w) ρbase) ws := rfl

/-- Chain lookup below the spine: the value of the
`(len - 1 - i)`-th spine element (outermost first). -/
theorem chainFrom_lt (ρval : Nat → V) :
    ∀ (ws : List VExpr) (ρbase : Nat → V) (i : Nat), i < ws.length →
      chainFrom V ρval ρbase ws i
        = interp V ρval (ws.getD (ws.length - 1 - i) default) := by
  intro ws
  induction ws with
  | nil => intro ρbase i hi; exact nomatch hi
  | cons w ws ih =>
    intro ρbase i hi
    rw [chainFrom_cons]
    by_cases hlt : i < ws.length
    · rw [ih _ i hlt,
        show (w :: ws).length - 1 - i = (ws.length - 1 - i) + 1 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_succ]
    · have hie : i = ws.length := by
        simp only [List.length_cons] at hi
        omega
      subst hie
      -- past the tail chain: reads the base's head
      have hge : ∀ (ws' : List VExpr) (ρb : Nat → V) (j : Nat),
          ws'.length ≤ j →
          chainFrom V ρval ρb ws' j = ρb (j - ws'.length) := by
        intro ws'
        induction ws' with
        | nil => intro ρb j _; simp [chainFrom_nil]
        | cons w' ws'' ih' =>
          intro ρb j hj
          rw [chainFrom_cons, ih' _ j (by simp at hj; omega)]
          simp only [List.length_cons] at hj ⊢
          rw [show j - ws''.length = (j - (ws''.length + 1)) + 1 from by
            omega]
          rfl
      rw [hge ws _ ws.length (Nat.le_refl _), Nat.sub_self,
        show (w :: ws).length - 1 - ws.length = 0 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_zero]
      rfl

/-- Chain lookup at or above the spine: the ambient environment,
shifted. -/
theorem chainFrom_ge (ρval : Nat → V) :
    ∀ (ws : List VExpr) (ρbase : Nat → V) (i : Nat), ws.length ≤ i →
      chainFrom V ρval ρbase ws i = ρbase (i - ws.length) := by
  intro ws
  induction ws with
  | nil => intro ρb i _; simp [chainFrom_nil]
  | cons w ws ih =>
    intro ρb i hi
    rw [chainFrom_cons, ih _ i (by simp at hi; omega)]
    simp only [List.length_cons] at hi ⊢
    rw [show i - ws.length = (i - (ws.length + 1)) + 1 from by omega]
    rfl

theorem chainE_lt {ρ : Nat → V} {ws : List VExpr} {i : Nat}
    (hi : i < ws.length) :
    chainE V ρ ws i = interp V ρ (ws.getD (ws.length - 1 - i) default) :=
  chainFrom_lt ρ ws ρ i hi

theorem chainE_ge {ρ : Nat → V} {ws : List VExpr} {i : Nat}
    (hi : ws.length ≤ i) : chainE V ρ ws i = ρ (i - ws.length) :=
  chainFrom_ge ρ ws ρ i hi

/-- **Evaluation is instantiation** — the [set] collapse of the whole
`Deq.instCtx`/`instSeq` apparatus: interpreting a fully spine-
instantiated term is interpreting the open term at the value chain. -/
theorem interp_instSeq :
    ∀ (ws : List VExpr) (e : VExpr) (ρ : Nat → V),
      interp V ρ (VExpr.instSeq ws (ws.length - 1) e)
        = interp V (chainE V ρ ws) e := by
  intro ws
  induction ws with
  | nil => intro e ρ; rfl
  | cons w ws ih =>
    intro e ρ
    rw [show (w :: ws).length - 1 = ws.length from by simp,
      VExpr.instSeq_cons, ih (e.inst w ws.length) ρ, interp_inst]
    congr 1
    funext i
    show instE V ws.length
        (interp V (shiftE V ws.length 0 (chainE V ρ ws)) w)
        (chainE V ρ ws) i
      = chainE V ρ (w :: ws) i
    have hsh : shiftE V ws.length 0 (chainE V ρ ws) = ρ := by
      funext j
      show chainE V ρ ws (j + ws.length) = ρ j
      rw [chainE_ge (by omega), Nat.add_sub_cancel]
    rw [hsh]
    unfold instE
    by_cases h1 : i < ws.length
    · rw [if_pos h1, chainE_lt h1,
        show chainE V ρ (w :: ws) i
          = interp V ρ ((w :: ws).getD ((w :: ws).length - 1 - i) default)
        from chainE_lt (by simp only [List.length_cons]; omega),
        show (w :: ws).length - 1 - i = (ws.length - 1 - i) + 1 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_succ]
    · rw [if_neg h1]
      by_cases h2 : i = ws.length
      · rw [if_pos h2, h2,
          show chainE V ρ (w :: ws) ws.length = interp V ρ w from by
            rw [chainE_lt (by simp only [List.length_cons]; omega),
              show (w :: ws).length - 1 - ws.length = 0 from by
                simp only [List.length_cons]; omega,
              List.getD_cons_zero]]
      · rw [if_neg h2,
          chainE_ge (ws := ws) (by omega),
          chainE_ge (ws := w :: ws)
            (by simp only [List.length_cons]; omega)]
        congr 1
        simp only [List.length_cons]
        omega

/-! ## The padding -/

/-- Pad an environment with `m` copies of `empty` below (the values of
the `.sort 0` padding slots — `empty ∈ˢ univ 0`). -/
noncomputable def padE (V : Type w) [SetTheory V] (m : Nat) (ρ' : Nat → V) :
    Nat → V :=
  fun i => if i < m then SetTheory.empty else ρ' (i - m)

@[simp] theorem padE_zero (ρ' : Nat → V) : padE V 0 ρ' = ρ' := by
  funext i; simp [padE]

/-- A padded prefix keeps a context satisfied: the padding entries are
`.sort 0`, their values `empty`, and every older entry's interpretation
reads only the environment above the padding. -/
theorem sat_padded {Γouter : List VExpr} {ρ' : Nat → V} (m : Nat)
    (h : Sat V Γouter ρ') :
    Sat V (List.replicate m (.sort 0) ++ Γouter) (padE V m ρ') := by
  intro i A hi
  by_cases him : i < m
  · rw [List.getElem?_append_left (by simpa using him),
      List.getElem?_replicate_of_lt him] at hi
    obtain rfl := Option.some.inj hi
    show padE V m ρ' i ∈ˢ interp V _ (.sort 0)
    rw [interp_sort, show padE V m ρ' i = SetTheory.empty from by
      simp [padE, him]]
    exact empty_mem_univ 0
  · rw [List.getElem?_append_right (by simpa using him)] at hi
    simp only [List.length_replicate] at hi
    have h1 := h (i - m) A hi
    have henv : (fun j => padE V m ρ' (j + i + 1))
        = (fun j => ρ' (j + (i - m) + 1)) := by
      funext j
      show padE V m ρ' (j + i + 1) = ρ' (j + (i - m) + 1)
      rw [show padE V m ρ' (j + i + 1) = ρ' (j + i + 1 - m) from by
        simp only [padE, if_neg (show ¬ j + i + 1 < m by omega)],
        show j + i + 1 - m = j + (i - m) + 1 from by omega]
    show padE V m ρ' i ∈ˢ interp V (fun j => padE V m ρ' (j + i + 1)) A
    rw [show padE V m ρ' i = ρ' (i - m) from by simp [padE, him], henv]
    exact h1


/-! ## Chains of plain values -/

/-- The chain over already-interpreted values (outermost first). -/
noncomputable def consChain (V : Type w) [SetTheory V] (ρ0 : Nat → V)
    (vs : List V) : Nat → V :=
  vs.foldl (fun ρ' v => cons V v ρ') ρ0

@[simp] theorem consChain_nil (ρ0 : Nat → V) : consChain V ρ0 [] = ρ0 :=
  rfl

theorem consChain_cons (ρ0 : Nat → V) (v : V) (vs : List V) :
    consChain V ρ0 (v :: vs) = consChain V (cons V v ρ0) vs := rfl

/-- The expression chain is the value chain of the interps. -/
theorem chainE_eq_consChain (ρ : Nat → V) (ws : List VExpr) :
    chainE V ρ ws = consChain V ρ (ws.map (interp V ρ)) := by
  show chainFrom V ρ ρ ws = _
  rw [show ∀ ρb, chainFrom V ρ ρb ws = consChain V ρb (ws.map (interp V ρ))
    from ?_]
  · intro ρb
    induction ws generalizing ρb with
    | nil => rfl
    | cons w ws ih => rw [chainFrom_cons, List.map_cons, consChain_cons, ih]

/-- Inserting the outermost chain value: consing at the spine's top is
`instE` at the spine's length. -/
theorem chainE_cons_eq_instE (ρ : Nat → V) (w : VExpr) (ws : List VExpr) :
    chainE V ρ (w :: ws)
      = instE V ws.length (interp V ρ w) (chainE V ρ ws) := by
  funext i
  unfold instE
  by_cases h1 : i < ws.length
  · rw [if_pos h1, chainE_lt h1,
      chainE_lt (ws := w :: ws) (by simp only [List.length_cons]; omega),
      show (w :: ws).length - 1 - i = (ws.length - 1 - i) + 1 from by
        simp only [List.length_cons]; omega,
      List.getD_cons_succ]
  · rw [if_neg h1]
    by_cases h2 : i = ws.length
    · rw [if_pos h2, h2, chainE_lt (ws := w :: ws)
        (by simp only [List.length_cons]; omega),
        show (w :: ws).length - 1 - ws.length = 0 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_zero]
    · rw [if_neg h2, chainE_ge (ws := ws) (by omega),
        chainE_ge (ws := w :: ws)
          (by simp only [List.length_cons]; omega)]
      congr 1
      simp only [List.length_cons]
      omega

/-! ## Fitting a tower from chain memberships -/

/-- **The tower fitting, from chain memberships**: values whose interps
inhabit the tower's open domains at the progressive chains fit the
tower (`TeleFitV`), with the fully instantiated body as residual.  The
[set] `VTeleTyped.ofPiTele`. -/
theorem teleFitV_of_tower :
    ∀ (k : Nat) {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele k T Γ R → ∀ {ws : List VExpr} {ρ : Nat → V},
      ws.length = k →
      (∀ n, n < k →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (chainE V ρ (ws.take n))
            (Γ.getD (k - 1 - n) default)) →
      TeleFitV V ρ T ws (VExpr.instSeq ws (k - 1) R) := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws ρ hlen _
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact TeleFitV.nil
  | succ k ihk =>
    intro T Γ R h ws ρ hlen hmem
    cases h with
    | @cons _ A B _ Γ' htail =>
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    -- the head membership: entry `k` of `Γ' ++ [A]` is `A`
    have h0 := hmem 0 (by omega)
    rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
        rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
        simp] at h0
    simp only [List.getD_cons_zero, List.take_zero, chainE,
      chainFrom_nil] at h0
    refine TeleFitV.cons h0 ?_
    -- the tail: the instantiated tower via the recursion at `k`
    have hinst := htail.inst w 0
    have hfit := ihk hinst (ws := ws') (ρ := ρ) hlen' ?_
    · rw [show VExpr.instSeq (w :: ws') (k + 1 - 1) R
          = VExpr.instSeq ws' (k - 1) (R.inst w k) from by
        rw [VExpr.instSeq_cons]
        simp only [Nat.add_sub_cancel]]
      rw [show (0 : Nat) + k = k from Nat.zero_add k] at hfit
      exact hfit
    · intro n hn
      have h1 := hmem (n + 1) (by omega)
      rw [List.getD_cons_succ,
        show (w :: ws').take (n + 1) = w :: ws'.take n from rfl,
        show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
            = Γ'.getD (k - 1 - n) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by omega)]
          congr 2
          omega] at h1
      rw [ctxInstAt_getD w 0 Γ' (k - 1 - n) (by omega),
        show 0 + Γ'.length - 1 - (k - 1 - n) = n from by omega]
      have htklen : (ws'.take n).length = n := by
        rw [List.length_take]
        omega
      rw [interp_inst,
        show shiftE V n 0 (chainE V ρ (ws'.take n)) = ρ from by
          funext j
          show chainE V ρ (ws'.take n) (j + n) = ρ j
          rw [chainE_ge (by omega), htklen]
          congr 1
          omega,
        show instE V n (interp V ρ w) (chainE V ρ (ws'.take n))
            = chainE V ρ (w :: ws'.take n) from by
          rw [chainE_cons_eq_instE, htklen]]
      exact h1


/-- The tail of a chain at an entry position is the partial chain of
the outer values. -/
theorem chainE_tail {ρ : Nat → V} {ws : List VExpr} {i : Nat}
    (hi : i < ws.length) :
    (fun j => chainE V ρ ws (j + i + 1))
      = chainE V ρ (ws.take (ws.length - 1 - i)) := by
  funext j
  have htk : (ws.take (ws.length - 1 - i)).length = ws.length - 1 - i := by
    rw [List.length_take]
    omega
  by_cases hj : j + i + 1 < ws.length
  · have hYlt : ws.length - 1 - i - 1 - j < ws.length - 1 - i := by
      omega
    rw [chainE_lt hj, chainE_lt (by rw [htk]; omega), htk,
      show ws.length - 1 - (j + i + 1)
          = ws.length - 1 - i - 1 - j from by omega,
      List.getD, List.getD, List.getElem?_take_of_lt hYlt]
  · rw [chainE_ge (by omega), chainE_ge (by rw [htk]; omega), htk]
    congr 1
    omega

/-- **`Sat` of a tower's context at the chain**, from the same
per-step chain memberships `teleFitV_of_tower` consumes. -/
theorem sat_of_tower {k : Nat} {T : VExpr} {Γ : List VExpr} {R : VExpr}
    (h : PiTele k T Γ R) {ws : List VExpr} {ρ : Nat → V}
    (hlen : ws.length = k)
    (hmem : ∀ n, n < k →
      interp V ρ (ws.getD n default)
        ∈ˢ interp V (chainE V ρ (ws.take n))
          (Γ.getD (k - 1 - n) default)) :
    Sat V Γ (chainE V ρ ws) := by
  intro i A hi
  have hΓlen : Γ.length = k := h.length
  have hik : i < k := by
    rw [← hΓlen]
    rcases Nat.lt_or_ge i Γ.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hi
      exact nomatch hi
  have h1 := hmem (k - 1 - i) (by omega)
  rw [show k - 1 - (k - 1 - i) = i from by omega,
    show Γ.getD i default = A from by rw [List.getD, hi]; rfl] at h1
  rw [chainE_lt (by omega),
    show ws.length - 1 - i = k - 1 - i from by omega,
    show (fun j => chainE V ρ ws (j + i + 1))
        = chainE V ρ (ws.take (k - 1 - i)) from by
      rw [← show ws.length - 1 - i = k - 1 - i from by omega]
      exact chainE_tail (by omega)]
  exact h1

/-! ## Value chains of plain values: the truthfulness descent -/

/-- **Truthfulness descends a fitted tower** — the pi-clause of
`AnnotOkV` iterated at chain values (no instantiation, no
truthfulness of the values: the clause quantifies members). -/
theorem annotOkV_descend :
    ∀ (k : Nat) {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele k T Γ R → ∀ (ρ0 : Nat → V) (vs : List V),
      vs.length = k → AnnotOkV V ρ0 T →
      (∀ n, n < k →
        vs.getD n SetTheory.empty
          ∈ˢ interp V (consChain V ρ0 (vs.take n))
            (Γ.getD (k - 1 - n) default)) →
      AnnotOkV V (consChain V ρ0 vs) R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ρ0 vs hlen hT _
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact hT
  | succ k ihk =>
    intro T Γ R h ρ0 vs hlen hT hmem
    cases h with
    | @cons _ A B _ Γ' htail =>
    match vs, hlen with
    | v :: vs', hlen =>
    have hlen' : vs'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    have h0 := hmem 0 (by omega)
    rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
        rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
        simp] at h0
    simp only [List.getD_cons_zero, List.take_zero, consChain_nil] at h0
    rw [AnnotOkV_pi] at hT
    rw [consChain_cons]
    refine ihk htail (cons V v ρ0) vs' hlen' (hT.2 v h0) ?_
    intro n hn
    have h1 := hmem (n + 1) (by omega)
    rw [List.getD_cons_succ,
      show (v :: vs').take (n + 1) = v :: vs'.take n from rfl,
      consChain_cons,
      show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
          = Γ'.getD (k - 1 - n) default from by
        rw [List.getD, List.getD,
          List.getElem?_append_left (by omega)]
        congr 2
        omega] at h1
    exact h1

/-- The chain over interps is the value chain. -/
theorem consChain_map_interp (ρ : Nat → V) (ws : List VExpr) :
    consChain V ρ (ws.map (interp V ρ)) = chainE V ρ ws :=
  (chainE_eq_consChain ρ ws).symm

/-! ## Applying along a fit, value-headed -/

/-- `TeleFitV.appN` with a *value* head: a member of the telescope's
interpretation applied along a fitting spine lands in the residual's
interpretation. -/
theorem TeleFitV.appN_val {ρ : Nat → V} {T rest : VExpr}
    {as : List VExpr} (h : TeleFitV V ρ T as rest) :
    ∀ {v : V}, v ∈ˢ interp V ρ T →
      (as.map (interp V ρ)).foldl SetTheory.app v ∈ˢ interp V ρ rest := by
  induction h with
  | nil => intro v hv; exact hv
  | @cons A B a rest as hmem htail ih =>
    intro v hv
    rw [List.map_cons, List.foldl_cons]
    refine ih ?_
    rw [interp_inst0]
    exact app_mem_piC hv hmem

/-! ## The singleton-fibre package

Every abstraction inhabits *some* product — over its own domain, with
singleton fibres.  This is the `AnnotOkV` app-package factory for the
fired rule reduct (the truthfulness-transport conjunct): the partial
applications of the rule's λ-tower are `lamC`s, and each is packaged
by its own domain with no fibre analysis at all. -/
theorem lamC_mem_upair (A : V) (F : V → V) :
    lamC A F ∈ˢ piC A (fun x => upair (F x) (F x)) :=
  lamC_mem fun _x _hx => mem_upair.mpr (Or.inl rfl)



/-! ## `CtxOkR` at the opened frame

The transpose of `ctxOk_of_openers`: any context whose entries at the
touched indices are the frame's own-depth denoted annotations
correlates with a kit expression — padding slots are never
consulted. -/
theorem ctxOkR_of_openers {μ : CheckMode} {cval : TConstVal} {env : Env}
    {φ : Name → Nat}
    (hcl : ∀ n ψ', VExpr.Closed (cval n ψ'))
    {k : Nat} {fvs : List Expr} {As : Nat → VExpr} {Δ' : List VExpr}
    (hΔlen : Δ'.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env φ i (Expr.fvarTypeD x) = some (As i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δ'[k - 1 - i]? = some (As i)) :
    CtxOkR μ cval env φ k Δ' e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨nm, ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2, h3⟩ : l.1 = pos ∧ l.2.1 = nm ∧ l.2.2 = ty := by
    injection hx with a b c
    exact ⟨a, b, c⟩
  subst h1 h2 h3
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2.2 := by
    simpa [Expr.WScoped] using hw
  have hfb : Expr.fvarsBelow l.1 l.2.2 := hwty.2.fvarsBelow
  refine ⟨by omega, hfb, (As l.1).liftN (k - l.1), ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hpos
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2.1 l.2.2) = l.2.2 from rfl]
      at hd1
    have hd2 := denote_lift (cval := cval) (env := env) (φ := φ) hcl
      (p := l.1) (e := l.2.2) hfb k (by omega)
    rw [hd2, hd1]
    rfl
  · refine ⟨(As l.1).liftN (k - 1 - l.1 + 1), ?_, ?_⟩
    · exact Infer.bvar (hent l.1 hlt)
    · rw [show k - 1 - l.1 + 1 = k - l.1 from by omega]
      exact DefEq.refl


end Setlec.SetR
