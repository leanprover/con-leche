import Setlec.SetR.Install.IndFrameS

/-!
# The [set] bottom stages (task #148, T5 c2)

The sealed per-stage decomposition of the plain bottom, mirroring
`IndBottomStages.lean` with the [set] apparatus: an install-time walk
element fires as an interp-equality at a padded chain (`openWalk_eqS`
— the one point where relation derivations become semantic equations,
the `openFrame_deq` transpose), and the chain/fit conversions ride
`interp_instSeq`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- Stripping the padding recovers the chain. -/
theorem padE_shiftE (m : Nat) (ρ' : Nat → V) :
    shiftE V m 0 (padE V m ρ') = ρ' := by
  funext j
  show padE V m ρ' (j + m) = ρ' j
  simp only [padE, if_neg (show ¬ j + m < m by omega),
    Nat.add_sub_cancel]

/-- The converse of `teleFitV_of_tower`: a fit's memberships, read in
chain form against the tower's context. -/
theorem teleFitV_to_chain :
    ∀ (k : Nat) {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele k T Γ R → ∀ {ws : List VExpr} {ρ : Nat → V} {rest : VExpr},
      ws.length = k → TeleFitV V ρ T ws rest →
      ∀ n, n < k →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (chainE V ρ (ws.take n))
            (Γ.getD (k - 1 - n) default) := by
  intro k
  induction k with
  | zero => intro T Γ R h ws ρ rest hlen hfit n hn; exact nomatch hn
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit n hn
    cases h with
    | @cons _ A B _ Γ' htail =>
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    cases hfit with
    | cons hmem htailFit =>
    match n, hn with
    | 0, _ =>
      rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
          simp]
      show interp V ρ ((w :: ws').getD 0 default)
          ∈ˢ interp V (chainE V ρ ((w :: ws').take 0)) A
      simp only [List.getD_cons_zero, List.take_zero]
      show _ ∈ˢ interp V (chainFrom V ρ ρ []) A
      rw [chainFrom_nil]
      exact hmem
    | n + 1, hn =>
      have hinst := htail.inst w 0
      have h1 := ihk hinst hlen' htailFit n (by omega)
      rw [ctxInstAt_getD w 0 Γ' (k - 1 - n) (by omega),
        show 0 + Γ'.length - 1 - (k - 1 - n) = n from by omega,
        interp_inst] at h1
      have htklen : (ws'.take n).length = n := by
        rw [List.length_take]
        omega
      rw [show shiftE V n 0 (chainE V ρ (ws'.take n)) = ρ from by
          funext j
          show chainE V ρ (ws'.take n) (j + n) = ρ j
          rw [chainE_ge (by omega), htklen]
          congr 1
          omega,
        show instE V n (interp V ρ w) (chainE V ρ (ws'.take n))
            = chainE V ρ (w :: ws'.take n) from by
          rw [chainE_cons_eq_instE, htklen]] at h1
      rw [List.getD_cons_succ,
        show (w :: ws').take (n + 1) = w :: ws'.take n from rfl,
        show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
            = Γ'.getD (k - 1 - n) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by omega)]
          congr 2
          omega]
      exact h1

/-- **A walk element fires at a padded chain** — the [set]
`openFrame_deq`: the D6-refined quantified-context derivation is
instantiated at the padded pinned context and read through the
unconditional `DefEq.sound`.  The one point where the kit's relation
derivations become semantic equations. -/
theorem openWalk_eqS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ' : Name → Nat} (henv : EnvSHyp V env cval φ')
    {k : Nat} {fvs : List Expr} {As : Nat → VExpr} {Δpad : List VExpr}
    (hΔlen : Δpad.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env φ' i (Expr.fvarTypeD x) = some (As i))
    {n : Nat}
    (hent : ∀ i, i < n → Δpad[k - 1 - i]? = some (As i))
    {a b : Expr}
    (hde : DefEqAtW μ env cval φ' k a b)
    (hleafA : ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltA : ∀ l ∈ a.fvarLeaves, l.1 < n)
    (hleafB : ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltB : ∀ l ∈ b.fvarLeaves, l.1 < n)
    {ρpad : Nat → V} (hsat : Sat V Δpad ρpad) :
    ∃ Av Bv, denote cval env φ' k a = some Av ∧
      denote cval env φ' k b = some Bv ∧
      interp V ρpad Av = interp V ρpad Bv := by
  obtain ⟨Av, Bv, hAv, hBv, hder⟩ := hde
  refine ⟨Av, Bv, hAv, hBv, ?_⟩
  have hctxA := ctxOkR_of_openers (μ := μ) henv.cval_closed hΔlen hshape
    hws hdoms hleafA hltA hent
  have hctxB := ctxOkR_of_openers (μ := μ) henv.cval_closed hΔlen hshape
    hws hdoms hleafB hltB hent
  exact DefEq.sound henv (hder Δpad hctxA hctxB) ρpad hsat


/-- A fit's prefix fits, to some intermediate residual. -/
theorem TeleFitV.take {ρ : Nat → V} :
    ∀ {T rest : VExpr} {as : List VExpr}, TeleFitV V ρ T as rest →
      ∀ n : Nat, ∃ mid, TeleFitV V ρ T (as.take n) mid := by
  intro T rest as h
  induction h with
  | @nil T' =>
    intro n
    refine ⟨T', ?_⟩
    rw [List.take_nil]
    exact TeleFitV.nil
  | @cons A B a rest' as' hmem htail ih =>
    intro n
    cases n with
    | zero => exact ⟨_, TeleFitV.nil⟩
    | succ n =>
      obtain ⟨mid, hm⟩ := ih n
      exact ⟨mid, TeleFitV.cons hmem hm⟩

/-- Pointwise reading of a `Forall2` (with the length fact). -/
theorem Forall2.length_getD {α β : Type _} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall2 R as bs →
      as.length = bs.length ∧
      ∀ (i : Nat) (da : α) (db : β), i < as.length →
        R (as.getD i da) (bs.getD i db) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => exact ⟨rfl, fun i da db hi => nomatch hi⟩
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      obtain ⟨hR, htail⟩ := h
      obtain ⟨hlen, hget⟩ := ih htail
      refine ⟨by simp [hlen], ?_⟩
      intro i da db hi
      cases i with
      | zero => simpa using hR
      | succ i =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact hget i da db (by simpa using hi)

/-- **The padded satisfaction from partial chain memberships**: the
first `n` fitted values satisfy the tower's outer context, padded to
full depth by `.sort 0`/`empty` slots. -/
theorem sat_pad_of_mems {K : Nat} {T : VExpr} {Γ : List VExpr}
    {R : VExpr} (htower : PiTele K T Γ R) {zs : List VExpr}
    {ρ : Nat → V} (hlen : zs.length = K) {n : Nat} (hn : n ≤ K)
    (hmem : ∀ m, m < n →
      interp V ρ (zs.getD m default)
        ∈ˢ interp V (chainE V ρ (zs.take m))
          (Γ.getD (K - 1 - m) default)) :
    Sat V (List.replicate (K - n) (.sort 0) ++ Γ.drop (K - n))
      (padE V (K - n) (chainE V ρ (zs.take n))) := by
  obtain ⟨mid, hpre, -⟩ := htower.prefix n hn
  have hΓlen : Γ.length = K := htower.length
  refine sat_padded (K - n) (sat_of_tower hpre
    (ws := zs.take n) (by rw [List.length_take]; omega) ?_)
  intro m hm
  have h1 := hmem m (by omega)
  rw [show (zs.take n).getD m default = zs.getD m default from by
      rw [List.getD, List.getD, List.getElem?_take_of_lt hm],
    show (zs.take n).take m = zs.take m from by
      rw [List.take_take]
      congr 1
      omega,
    show (Γ.drop (K - n)).getD (n - 1 - m) default
        = Γ.getD (K - 1 - m) default from by
      rw [List.getD, List.getD, List.getElem?_drop,
        show K - n + (n - 1 - m) = K - 1 - m from by omega]]
  exact h1



/-- `instSeq` hits a frame variable at the full spine (the pad-free
`padHit`). -/
theorem instSeq_bvar_full {K : Nat} {p : Nat} {vals : List VExpr}
    (hp : p < K) (hvl : vals.length = K) :
    VExpr.instSeq vals (K - 1) (.bvar (K - 1 - p))
      = vals.getD p default := by
  have h := padHit (K := K) K p vals hp hvl (Nat.le_refl K)
  rwa [Nat.sub_self, List.replicate_zero, List.append_nil] at h

/-- Absorb the unused inner substitutions of a lifted term: only the
outer `n` values reach it. -/
theorem instSeq_absorb_left {vals : List VExpr} {K n : Nat} {X : VExpr}
    (hlen : vals.length = K) (hn : n ≤ K) :
    VExpr.instSeq vals (K - 1) (VExpr.liftN (K - n) X)
      = VExpr.instSeq (vals.take n) (n - 1) X := by
  have h := instSeq_append_absorb (vals.take n) (vals.drop n) X
  rw [List.take_append_drop] at h
  rw [show K - 1 = (vals.take n).length + (vals.drop n).length - 1 from by
      rw [List.length_take, List.length_drop, hlen]
      omega,
    show K - n = (vals.drop n).length from by
      rw [List.length_drop, hlen],
    h,
    show (vals.take n).length = n from by
      rw [List.length_take, hlen]
      omega]

set_option maxHeartbeats 1600000 in
/-- **The field domain, crossed** (the [set] zipper's field-branch
term core, V-free): the scattered constructor run's `cnP + j`-th
domain denotes at its own frame depth `rP + j` with its leaves among
the first `rP + j` openers, and its spine instantiation at the fired
statement values is the constructor tower's own domain instantiated at
the mixed spine. -/
theorem zipFieldTermEq {cval : TConstVal} {env : Env} {ψ' : Name → Nat}
    (hcl : ∀ n ψ'', VExpr.Closed (cval n ψ''))
    {rP cnP cnF : Nat} {fvs : List Expr}
    (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hbFvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hplainLe : cnP ≤ rP)
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : VExpr}
    (hTVjK : denote cval env ψ' (rP + cnF) ctyR = some TVj)
    (hTVjcl : VExpr.Closed TVj)
    {Γj : List VExpr} {Rj : VExpr}
    (htowerJ : PiTele (cnP + cnF) TVj Γj Rj)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP) ctyR
      = some (cdoms, cres))
    {zs : List VExpr} (hzslen : zs.length = rP + cnF)
    {mix : List VExpr} (hmixlen : mix.length = cnP + cnF)
    (hmixzs : ∀ q, q < cnP + cnF → q < mix.length ∧
      mix[q]? = some (zs.getD (if q < cnP then q else rP + (q - cnP))
        default))
    {j : Nat} (hj : j < cnF) :
    Expr.fvarsBelow (rP + j) (cdoms.getD (cnP + j) default) ∧
    (∀ l ∈ (cdoms.getD (cnP + j) default).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + j) ∧
    ∃ vdomLow,
      denote cval env ψ' (rP + j) (cdoms.getD (cnP + j) default)
        = some vdomLow ∧
      VExpr.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow
        = VExpr.instSeq (mix.take (cnP + j)) (cnP + j - 1)
            (Γj.getD (cnP + cnF - 1 - (cnP + j)) default) := by
  have hΓjlen : Γj.length = cnP + cnF := htowerJ.length
  -- the scattered spine and its per-element facts
  have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hfvslen]
    omega
  have hspGet : ∀ q, q < cnP + cnF →
      ∃ x, (fvs.take cnP ++ fvs.drop rP)[q]? = some x ∧
        fvs[if q < cnP then q else rP + (q - cnP)]? = some x := by
    intro q hq
    by_cases hqc : q < cnP
    · rcases hx : fvs[q]? with _ | x
      · rw [List.getElem?_eq_none_iff] at hx
        omega
      · refine ⟨x, ?_, by rw [if_pos hqc]; exact hx⟩
        rw [List.getElem?_append_left
          (by rw [List.length_take, hfvslen]; omega),
          List.getElem?_take_of_lt hqc]
        exact hx
    · rcases hx : fvs[rP + (q - cnP)]? with _ | x
      · rw [List.getElem?_eq_none_iff] at hx
        rw [hfvslen] at hx
        omega
      · refine ⟨x, ?_, by rw [if_neg hqc]; exact hx⟩
        have hmin : min cnP (rP + cnF) = cnP := by omega
        rw [List.getElem?_append_right
          (by rw [List.length_take, hfvslen]; omega),
          List.getElem?_drop, List.length_take, hfvslen, hmin,
          show rP + (q - cnP) = rP + (q - cnP) from rfl]
        exact hx
  have hspIdx : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ nm ty, x = Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm ty ∧
        x ∈ fvs := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    obtain ⟨x', hx', hfx⟩ := hspGet q hq
    obtain rfl : x = x' := by
      rw [hx] at hx'
      exact Option.some.inj hx'
    obtain ⟨nm, ty, hxe⟩ := hshapeS _ _ hfx
    exact ⟨nm, ty, hxe, List.mem_of_getElem? hfx⟩
  have hspFacts : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      (∃ w, denote cval env ψ' (rP + cnF) x = some w) ∧
        Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨nm, ty, rfl, hmem⟩ := hspIdx q x hx
    exact ⟨⟨_, denote_fvar cval env ψ' (rP + cnF) _ nm ty⟩,
      hwsFvs _ hmem, hbFvs _ hmem⟩
  -- truncate the scattered run at `cnP + j`
  obtain ⟨midJ, htr, hdr⟩ :=
    instPisAt_take (fvs.take cnP ++ fvs.drop rP) (cnP + j) hcinst
  obtain ⟨x0, sp', hsp0⟩ : ∃ x sp',
      (fvs.take cnP ++ fvs.drop rP).drop (cnP + j) = x :: sp' := by
    rcases hsp : (fvs.take cnP ++ fvs.drop rP).drop (cnP + j)
      with _ | ⟨x, sp'⟩
    · exfalso
      have := congrArg List.length hsp
      rw [List.length_drop, hsplen] at this
      simp at this
      omega
    · exact ⟨x, sp', rfl⟩
  rw [hsp0] at hdr
  obtain ⟨nmJ, domJ, bodyJ, mbJ, rfl, hds⟩ : ∃ nmJ domJ bodyJ mbJ,
      midJ = .forallE nmJ domJ bodyJ mbJ ∧
      (cdoms.drop (cnP + j))[0]? = some domJ := by
    cases midJ with
    | forallE nmJ domJ bodyJ mbJ =>
      simp only [Expr.instPisAt] at hdr
      rcases hrec : Expr.instPisAt sp' (bodyJ.instantiate1 x0)
        with _ | ⟨ds', rs'⟩
      · rw [hrec] at hdr
        exact nomatch hdr
      · rw [hrec] at hdr
        have hdr' : (some (domJ :: ds', rs') :
            Option (List Expr × Expr))
            = some (cdoms.drop (cnP + j), cres) := hdr
        injection hdr' with hdr''
        have h1 : domJ :: ds' = cdoms.drop (cnP + j) :=
          congrArg Prod.fst hdr''
        refine ⟨nmJ, domJ, bodyJ, mbJ, rfl, ?_⟩
        rw [← h1]
        rfl
    | bvar i => simp [Expr.instPisAt] at hdr
    | sort u => simp [Expr.instPisAt] at hdr
    | const c us => simp [Expr.instPisAt] at hdr
    | fvar a b c => simp [Expr.instPisAt] at hdr
    | lam a b c d => simp [Expr.instPisAt] at hdr
    | app a b => simp [Expr.instPisAt] at hdr
    | letE a b c d => simp [Expr.instPisAt] at hdr
    | proj a b c => simp [Expr.instPisAt] at hdr
    | lit l => simp [Expr.instPisAt] at hdr
  have hcdlen : cdoms.length = cnP + cnF := by
    have := instPisAt_length _ hcinst
    rw [hsplen] at this
    omega
  have hdomJ : cdoms.getD (cnP + j) default = domJ := by
    have h0 : (cdoms.drop (cnP + j))[0]? = some domJ := hds
    rw [List.getElem?_drop, Nat.add_zero] at h0
    rw [List.getD, h0]
    rfl
  -- leaves of the domain: among the first `rP + j` openers
  have hleafDom : ∀ l ∈ domJ.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + j := by
    intro l hl
    have hlmid : l ∈ (Expr.forallE nmJ domJ bodyJ mbJ).fvarLeaves := by
      rw [Expr.fvarLeaves]
      exact List.mem_append_left _ hl
    rcases instPisAt_leaves _ htr l (Or.inr hlmid) with hty | ⟨a, ha, hla⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hty
      exact nomatch hty
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      have hqm : q < cnP + j := by
        rcases Nat.lt_or_ge q (cnP + j) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [List.length_take]; omega)]
            at hq
          exact nomatch hq
      have hq' : (fvs.take cnP ++ fvs.drop rP)[q]? = some a := by
        rw [← List.getElem?_take_of_lt hqm]
        exact hq
      obtain ⟨nm, ty, rfl, hmem⟩ := hspIdx q a hq'
      have hidx : (if q < cnP then q else rP + (q - cnP)) < rP + j := by
        by_cases hqc : q < cnP
        · rw [if_pos hqc]; omega
        · rw [if_neg hqc]; omega
      rw [Expr.fvarLeaves] at hla
      rcases List.mem_cons.mp hla with rfl | hla'
      · exact ⟨hmem, hidx⟩
      · have hwsty := hwsFvs _ hmem
        have hwsty' : Expr.WScoped (if q < cnP then q else rP + (q - cnP))
            ty := by
          have h' := hwsty
          simp only [Expr.WScoped] at h'
          exact h'.2
        have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty' l hla'
        refine ⟨hleafClosed l ⟨_, hmem, ?_⟩, by omega⟩
        rw [Expr.fvarLeaves]
        exact List.mem_cons_of_mem _ hla'
  have hfbDom : Expr.fvarsBelow (rP + j) domJ :=
    Expr.fvarsBelow_of_fvarLeaves fun l hl => (hleafDom l hl).2
  -- the truncated residual denotes at the frame depth
  have hfbCty : Expr.fvarsBelow (rP + cnF) ctyR := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hl
    exact nomatch hl
  obtain ⟨vMid, hvMid⟩ := instPisAt_fvar_denote_defined hcl _ htr
    (D := rP + cnF)
    (fun q x hx => hspFacts q x (by
      rw [← List.getElem?_take_of_lt (show q < cnP + j from by
        rcases Nat.lt_or_ge q (cnP + j) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none
            (by rw [List.length_take]; omega)] at hx
          exact nomatch hx)]
      exact hx))
    hfbCty hCbR hTVjK
  -- read the pi apart: the domain denotes at depth `K`
  rw [denote_forallE] at hvMid
  rcases hvd : denote cval env ψ' (rP + cnF) domJ with _ | vDomK
  · rw [hvd] at hvMid
    exact nomatch hvMid
  rw [hvd] at hvMid
  rcases hvb : denote cval env ψ' (rP + cnF + 1)
      (bodyJ.instantiate1 (.fvar (rP + cnF) nmJ domJ)) with _ | vBodyK
  · rw [hvb] at hvMid
    exact nomatch hvMid
  rw [hvb] at hvMid
  obtain rfl : vMid = .pi vDomK vBodyK := (Option.some.inj hvMid).symm
  -- the domain at its own depth, lifted
  have hlow := denote_lift (cval := cval) (env := env) (φ := ψ') hcl
    (p := rP + j) (e := domJ) hfbDom (rP + cnF) (by omega)
  rw [hvd] at hlow
  rcases hvl : denote cval env ψ' (rP + j) domJ with _ | vdomLow
  · rw [hvl] at hlow
    exact nomatch hlow
  rw [hvl] at hlow
  have hVK : vDomK = VExpr.liftN (rP + cnF - (rP + j)) vdomLow 0 :=
    Option.some.inj hlow
  refine ⟨by rw [hdomJ]; exact hfbDom,
    by rw [hdomJ]; exact hleafDom,
    vdomLow, by rw [hdomJ]; exact hvl, ?_⟩
  -- the mid tower of the constructor
  obtain ⟨mid', hpre, hpost⟩ := htowerJ.prefix (cnP + j) (by omega)
  have hlenTake : ((fvs.take cnP ++ fvs.drop rP).take (cnP + j)).length
      = cnP + j := by
    rw [List.length_take, hsplen]
    omega
  have hspTake : ∀ (q : Nat) (x : Expr),
      ((fvs.take cnP ++ fvs.drop rP).take (cnP + j))[q]? = some x →
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x ∧ q < cnP + j := by
    intro q x hx
    have hqm : q < cnP + j := by
      rcases Nat.lt_or_ge q (cnP + j) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [List.length_take]; omega)]
          at hx
        exact nomatch hx
    rw [List.getElem?_take_of_lt hqm] at hx
    exact ⟨hx, hqm⟩
  have htow : PiTele
      ((fvs.take cnP ++ fvs.drop rP).take (cnP + j)).length
      (VExpr.instSeq zs (rP + cnF - 1) TVj)
      (Γj.drop (cnP + cnF - (cnP + j))) mid' := by
    rw [hlenTake, VExpr.instSeq_eq_self_of_closed hTVjcl]
    exact hpre
  have hwsCond : ∀ (q : Nat) (x : Expr),
      ((fvs.take cnP ++ fvs.drop rP).take (cnP + j))[q]? = some x →
      ∃ w0, denote cval env ψ' (rP + cnF) x = some w0 ∧
        (mix.take (cnP + j))[q]? = some
          (VExpr.instSeq zs (rP + cnF - 1) w0) := by
    intro q x hx
    obtain ⟨hx', hqm⟩ := hspTake q x hx
    obtain ⟨nm, ty, rfl, hmem⟩ := hspIdx q x hx'
    have hidxK : (if q < cnP then q else rP + (q - cnP)) < rP + cnF := by
      by_cases hqc : q < cnP
      · rw [if_pos hqc]
        omega
      · rw [if_neg hqc]
        omega
    refine ⟨.bvar (rP + cnF - 1 - (if q < cnP then q else rP + (q - cnP))),
      denote_fvar cval env ψ' (rP + cnF) _ nm ty, ?_⟩
    rw [instSeq_bvar_full hidxK hzslen,
      List.getElem?_take_of_lt hqm]
    exact (hmixzs q (by omega)).2
  have hvMid' : denote cval env ψ' (rP + cnF)
      (Expr.forallE nmJ domJ bodyJ mbJ) = some (.pi vDomK vBodyK) := by
    rw [denote_forallE, hvd, hvb]
  have hcross := instPisAt_denote_cross hcl _ htr (D := rP + cnF)
    (vals := zs) hzslen
    (fun q x hx => ((hspFacts q x (hspTake q x hx).1).2))
    hfbCty hCbR hTVjK hvMid'
    (ws := mix.take (cnP + j))
    (by rw [List.length_take, List.length_take, hmixlen, hsplen])
    hwsCond htow
  -- split the crossed pis and read the domains apart
  obtain ⟨Anext, Bnext, rfl, hAnext⟩ : ∃ A B, mid' = .pi A B ∧
      A = Γj.getD (cnP + cnF - 1 - (cnP + j)) default := by
    have hcnt : cnP + cnF - (cnP + j) = (cnF - j - 1) + 1 := by omega
    rw [hcnt] at hpost
    generalize hg : List.take (cnF - j - 1 + 1) Γj = Γt at hpost
    cases hpost with
    | @cons _ A B _ Γ'' htl =>
      refine ⟨A, B, rfl, ?_⟩
      have h1 : (Γ'' ++ [A]).getD Γ''.length default = A := by
        rw [List.getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self]
        rfl
      have hΓ''len : Γ''.length = cnF - j - 1 := htl.length
      have h2 : (List.take (cnF - j - 1 + 1) Γj).getD
          (cnF - j - 1) default = Γj.getD (cnF - j - 1) default := by
        rw [List.getD, List.getD,
          List.getElem?_take_of_lt (by omega)]
      rw [show cnP + cnF - 1 - (cnP + j) = cnF - j - 1 from by omega,
        ← h2, hg, ← hΓ''len, h1]
  rw [VExpr.instSeq_pi _ _ _ _ (by rw [hzslen]; omega),
    VExpr.instSeq_pi _ _ _ _ (by
      rw [List.length_take, hmixlen]
      omega)] at hcross
  have hdomEq : VExpr.instSeq zs (rP + cnF - 1) vDomK
      = VExpr.instSeq (mix.take (cnP + j)) (cnP + j - 1) Anext := by
    injection hcross with h1 h2
    rw [show (List.take (cnP + j) mix).length = cnP + j from by
      rw [List.length_take, hmixlen]
      omega] at h1
    exact h1
  have h2 : (zs.take (rP + j)).length = rP + j := by
    rw [List.length_take, hzslen]
    omega
  have habs : VExpr.instSeq zs (rP + cnF - 1)
      (VExpr.liftN (rP + cnF - (rP + j)) vdomLow)
      = VExpr.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow :=
    instSeq_absorb_left hzslen (by omega)
  calc VExpr.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow
      = VExpr.instSeq zs (rP + cnF - 1)
          (VExpr.liftN (rP + cnF - (rP + j)) vdomLow) := habs.symm
    _ = VExpr.instSeq zs (rP + cnF - 1) vDomK := by rw [← hVK]
    _ = VExpr.instSeq (mix.take (cnP + j)) (cnP + j - 1) Anext :=
        hdomEq
    _ = VExpr.instSeq (mix.take (cnP + j)) (cnP + j - 1)
          (Γj.getD (cnP + cnF - 1 - (cnP + j)) default) := by
        rw [← hAnext]


set_option maxHeartbeats 3200000 in
/-- **The zipper**: the fired statement spine `xs.take rP ++ ys.drop
cnP` satisfies and fits the checked statement's telescope.  The [set]
`zipperStage` + `paramBridge` + mixed-fit stage in one construction:
a strong induction building the chain memberships, each step firing
the corresponding domain walk at the padded context
(`sat_pad_of_mems`), the prefix steps converting the recursor fit
through the renamed-domain identification, the field steps through
the crossed constructor domain (`zipFieldTermEq`). -/
theorem zipperS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    {f : Name → Name}
    {rP cnP cnF mI : Nat} {xs ys : List VExpr} {ρ : Nat → V}
    (hrPmI : rP ≤ mI) (hplainLe : cnP ≤ rP)
    (hlenX : xs.length = mI) (hlenY : ys.length = cnP + cnF)
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hbFvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {Tstmt : VExpr} {Γs : List VExpr} {Rbody : VExpr}
    (htowerS : PiTele (rP + cnF) Tstmt Γs Rbody)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (_hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    {TV : VExpr} {ΓP : List VExpr} {RP : VExpr}
    (htowerP : PiTele rP TV ΓP RP)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    {tyAR : Expr} (htyRw : tyAR.hasFvar = false)
    (_htyRb : tyAR.looseBVarsBounded 0 = true)
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    (hrenP : ∀ n, n < rP →
      RenEqT f ((fvsP.map Expr.fvarTypeD).getD n default)
        (rdoms.getD n default))
    (hroT : RenameOkT cval env f)
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : VExpr}
    (hTVjK : denote cval env ψ' (rP + cnF) ctyR = some TVj)
    (hTVjcl : VExpr.Closed TVj)
    {Γj : List VExpr} {Rj : VExpr}
    (htowerJ : PiTele (cnP + cnF) TVj Γj Rj)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP) ctyR
      = some (cdoms, cres))
    {restRpre restC : VExpr}
    (hfitRpre : TeleFitV V ρ TV (xs.take rP) restRpre)
    (hfitC : TeleFitV V ρ TVj ys restC)
    (hpar : ∀ i, i < cnP →
      interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default))
    (hdePre : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP)) :
    Sat V Γs (chainE V ρ (xs.take rP ++ ys.drop cnP)) ∧
    TeleFitV V ρ Tstmt (xs.take rP ++ ys.drop cnP)
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        Rbody) := by
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hΓjlen : Γj.length = cnP + cnF := htowerJ.length
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hlenX,
      hlenY]
    omega
  -- zs element access
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left (by rw [hxtlen]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right (by rw [hxtlen]; omega),
      hxtlen, List.getElem?_drop,
      show rP + j - rP = j from by omega,
      show cnP + j = cnP + j from rfl]
    rfl
  have hmixGet : ∀ q, q < cnP + cnF → q < (xs.take cnP ++ ys.drop cnP).length ∧
      (xs.take cnP ++ ys.drop cnP)[q]? = some
        ((xs.take rP ++ ys.drop cnP).getD
          (if q < cnP then q else rP + (q - cnP)) default) := by
    intro q hq
    refine ⟨by omega, ?_⟩
    by_cases hqc : q < cnP
    · rw [if_pos hqc, List.getElem?_append_left
        (by rw [List.length_take, hlenX]; omega),
        List.getElem?_take_of_lt hqc, hzsPre q (by omega)]
      rw [List.getD]
      rcases hx : xs[q]? with _ | v
      · rw [List.getElem?_eq_none_iff] at hx
        omega
      · rfl
    · rw [if_neg hqc, List.getElem?_append_right
        (by rw [List.length_take, hlenX]; omega),
        hzsFld (q - cnP) (by omega),
        show cnP + (q - cnP) = q from by omega]
      rw [List.length_take, hlenX,
        show min cnP mI = cnP from by omega, List.getElem?_drop,
        show cnP + (q - cnP) = q from by omega]
      rw [List.getD]
      rcases hy : ys[q]? with _ | v
      · rw [List.getElem?_eq_none_iff] at hy
        omega
      · rfl
  -- the mixed chain memberships (the [set] mixed fit, in chain form)
  have hchainC := teleFitV_to_chain (cnP + cnF) htowerJ hlenY hfitC
  have hchainEnvEq : ∀ q, q ≤ cnP + cnF →
      chainE V ρ ((xs.take cnP ++ ys.drop cnP).take q)
        = chainE V ρ (ys.take q) := by
    intro q hq
    funext i
    have htq : ((xs.take cnP ++ ys.drop cnP).take q).length = q := by
      rw [List.length_take, hmixlen]
      omega
    have htq' : (ys.take q).length = q := by
      rw [List.length_take, hlenY]
      omega
    by_cases hiq : i < q
    · rw [chainE_lt (by omega), chainE_lt (by omega), htq, htq']
      have hlt : q - 1 - i < q := by omega
      rw [show ((xs.take cnP ++ ys.drop cnP).take q).getD (q - 1 - i)
            default
          = (xs.take cnP ++ ys.drop cnP).getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt],
        show (ys.take q).getD (q - 1 - i) default
          = ys.getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt]]
      have h1 := (hmixGet (q - 1 - i) (by omega)).2
      rw [List.getD, h1]
      by_cases hc : q - 1 - i < cnP
      · rw [if_pos hc]
        show interp V ρ ((xs.take rP ++ ys.drop cnP).getD (q - 1 - i)
          default) = _
        rw [hzsPre _ (by omega)]
        exact (hpar _ hc).symm
      · rw [if_neg hc]
        show interp V ρ ((xs.take rP ++ ys.drop cnP).getD
          (rP + (q - 1 - i - cnP)) default) = _
        rw [hzsFld _ (by omega),
          show cnP + (q - 1 - i - cnP) = q - 1 - i from by omega]
    · rw [chainE_ge (by omega), chainE_ge (by omega), htq, htq']
  have hmixMem : ∀ q, q < cnP + cnF →
      interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        ∈ˢ interp V (chainE V ρ ((xs.take cnP ++ ys.drop cnP).take q))
          (Γj.getD (cnP + cnF - 1 - q) default) := by
    intro q hq
    have h1 := hchainC q hq
    rw [hchainEnvEq q (by omega)]
    have hval : interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
      have h2 := (hmixGet q hq).2
      rw [List.getD, h2]
      by_cases hqc : q < cnP
      · rw [if_pos hqc]
        show interp V ρ ((xs.take rP ++ ys.drop cnP).getD q default) = _
        rw [hzsPre q (by omega)]
        exact (hpar q hqc).symm
      · rw [if_neg hqc]
        show interp V ρ ((xs.take rP ++ ys.drop cnP).getD
          (rP + (q - cnP)) default) = _
        rw [hzsFld (q - cnP) (by omega),
          show cnP + (q - cnP) = q from by omega]
    rw [hval]
    exact h1
  -- the prefix chain memberships
  have hchainP := teleFitV_to_chain rP htowerP hxtlen hfitRpre
  -- the frame entries, `As`-form
  have hAs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some ((fun i => Γs.getD (rP + cnF - 1 - i) default) i) :=
    hdomsS0
  -- the strong induction on the fitted prefix
  have hall : ∀ n, n ≤ rP + cnF → ∀ m, m < n →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD m default)
        ∈ˢ interp V (chainE V ρ ((xs.take rP ++ ys.drop cnP).take m))
          (Γs.getD (rP + cnF - 1 - m) default) := by
    intro n
    induction n with
    | zero => intro _ m hm; exact nomatch hm
    | succ n ihn =>
      intro hn m hm
      rcases Nat.lt_or_ge m n with hmn | hmn
      · exact ihn (by omega) m hmn
      · obtain rfl : n = m := by omega
        -- the padded satisfaction from the memberships so far
        have hsat := sat_pad_of_mems htowerS hzslen
          (n := n) (by omega) (fun m' hm' => ihn (by omega) m' hm')
        have hent : ∀ i, i < n →
            (List.replicate (rP + cnF - n) (VExpr.sort 0)
              ++ Γs.drop (rP + cnF - n))[rP + cnF - 1 - i]?
              = some ((fun i => Γs.getD (rP + cnF - 1 - i) default) i) := by
          intro i hi
          rw [List.getElem?_append_right
            (by rw [List.length_replicate]; omega),
            List.length_replicate, List.getElem?_drop,
            show rP + cnF - n + (rP + cnF - 1 - i - (rP + cnF - n))
              = rP + cnF - 1 - i from by omega]
          show Γs[rP + cnF - 1 - i]?
            = some (Γs.getD (rP + cnF - 1 - i) default)
          rw [List.getD]
          rcases hg : Γs[rP + cnF - 1 - i]? with _ | A
          · rw [List.getElem?_eq_none_iff] at hg
            omega
          · rfl
        have htklen : (((xs.take rP ++ ys.drop cnP)).take n).length
            = n := by
          rw [List.length_take, hzslen]
          omega
        rcases Nat.lt_or_ge n rP with hnrP | hnrP
        · -- prefix step
          have hfvsn : ∃ x, fvs[n]? = some x := by
            rcases hx : fvs[n]? with _ | x
            · rw [List.getElem?_eq_none_iff] at hx
              omega
            · exact ⟨x, rfl⟩
          obtain ⟨x, hx⟩ := hfvsn
          obtain ⟨nm, ty, rfl⟩ := hshapeS n x hx
          -- the walk element
          obtain ⟨hwlen, hwget⟩ := Forall2.length_getD hdePre
          have hde_n := hwget n default default (by
            rw [List.length_map, List.length_take, hfvslen]
            omega)
          rw [show ((fvs.take rP).map Expr.fvarTypeD).getD n default
              = Expr.fvarTypeD (Expr.fvar n nm ty) from by
            rw [List.getD, List.getElem?_map,
              List.getElem?_take_of_lt hnrP, hx]
            rfl] at hde_n
          -- the prefix-side identification
          have hfvsPn : ∃ xP, fvsP[n]? = some xP := by
            rcases hxP : fvsP[n]? with _ | xP
            · rw [List.getElem?_eq_none_iff] at hxP
              omega
            · exact ⟨xP, rfl⟩
          obtain ⟨xP, hxP⟩ := hfvsPn
          obtain ⟨nmP, tyP, rfl⟩ := hshapeP n xP hxP
          have hrdden : denote cval env ψ' n (rdoms.getD n default)
              = some (ΓP.getD (rP - 1 - n) default) := by
            have h1 := (hrenP n hnrP).denote (φ := ψ') hroT n
            rw [show (fvsP.map Expr.fvarTypeD).getD n default
                = Expr.fvarTypeD (Expr.fvar n nmP tyP) from by
              rw [List.getD, List.getElem?_map, hxP]
              rfl] at h1
            rw [h1]
            exact hdomsP0 n _ hxP
          -- scoping of the two subjects
          have hwsTy : Expr.WScoped n ty := by
            have h' := hwsFvs _ (List.mem_of_getElem? hx)
            simp only [Expr.WScoped] at h'
            exact h'.2
          have hwsRd : Expr.WScoped n (rdoms.getD n default) := by
            have h1 := instPisAt_index_WScoped (fvs.take rP)
              (d := 0) hrinst
              (Expr.WScoped.of_not_hasFvar htyRw) ?_ n
              (rdoms.getD n default) ?_
            · simpa using h1
            · intro i a ha
              have hi : i < rP := by
                rcases Nat.lt_or_ge i rP with h' | h'
                · exact h'
                · rw [List.getElem?_eq_none
                    (by rw [List.length_take]; omega)] at ha
                  exact nomatch ha
              rw [List.getElem?_take_of_lt hi] at ha
              obtain ⟨nm', ty', rfl⟩ := hshapeS i a ha
              have h'' := hwsFvs _ (List.mem_of_getElem? ha)
              simp only [Expr.WScoped] at h'' ⊢
              exact ⟨by omega, h''.2⟩
            · have hlt : n < rdoms.length := by
                have := instPisAt_length _ hrinst
                rw [List.length_take] at this
                omega
              rw [List.getD]
              rcases hr : rdoms[n]? with _ | r
              · rw [List.getElem?_eq_none_iff] at hr
                omega
              · rfl
          -- leaves of the two subjects
          have hleafTy : ∀ l ∈ ty.fvarLeaves,
              Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
            intro l hl
            refine hleafClosed l ⟨_, List.mem_of_getElem? hx, ?_⟩
            rw [Expr.fvarLeaves]
            exact List.mem_cons_of_mem _ hl
          have hleafRd : ∀ l ∈ (rdoms.getD n default).fvarLeaves,
              Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
            intro l hl
            have hmem : rdoms.getD n default ∈ rdoms := by
              have hlt : n < rdoms.length := by
                have := instPisAt_length _ hrinst
                rw [List.length_take] at this
                omega
              rw [List.getD]
              rcases hr : rdoms[n]? with _ | r
              · rw [List.getElem?_eq_none_iff] at hr
                omega
              · exact List.mem_of_getElem? hr
            rcases instPisAt_leaves _ hrinst l
              (Or.inl ⟨_, hmem, hl⟩) with hty' | ⟨a, ha, hla⟩
            · exfalso
              rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyRw] at hty'
              exact nomatch hty'
            · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
              have hqrP : q < rP := by
                rcases Nat.lt_or_ge q rP with h' | h'
                · exact h'
                · rw [List.getElem?_eq_none
                    (by rw [List.length_take]; omega)] at hq
                  exact nomatch hq
              rw [List.getElem?_take_of_lt hqrP] at hq
              obtain ⟨nm', ty', rfl⟩ := hshapeS q _ hq
              rw [Expr.fvarLeaves] at hla
              rcases List.mem_cons.mp hla with rfl | hla'
              · exact List.mem_of_getElem? hq
              · refine hleafClosed l ⟨_, List.mem_of_getElem? hq, ?_⟩
                rw [Expr.fvarLeaves]
                exact List.mem_cons_of_mem _ hla'
          -- fire the walk at the padded context
          obtain ⟨Av, Bv, hAv, hBv, heq⟩ := openWalk_eqS henv
            (k := rP + cnF) (fvs := fvs)
            (As := fun i => Γs.getD (rP + cnF - 1 - i) default)
            (by rw [List.length_append, List.length_replicate,
                List.length_drop, hΓslen]; omega)
            hshapeS hwsFvs hAs (n := n) hent hde_n
            hleafTy (Expr.fvarLeaves_lt_of_wscoped hwsTy)
            hleafRd (Expr.fvarLeaves_lt_of_wscoped hwsRd) hsat
          -- identify the denotations
          have hAv' : Av = VExpr.liftN (rP + cnF - n)
              (Γs.getD (rP + cnF - 1 - n) default) := by
            have hd := denote_lift (cval := cval) (env := env)
              (φ := ψ') henv.cval_closed (p := n) (e := ty)
              (Expr.WScoped.fvarsBelow hwsTy) (rP + cnF) (by omega)
            have h0 := hdomsS0 n _ hx
            rw [show Expr.fvarTypeD (Expr.fvar n nm ty) = ty from rfl]
              at h0
            rw [h0] at hd
            rw [show Expr.fvarTypeD (Expr.fvar n nm ty) = ty from rfl]
              at hAv
            rw [hd] at hAv
            exact (Option.some.inj hAv).symm
          have hBv' : Bv = VExpr.liftN (rP + cnF - n)
              (ΓP.getD (rP - 1 - n) default) := by
            have hd := denote_lift (cval := cval) (env := env)
              (φ := ψ') henv.cval_closed (p := n)
              (e := rdoms.getD n default)
              (Expr.WScoped.fvarsBelow hwsRd) (rP + cnF) (by omega)
            rw [hrdden] at hd
            rw [hd] at hBv
            exact (Option.some.inj hBv).symm
          rw [hAv', hBv'] at heq
          rw [interp_liftN, interp_liftN, padE_shiftE] at heq
          -- combine with the prefix fit's membership
          have h1 := hchainP n hnrP
          rw [show (xs.take rP).take n
              = (xs.take rP ++ ys.drop cnP).take n from by
            rw [List.take_append_of_le_length (by omega)],
            show ΓP.getD (rP - 1 - n) default
              = ΓP.getD (rP - 1 - n) default from rfl] at h1
          rw [hzsPre n hnrP]
          rw [show (xs.take rP).getD n default = xs.getD n default from by
              rw [List.getD, List.getD, List.getElem?_take_of_lt hnrP]]
            at h1
          rw [← heq] at h1
          exact h1
        · -- field step
          obtain ⟨hfbDom, hleafDom, vdomLow, hvdlow, hterm⟩ :=
            zipFieldTermEq henv.cval_closed hfvslen hshapeS hwsFvs
              hbFvs hleafClosed hplainLe hCwR hCbR hTVjK hTVjcl
              htowerJ hcinst hzslen hmixlen hmixGet
              (j := n - rP) (by omega)
          have hfvsn : ∃ x, fvs[n]? = some x := by
            rcases hx : fvs[n]? with _ | x
            · rw [List.getElem?_eq_none_iff] at hx
              omega
            · exact ⟨x, rfl⟩
          obtain ⟨x, hx⟩ := hfvsn
          obtain ⟨nm, ty, rfl⟩ := hshapeS n x hx
          obtain ⟨hwlen, hwget⟩ := Forall2.length_getD hdeFld
          have hde_n := hwget (n - rP) default default (by
            rw [List.length_map, List.length_drop, hfvslen]
            omega)
          rw [show ((fvs.drop rP).map Expr.fvarTypeD).getD (n - rP)
                default
              = Expr.fvarTypeD (Expr.fvar n nm ty) from by
            rw [List.getD, List.getElem?_map, List.getElem?_drop,
              show rP + (n - rP) = n from by omega, hx]
            rfl,
            show (cdoms.drop cnP).getD (n - rP) default
              = cdoms.getD (cnP + (n - rP)) default from by
            rw [List.getD, List.getD, List.getElem?_drop]] at hde_n
          have hwsTy : Expr.WScoped n ty := by
            have h' := hwsFvs _ (List.mem_of_getElem? hx)
            simp only [Expr.WScoped] at h'
            exact h'.2
          have hleafTy : ∀ l ∈ ty.fvarLeaves,
              Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
            intro l hl
            refine hleafClosed l ⟨_, List.mem_of_getElem? hx, ?_⟩
            rw [Expr.fvarLeaves]
            exact List.mem_cons_of_mem _ hl
          have hnEq : rP + (n - rP) = n := by omega
          rw [hnEq] at hleafDom
          obtain ⟨Av, Bv, hAv, hBv, heq⟩ := openWalk_eqS henv
            (k := rP + cnF) (fvs := fvs)
            (As := fun i => Γs.getD (rP + cnF - 1 - i) default)
            (by rw [List.length_append, List.length_replicate,
                List.length_drop, hΓslen]; omega)
            hshapeS hwsFvs hAs (n := n) hent hde_n
            hleafTy (Expr.fvarLeaves_lt_of_wscoped hwsTy)
            (fun l hl => (hleafDom l hl).1)
            (fun l hl => (hleafDom l hl).2) hsat
          have hAv' : Av = VExpr.liftN (rP + cnF - n)
              (Γs.getD (rP + cnF - 1 - n) default) := by
            have hd := denote_lift (cval := cval) (env := env)
              (φ := ψ') henv.cval_closed (p := n) (e := ty)
              (Expr.WScoped.fvarsBelow hwsTy) (rP + cnF) (by omega)
            have h0 := hdomsS0 n _ hx
            rw [show Expr.fvarTypeD (Expr.fvar n nm ty) = ty from rfl]
              at h0
            rw [h0] at hd
            rw [show Expr.fvarTypeD (Expr.fvar n nm ty) = ty from rfl]
              at hAv
            rw [hd] at hAv
            exact (Option.some.inj hAv).symm
          have hBv' : Bv = VExpr.liftN (rP + cnF - n) vdomLow := by
            have hd := denote_lift (cval := cval) (env := env)
              (φ := ψ') henv.cval_closed (p := n)
              (e := cdoms.getD (cnP + (n - rP)) default)
              (by
                rw [show rP + (n - rP) = n from by omega] at hfbDom
                exact hfbDom)
              (rP + cnF) (by omega)
            rw [show rP + (n - rP) = n from by omega] at hvdlow
            rw [hvdlow] at hd
            rw [hd] at hBv
            exact (Option.some.inj hBv).symm
          rw [hAv', hBv'] at heq
          rw [interp_liftN, interp_liftN, padE_shiftE] at heq
          -- the fire-side membership, crossed to the statement chain
          have h1 := hmixMem (cnP + (n - rP)) (by omega)
          rw [show cnP + cnF - 1 - (cnP + (n - rP))
              = cnP + cnF - 1 - (cnP + (n - rP)) from rfl] at h1
          -- to instSeq form and across the term identity
          have htake1 : ((xs.take cnP ++ ys.drop cnP).take
              (cnP + (n - rP))).length = cnP + (n - rP) := by
            rw [List.length_take, hmixlen]
            omega
          rw [show interp V
              (chainE V ρ ((xs.take cnP ++ ys.drop cnP).take
                (cnP + (n - rP))))
              (Γj.getD (cnP + cnF - 1 - (cnP + (n - rP))) default)
            = interp V ρ (VExpr.instSeq
                ((xs.take cnP ++ ys.drop cnP).take (cnP + (n - rP)))
                (cnP + (n - rP) - 1)
                (Γj.getD (cnP + cnF - 1 - (cnP + (n - rP))) default))
            from by
              rw [← interp_instSeq, htake1]] at h1
          rw [show rP + (n - rP) = n from by omega] at hterm
          rw [← hterm] at h1
          have htake2 : ((xs.take rP ++ ys.drop cnP).take n).length
              = n := by
            rw [List.length_take, hzslen]
            omega
          rw [show interp V ρ (VExpr.instSeq
              ((xs.take rP ++ ys.drop cnP).take n) (n - 1) vdomLow)
            = interp V (chainE V ρ ((xs.take rP ++ ys.drop cnP).take n))
                vdomLow from by
              rw [← interp_instSeq, htake2]] at h1
          have hval : interp V ρ
              ((xs.take cnP ++ ys.drop cnP).getD (cnP + (n - rP))
                default)
              = interp V ρ ((xs.take rP ++ ys.drop cnP).getD n
                default) := by
            have h2 := (hmixGet (cnP + (n - rP)) (by omega)).2
            rw [List.getD, h2,
              if_neg (show ¬ cnP + (n - rP) < cnP from by omega),
              show rP + (cnP + (n - rP) - cnP) = n from by omega]
            rfl
          rw [hval] at h1
          rw [← heq] at h1
          exact h1
  have hallK := hall (rP + cnF) (Nat.le_refl _)
  exact ⟨sat_of_tower htowerS hzslen hallK,
    teleFitV_of_tower (rP + cnF) htowerS hzslen hallK⟩



/-- The chain memberships, read back off the constructed satisfaction
(the inverse of `sat_of_tower`, in `consChain` form — what the
truthfulness descent consumes). -/
theorem sat_chain_mems {k : Nat} {T : VExpr} {Γ : List VExpr}
    {R : VExpr} (htower : PiTele k T Γ R) {ws : List VExpr}
    {ρ : Nat → V} (hlen : ws.length = k)
    (hsat : Sat V Γ (chainE V ρ ws)) :
    ∀ n, n < k →
      (ws.map (interp V ρ)).getD n SetTheory.empty
        ∈ˢ interp V (consChain V ρ ((ws.map (interp V ρ)).take n))
          (Γ.getD (k - 1 - n) default) := by
  intro n hn
  have hΓlen : Γ.length = k := htower.length
  have hval : (ws.map (interp V ρ)).getD n SetTheory.empty
      = interp V ρ (ws.getD n default) := by
    rw [List.getD, List.getD, List.getElem?_map]
    rcases hx : ws[n]? with _ | w
    · rw [List.getElem?_eq_none_iff] at hx
      omega
    · rfl
  have henv : consChain V ρ ((ws.map (interp V ρ)).take n)
      = chainE V ρ (ws.take n) := by
    rw [← List.map_take, consChain_map_interp]
  have hg : Γ[k - 1 - n]? = some (Γ.getD (k - 1 - n) default) := by
    rw [List.getD]
    rcases hA : Γ[k - 1 - n]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hA
      omega
    · rfl
  have h1 := hsat (k - 1 - n) _ hg
  rw [chainE_lt (by omega),
    show ws.length - 1 - (k - 1 - n) = n from by omega] at h1
  rw [show (fun j => chainE V ρ ws (j + (k - 1 - n) + 1))
      = chainE V ρ (ws.take (ws.length - 1 - (k - 1 - n))) from
      chainE_tail (by omega),
    show ws.length - 1 - (k - 1 - n) = n from by omega] at h1
  rw [hval, henv]
  exact h1

set_option maxHeartbeats 3200000 in
/-- **The firing stage**: the checked equation, fired at the zipped
chain — the theorem's inhabitant applied along the fit lands in the
interpreted `Eq`-spine, the spine computes to the truth set through
`eq_lawV` (its domain memberships from the sides pack and from graph
rigidity of the pinned `Eq` former against the statement's own
truthfulness), and `mem_eqv` reads the equation off. -/
theorem fireS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    (heqlaw : EqLawV V env cval)
    (heqfE : env.find? eqName = some eqA)
    {rP cnF : Nat} {fvs : List Expr}
    (_hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    {Tstmt : VExpr} {Γs : List VExpr} {Rbody : VExpr}
    (htowerS : PiTele (rP + cnF) Tstmt Γs Rbody)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    (hstmtAnnot : ∀ ρ0 : Nat → V, AnnotOkV V ρ0 Tstmt)
    (hstmtInhab : ∀ ρ0 : Nat → V, ∃ pv : V, pv ∈ˢ interp V ρ0 Tstmt)
    {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (hRbody : denote cval env ψ' (rP + cnF) tbody = some Rbody)
    (htbody : tbody = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS])
    (hsidesTy : IotaSidesTyR μ env cval ψ' (rP + cnF) αS lhsS rhsS)
    (hleafα : ∀ l ∈ αS.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltα : ∀ l ∈ αS.fvarLeaves, l.1 < rP + cnF)
    (hleafL : ∀ l ∈ lhsS.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltL : ∀ l ∈ lhsS.fvarLeaves, l.1 < rP + cnF)
    (hleafR : ∀ l ∈ rhsS.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltR : ∀ l ∈ rhsS.fvarLeaves, l.1 < rP + cnF)
    {zs : List VExpr} {ρ : Nat → V} (hzslen : zs.length = rP + cnF)
    (hsat : Sat V Γs (chainE V ρ zs))
    (hfit : TeleFitV V ρ Tstmt zs
      (VExpr.instSeq zs (rP + cnF - 1) Rbody)) :
    ∃ vα vL vR,
      denote cval env ψ' (rP + cnF) αS = some vα ∧
      denote cval env ψ' (rP + cnF) lhsS = some vL ∧
      denote cval env ψ' (rP + cnF) rhsS = some vR ∧
      interp V (chainE V ρ zs) vL = interp V (chainE V ρ zs) vR := by
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  -- read the equation spine apart
  rw [htbody] at hRbody
  obtain ⟨vEq, vs3, hvEq, hsp3, rfl⟩ := denote_mkAppN_inv hRbody
  obtain ⟨vα, vL, vR, rfl, hvα, hvL, hvR⟩ : ∃ vα vL vR,
      vs3 = [vα, vL, vR] ∧
      denote cval env ψ' (rP + cnF) αS = some vα ∧
      denote cval env ψ' (rP + cnF) lhsS = some vL ∧
      denote cval env ψ' (rP + cnF) rhsS = some vR := by
    cases hsp3 with
    | cons hα htail =>
      cases htail with
      | cons hL htail2 =>
        cases htail2 with
        | cons hR htail3 =>
          cases htail3 with
          | nil => exact ⟨_, _, _, rfl, hα, hL, hR⟩
  -- the head is the stored `Eq`'s valuation
  have hvEq' : vEq = cval eqName
      (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]) := by
    rw [denote_const, heqfE] at hvEq
    dsimp only at hvEq
    rw [if_pos (show ([ℓA] : List Level).length
        = eqA.toConstantVal.levelParams.length from rfl)] at hvEq
    exact (Option.some.inj hvEq).symm
  -- the `Eq` law at the instantiation
  obtain ⟨hnept, hlaw⟩ := heqlaw heqfE
    (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA])
  -- the sides' membership facts at the full context
  obtain ⟨Av0, Lv0, Rv0, hAv0, hLv0, hRv0, hpacks⟩ := hsidesTy
  obtain rfl : vα = Av0 := by
    rw [hvα] at hAv0
    exact Option.some.inj hAv0
  obtain rfl : vL = Lv0 := by
    rw [hvL] at hLv0
    exact Option.some.inj hLv0
  obtain rfl : vR = Rv0 := by
    rw [hvR] at hRv0
    exact Option.some.inj hRv0
  have hent : ∀ i, i < rP + cnF →
      Γs[rP + cnF - 1 - i]?
        = some ((fun i => Γs.getD (rP + cnF - 1 - i) default) i) := by
    intro i hi
    show Γs[rP + cnF - 1 - i]?
      = some (Γs.getD (rP + cnF - 1 - i) default)
    rw [List.getD]
    rcases hg : Γs[rP + cnF - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg
      omega
    · rfl
  have hctxα := ctxOkR_of_openers (μ := μ) henv.cval_closed hΓslen
    hshapeS hwsFvs hdomsS0 hleafα hltα hent
  have hctxL := ctxOkR_of_openers (μ := μ) henv.cval_closed hΓslen
    hshapeS hwsFvs hdomsS0 hleafL hltL hent
  have hctxR := ctxOkR_of_openers (μ := μ) henv.cval_closed hΓslen
    hshapeS hwsFvs hdomsS0 hleafR hltR hent
  obtain ⟨⟨tl, hInfL, hDeqL⟩, ⟨tr, hInfR, hDeqR⟩⟩ :=
    hpacks Γs hctxα hctxL hctxR
  have hLmem : interp V (chainE V ρ zs) vL
      ∈ˢ interp V (chainE V ρ zs) vα := by
    have h1 := (Infer.sound henv hInfL (chainE V ρ zs) hsat).2
    have h2 := DefEq.sound henv hDeqL (chainE V ρ zs) hsat
    rw [h2] at h1
    exact h1
  have hRmem : interp V (chainE V ρ zs) vR
      ∈ˢ interp V (chainE V ρ zs) vα := by
    have h1 := (Infer.sound henv hInfR (chainE V ρ zs) hsat).2
    have h2 := DefEq.sound henv hDeqR (chainE V ρ zs) hsat
    rw [h2] at h1
    exact h1
  -- the slot's universe membership, by graph rigidity
  have hdescend := annotOkV_descend (rP + cnF) htowerS ρ
    (zs.map (interp V ρ)) (by rw [List.length_map, hzslen])
    (hstmtAnnot ρ) (sat_chain_mems htowerS hzslen hsat)
  rw [consChain_map_interp] at hdescend
  have hαuniv : interp V (chainE V ρ zs) vα
      ∈ˢ univ ((Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA])
        uN) := by
    rw [show VExpr.mkAppN vEq [vα, vL, vR]
        = .app (.app (.app vEq vα) vL) vR from rfl] at hdescend
    rw [AnnotOkV_app] at hdescend
    have h1 := hdescend.1
    rw [AnnotOkV_app] at h1
    have h2 := h1.1
    rw [AnnotOkV_app] at h2
    obtain ⟨-, -, A, B, hEqIn, hαIn⟩ := h2
    -- the pinned `Eq` type, instantiated and denoted
    have hinst : eqA.toConstantVal.type.instantiateLevelParams
        eqA.toConstantVal.levelParams [ℓA]
        = .forallE (.str .anonymous "α") (.sort ℓA)
            (.forallE (.str .anonymous "a") (.bvar 0)
              (.forallE (.str .anonymous "b") (.bvar 1)
                (.sort .zero) ⟨.default⟩) ⟨.default⟩) ⟨.implicit⟩ := by
      rfl
    have hb1 : (Expr.forallE (.str .anonymous "a") (.bvar 0)
        (.forallE (.str .anonymous "b") (.bvar 1)
          (.sort .zero) ⟨.default⟩) ⟨.default⟩).instantiate1
        (.fvar 0 (.str .anonymous "α") (.sort ℓA))
        = .forallE (.str .anonymous "a")
            (.fvar 0 (.str .anonymous "α") (.sort ℓA))
            (.forallE (.str .anonymous "b")
              (.fvar 0 (.str .anonymous "α") (.sort ℓA))
              (.sort .zero) ⟨.default⟩) ⟨.default⟩ := by
      rfl
    have hb2 : (Expr.forallE (.str .anonymous "b")
        (.fvar 0 (.str .anonymous "α") (.sort ℓA))
        (.sort .zero) ⟨.default⟩).instantiate1
        (.fvar 1 (.str .anonymous "a")
          (.fvar 0 (.str .anonymous "α") (.sort ℓA)))
        = .forallE (.str .anonymous "b")
            (.fvar 0 (.str .anonymous "α") (.sort ℓA))
            (.sort .zero) ⟨.default⟩ := by
      rfl
    have hb3 : (Expr.sort .zero).instantiate1
        (.fvar 2 (.str .anonymous "b")
          (.fvar 0 (.str .anonymous "α") (.sort ℓA))) = .sort .zero := by
      rfl
    have hTden : denoteClosed cval env ψ'
        (eqA.toConstantVal.type.instantiateLevelParams
          eqA.toConstantVal.levelParams [ℓA])
        = some (.pi (.sort (ℓA.eval ψ'))
            (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := by
      show denote cval env ψ' 0 _ = _
      rw [hinst, denote_forallE, denote_sort, hb1, denote_forallE,
        denote_fvar, hb2, denote_forallE, denote_fvar, hb3,
        denote_sort]
      rfl
    have hmem := henv.mem_type eqName eqA heqfE [ℓA] (by rfl)
      _ hTden (chainE V ρ zs)
    have hEqIn2 : interp V (chainE V ρ zs) vEq
        ∈ˢ piC (univ (ℓA.eval ψ'))
          (fun x => interp V (cons V x (chainE V ρ zs))
            (VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := by
      have h3 := hmem.1
      rw [interp_pi, interp_sort] at h3
      rw [hvEq']
      exact h3
    have hne : interp V (chainE V ρ zs) vEq ≠ pt := by
      rw [hvEq']
      exact hnept (chainE V ρ zs)
    have hAeq : A = univ (ℓA.eval ψ') :=
      piC_dom_unique hEqIn hEqIn2 hne
    rw [hAeq] at hαIn
    rw [show (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]) uN
        = ℓA.eval ψ' from rfl]
    exact hαIn
  -- fire the theorem's inhabitant along the fit
  obtain ⟨pv, hpv⟩ := hstmtInhab ρ
  have happ := hfit.appN_val hpv
  -- the residual computes to the interpreted equation spine
  have hEqcl : VExpr.Closed vEq := by
    rw [hvEq']
    exact henv.cval_closed _ _
  have hresid : interp V ρ
      (VExpr.instSeq zs (rP + cnF - 1) (VExpr.mkAppN vEq [vα, vL, vR]))
      = eqv (interp V (chainE V ρ zs) vL)
        (interp V (chainE V ρ zs) vR) := by
    rw [show rP + cnF - 1 = zs.length - 1 from by rw [hzslen],
      VExpr.instSeq_mkAppN,
      VExpr.instSeq_eq_self_of_closed hEqcl]
    have hlist : [vα, vL, vR].map (VExpr.instSeq zs (zs.length - 1))
        = [VExpr.instSeq zs (zs.length - 1) vα,
           VExpr.instSeq zs (zs.length - 1) vL,
           VExpr.instSeq zs (zs.length - 1) vR] := rfl
    rw [hlist, hvEq']
    rw [hlaw ρ _ _ _ ?_ ?_ ?_]
    · rw [interp_instSeq, interp_instSeq]
    · rw [interp_instSeq]
      rw [show (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]) uN
          = ℓA.eval ψ' from rfl]
      exact hαuniv
    · rw [interp_instSeq, interp_instSeq]
      exact hLmem
    · rw [interp_instSeq, interp_instSeq]
      exact hRmem
  rw [hresid] at happ
  exact ⟨vα, vL, vR, hvα, hvL, hvR, mem_eqv happ⟩




/-- Pointwise reading of a denoted spine. -/
theorem denoteSpine_getElem?' {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List VExpr},
      DenoteSpine cval env φ d as vs →
      ∀ (i : Nat) (x : Expr), as[i]? = some x →
        ∃ v, vs[i]? = some v ∧ denote cval env φ d x = some v := by
  intro as vs h
  induction h with
  | nil => intro i x hx; exact nomatch hx
  | @cons a v as' vs' ha _ ih =>
    intro i x hx
    cases i with
    | zero =>
      obtain rfl : a = x := Option.some.inj hx
      exact ⟨v, rfl, ha⟩
    | succ j =>
      obtain ⟨v', hv', hd⟩ := ih j x (by simpa using hx)
      exact ⟨v', by simpa using hv', hd⟩

set_option maxHeartbeats 1600000 in
/-- **The reduct stage**: the statement's rhs equals the rule's own
application at the fired spine — the rhs walk fired at the full
context, the applied form's head running back to the closed rule
denotation, and the opener spine reading off the chain. -/
theorem reductS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    {f : Name → Name} (hro : RenameOkT cval env f)
    {rP cnF : Nat} {fvs : List Expr}
    (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {Γs : List VExpr} (hΓslen : Γs.length = rP + cnF)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {RV : VExpr} (hRV : denoteClosed cval env ψ' rhsA = some RV)
    {rhsS : Expr} {vR : VExpr}
    (hvR : denote cval env ψ' (rP + cnF) rhsS = some vR)
    (hleafR : ∀ l ∈ rhsS.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltR : ∀ l ∈ rhsS.fvarLeaves, l.1 < rP + cnF)
    (hdeRhs : DefEqAtW μ env cval ψ' (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs))
    {zs : List VExpr} {ρ : Nat → V} (hzslen : zs.length = rP + cnF)
    (hsat : Sat V Γs (chainE V ρ zs)) :
    interp V (chainE V ρ zs) vR = interp V ρ (VExpr.mkAppN RV zs) := by
  obtain ⟨Av, Bv, hAv, hBv, hder⟩ := hdeRhs
  obtain rfl : vR = Av := by
    rw [hvR] at hAv
    exact Option.some.inj hAv
  -- the applied form's leaves and bounds
  have hleafApp : ∀ l ∈ (Expr.mkAppN (rhsA.renameConsts f)
      fvs).fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with hf | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        ((hasFvar_renameConsts f rhsA).trans hrhsw)] at hf
      exact nomatch hf
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      obtain ⟨nm, ty, rfl⟩ := hshapeS q x hq
      rw [Expr.fvarLeaves] at hlx
      rcases List.mem_cons.mp hlx with rfl | hlx'
      · exact hx
      · exact hleafClosed l ⟨_, hx, by
          rw [Expr.fvarLeaves]
          exact List.mem_cons_of_mem _ hlx'⟩
  have hltApp : ∀ l ∈ (Expr.mkAppN (rhsA.renameConsts f)
      fvs).fvarLeaves, l.1 < rP + cnF := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with hf | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        ((hasFvar_renameConsts f rhsA).trans hrhsw)] at hf
      exact nomatch hf
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      have hqK : q < rP + cnF := by
        rcases Nat.lt_or_ge q (rP + cnF) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by omega)] at hq
          exact nomatch hq
      obtain ⟨nm, ty, rfl⟩ := hshapeS q x hq
      rw [Expr.fvarLeaves] at hlx
      rcases List.mem_cons.mp hlx with rfl | hlx'
      · exact hqK
      · have hw := hwsFvs _ hx
        have hw' : Expr.WScoped q ty := by
          have h' := hw
          simp only [Expr.WScoped] at h'
          exact h'.2
        have := Expr.fvarLeaves_lt_of_wscoped hw' l hlx'
        omega
  -- fire the walk at the full context
  have hent : ∀ i, i < rP + cnF →
      Γs[rP + cnF - 1 - i]?
        = some ((fun i => Γs.getD (rP + cnF - 1 - i) default) i) := by
    intro i hi
    show Γs[rP + cnF - 1 - i]?
      = some (Γs.getD (rP + cnF - 1 - i) default)
    rw [List.getD]
    rcases hg : Γs[rP + cnF - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg
      omega
    · rfl
  have hctxR := ctxOkR_of_openers (μ := μ) henv.cval_closed hΓslen
    hshapeS hwsFvs hdomsS0 hleafR hltR hent
  have hctxApp := ctxOkR_of_openers (μ := μ) henv.cval_closed hΓslen
    hshapeS hwsFvs hdomsS0 hleafApp hltApp hent
  have heq := DefEq.sound henv (hder Γs hctxR hctxApp)
    (chainE V ρ zs) hsat
  rw [heq]
  -- decompose the applied form's denotation
  obtain ⟨vhead, vsp, hvhead, hspine, rfl⟩ := denote_mkAppN_inv hBv
  have hvhead' : RV = vhead := by
    rw [denote_renameConsts hro rhsA (rP + cnF),
      denote_depth_closed henv.cval_closed hrhsw hrhsb (rP + cnF)]
      at hvhead
    exact Option.some.inj (hRV.symm.trans hvhead)
  subst hvhead'
  -- the spine's values are the chain's
  have hsplen : vsp.length = rP + cnF := by
    have := hspine.length
    omega
  rw [interp_mkAppN_map, interp_mkAppN_map]
  have hheadEq : interp V (chainE V ρ zs) RV = interp V ρ RV :=
    interp_closed V (denote_closed henv.cval_closed hrhsw hrhsb hRV)
      _ ρ
  rw [hheadEq]
  congr 1
  -- pointwise: opener `i`'s value is the chain's slot
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i (rP + cnF) with hiK | hiK
  · have hfi : ∃ x, fvs[i]? = some x := by
      rcases hx : fvs[i]? with _ | x
      · rw [List.getElem?_eq_none_iff] at hx
        omega
      · exact ⟨x, rfl⟩
    obtain ⟨x, hx⟩ := hfi
    obtain ⟨nm, ty, rfl⟩ := hshapeS i x hx
    obtain ⟨v, hvspi, hdv⟩ := denoteSpine_getElem?' hspine i _ hx
    rw [denote_fvar] at hdv
    obtain rfl : VExpr.bvar (rP + cnF - 1 - i) = v :=
      Option.some.inj hdv
    have hzsi : ∃ z, zs[i]? = some z := by
      rcases hz : zs[i]? with _ | z
      · rw [List.getElem?_eq_none_iff] at hz
        omega
      · exact ⟨z, rfl⟩
    obtain ⟨z, hz⟩ := hzsi
    rw [hvspi, hz]
    show some (interp V (chainE V ρ zs) (.bvar (rP + cnF - 1 - i)))
      = some (interp V ρ z)
    rw [interp_bvar, chainE_lt (by omega),
      show zs.length - 1 - (rP + cnF - 1 - i) = i from by omega,
      show zs.getD i default = z from by rw [List.getD, hz]; rfl]
  · rw [List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by omega)]
    rfl


/-- A fit's residual is determined: the tower body, spine-instantiated. -/
theorem teleFitV_rest_eq :
    ∀ (k : Nat) {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele k T Γ R → ∀ {ws : List VExpr} {ρ : Nat → V} {rest : VExpr},
      ws.length = k → TeleFitV V ρ T ws rest →
      rest = VExpr.instSeq ws (k - 1) R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws ρ rest hlen hfit
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    cases hfit
    rfl
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit
    cases h with
    | @cons _ A B _ Γ' htail =>
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    cases hfit with
    | cons hmem htailFit =>
      have := ihk (htail.inst w 0) hlen' htailFit
      rw [this, VExpr.instSeq_cons,
        show k + 1 - 1 - 1 = k - 1 from by omega, Nat.add_sub_cancel,
        Nat.zero_add]

end Setlec.SetR
