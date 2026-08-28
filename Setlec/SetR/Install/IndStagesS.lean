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
    (hwsA : Expr.WScoped n a)
    (hleafB : ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hwsB : Expr.WScoped n b)
    {ρpad : Nat → V} (hsat : Sat V Δpad ρpad) :
    ∃ Av Bv, denote cval env φ' k a = some Av ∧
      denote cval env φ' k b = some Bv ∧
      interp V ρpad Av = interp V ρpad Bv := by
  obtain ⟨Av, Bv, hAv, hBv, hder⟩ := hde
  refine ⟨Av, Bv, hAv, hBv, ?_⟩
  have hctxA := ctxOkR_of_openers (μ := μ) henv.cval_closed hΔlen hshape
    hws hdoms hleafA hwsA hent
  have hctxB := ctxOkR_of_openers (μ := μ) henv.cval_closed hΔlen hshape
    hws hdoms hleafB hwsB hent
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
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) ∧
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
    by rw [hdomJ]; exact fun l hl => (hleafDom l hl).1,
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

end Setlec.SetR
