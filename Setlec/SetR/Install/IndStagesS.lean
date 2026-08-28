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
the mixed spine.

The constructor run's spine `sp` is **abstract**: its parameter
positions are the frame's own openers on a `.plain` fire and the
instantiated pins on a `.nested` one (task #148, T5 c3).  All the
stage needs of them is the leaf/scope discipline (`hspLeaf`,
`hspScope` — a position-`q` element's leaves sit among the openers
below `rP + (q + 1 - cnP)`) and the crossing datum `hmixsp`: the
element denotes, and the mixed value at that position is the
denotation instantiated along the fired statement spine. -/
theorem zipFieldTermEq {cval : TConstVal} {env : Env} {ψ' : Name → Nat}
    (hcl : ∀ n ψ'', VExpr.Closed (cval n ψ''))
    {rP cnP cnF : Nat} {fvs : List Expr}
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : VExpr}
    (hTVjK : denote cval env ψ' (rP + cnF) ctyR = some TVj)
    (hTVjcl : VExpr.Closed TVj)
    {Γj : List VExpr} {Rj : VExpr}
    (htowerJ : PiTele (cnP + cnF) TVj Γj Rj)
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    {zs : List VExpr} (hzslen : zs.length = rP + cnF)
    {mix : List VExpr} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denote cval env ψ' (rP + cnF) x = some w0 ∧
        mix[q]? = some (VExpr.instSeq zs (rP + cnF - 1) w0))
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
  -- the scattered spine's per-element facts
  have hspFacts : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      (∃ w, denote cval env ψ' (rP + cnF) x = some w) ∧
        Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨w0, hw0, _⟩ := hmixsp q x hx
    exact ⟨⟨w0, hw0⟩, hspScope q x hx⟩
  -- truncate the scattered run at `cnP + j`
  obtain ⟨midJ, htr, hdr⟩ := instPisAt_take sp (cnP + j) hcinst
  obtain ⟨x0, sp', hsp0⟩ : ∃ x sp',
      sp.drop (cnP + j) = x :: sp' := by
    rcases hsp : sp.drop (cnP + j)
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
    have h := instPisAt_length _ hcinst
    rw [hsplen] at h
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
      have hq' : sp[q]? = some a := by
        rw [← List.getElem?_take_of_lt hqm]
        exact hq
      obtain ⟨hmem, hlt⟩ := hspLeaf q a hq' l hla
      exact ⟨hmem, by omega⟩
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
  have hlenTake : (sp.take (cnP + j)).length = cnP + j := by
    rw [List.length_take, hsplen]
    omega
  have hspTake : ∀ (q : Nat) (x : Expr),
      (sp.take (cnP + j))[q]? = some x →
      sp[q]? = some x ∧ q < cnP + j := by
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
      (sp.take (cnP + j)).length
      (VExpr.instSeq zs (rP + cnF - 1) TVj)
      (Γj.drop (cnP + cnF - (cnP + j))) mid' := by
    rw [hlenTake, VExpr.instSeq_eq_self_of_closed hTVjcl]
    exact hpre
  have hwsCond : ∀ (q : Nat) (x : Expr),
      (sp.take (cnP + j))[q]? = some x →
      ∃ w0, denote cval env ψ' (rP + cnF) x = some w0 ∧
        (mix.take (cnP + j))[q]? = some
          (VExpr.instSeq zs (rP + cnF - 1) w0) := by
    intro q x hx
    obtain ⟨hx', hqm⟩ := hspTake q x hx
    obtain ⟨w0, hw0, hmx⟩ := hmixsp q x hx'
    exact ⟨w0, hw0, by rw [List.getElem?_take_of_lt hqm]; exact hmx⟩
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
the crossed constructor domain (`zipFieldTermEq`).

The constructor's run spine `sp` and the mixed value spine `mix` are
**abstract** (task #148, T5 c3): on a `.plain` fire they are the frame
prefix `fvs.take cnP ++ fvs.drop rP` and `xs.take cnP ++ ys.drop cnP`,
on a `.nested` one the instantiated pins and their values.  The stage
consumes them through the leaf/scope discipline, the crossing datum
`hmixsp`, and the two mixed-value readings `hmixFldEq`/`hmixPar`. -/
theorem zipperS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    {f : Name → Name}
    {rP cnP cnF mI : Nat} {xs ys : List VExpr} {ρ : Nat → V}
    (hrPmI : rP ≤ mI)
    (hlenX : xs.length = mI) (hlenY : ys.length = cnP + cnF)
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
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
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    {mix : List VExpr} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denote cval env ψ' (rP + cnF) x = some w0 ∧
        mix[q]? = some (VExpr.instSeq
          (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0))
    (hmixFldEq : ∀ j, j < cnF →
      mix.getD (cnP + j) default = ys.getD (cnP + j) default)
    (hmixPar : ∀ q, q < cnP →
      interp V ρ (mix.getD q default) = interp V ρ (ys.getD q default))
    {restRpre restC : VExpr}
    (hfitRpre : TeleFitV V ρ TV (xs.take rP) restRpre)
    (hfitC : TeleFitV V ρ TVj ys restC)
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
  -- the mixed values read as the constructor's own spine, pointwise
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ (mix.getD q default) = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
  -- the mixed chain memberships (the [set] mixed fit, in chain form)
  have hchainC := teleFitV_to_chain (cnP + cnF) htowerJ hlenY hfitC
  have hchainEnvEq : ∀ q, q ≤ cnP + cnF →
      chainE V ρ (mix.take q) = chainE V ρ (ys.take q) := by
    intro q hq
    funext i
    have htq : (mix.take q).length = q := by
      rw [List.length_take, hmixlen]
      omega
    have htq' : (ys.take q).length = q := by
      rw [List.length_take, hlenY]
      omega
    by_cases hiq : i < q
    · rw [chainE_lt (by omega), chainE_lt (by omega), htq, htq']
      have hlt : q - 1 - i < q := by omega
      rw [show (mix.take q).getD (q - 1 - i) default
          = mix.getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt],
        show (ys.take q).getD (q - 1 - i) default
          = ys.getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt]]
      exact hmixVal _ (by omega)
    · rw [chainE_ge (by omega), chainE_ge (by omega), htq, htq']
  have hmixMem : ∀ q, q < cnP + cnF →
      interp V ρ (mix.getD q default)
        ∈ˢ interp V (chainE V ρ (mix.take q))
          (Γj.getD (cnP + cnF - 1 - q) default) := by
    intro q hq
    have h1 := hchainC q hq
    rw [hchainEnvEq q (by omega), hmixVal q hq]
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
            zipFieldTermEq henv.cval_closed hCwR hCbR hTVjK hTVjcl
              htowerJ hsplen hspLeaf hspScope hcinst hzslen hmixlen
              hmixsp (j := n - rP) (by omega)
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
          have htake1 : (mix.take (cnP + (n - rP))).length
              = cnP + (n - rP) := by
            rw [List.length_take, hmixlen]
            omega
          rw [show interp V
              (chainE V ρ (mix.take (cnP + (n - rP))))
              (Γj.getD (cnP + cnF - 1 - (cnP + (n - rP))) default)
            = interp V ρ (VExpr.instSeq
                (mix.take (cnP + (n - rP)))
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
          have hval : interp V ρ (mix.getD (cnP + (n - rP)) default)
              = interp V ρ ((xs.take rP ++ ys.drop cnP).getD n
                default) := by
            have hz := hzsFld (n - rP) (by omega)
            rw [show rP + (n - rP) = n from by omega] at hz
            rw [hmixFldEq (n - rP) (by omega), hz]
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


set_option maxHeartbeats 6400000 in
/-- **The point stage**: the statement's lhs, position by position, is
the fired redex — prefix openers read the chain, index arguments cross
through the canonical residual (the index walk + `IotaIndexPinV`), and
the major is the canonical constructor application reconciled through
the parameter equalities and the fire-site level guard.

The major's spine `sp`, its head `ctorHead` and the mixed value spine
`mix` are **abstract** (task #148, T5 c3): a `.plain` fire supplies
the frame's openers under the parameter-mapped constructor head, a
`.nested` one the instantiated pins under the stored `lvls`, and the
major is matched **up to `ErasedEq`** (the nested pin's own form). -/
theorem pointS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ : Name → Nat} {lps : List Name} {us : List Level}
    {ψ' : Name → Nat} (_hψ'E : ψ' = Level.substFn φ lps us)
    {zs : List VExpr}
    (henv : EnvSHyp V env cval ψ')
    {f : Name → Name} (hro : RenameOkT cval env f)
    {Rn : Name}
    {rP cnP cnF mI : Nat} {xs ys : List VExpr} {ρ : Nat → V}
    (hzs : zs = xs.take rP ++ ys.drop cnP)
    (hrPmI : rP ≤ mI)
    (hlenX : xs.length = mI) (hlenY : ys.length = cnP + cnF)
    {ctor : Name} {cvj : ConstantVal} {usj : List Level}
    {ciRm : ConstantInfo} (hfRnE : env.find? (f Rn) = some ciRm)
    (hRmlps : ciRm.toConstantVal.levelParams = lps)
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    {Γs : List VExpr} (hΓslen : Γs.length = rP + cnF)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env (ψ') i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    (hsat : Sat V Γs (chainE V ρ zs))
    {lhsS : Expr} {vL : VExpr}
    (hvL : denote cval env (ψ') (rP + cnF) lhsS
      = some vL)
    (hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    {ctorHead : Expr} {sp : List Expr}
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN ctorHead sp))
    (hctorHead : denote cval env ψ' (rP + cnF) ctorHead
      = some (cval ctor (Level.substFn φ cvj.levelParams usj)))
    (hleafLhs : ∀ l ∈ lhsS.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltLhs : ∀ l ∈ lhsS.fvarLeaves, l.1 < rP + cnF)
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : VExpr}
    (hTVjK : denote cval env (ψ') (rP + cnF) ctyR
      = some TVj)
    (hTVjcl : VExpr.Closed TVj)
    {Γj : List VExpr} {Rj : VExpr}
    (htowerJ : PiTele (cnP + cnF) TVj Γj Rj)
    (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {vHC : VExpr} {vArgsC : List VExpr}
    (hRjdec : Rj = VExpr.mkAppN vHC vArgsC)
    (hArgsClen : vArgsC.length = cnP + (mI - rP))
    (hdeIdx : DefEqListW μ env cval (ψ') (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    {mix : List VExpr} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denote cval env ψ' (rP + cnF) x = some w0 ∧
        mix[q]? = some (VExpr.instSeq zs (rP + cnF - 1) w0))
    (hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ (mix.getD q default) = interp V ρ (ys.getD q default))
    {restC : VExpr} (hfitC : TeleFitV V ρ TVj ys restC)
    (hidx : IotaIndexPinV V ρ restC cnP mI rP xs) :
    interp V (chainE V ρ zs) vL
      = interp V ρ
          (VExpr.mkAppN (cval Rn (ψ'))
            (xs ++ [VExpr.mkAppN
              (cval ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : zs.length = rP + cnF := by
    rw [hzs, List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  have hzsPre : ∀ n, n < rP →
      zs.getD n default = xs.getD n default := by
    intro n hn
    rw [hzs, List.getD, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      zs.getD (rP + j) default = ys.getD (cnP + j) default := by
    intro j hj
    rw [hzs, List.getD, List.getElem?_append_right (by omega), hxtlen,
      List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  -- decompose the lhs
  have hlhsApp : lhsS = Expr.mkAppN
      (.const (f Rn) (lps.map .param)) lhsS.getAppArgs := by
    rw [← hlhead]
    exact (Expr.mkAppN_getApp lhsS).symm
  rw [hlhsApp] at hvL
  obtain ⟨vLf, vLargs, hvLf, hLspine, rfl⟩ := denote_mkAppN_inv hvL
  have hvLargsLen : vLargs.length = mI + 1 := by
    rw [hLspine.length, hlarity]
  have hcl' := henv.cval_closed
  -- shared scattered-spine facts
  have hspFacts : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      (∃ w, denote cval env ψ' (rP + cnF) x = some w) ∧
        Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨w0, hw0, _⟩ := hmixsp q x hx
    exact ⟨⟨w0, hw0⟩, hspScope q x hx⟩
  have hfbCty : Expr.fvarsBelow (rP + cnF) ctyR := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hl
    exact nomatch hl
  have hfvsLt : ∀ l : Nat × Name × Expr,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨nm', ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1]
    rw [hfvslen] at hql
    exact hql
  -- the head of the statement's lhs is the recursor's leaf
  have hconstDen : ∀ (c : Name) (ci : ConstantInfo) (ks : List Name),
      env.find? c = some ci → ci.toConstantVal.levelParams = ks →
      denote cval env ψ' (rP + cnF) (.const c (ks.map .param))
        = some (cval c ψ') := by
    intro c ci ks hf hlp
    rw [denote_const, hf]
    dsimp only
    rw [if_pos (by rw [hlp, List.length_map]), hlp,
      show Level.substFn ψ' ks (ks.map .param) = ψ' from
        funext fun _ => Level.substFn_map_param]
  have hvLfEq : vLf = cval Rn ψ' := by
    rw [hconstDen (f Rn) ciRm lps hfRnE hRmlps] at hvLf
    rw [hro.2.2] at hvLf
    exact (Option.some.inj hvLf).symm
  -- reduce to the mapped spine equality
  rw [hvLfEq, interp_mkAppN_map, interp_mkAppN_map,
    interp_closed V (hcl' Rn ψ') (chainE V ρ zs) ρ]
  suffices hmap : vLargs.map (interp V (chainE V ρ zs))
      = (xs ++ [VExpr.mkAppN
          (cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).map
          (interp V ρ) by
    rw [hmap]
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i (mI + 1) with hi | hi
  · -- in range: extract the lhs argument and its denotation
    rcases hai : lhsS.getAppArgs[i]? with _ | ai
    · rw [List.getElem?_eq_none_iff, hlarity] at hai
      omega
    obtain ⟨vi, hvi, hdi⟩ := denoteSpine_getElem?' hLspine i ai hai
    rw [hvi]
    rcases Nat.lt_or_ge i rP with hiP | hiP
    · -- prefix branch: the opener reads the chain at an `xs` slot
      have hlargsFv : lhsS.getAppArgs[i]? = fvs[i]? := by
        have h1 := congrArg (fun l => l[i]?) hlpre
        simp only [List.getElem?_take_of_lt hiP] at h1
        exact h1
      obtain ⟨nm, ty, rfl⟩ := hshapeS i ai (by rw [← hlargsFv]; exact hai)
      rw [denote_fvar] at hdi
      obtain rfl : vi = .bvar (rP + cnF - 1 - i) :=
        (Option.some.inj hdi).symm
      rw [List.getElem?_append_left (by rw [hlenX]; omega)]
      rcases hx : xs[i]? with _ | xv
      · rw [List.getElem?_eq_none_iff, hlenX] at hx
        omega
      have hgx : xs.getD i default = xv := by
        rw [List.getD, hx]
        rfl
      have hbb : rP + cnF - 1 - i < zs.length := by
        rw [hzslen]
        omega
      rw [Option.map_some, Option.map_some, interp_bvar, chainE_lt hbb,
        hzslen, show rP + cnF - 1 - (rP + cnF - 1 - i) = i from by omega,
        hzsPre i hiP, hgx]
    · rcases Nat.lt_or_ge i mI with hiM | hiM
      · -- index branch: walk, cross, and the fired index pin
        have hj : i - rP < mI - rP := by omega
        have hmIrP : rP < mI := by omega
        -- the walk element
        obtain ⟨hwlen, hwget⟩ := Forall2.length_getD hdeIdx
        have hlenL : ((lhsS.getAppArgs.drop rP).take (mI - rP)).length
            = mI - rP := by
          rw [List.length_take, List.length_drop, hlarity]
          omega
        have hde := hwget (i - rP) default default (by rw [hlenL]; omega)
        have hLsub : ((lhsS.getAppArgs.drop rP).take (mI - rP)).getD
              (i - rP) default
            = ai := by
          rw [List.getD, List.getElem?_take_of_lt hj, List.getElem?_drop,
            show rP + (i - rP) = i from by omega, hai]
          rfl
        rcases hbx : cres.getAppArgs[cnP + (i - rP)]? with _ | bx
        · rw [List.getElem?_eq_none_iff, hclen] at hbx
          omega
        have hRsub : (cres.getAppArgs.drop cnP).getD (i - rP) default
            = bx := by
          rw [List.getD, List.getElem?_drop, hbx]
          rfl
        rw [hLsub, hRsub] at hde
        -- leaves of the two subjects
        have hleafA : ∀ l ∈ ai.fvarLeaves,
            Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
          intro l hl
          exact hleafLhs l
            (fvarLeaves_getAppArgs (List.mem_of_getElem? hai) l hl)
        have hltA : ∀ l ∈ ai.fvarLeaves, l.1 < rP + cnF := by
          intro l hl
          exact hltLhs l
            (fvarLeaves_getAppArgs (List.mem_of_getElem? hai) l hl)
        have hleafB : ∀ l ∈ bx.fvarLeaves,
            Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
          intro l hl
          have hlc : l ∈ cres.fvarLeaves :=
            fvarLeaves_getAppArgs (List.mem_of_getElem? hbx) l hl
          rcases instPisAt_leaves _ hcinst l (Or.inr hlc) with
            hty | ⟨a, ha, hla⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hty
            exact nomatch hty
          · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
            exact (hspLeaf q _ hq l hla).1
        have hltB : ∀ l ∈ bx.fvarLeaves, l.1 < rP + cnF := by
          intro l hl
          exact hfvsLt l (hleafB l hl)
        -- fire the walk at the full context
        have hent : ∀ i', i' < rP + cnF →
            Γs[rP + cnF - 1 - i']? =
              some (Γs.getD (rP + cnF - 1 - i') default) := by
          intro i' hi'
          rw [List.getD]
          rcases hg : Γs[rP + cnF - 1 - i']? with _ | g
          · rw [List.getElem?_eq_none_iff, hΓslen] at hg
            omega
          · rfl
        obtain ⟨Av, Bv, hAv, hBv, heqAB⟩ := openWalk_eqS henv
          (k := rP + cnF) (fvs := fvs)
          (As := fun i' => Γs.getD (rP + cnF - 1 - i') default)
          hΓslen hshapeS hwsFvs
          (fun i' x hx => hdomsS0 i' x hx) (n := rP + cnF) hent hde
          hleafA hltA hleafB hltB hsat
        obtain rfl : vi = Av := by
          rw [hdi] at hAv
          exact Option.some.inj hAv
        -- the residual's denotation and spine
        obtain ⟨vCres, hvCres⟩ := instPisAt_fvar_denote_defined hcl'
          _ hcinst (D := rP + cnF) hspFacts hfbCty hCbR hTVjK
        have hvCres1 : denote cval env ψ' (rP + cnF)
            (Expr.mkAppN cres.getAppFn cres.getAppArgs) = some vCres := by
          rw [Expr.mkAppN_getApp]
          exact hvCres
        obtain ⟨vcH, vcArgs, hvcH, hcsp, hvCresEq⟩ :=
          denote_mkAppN_inv hvCres1
        have hvcArgsLen : vcArgs.length = cnP + (mI - rP) := by
          rw [hcsp.length, hclen]
        obtain ⟨bv', hbv', hdb'⟩ := denoteSpine_getElem?' hcsp _ bx hbx
        obtain rfl : Bv = bv' := by
          rw [hdb'] at hBv
          exact (Option.some.inj hBv).symm
        -- the mixed spine and the full cross
        have htowFull : PiTele sp.length
            (VExpr.instSeq zs (rP + cnF - 1) TVj) Γj Rj := by
          rw [hsplen, VExpr.instSeq_eq_self_of_closed hTVjcl]
          exact htowerJ
        have hcross := instPisAt_denote_cross hcl' _ hcinst
          (D := rP + cnF) (vals := zs) hzslen
          (fun q x hx => (hspFacts q x hx).2) hfbCty hCbR hTVjK hvCres
          (ws := mix)
          (by rw [hmixlen, hsplen]) hmixsp htowFull
        rw [hvCresEq, VExpr.instSeq_mkAppN, hRjdec, VExpr.instSeq_mkAppN,
          hmixlen] at hcross
        have hcrossSp := (VExpr.mkAppN_inj hcross
          (by rw [List.length_map, List.length_map, hvcArgsLen,
            hArgsClen])).2
        -- element of the crossed spines
        rcases hva : vArgsC[cnP + (i - rP)]? with _ | va
        · rw [List.getElem?_eq_none_iff, hArgsClen] at hva
          omega
        have hel : VExpr.instSeq zs (rP + cnF - 1) Bv
            = VExpr.instSeq mix (cnP + cnF - 1) va := by
          have h1 := congrArg (fun l => l[cnP + (i - rP)]?) hcrossSp
          simp only [List.getElem?_map, hbv', hva, Option.map_some] at h1
          exact Option.some.inj h1
        -- the fired pin identifies the `ys`-instantiated element
        have hrest : restC = VExpr.instSeq ys (cnP + cnF - 1) Rj :=
          teleFitV_rest_eq (cnP + cnF) htowerJ (by rw [hlenY]) hfitC
        obtain ⟨H, cargs, hrestEq, hcarLen, hcarInterp⟩ := hidx
        rcases hcarLen with hcase | hcarLen
        · omega
        have hrest2 : VExpr.mkAppN H cargs
            = VExpr.mkAppN (VExpr.instSeq ys (cnP + cnF - 1) vHC)
                (vArgsC.map (VExpr.instSeq ys (cnP + cnF - 1))) := by
          rw [← hrestEq, hrest, hRjdec, VExpr.instSeq_mkAppN]
        have hcargsSp := (VExpr.mkAppN_inj hrest2
          (by rw [hcarLen, List.length_map, hArgsClen])).2
        have hcel : cargs.getD (cnP + (i - rP)) default
            = VExpr.instSeq ys (cnP + cnF - 1) va := by
          have h1 := congrArg (fun l => l[cnP + (i - rP)]?) hcargsSp
          simp only [List.getElem?_map, hva, Option.map_some] at h1
          rw [List.getD, h1]
          rfl
        -- the mixed chain equals the constructor chain
        have hchainEq : chainE V ρ mix = chainE V ρ ys := by
          funext q
          rcases Nat.lt_or_ge q (cnP + cnF) with hq | hq
          · rw [chainE_lt (by rw [hmixlen]; exact hq),
              chainE_lt (by rw [hlenY]; exact hq), hmixlen, hlenY]
            exact hmixVal _ (by omega)
          · rw [chainE_ge (by rw [hmixlen]; exact hq),
              chainE_ge (by rw [hlenY]; exact hq), hmixlen, hlenY]
        -- assemble
        rw [List.getElem?_append_left (by rw [hlenX]; omega)]
        rcases hx : xs[i]? with _ | xv
        · rw [List.getElem?_eq_none_iff, hlenX] at hx
          omega
        rw [Option.map_some, Option.map_some]
        have hgx : xs.getD i default = xv := by
          rw [List.getD, hx]
          rfl
        have hchain : interp V (chainE V ρ zs) vi
            = interp V ρ (xs.getD i default) := by
          calc interp V (chainE V ρ zs) vi
              = interp V (chainE V ρ zs) Bv := heqAB
            _ = interp V ρ (VExpr.instSeq zs (zs.length - 1) Bv) :=
                (interp_instSeq zs Bv ρ).symm
            _ = interp V ρ (VExpr.instSeq mix (cnP + cnF - 1) va) := by
                rw [hzslen]
                exact congrArg (interp V ρ) hel
            _ = interp V (chainE V ρ mix) va := by
                rw [show cnP + cnF - 1 = mix.length - 1 from by
                  rw [hmixlen]]
                exact interp_instSeq _ va ρ
            _ = interp V (chainE V ρ ys) va := by rw [hchainEq]
            _ = interp V ρ (VExpr.instSeq ys (ys.length - 1) va) :=
                (interp_instSeq ys va ρ).symm
            _ = interp V ρ (cargs.getD (cnP + (i - rP)) default) := by
                rw [hlenY, hcel]
            _ = interp V ρ (xs.getD (rP + (i - rP)) default) :=
                hcarInterp (i - rP) hj
            _ = interp V ρ (xs.getD i default) := by
                rw [show rP + (i - rP) = i from by omega]
        rw [hchain, hgx]
      · -- major branch: i = mI
        obtain rfl : mI = i := by omega
        -- the last lhs argument is the canonical constructor
        -- application, up to erasure
        have hmajA : Expr.ErasedEq ai (Expr.mkAppN ctorHead sp) := by
          have h1 := hmaj
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
            hlarity, Nat.add_sub_cancel] at h1
          rcases h2 : lhsS.getAppArgs[mI]? with _ | y
          · rw [List.getElem?_eq_none_iff, hlarity] at h2
            omega
          · rw [h2, Option.getD_some] at h1
            rw [hai] at h2
            obtain rfl : ai = y := Option.some.inj h2
            exact h1
        rw [denote_erasedEq hmajA (rP + cnF)] at hdi
        -- decompose its denotation
        obtain ⟨vch, vmargs, hvch, hcspM, hviEq⟩ := denote_mkAppN_inv hdi
        have hvchEq : vch = cval ctor
            (Level.substFn φ cvj.levelParams usj) := by
          rw [hctorHead] at hvch
          exact (Option.some.inj hvch).symm
        have hmargsLen : vmargs.length = cnP + cnF := by
          rw [hcspM.length, hsplen]
        -- the right-hand element is the pinned constructor application
        rw [List.getElem?_append_right (by rw [hlenX]; omega), hlenX,
          Nat.sub_self]
        rw [show ([VExpr.mkAppN
            (cval ctor (Level.substFn φ cvj.levelParams usj)) ys])[0]?
          = some (VExpr.mkAppN
              (cval ctor (Level.substFn φ cvj.levelParams usj)) ys)
          from rfl]
        rw [Option.map_some, Option.map_some]
        rw [hviEq, interp_mkAppN_map, interp_mkAppN_map, hvchEq,
          interp_closed V
            (hcl' ctor (Level.substFn φ cvj.levelParams usj))
            (chainE V ρ zs) ρ]
        suffices hsp2 : vmargs.map (interp V (chainE V ρ zs))
            = ys.map (interp V ρ) by
          rw [hsp2]
        refine List.ext_getElem? fun q => ?_
        rw [List.getElem?_map, List.getElem?_map]
        rcases Nat.lt_or_ge q (cnP + cnF) with hq | hq
        · rcases hxq : sp[q]? with _ | xq
          · rw [List.getElem?_eq_none_iff, hsplen] at hxq
            omega
          obtain ⟨w0, hw0, hmx⟩ := hmixsp q xq hxq
          obtain ⟨vq, hvq, hdq⟩ := denoteSpine_getElem?' hcspM q _ hxq
          rw [hvq]
          rcases hyq : ys[q]? with _ | yq
          · rw [List.getElem?_eq_none_iff, hlenY] at hyq
            omega
          rw [Option.map_some, Option.map_some]
          have hvqw : vq = w0 := by
            rw [hw0] at hdq
            exact (Option.some.inj hdq).symm
          rw [hvqw]
          have hgy : ys.getD q default = yq := by
            rw [List.getD, hyq]
            rfl
          have hgm : mix.getD q default
              = VExpr.instSeq zs (rP + cnF - 1) w0 := by
            rw [List.getD, hmx]
            rfl
          have hcalc : interp V (chainE V ρ zs) w0
              = interp V ρ (ys.getD q default) := by
            calc interp V (chainE V ρ zs) w0
                = interp V ρ (VExpr.instSeq zs (zs.length - 1) w0) :=
                  (interp_instSeq zs w0 ρ).symm
              _ = interp V ρ (mix.getD q default) := by
                  rw [hzslen, hgm]
              _ = interp V ρ (ys.getD q default) := hmixVal q hq
          rw [hcalc, hgy]
        · rw [List.getElem?_eq_none (by rw [hmargsLen]; omega),
            List.getElem?_eq_none (by rw [hlenY]; omega)]
          rfl
  · -- out of range: both sides are `none`
    rw [List.getElem?_eq_none (by rw [hvLargsLen]; omega),
      List.getElem?_eq_none (by
        rw [List.length_append, hlenX, List.length_cons, List.length_nil]
        omega)]
    rfl


/-! ## The truthfulness-transport machinery (`annotS`)

The [set] transpose of the model's `closeLamsAt_fold`/`annotOk_spine`
pair: the reduct's per-application `AnnotOkV` packages come from the
rule rhs's *own* λ-tower (read through `instLamsAt_denoteTele`), whose
layer domains the fired lam-domain walk identifies with the satisfied
context — each partial application is then a `lamC` over a domain the
next value inhabits, and `lamC_mem_upair` supplies the `piC` package.
-/

theorem chainE_nil (ρ : Nat → V) : chainE V ρ [] = ρ := by
  funext j
  rw [chainE_ge (by simp), List.length_nil, Nat.sub_zero]

theorem chainE_snoc (ρ : Nat → V) (ws : List VExpr) (w : VExpr) :
    chainE V ρ (ws ++ [w]) = cons V (interp V ρ w) (chainE V ρ ws) := by
  funext j
  have hlen : (ws ++ [w]).length = ws.length + 1 := by
    rw [List.length_append, List.length_cons, List.length_nil]
  cases j with
  | zero =>
    rw [show cons V (interp V ρ w) (chainE V ρ ws) 0
        = interp V ρ w from rfl,
      chainE_lt (by rw [hlen]; omega), hlen,
      show ws.length + 1 - 1 - 0 = ws.length from by omega, List.getD,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  | succ j =>
    rw [show cons V (interp V ρ w) (chainE V ρ ws) (j + 1)
      = chainE V ρ ws j from rfl]
    rcases Nat.lt_or_ge j ws.length with hj | hj
    · rw [chainE_lt (by rw [hlen]; omega), chainE_lt hj, hlen,
        show ws.length + 1 - 1 - (j + 1) = ws.length - 1 - j from by
          omega, List.getD, List.getD,
        List.getElem?_append_left (by omega)]
    · rw [chainE_ge (by rw [hlen]; omega), chainE_ge hj, hlen,
        show j + 1 - (ws.length + 1) = j - ws.length from by omega]

/-- Shifting the full chain by `m` is the chain of the prefix. -/
theorem shiftE_chainE_take {ρ : Nat → V} {zs : List VExpr} {m : Nat}
    (hm : m ≤ zs.length) :
    shiftE V m 0 (chainE V ρ zs)
      = chainE V ρ (zs.take (zs.length - m)) := by
  funext j
  have htk : (zs.take (zs.length - m)).length = zs.length - m := by
    rw [List.length_take]
    omega
  show chainE V ρ zs (if j < 0 then j else j + m) = _
  rw [if_neg (by omega)]
  rcases Nat.lt_or_ge j (zs.length - m) with hj | hj
  · rw [chainE_lt (by omega), chainE_lt (by rw [htk]; exact hj), htk,
      List.getD, List.getD,
      List.getElem?_take_of_lt (show zs.length - m - 1 - j
        < zs.length - m from by omega),
      show zs.length - 1 - (j + m) = zs.length - m - 1 - j from by omega]
  · rw [chainE_ge (by omega), chainE_ge (by rw [htk]; exact hj), htk,
      show j + m - zs.length = j - (zs.length - m) from by omega]

theorem VExpr.mkAppN_snoc :
    ∀ (as : List VExpr) (f b : VExpr),
      VExpr.mkAppN f (as ++ [b]) = .app (VExpr.mkAppN f as) b := by
  intro as
  induction as with
  | nil => intro f b; rfl
  | cons a as ih => intro f b; exact ih (.app f a) b

/-- `ctxOkR_of_openers` with the `Infer`-up-to-`DefEq` slack supplied
per opener — the builder for subjects living on a *different* frame
than the context's own (the P-frame walk subjects fired at the
statement context): the caller composes the annotation walks into the
per-position `DefEq`. -/
theorem ctxOkR_of_walked_openers {μ : CheckMode} {cval : TConstVal}
    {env : Env} {φ : Name → Nat}
    {k : Nat} {fvs' : List Expr} {Δ' : List VExpr}
    (hΔlen : Δ'.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs'[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs', Expr.WScoped k x)
    (hslack : ∀ (i : Nat) (x : Expr), fvs'[i]? = some x →
      ∃ T, denote cval env φ k (Expr.fvarTypeD x) = some T ∧
        ∃ T', Infer μ env cval φ Δ' (.bvar (k - 1 - i)) T' ∧
          DefEq μ env cval φ Δ' T' T)
    {e : Expr}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs') :
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
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2.2 := by
    simpa [Expr.WScoped] using hw
  obtain ⟨T, hT, hslk⟩ := hslack l.1 _ hpos
  exact ⟨hwty.1, hwty.2.fvarsBelow, T, hT, hslk⟩

set_option maxHeartbeats 800000 in
/-- **The λ-tower descent**: applying an interpreted λ-tower along
values that inhabit its layer domains (each at the prefix chain) walks
the tower by β — the partial application *is* the next layer's `lamC`
— and assembles the application's hereditary truthfulness, each `piC`
package by `lamC_mem_upair`. -/
theorem lamTowerStepS :
    ∀ (n : Nat) {K : Nat} (_hn : n ≤ K) {Γl : List VExpr} {C : VExpr}
      (_hΓ : Γl.length = K) {ws : List VExpr} (_hw : ws.length = K)
      {ρ : Nat → V}
      (_hmem : ∀ k, k < K → interp V ρ (ws.getD k default)
        ∈ˢ interp V (chainE V ρ (ws.take k))
            (Γl.getD (K - 1 - k) default)),
      interp V ρ (VExpr.mkAppN (lamCtx Γl C) (ws.take n))
        = interp V (chainE V ρ (ws.take n))
            (lamCtx (Γl.take (K - n)) C) ∧
      (AnnotOkV V ρ (lamCtx Γl C) → (∀ w ∈ ws, AnnotOkV V ρ w) →
        AnnotOkV V ρ (VExpr.mkAppN (lamCtx Γl C) (ws.take n))) := by
  intro n
  induction n with
  | zero =>
    intro K hn Γl C _hΓ ws _hw ρ _hmem
    rw [List.take_zero, Nat.sub_zero, chainE_nil,
      List.take_of_length_le (by omega)]
    exact ⟨rfl, fun hL _ => hL⟩
  | succ n ih =>
    intro K hn Γl C hΓ ws hw ρ hmem
    have hnK : n < K := by omega
    obtain ⟨heq, hann⟩ := ih (by omega) hΓ hw hmem
    have hwn : ws[n]? = some (ws.getD n default) := by
      rcases hx : ws[n]? with _ | x
      · rw [List.getElem?_eq_none_iff, hw] at hx
        omega
      · rw [List.getD, hx]
        rfl
    have htk : ws.take (n + 1) = ws.take n ++ [ws.getD n default] := by
      rw [List.take_add_one, hwn]
      rfl
    have hΓn : Γl[K - n - 1]? = some (Γl.getD (K - 1 - n) default) := by
      rw [show K - 1 - n = K - n - 1 from by omega]
      rcases hx : Γl[K - n - 1]? with _ | x
      · rw [List.getElem?_eq_none_iff, hΓ] at hx
        omega
      · rw [List.getD, hx]
        rfl
    have hΓtk : Γl.take (K - n) = Γl.take (K - n - 1)
        ++ [Γl.getD (K - 1 - n) default] := by
      rw [show K - n = (K - n - 1) + 1 from by omega, List.take_add_one,
        hΓn]
      rfl
    have hval : interp V ρ (VExpr.mkAppN (lamCtx Γl C) (ws.take n))
        = lamC (interp V (chainE V ρ (ws.take n))
              (Γl.getD (K - 1 - n) default))
            (fun x => interp V (cons V x (chainE V ρ (ws.take n)))
              (lamCtx (Γl.take (K - n - 1)) C)) := by
      rw [heq, hΓtk, lamCtx_snoc, interp_lam]
    have hwmem : ws.getD n default ∈ ws := by
      have := hwn
      exact List.mem_of_getElem? this
    refine ⟨?_, ?_⟩
    · rw [htk, VExpr.mkAppN_snoc, interp_app, hval,
        app_lamC (hmem n hnK), chainE_snoc,
        show K - (n + 1) = K - n - 1 from by omega]
    · intro hL hws
      rw [htk, VExpr.mkAppN_snoc, AnnotOkV_app]
      refine ⟨hann hL hws, hws _ hwmem,
        interp V (chainE V ρ (ws.take n)) (Γl.getD (K - 1 - n) default),
        fun x => upair
          (interp V (cons V x (chainE V ρ (ws.take n)))
            (lamCtx (Γl.take (K - n - 1)) C))
          (interp V (cons V x (chainE V ρ (ws.take n)))
            (lamCtx (Γl.take (K - n - 1)) C)),
        ?_, hmem n hnK⟩
      rw [hval]
      exact lamC_mem_upair _ _


set_option maxHeartbeats 3200000 in
/-- **The per-position annotation identification** (`annotS` stage 1):
at every frame position the statement's opener annotation is `DefEq`
(under any context validating the two walked subjects) to the P-frame's
canonical annotation — the prefix through the recursor-domain walk, the
fields through the constructor-domain walk, each composed with the
renamed-equal reading of the canonical run (`instPisAt_renEq`:
same-index openers, renamed base). -/
theorem annotPFrameEqS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat}
    {f : Name → Name} (hro : RenameOkT cval env f)
    {rP cnP cnF : Nat}
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    {tyA tyAR : Expr} (hrenTy : RenEqT f tyA tyAR)
    {fvsPl : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsPl, restP))
    {cvjty cvjR : Expr} (hrenCvj : RenEqT f cvjty cvjR)
    {psP psR : List Expr}
    (hpsPlen : psP.length = cnP) (hpsRlen : psR.length = cnP)
    (hpsRen : ∀ (i : Nat) (a a' : Expr), psP[i]? = some a →
      psR[i]? = some a' → RenEqT f a a')
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt psP cvjty = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (psR ++ fvs.drop rP) cvjR
      = some (cdoms, cres))
    (hdePre : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP)) :
    ∀ i, i < rP + cnF →
      ∃ Ai Bi,
        denote cval env ψ' (rP + cnF)
          (Expr.fvarTypeD (fvs.getD i default)) = some Ai ∧
        denote cval env ψ' (rP + cnF)
          (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD i default)) = some Bi ∧
        ∀ Δ : List VExpr,
          CtxOkR μ cval env ψ' (rP + cnF) Δ
            (Expr.fvarTypeD (fvs.getD i default)) →
          CtxOkR μ cval env ψ' (rP + cnF) Δ
            (if i < rP then rdoms.getD i default
              else cdoms.getD (cnP + (i - rP)) default) →
          DefEq μ env cval ψ' Δ Ai Bi := by
  intro i hiK
  have hfvsPlen : fvsPl.length = rP := openPisAtFvars_length _ hopenP
  have hxlen : xFvsP.length = cnF := openPisAtFvars_length _ hopenXP
  have hPpre : Expr.instPisAt fvsPl tyA
      = some (fvsPl.map Expr.fvarTypeD, restP) :=
    openPisAtFvars_instPisAt _ hopenP
  have hPx : Expr.instPisAt xFvsP crestP
      = some (xFvsP.map Expr.fvarTypeD, ldoms) :=
    openPisAtFvars_instPisAt _ hopenXP
  have hPfld : Expr.instPisAt (psP ++ xFvsP) cvjty
      = some (cdomsP ++ xFvsP.map Expr.fvarTypeD, ldoms) :=
    Expr.instPisAt_append _ hcinstP hPx
  have hcdomsPlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [hpsPlen] at h
    omega
  have hcdomslen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    rw [List.length_append, List.length_drop, hpsRlen, hfvslen] at h
    omega
  rcases Nat.lt_or_ge i rP with hi | hi
  · -- prefix: statement annotation ↔ `rdoms[i]` ↔ P annotation
    obtain ⟨hwlen, hwget⟩ := Forall2.length_getD hdePre
    have hslen : ((fvs.take rP).map Expr.fvarTypeD).length = rP := by
      rw [List.length_map, List.length_take, hfvslen]
      omega
    have hde := hwget i default default (by rw [hslen]; omega)
    rcases hfx : fvs[i]? with _ | fx
    · rw [List.getElem?_eq_none_iff, hfvslen] at hfx
      omega
    have hLsub : ((fvs.take rP).map Expr.fvarTypeD).getD i default
        = Expr.fvarTypeD (fvs.getD i default) := by
      rw [List.getD, List.getElem?_map,
        List.getElem?_take_of_lt hi, hfx, List.getD, hfx]
      rfl
    rw [hLsub] at hde
    obtain ⟨Ai, Bi, hAi, hBi, hder⟩ := hde
    -- the canonical run's `RenEqT` alignment against `rdoms`
    have hrenD := instPisAt_renEq fvsPl (fvs.take rP) hPpre hrinst
      hrenTy
      (fun i0 a a' ha ha' => by
        obtain ⟨nm, ty, ha2⟩ := openPisAtFvars_index _ _ _ hopenP i0 a ha
        have hi0 : i0 < rP := by
          have := (List.getElem?_eq_some_iff.mp ha).1
          rw [hfvsPlen] at this
          exact this
        rw [List.getElem?_take_of_lt hi0] at ha'
        obtain ⟨nm', ty', ha2'⟩ := hshapeS i0 a' ha'
        rw [ha2, ha2', show (0 : Nat) + i0 = i0 from by omega]
        exact RenEqT.fvar)
      (by rw [hfvsPlen, List.length_take, hfvslen]; omega)
    rcases hpi : fvsPl[i]? with _ | pxi
    · rw [List.getElem?_eq_none_iff, hfvsPlen] at hpi
      omega
    have hrenI : RenEqT f (Expr.fvarTypeD pxi) (rdoms.getD i default) := by
      rcases hri : rdoms[i]? with _ | ri
      · rw [List.getElem?_eq_none_iff, ← hwlen, hslen] at hri
        omega
      · rw [List.getD, hri]
        exact hrenD.1 i _ _ (by rw [List.getElem?_map, hpi]; rfl) hri
    have hPsub : (fvsPl ++ xFvsP).getD i default = pxi := by
      rw [List.getD, List.getElem?_append_left (by rw [hfvsPlen]; omega),
        hpi]
      rfl
    have hBden : denote cval env ψ' (rP + cnF) (Expr.fvarTypeD pxi)
        = some Bi := by
      have h := RenEqT.denote (cval := cval) (env := env) (φ := ψ') hro
        hrenI (rP + cnF)
      rcases hrd : rdoms[i]? with _ | ri
      · rw [List.getElem?_eq_none_iff, ← hwlen, hslen] at hrd
        omega
      · rw [← h]
        exact hBi
    refine ⟨Ai, Bi, hAi, by rw [hPsub]; exact hBden, ?_⟩
    intro Δ h1 h2
    rw [if_pos hi] at h2
    exact hder Δ h1 h2
  · -- field: statement annotation ↔ `cdoms[cnP + j]` ↔ P annotation
    obtain ⟨hwlen, hwget⟩ := Forall2.length_getD hdeFld
    have hslen : ((fvs.drop rP).map Expr.fvarTypeD).length = cnF := by
      rw [List.length_map, List.length_drop, hfvslen]
      omega
    have hde := hwget (i - rP) default default (by rw [hslen]; omega)
    have hlenSpines : (psP ++ xFvsP).length
        = (psR ++ fvs.drop rP).length := by
      rw [List.length_append, List.length_append, List.length_drop,
        hpsPlen, hpsRlen, hfvslen, hxlen]
      omega
    rcases hfx : fvs[i]? with _ | fx
    · rw [List.getElem?_eq_none_iff, hfvslen] at hfx
      omega
    have hLsub : ((fvs.drop rP).map Expr.fvarTypeD).getD (i - rP) default
        = Expr.fvarTypeD (fvs.getD i default) := by
      rw [List.getD, List.getElem?_map, List.getElem?_drop,
        show rP + (i - rP) = i from by omega, hfx, List.getD, hfx]
      rfl
    have hRsub : (cdoms.drop cnP).getD (i - rP) default
        = cdoms.getD (cnP + (i - rP)) default := by
      rw [List.getD, List.getD, List.getElem?_drop]
    rw [hLsub, hRsub] at hde
    obtain ⟨Ai, Bi, hAi, hBi, hder⟩ := hde
    -- the composed canonical run's `RenEqT` alignment against `cdoms`
    have hrenD := instPisAt_renEq (psP ++ xFvsP)
      (psR ++ fvs.drop rP) hPfld hcinst hrenCvj
      (fun i0 a a' ha ha' => by
        rcases Nat.lt_or_ge i0 cnP with h0 | h0
        · rw [List.getElem?_append_left (by rw [hpsPlen]; omega)] at ha
          rw [List.getElem?_append_left (by rw [hpsRlen]; omega)] at ha'
          exact hpsRen i0 a a' ha ha'
        · rw [List.getElem?_append_right (by rw [hpsPlen]; omega),
            hpsPlen] at ha
          rw [List.getElem?_append_right (by rw [hpsRlen]; omega),
            hpsRlen, List.getElem?_drop] at ha'
          obtain ⟨nm, ty, ha2⟩ :=
            openPisAtFvars_index _ _ _ hopenXP (i0 - cnP) a ha
          obtain ⟨nm', ty', ha2'⟩ := hshapeS (rP + (i0 - cnP)) a' ha'
          rw [ha2, ha2']
          exact RenEqT.fvar)
      hlenSpines
    rcases hpi : xFvsP[i - rP]? with _ | pxi
    · rw [List.getElem?_eq_none_iff, hxlen] at hpi
      omega
    have hrenI : RenEqT f (Expr.fvarTypeD pxi)
        (cdoms.getD (cnP + (i - rP)) default) := by
      rcases hri : cdoms[cnP + (i - rP)]? with _ | ri
      · rw [List.getElem?_eq_none_iff, hcdomslen] at hri
        omega
      · rw [List.getD, hri]
        refine hrenD.1 (cnP + (i - rP)) _ _ ?_ hri
        rw [List.getElem?_append_right
            (by rw [hcdomsPlen]; omega), hcdomsPlen,
          show cnP + (i - rP) - cnP = i - rP from by omega,
          List.getElem?_map, hpi]
        rfl
    have hPsub : (fvsPl ++ xFvsP).getD i default = pxi := by
      rw [List.getD, List.getElem?_append_right (by rw [hfvsPlen]; omega),
        hfvsPlen, hpi]
      rfl
    have hBden : denote cval env ψ' (rP + cnF) (Expr.fvarTypeD pxi)
        = some Bi := by
      have h := RenEqT.denote (cval := cval) (env := env) (φ := ψ') hro
        hrenI (rP + cnF)
      rw [← h]
      exact hBi
    refine ⟨Ai, Bi, hAi, by rw [hPsub]; exact hBden, ?_⟩
    intro Δ h1 h2
    rw [if_neg (by omega)] at h2
    exact hder Δ h1 h2


set_option maxHeartbeats 6400000 in
/-- **The layer memberships** (`annotS` stage 2): each fired-spine value
inhabits the rule rhs's own λ-layer domain, denoted at its depth and
read at the prefix chain — through the satisfied statement context, the
per-position annotation identification, and the fired lam-domain walk.
This is `lamTowerStepS`'s `hmem` input. -/
theorem annotMemS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    {f : Name → Name} (hro : RenameOkT cval env f)
    {rP cnP cnF : Nat}
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {Γs : List VExpr} (hΓslen : Γs.length = rP + cnF)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    {zs : List VExpr} (hzslen : zs.length = rP + cnF)
    {ρ : Nat → V} (hsat : Sat V Γs (chainE V ρ zs))
    {Tstmt Rstmt : VExpr}
    (htowerS : PiTele (rP + cnF) Tstmt Γs Rstmt)
    {tyA tyAR : Expr} (htyw : tyA.hasFvar = false)
    (htyRw : tyAR.hasFvar = false) (hrenTy : RenEqT f tyA tyAR)
    {fvsPl : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsPl, restP))
    {cvjty cvjR : Expr} (hCvw : cvjty.hasFvar = false)
    (hCvRw : cvjR.hasFvar = false) (hrenCvj : RenEqT f cvjty cvjR)
    {psP psR : List Expr}
    (hpsPlen : psP.length = cnP) (hpsRlen : psR.length = cnP)
    (hpsRen : ∀ (i : Nat) (a a' : Expr), psP[i]? = some a →
      psR[i]? = some a' → RenEqT f a a')
    (hpsPws : ∀ a ∈ psP, Expr.WScoped rP a)
    (hpsPleaf : ∀ a ∈ psP, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl)
    (hpsRleaf : ∀ a ∈ psR, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt psP cvjty = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (psR ++ fvs.drop rP) cvjR
      = some (cdoms, cres))
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    {ldomsL : List Expr} {lrest2 : Expr}
    (hinstLam : Expr.instLamsAt (fvsPl ++ xFvsP) rhsA
      = some (ldomsL, lrest2))
    (hdePre : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hdeLam : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvsPl ++ xFvsP).map Expr.fvarTypeD) ldomsL) :
    ∀ k, k < rP + cnF →
      ∃ Dk, denote cval env ψ' k (ldomsL.getD k default) = some Dk ∧
        interp V ρ (zs.getD k default)
          ∈ˢ interp V (chainE V ρ (zs.take k)) Dk := by
  intro k hkK
  have hcl' := henv.cval_closed
  -- frame lengths and shapes
  have hfvsPlen : fvsPl.length = rP := openPisAtFvars_length _ hopenP
  have hxlen : xFvsP.length = cnF := openPisAtFvars_length _ hopenXP
  have hPlen : (fvsPl ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPlen, hxlen]
  have hPshape : ∀ (i : Nat) (x : Expr), (fvsPl ++ xFvsP)[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    rcases Nat.lt_or_ge i rP with hi | hi
    · rw [List.getElem?_append_left (by rw [hfvsPlen]; exact hi)] at hx
      obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
      exact ⟨nm, ty, by rw [hx', Nat.zero_add]⟩
    · rw [List.getElem?_append_right (by rw [hfvsPlen]; exact hi),
        hfvsPlen] at hx
      obtain ⟨nm, ty, hx'⟩ :=
        openPisAtFvars_index _ _ _ hopenXP (i - rP) x hx
      exact ⟨nm, ty, by rw [hx', show rP + (i - rP) = i from by omega]⟩
  -- frame scoping
  have hwsPre0 := openPisAtFvars_WScoped rP tyA 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  have hwsPre1 : ∀ x ∈ fvsPl, Expr.WScoped rP x := by
    intro x hx
    have h := hwsPre0.1 x hx
    rw [Nat.zero_add] at h
    exact h
  have hwsCrest : Expr.WScoped rP crestP := by
    have h := (instPisAt_WScoped (d := rP) psP cvjty hcinstP
      (Expr.WScoped.of_not_hasFvar hCvw) hpsPws).2
    exact h
  have hwsX := openPisAtFvars_WScoped cnF crestP rP hopenXP hwsCrest
  have hPws : ∀ x ∈ fvsPl ++ xFvsP, Expr.WScoped (rP + cnF) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Expr.WScoped.mono (by omega) (hwsPre1 x hx)
    · exact hwsX.1 x hx
  -- P-frame leaf closure
  have hPleafClosed : ∀ l, (∃ x ∈ fvsPl ++ xFvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl ++ xFvsP := by
    have hpre : ∀ l, (∃ x ∈ fvsPl, l ∈ x.fvarLeaves) →
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl := by
      intro l ⟨x, hx, hl⟩
      rcases openPisAtFvars_leaves _ hopenP l (Or.inr ⟨x, hx, hl⟩) with
        h0 | h0
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
        exact nomatch h0
      · exact h0
    intro l ⟨x, hx, hl⟩
    rcases List.mem_append.mp hx with hx' | hx'
    · exact List.mem_append_left _ (hpre l ⟨x, hx', hl⟩)
    · rcases openPisAtFvars_leaves _ hopenXP l (Or.inr ⟨x, hx', hl⟩) with
        h0 | h0
      · rcases instPisAt_leaves _ hcinstP l (Or.inr h0) with h1 | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCvw] at h1
          exact nomatch h1
        · exact List.mem_append_left _ (hpsPleaf a ha l hla)
      · exact List.mem_append_right _ h0
  -- statement-frame facts
  have hfvsLt : ∀ l : Nat × Name × Expr,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨nm', ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1]
    rw [hfvslen] at hql
    exact hql
  have hent : ∀ i', i' < rP + cnF →
      Γs[rP + cnF - 1 - i']? =
        some (Γs.getD (rP + cnF - 1 - i') default) := by
    intro i' hi'
    rw [List.getD]
    rcases hg : Γs[rP + cnF - 1 - i']? with _ | g
    · rw [List.getElem?_eq_none_iff, hΓslen] at hg
      omega
    · rfl
  have hCtxStmt : ∀ e : Expr,
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) →
      CtxOkR μ cval env ψ' (rP + cnF) Γs e := by
    intro e hleaf
    exact ctxOkR_of_openers (μ := μ) hcl' hΓslen hshapeS hwsFvs
      (fun i' x hx => hdomsS0 i' x hx) (n := rP + cnF) hleaf
      (fun l hl => hfvsLt l (hleaf l hl)) hent
  -- statement-frame contexts for the identification's subjects
  have hleafStmtAnn : ∀ i, i < rP + cnF →
      ∀ l ∈ (Expr.fvarTypeD (fvs.getD i default)).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro i hi l hl
    rcases hfx : fvs[i]? with _ | fx
    · rw [List.getElem?_eq_none_iff, hfvslen] at hfx
      omega
    obtain ⟨nm, ty, rfl⟩ := hshapeS i fx hfx
    rw [List.getD, hfx] at hl
    refine hleafClosed l ⟨_, List.mem_of_getElem? hfx, ?_⟩
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  have hleafRdoms : ∀ i, i < rP →
      ∀ l ∈ (rdoms.getD i default).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro i hi l hl
    have hrlen : rdoms.length = rP := by
      have h := instPisAt_length _ hrinst
      rw [List.length_take, hfvslen] at h
      omega
    have hmem : rdoms.getD i default ∈ rdoms := by
      rw [List.getD]
      rcases hr : rdoms[i]? with _ | r
      · rw [List.getElem?_eq_none_iff, hrlen] at hr
        omega
      · exact List.mem_of_getElem? hr
    rcases instPisAt_leaves _ hrinst l (Or.inl ⟨_, hmem, hl⟩) with
      h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyRw] at h0
      exact nomatch h0
    · exact hleafClosed l ⟨a, List.mem_of_mem_take ha, hla⟩
  have hleafCdoms : ∀ i, i < cnP + cnF →
      ∀ l ∈ (cdoms.getD i default).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro i hi l hl
    have hclen : cdoms.length = cnP + cnF := by
      have h := instPisAt_length _ hcinst
      rw [List.length_append, List.length_drop, hpsRlen, hfvslen] at h
      omega
    have hmem : cdoms.getD i default ∈ cdoms := by
      rw [List.getD]
      rcases hr : cdoms[i]? with _ | r
      · rw [List.getElem?_eq_none_iff, hclen] at hr
        omega
      · exact List.mem_of_getElem? hr
    rcases instPisAt_leaves _ hcinst l (Or.inl ⟨_, hmem, hl⟩) with
      h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCvRw] at h0
      exact nomatch h0
    · rcases List.mem_append.mp ha with ha' | ha'
      · exact hpsRleaf a ha' l hla
      · exact hleafClosed l ⟨a, List.mem_of_mem_drop ha', hla⟩
  -- the per-position identification, fired at the statement context
  have hIdent := annotPFrameEqS (μ := μ) hro hfvslen hshapeS
    hrenTy hopenP hrenCvj hpsPlen hpsRlen hpsRen hcinstP hopenXP
    hrinst hcinst hdePre hdeFld
  have hIdentEq : ∀ i, i < rP + cnF →
      ∃ Ai Bi,
        denote cval env ψ' (rP + cnF)
          (Expr.fvarTypeD (fvs.getD i default)) = some Ai ∧
        denote cval env ψ' (rP + cnF)
          (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD i default)) = some Bi ∧
        DefEq μ env cval ψ' Γs Ai Bi := by
    intro i hi
    obtain ⟨Ai, Bi, hAi, hBi, hder⟩ := hIdent i hi
    refine ⟨Ai, Bi, hAi, hBi, hder Γs (hCtxStmt _ (hleafStmtAnn i hi)) ?_⟩
    by_cases hip : i < rP
    · rw [if_pos hip]
      exact hCtxStmt _ (hleafRdoms i hip)
    · rw [if_neg hip]
      exact hCtxStmt _ (hleafCdoms (cnP + (i - rP)) (by omega))
  -- the P-frame slack at the statement context
  have hslackP : ∀ (i : Nat) (x : Expr), (fvsPl ++ xFvsP)[i]? = some x →
      ∃ T, denote cval env ψ' (rP + cnF) (Expr.fvarTypeD x) = some T ∧
        ∃ T', Infer μ env cval ψ' Γs
            (.bvar (rP + cnF - 1 - i)) T' ∧
          DefEq μ env cval ψ' Γs T' T := by
    intro i x hxi
    have hiK' : i < rP + cnF := by
      have := (List.getElem?_eq_some_iff.mp hxi).1
      rw [hPlen] at this
      exact this
    obtain ⟨Ai, Bi, hAi, hBi, hdefIB⟩ := hIdentEq i hiK'
    have hxg : (fvsPl ++ xFvsP).getD i default = x := by
      rw [List.getD, hxi]
      rfl
    rw [hxg] at hBi
    refine ⟨Bi, hBi,
      (Γs.getD (rP + cnF - 1 - i) default).liftN (rP + cnF - 1 - i + 1),
      Infer.bvar (hent i hiK'), ?_⟩
    -- the inferred slot is the statement annotation, lifted
    rcases hfx : fvs[i]? with _ | fx
    · rw [List.getElem?_eq_none_iff, hfvslen] at hfx
      omega
    obtain ⟨nm, ty, rfl⟩ := hshapeS i fx hfx
    have hfb : Expr.fvarsBelow i ty := by
      have hw := hwsFvs _ (List.mem_of_getElem? hfx)
      have : i < rP + cnF ∧ Expr.WScoped i ty := by
        simpa [Expr.WScoped] using hw
      exact this.2.fvarsBelow
    have hlift := denote_lift (cval := cval) (env := env) (φ := ψ') hcl'
      (p := i) (e := ty) hfb (rP + cnF) (by omega)
    have h0 := hdomsS0 i _ hfx
    rw [show Expr.fvarTypeD (Expr.fvar i nm ty) = ty from rfl] at h0
    rw [h0] at hlift
    have hAi' : Ai = (Γs.getD (rP + cnF - 1 - i) default).liftN
        (rP + cnF - i) := by
      rw [show Expr.fvarTypeD (fvs.getD i default) = ty from by
          rw [List.getD, hfx]
          rfl, hlift] at hAi
      exact (Option.some.inj hAi).symm
    rw [show rP + cnF - 1 - i + 1 = rP + cnF - i from by omega, ← hAi']
    exact hdefIB
  -- the fired lam-domain walk at position `k`
  obtain ⟨hwlenL, hwgetL⟩ := Forall2.length_getD hdeLam
  have hslenL : ((fvsPl ++ xFvsP).map Expr.fvarTypeD).length
      = rP + cnF := by
    rw [List.length_map, hPlen]
  have hdeK := hwgetL k default default (by rw [hslenL]; omega)
  have hLsubL : ((fvsPl ++ xFvsP).map Expr.fvarTypeD).getD k default
      = Expr.fvarTypeD ((fvsPl ++ xFvsP).getD k default) := by
    rcases hp : (fvsPl ++ xFvsP)[k]? with _ | px
    · rw [List.getElem?_eq_none_iff, hPlen] at hp
      omega
    · rw [List.getD, List.getElem?_map, hp, List.getD, hp]
      rfl
  rw [hLsubL] at hdeK
  obtain ⟨Bk, Lk, hBkden, hLkden, hderL⟩ := hdeK
  -- contexts for the lam walk's subjects (P-frame leaves)
  have hldomsLen : ldomsL.length = rP + cnF := by
    rw [instLamsAt_length _ hinstLam, hPlen]
  have hLkg : ldomsL.getD k default ∈ ldomsL := by
    rw [List.getD]
    rcases hr : ldomsL[k]? with _ | r
    · rw [List.getElem?_eq_none_iff, hldomsLen] at hr
      omega
    · exact List.mem_of_getElem? hr
  have hleafLdom : ∀ l ∈ (ldomsL.getD k default).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl ++ xFvsP := by
    intro l hl
    rcases instLamsAt_leaves _ hinstLam l (Or.inl ⟨_, hLkg, hl⟩) with
      h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at h0
      exact nomatch h0
    · exact hPleafClosed l ⟨a, ha, hla⟩
  have hleafPAnn : ∀ l ∈
      (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD k default)).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl ++ xFvsP := by
    intro l hl
    rcases hp : (fvsPl ++ xFvsP)[k]? with _ | px
    · rw [List.getElem?_eq_none_iff, hPlen] at hp
      omega
    obtain ⟨nm, ty, rfl⟩ := hPshape k px hp
    rw [List.getD, hp] at hl
    refine hPleafClosed l ⟨_, List.mem_of_getElem? hp, ?_⟩
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  have hctxPA : CtxOkR μ cval env ψ' (rP + cnF) Γs
      (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD k default)) :=
    ctxOkR_of_walked_openers hΓslen hPshape hPws hslackP hleafPAnn
  have hctxPL : CtxOkR μ cval env ψ' (rP + cnF) Γs
      (ldomsL.getD k default) :=
    ctxOkR_of_walked_openers hΓslen hPshape hPws hslackP hleafLdom
  have hdefL := hderL Γs hctxPA hctxPL
  -- the low-depth denote of the layer domain
  obtain ⟨mid, htkRun, hdropRun⟩ :=
    instLamsAt_take (fvsPl ++ xFvsP) k hinstLam
  have hfbLdom : Expr.fvarsBelow k (ldomsL.getD k default) := by
    -- the drop run exposes the layer as the next binder's domain
    have hdlen : ((fvsPl ++ xFvsP).drop k).length = rP + cnF - k := by
      rw [List.length_drop, hPlen]
    rcases hdp : (fvsPl ++ xFvsP).drop k with _ | ⟨x0, sp'⟩
    · rw [hdp] at hdlen
      simp at hdlen
      omega
    rw [hdp] at hdropRun
    match mid, hdropRun with
    | .lam nmM domM bodyM mM, hdropRun => ?_
    simp only [Expr.instLamsAt] at hdropRun
    cases h1 : Expr.instLamsAt sp' (bodyM.instantiate1 x0) with
    | none => rw [h1] at hdropRun; exact nomatch hdropRun
    | some p => ?_
    rw [h1] at hdropRun
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      at hdropRun
    obtain ⟨hds, -⟩ := hdropRun
    have hgd : ldomsL.getD k default = domM := by
      have h2 : ldomsL[k]? = some domM := by
        have h3 := congrArg (fun l => l[0]?) hds
        simp only [List.getElem?_drop, Nat.add_zero,
          List.getElem?_cons_zero] at h3
        exact h3.symm
      rw [List.getD, h2]
      rfl
    -- the take run's residual is scoped below `k`
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    have hlM : l ∈ (Expr.lam nmM domM bodyM mM).fvarLeaves := by
      rw [Expr.fvarLeaves]
      rw [hgd] at hl
      exact List.mem_append_left _ hl
    rcases instLamsAt_leaves _ htkRun l (Or.inr hlM) with
      h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at h0
      exact nomatch h0
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      have hql : q < k := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [List.length_take, hPlen] at this
        omega
      rw [List.getElem?_take_of_lt hql] at hq
      obtain ⟨nm, ty, rfl⟩ := hPshape q a hq
      rw [Expr.fvarLeaves] at hla
      rcases List.mem_cons.mp hla with rfl | hla'
      · exact hql
      · have hw := hPws _ (List.mem_of_getElem? hq)
        have hwty : q < rP + cnF ∧ Expr.WScoped q ty := by
          simpa [Expr.WScoped] using hw
        have := Expr.fvarLeaves_lt_of_wscoped hwty.2 l hla'
        omega
  have hliftL := denote_lift (cval := cval) (env := env) (φ := ψ') hcl'
    (p := k) (e := ldomsL.getD k default) hfbLdom (rP + cnF) (by omega)
  rw [hLkden] at hliftL
  rcases hDk : denote cval env ψ' k (ldomsL.getD k default) with _ | Dk
  · rw [hDk] at hliftL
    exact nomatch hliftL
  rw [hDk] at hliftL
  have hLkEq : Lk = Dk.liftN (rP + cnF - k) := Option.some.inj hliftL
  refine ⟨Dk, rfl, ?_⟩
  -- the satisfied context's membership at `k`
  have hm := sat_chain_mems htowerS hzslen hsat k hkK
  have hmv : (zs.map (interp V ρ)).getD k SetTheory.empty
      = interp V ρ (zs.getD k default) := by
    rw [List.getD, List.getD, List.getElem?_map]
    rcases hx : zs[k]? with _ | w
    · rw [List.getElem?_eq_none_iff, hzslen] at hx
      omega
    · rfl
  have hmc : consChain V ρ ((zs.map (interp V ρ)).take k)
      = chainE V ρ (zs.take k) := by
    rw [← List.map_take, consChain_map_interp]
  rw [hmv, hmc] at hm
  -- the ambient-set equalities, composed
  obtain ⟨Ak, Bk', hAk, hBk', hdefAB⟩ := hIdentEq k hkK
  obtain rfl : Bk = Bk' := by
    rw [hBkden] at hBk'
    exact Option.some.inj hBk'
  -- (1) the statement slot, lifted, is `Ak`
  rcases hfx : fvs[k]? with _ | fx
  · rw [List.getElem?_eq_none_iff, hfvslen] at hfx
    omega
  obtain ⟨nm, ty, rfl⟩ := hshapeS k fx hfx
  have hfb : Expr.fvarsBelow k ty := by
    have hw := hwsFvs _ (List.mem_of_getElem? hfx)
    have : k < rP + cnF ∧ Expr.WScoped k ty := by
      simpa [Expr.WScoped] using hw
    exact this.2.fvarsBelow
  have hlift := denote_lift (cval := cval) (env := env) (φ := ψ') hcl'
    (p := k) (e := ty) hfb (rP + cnF) (by omega)
  have h0 := hdomsS0 k _ hfx
  rw [show Expr.fvarTypeD (Expr.fvar k nm ty) = ty from rfl] at h0
  rw [h0] at hlift
  have hAkEq : Ak = (Γs.getD (rP + cnF - 1 - k) default).liftN
      (rP + cnF - k) := by
    rw [show Expr.fvarTypeD (fvs.getD k default) = ty from by
        rw [List.getD, hfx]
        rfl, hlift] at hAk
    exact (Option.some.inj hAk).symm
  -- the lifted interp reads the truncated chain
  have habs : ∀ X : VExpr,
      interp V (chainE V ρ zs) (X.liftN (rP + cnF - k))
        = interp V (chainE V ρ (zs.take k)) X := by
    intro X
    rw [interp_liftN, shiftE_chainE_take (by omega), hzslen,
      show rP + cnF - (rP + cnF - k) = k from by omega]
  -- interp equalities from the two fired walks
  have hIAB : interp V (chainE V ρ zs) Ak = interp V (chainE V ρ zs) Bk :=
    DefEq.sound henv hdefAB (chainE V ρ zs) hsat
  have hIBL : interp V (chainE V ρ zs) Bk = interp V (chainE V ρ zs) Lk :=
    DefEq.sound henv hdefL (chainE V ρ zs) hsat
  -- compose
  have hfinal : interp V (chainE V ρ (zs.take k))
        (Γs.getD (rP + cnF - 1 - k) default)
      = interp V (chainE V ρ (zs.take k)) Dk := by
    calc interp V (chainE V ρ (zs.take k))
          (Γs.getD (rP + cnF - 1 - k) default)
        = interp V (chainE V ρ zs)
            ((Γs.getD (rP + cnF - 1 - k) default).liftN
              (rP + cnF - k)) := (habs _).symm
      _ = interp V (chainE V ρ zs) Ak := by rw [← hAkEq]
      _ = interp V (chainE V ρ zs) Bk := hIAB
      _ = interp V (chainE V ρ zs) Lk := hIBL
      _ = interp V (chainE V ρ zs) (Dk.liftN (rP + cnF - k)) := by
          rw [← hLkEq]
      _ = interp V (chainE V ρ (zs.take k)) Dk := habs _
  rw [← hfinal]
  exact hm


set_option maxHeartbeats 1600000 in
/-- **The truthfulness transport** (`annotS`): the applied rule rhs is
hereditarily truthful — its λ-tower read through `instLamsAt_denoteTele`,
the fired spine's layer memberships from `annotMemS`, and the descent
by `lamTowerStepS`. -/
theorem annotS {μ : CheckMode} {env : Env} {cval : TConstVal}
    {ψ' : Name → Nat} (henv : EnvSHyp V env cval ψ')
    {f : Name → Name} (hro : RenameOkT cval env f)
    {rP cnP cnF : Nat}
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {Γs : List VExpr} (hΓslen : Γs.length = rP + cnF)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    {zs : List VExpr} (hzslen : zs.length = rP + cnF)
    {ρ : Nat → V} (hsat : Sat V Γs (chainE V ρ zs))
    {Tstmt Rstmt : VExpr}
    (htowerS : PiTele (rP + cnF) Tstmt Γs Rstmt)
    {tyA tyAR : Expr} (htyw : tyA.hasFvar = false)
    (htyRw : tyAR.hasFvar = false) (hrenTy : RenEqT f tyA tyAR)
    {fvsPl : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsPl, restP))
    {cvjty cvjR : Expr} (hCvw : cvjty.hasFvar = false)
    (hCvRw : cvjR.hasFvar = false) (hrenCvj : RenEqT f cvjty cvjR)
    {psP psR : List Expr}
    (hpsPlen : psP.length = cnP) (hpsRlen : psR.length = cnP)
    (hpsRen : ∀ (i : Nat) (a a' : Expr), psP[i]? = some a →
      psR[i]? = some a' → RenEqT f a a')
    (hpsPws : ∀ a ∈ psP, Expr.WScoped rP a)
    (hpsPleaf : ∀ a ∈ psP, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsPl)
    (hpsRleaf : ∀ a ∈ psR, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt psP cvjty = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (psR ++ fvs.drop rP) cvjR
      = some (cdoms, cres))
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    {ldomsL : List Expr} {lrest2 : Expr}
    (hinstLam : Expr.instLamsAt (fvsPl ++ xFvsP) rhsA
      = some (ldomsL, lrest2))
    (hdePre : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hdeLam : DefEqListW μ env cval ψ' (rP + cnF)
      ((fvsPl ++ xFvsP).map Expr.fvarTypeD) ldomsL)
    {RV : VExpr} (hRV : denote cval env ψ' 0 rhsA = some RV)
    (hRVannot : AnnotOkV V ρ RV)
    (hzsAnnot : ∀ w ∈ zs, AnnotOkV V ρ w) :
    AnnotOkV V ρ (VExpr.mkAppN RV zs) := by
  have hfvsPlen : fvsPl.length = rP := openPisAtFvars_length _ hopenP
  have hxlen : xFvsP.length = cnF := openPisAtFvars_length _ hopenXP
  have hPlen : (fvsPl ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPlen, hxlen]
  have hPshape : ∀ (i : Nat) (x : Expr), (fvsPl ++ xFvsP)[i]? = some x →
      ∃ nm ty, x = Expr.fvar (0 + i) nm ty := by
    intro i x hx
    rcases Nat.lt_or_ge i rP with hi | hi
    · rw [List.getElem?_append_left (by rw [hfvsPlen]; exact hi)] at hx
      obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
      exact ⟨nm, ty, hx'⟩
    · rw [List.getElem?_append_right (by rw [hfvsPlen]; exact hi),
        hfvsPlen] at hx
      obtain ⟨nm, ty, hx'⟩ :=
        openPisAtFvars_index _ _ _ hopenXP (i - rP) x hx
      exact ⟨nm, ty, by
        rw [hx', show rP + (i - rP) = 0 + i from by omega]⟩
  obtain ⟨Γlam, C, rfl, hΓlen, hrest, hdoms⟩ :=
    instLamsAt_denoteTele (fvsPl ++ xFvsP) hinstLam hPshape hRV
  rw [hPlen] at hΓlen
  have hldomsLen : ldomsL.length = rP + cnF := by
    rw [instLamsAt_length _ hinstLam, hPlen]
  have hmem : ∀ k, k < rP + cnF →
      interp V ρ (zs.getD k default)
        ∈ˢ interp V (chainE V ρ (zs.take k))
            (Γlam.getD (rP + cnF - 1 - k) default) := by
    intro k hk
    obtain ⟨Dk, hDkden, hmemk⟩ := annotMemS henv hro hfvslen
      hshapeS hwsFvs hleafClosed hΓslen hdomsS0 hzslen hsat htowerS
      htyw htyRw hrenTy hopenP hCvw hCvRw hrenCvj hpsPlen hpsRlen
      hpsRen hpsPws hpsPleaf hpsRleaf hcinstP hopenXP
      hrinst hcinst hrhsw hinstLam hdePre hdeFld hdeLam k hk
    have hlx : ldomsL[k]? = some (ldomsL.getD k default) := by
      rcases hr : ldomsL[k]? with _ | r
      · rw [List.getElem?_eq_none_iff, hldomsLen] at hr
        omega
      · rw [List.getD, hr]
        rfl
    have hD2 := hdoms k _ hlx
    rw [Nat.zero_add, hPlen, hDkden] at hD2
    obtain rfl : Dk = Γlam.getD (rP + cnF - 1 - k) default :=
      Option.some.inj hD2
    exact hmemk
  have hstep := lamTowerStepS (V := V) (C := C) (rP + cnF)
    (Nat.le_refl _) hΓlen hzslen hmem
  rw [List.take_of_length_le (by omega)] at hstep
  exact hstep.2 hRVannot hzsAnnot


end Setlec.SetR
