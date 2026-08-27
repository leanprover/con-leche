import Setlec.TTVerify.IndBottom

/-!
# Sealed stages of the modeled-iota bottoms (task #119, DESIGN §19.1)

The bottoms' largest proof blocks, lifted out of the monolithic
theorems so each elaborates in a small context — the landed plain
bottom peaked at 13.3 GB RSS as a single declaration.  Every lemma
here restates one of `IndBottomPlainTT`'s `have`-blocks verbatim
(same statement, essentially the same body), parameterized by the
block's free hypotheses under their original names; the main proofs
bind the lemmas back under those names, so the extraction is
proof-content-neutral.
-/

set_option maxHeartbeats 3200000

namespace Setlec.TTVerify

open Setlec.TT

/-- The frame-generic workhorse (`hopenDeqG`): an install-time
definitional equality over a frame's openers, instantiated along a
fitted prefix, padding the rest. -/
theorem openFrame_deq {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat}
    {ψ : Name → Nat} {Δ : List VExpr} {K : Nat}
    (ihd : DefEqClaimsTT m₀ ψ F) :
    ∀ (fvsF : List Expr) (ΓF : List VExpr) (mF : Nat),
    ΓF.length = mF →
    (∀ (i : Nat) (x : Expr), fvsF[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty) →
    (∀ x ∈ fvsF, Expr.WScoped (K) x) →
    (∀ (i : Nat) (x : Expr), fvsF[i]? = some x →
      denote m₀.cval env₀ (ψ) i (Expr.fvarTypeD x)
        = some (ΓF.getD (mF - 1 - i) default)) →
    ∀ (a b : Expr) (n : Nat), n ≤ mF → mF ≤ K →
    isDefEqCore env₀ F (K) a b = .ok true →
    (∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
    (∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
    Expr.WScoped n a → Expr.WScoped n b →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a → Expr.LeavesBounded b →
    ∀ {va vb : VExpr},
      denote m₀.cval env₀ (ψ) (K) a
        = some va →
      denote m₀.cval env₀ (ψ) (K) b
        = some vb →
    ∀ {ws : List VExpr}, CtxSpine Δ (ΓF.drop (mF - n)) ws →
      Deq Δ
        (VExpr.instSeq (ws ++ List.replicate (K - n) dummyPropT)
          ((ws ++ List.replicate (K - n) dummyPropT).length - 1)
          va)
        (VExpr.instSeq (ws ++ List.replicate (K - n) dummyPropT)
          ((ws ++ List.replicate (K - n) dummyPropT).length - 1)
          vb) := by
  have hcl := m₀.cval_closed
  intro fvsF ΓF mF hΓFl hshapeF hwsF hdomsF a b n hn hmF hde hla hlb
    hwa hwb hba hbb hLa hLb va vb hva hvb ws hcs
  have hΔl : (List.replicate (K - n) (VExpr.sort 0) ++
      ΓF.drop (mF - n)).length = K := by
    simp only [List.length_append, List.length_replicate,
      List.length_drop, hΓFl]
    omega
  have hent : ∀ i, i < n →
      (List.replicate (K - n) (VExpr.sort 0) ++
        ΓF.drop (mF - n))[K - 1 - i]? =
      some (ΓF.getD (mF - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
        (by rw [List.length_replicate]; omega),
      List.length_replicate, List.getElem?_drop,
      show mF - n + (K - 1 - i - (K - n)) =
        mF - 1 - i from by omega]
    simp only [List.getD]
    rw [List.getElem?_eq_getElem (show mF - 1 - i < ΓF.length from
      by omega)]
    rfl
  have hctx : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
      Expr.WScoped n e →
      CtxOk m₀.cval env₀ (ψ) (K)
        (List.replicate (K - n) (VExpr.sort 0) ++
          ΓF.drop (mF - n)) e := by
    intro e hleaf hws
    exact ctxOk_of_openers hcl hΔl hshapeF hwsF hdomsF hleaf hws hent
  have hdeq := ihd hde (hwa.mono (by omega)) hba hLa
    (hwb.mono (by omega)) hbb hLb
    (hctx a hla hwa) (hctx b hlb hwb) hva hvb
  exact Deq.instCtx (hcs.pad (K - n)) (Deq.weakenTail Δ hdeq)


/-- The parameter bridge (`hparBridge`): at each `j < cnP`, the
recursor's `j`-th instantiated domain and the constructor's are
`Deq`, along the fired prefix. -/
theorem paramBridge {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat}
    {ψ : Name → Nat} {Δ : List VExpr}
    (ihd : DefEqClaimsTT m₀ ψ F)
    {rP cnP cnF : Nat} {xs : List VExpr}
    {fvsP fvsC : List Expr} {ΓP Γj : List VExpr}
    {cdomsP : List Expr} {crestP cvjty : Expr}
    (hplainLe : cnP ≤ rP)
    (hxslen : rP ≤ xs.length)
    (hfvsPlen : fvsP.length = rP)
    (hfvsClen : fvsC.length = cnP + cnF)
    (hΓPlen : ΓP.length = rP)
    (hΓjlen : Γj.length = cnP + cnF)
    (hcdomsPlen : cdomsP.length = cnP)
    (hCw : cvjty.hasFvar = false)
    (hCb : cvjty.looseBVarsBounded 0 = true)
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvjty
      = some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hshapeC : ∀ (i : Nat) (x : Expr), fvsC[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hwsFvsP' : ∀ x ∈ fvsP, Expr.WScoped (rP + cnF) x)
    (hbAnnsP : ∀ x ∈ fvsP, (Expr.fvarTypeD x).looseBVarsBounded 0
      = true)
    (hleafP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP)
    (hLBP : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP) →
      Expr.LeavesBounded e)
    (hdomsP0' : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denote m₀.cval env₀ ψ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    (hdomsJ0' : ∀ (i : Nat) (x : Expr), fvsC[i]? = some x →
      denote m₀.cval env₀ ψ i (Expr.fvarTypeD x)
        = some (Γj.getD (cnP + cnF - 1 - i) default))
    (hPCdoms : ∀ (j : Nat) (x x' : Expr),
      ((fvsC.map Expr.fvarTypeD).take cnP)[j]? = some x →
      cdomsP[j]? = some x' → Expr.ErasedEq x x')
    (hcsRpre : ∀ j, j ≤ rP →
      CtxSpine Δ (ΓP.drop (rP - j)) (xs.take j)) :
    ∀ j, j < cnP →
    Deq Δ
      (VExpr.instSeq (xs.take j) (j - 1) (ΓP.getD (rP - 1 - j) default))
      (VExpr.instSeq (xs.take j) (j - 1)
        (Γj.getD (cnP + cnF - 1 - j) default)) := by
  have hcl := m₀.cval_closed
  have hopenDeqG := openFrame_deq (Δ := Δ) (K := rP + cnF) m₀ ihd
  intro j hj
  -- the two sides of hdePars at position j
  have hjP : j < fvsP.length := by omega
  obtain ⟨nmP, tyP, hfvsPj⟩ := hshapeP j fvsP[j]
    (List.getElem?_eq_getElem hjP)
  have hjC : j < fvsC.length := by omega
  obtain ⟨nmC, tyC, hfvsCj⟩ := hshapeC j fvsC[j]
    (List.getElem?_eq_getElem hjC)
  have haP : ((fvsP.take cnP).map Expr.fvarTypeD)[j]? = some tyP := by
    rw [List.getElem?_map, List.getElem?_take_of_lt hj,
      List.getElem?_eq_getElem hjP, hfvsPj]
    rfl
  have hbP : cdomsP[j]? = some (cdomsP.getD j default) := by
    simp [List.getD, List.getElem?_eq_getElem
      (show j < cdomsP.length from by omega)]
  have hde := DefEqListOk.pointwise hdePars j haP hbP
  -- the two sides' denotes at the frame depth
  have hwtyP : Expr.WScoped j tyP := by
    have h1 := hwsFvsP fvsP[j] (List.getElem_mem hjP)
    rw [hfvsPj] at h1
    exact ((by simpa [Expr.WScoped] using h1) :
      j < rP ∧ Expr.WScoped j tyP).2
  have hvaden : denote m₀.cval env₀ (ψ)
      (rP + cnF) tyP =
      some ((ΓP.getD (rP - 1 - j) default).liftN (rP + cnF - j)) := by
    have h1 := hdomsP0' j fvsP[j] (List.getElem?_eq_getElem hjP)
    rw [hfvsPj] at h1
    rw [show Expr.fvarTypeD (Expr.fvar j nmP tyP) = tyP from rfl] at h1
    rw [denote_lift hcl hwtyP.fvarsBelow (rP + cnF) (by omega), h1]
    rfl
  -- the constructor side: its parameter domain is the C-opening's
  have hwcdP : Expr.WScoped j (cdomsP.getD j default) := by
    have h1 := instPisAt_index_WScoped (d := 0) (fvsP.take cnP) hcinstP
      (Expr.WScoped.of_not_hasFvar hCw) ?_ j (cdomsP.getD j default) hbP
    · simpa using h1
    · intro i a ha
      have hia : i < cnP := by
        rcases Nat.lt_or_ge i cnP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take]; omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hia] at ha
      obtain ⟨nm1, ty1, rfl⟩ := hshapeP i a ha
      have h2 := hwsFvsP (Expr.fvar i nm1 ty1) (List.mem_of_getElem? ha)
      have h3 : i < rP ∧ Expr.WScoped i ty1 := by
        simpa [Expr.WScoped] using h2
      show Expr.WScoped (0 + i + 1) (Expr.fvar i nm1 ty1)
      simp only [Expr.WScoped]
      exact ⟨by omega, h3.2⟩
  have hvbden : denote m₀.cval env₀ (ψ)
      (rP + cnF) (cdomsP.getD j default) =
      some ((Γj.getD (cnP + cnF - 1 - j) default).liftN
        (rP + cnF - j)) := by
    have hee := hPCdoms j tyC (cdomsP.getD j default)
      (by rw [List.getElem?_take_of_lt hj, List.getElem?_map,
        List.getElem?_eq_getElem hjC, hfvsCj]; rfl) hbP
    have h1 := hdomsJ0' j fvsC[j] (List.getElem?_eq_getElem hjC)
    rw [hfvsCj] at h1
    rw [show Expr.fvarTypeD (Expr.fvar j nmC tyC) = tyC from rfl] at h1
    rw [denote_lift hcl hwcdP.fvarsBelow (rP + cnF) (by omega),
      ← denote_erasedEq hee j, h1]
    rfl
  -- leaves
  have hlaP : ∀ l ∈ tyP.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro l hl
    refine hleafP l ⟨fvsP[j], List.getElem_mem hjP, ?_⟩
    rw [hfvsPj, Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  have hlbP : ∀ l ∈ (cdomsP.getD j default).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro l hl
    rcases instPisAt_leaves _ hcinstP l
        (Or.inl ⟨cdomsP.getD j default,
          List.mem_of_getElem? hbP, hl⟩) with h1 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at h1
      exact nomatch h1
    · exact hleafP l ⟨a, List.mem_of_mem_take ha, hla⟩
  -- bounds
  have hbaP : tyP.looseBVarsBounded 0 = true := by
    have h1 := hbAnnsP fvsP[j] (List.getElem_mem hjP)
    rw [hfvsPj] at h1
    exact h1
  have hspBounded : ∀ a ∈ fvsP.take cnP, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
    obtain ⟨nm1, ty1, rfl⟩ := hshapeP q a hq
    rfl
  have hbbP : (cdomsP.getD j default).looseBVarsBounded 0 = true := by
    obtain ⟨h1, -⟩ := instPisAt_bounded (fvsP.take cnP) hcinstP hCb
      hspBounded
    exact h1 _ (List.mem_of_getElem? hbP)
  have hgen := hopenDeqG fvsP ΓP rP hΓPlen hshapeP hwsFvsP' hdomsP0'
    tyP (cdomsP.getD j default) j (by omega) (by omega) hde
    hlaP hlbP hwtyP hwcdP hbaP hbbP (hLBP _ hlaP) (hLBP _ hlbP)
    hvaden hvbden (hcsRpre j (by omega))
  have hlen1 : (xs.take j).length = j := by
    rw [List.length_take]
    omega
  have habs1 := instSeq_append_absorb (xs.take j)
    (List.replicate (rP + cnF - j) dummyPropT)
    (ΓP.getD (rP - 1 - j) default)
  have habs2 := instSeq_append_absorb (xs.take j)
    (List.replicate (rP + cnF - j) dummyPropT)
    (Γj.getD (cnP + cnF - 1 - j) default)
  rw [hlen1, List.length_replicate,
    show j + (rP + cnF - j) - 1 = rP + cnF - 1 from by omega]
    at habs1 habs2
  rw [List.length_append, hlen1, List.length_replicate,
    show j + (rP + cnF - j) - 1 = rP + cnF - 1 from by omega,
    habs1, habs2] at hgen
  exact hgen

/-- A padded fired spine resolves a frame variable to its slot's value
(`hpadhit`). -/
theorem padHit {K : Nat} :
    ∀ (n p : Nat) (vals : List VExpr), p < n →
    vals.length = n → n ≤ K →
    VExpr.instSeq (vals ++ List.replicate (K - n) dummyPropT)
      (K - 1) (.bvar (K - 1 - p)) =
      vals.getD p default := by
  intro n p vals hp hvl hn
  have hlenT : (vals ++ List.replicate (K - n) dummyPropT).length
      = K := by
    simp only [List.length_append, List.length_replicate, hvl]
    omega
  have hidx : (vals ++ List.replicate (K - n)
      dummyPropT)[(vals ++ List.replicate (K - n)
        dummyPropT).length - 1 - (K - 1 - p)]? =
      some (vals.getD p default) := by
    rw [hlenT, show K - 1 - (K - 1 - p) = p from by omega,
      List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega : p < vals.length)]
    simp [List.getD, List.getElem?_eq_getElem
      (by omega : p < vals.length)]
  have h1 := VExpr.instSeq_bvar_hit
    (vals ++ List.replicate (K - n) dummyPropT) 0
    (K - 1 - p) (vals.getD p default) hidx (by omega)
  simp only [Nat.zero_add] at h1
  rw [hlenT] at h1
  rw [h1, VExpr.liftN_zero]

set_option maxHeartbeats 6400000 in
/-- The statement fitting (`hzip`, the zipper): the fired spine
`xs.take rP ++ ys.drop cnP` fits the checked statement's telescope,
each position's typing converted from the fire site's fittings along
the install's opened definitional equalities. -/
theorem zipperStage {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat}
    {ψ : Name → Nat} {Δ : List VExpr}
    (ihd : DefEqClaimsTT m₀ ψ F)
    {f : Name → Name} (hro : RenameOkT m₀.cval env₀ f)
    {rP cnP cnF mI : Nat} {xs ys : List VExpr}
    {fvs fvsP : List Expr} {Γs ΓP Γj : List VExpr}
    {Tstmt Rbody TVj Rj : VExpr}
    {tyA cvjty : Expr} {cdoms rdoms : List Expr} {cres rrest : Expr}
    (hplainLe : cnP ≤ rP) (_hrPmI : rP ≤ mI)
    (_hlenX : xs.length = mI) (hlenY : ys.length = cnP + cnF)
    (hfvslen : fvs.length = rP + cnF) (hfvsPlen : fvsP.length = rP)
    (hΓslen : Γs.length = rP + cnF) (hΓPlen : ΓP.length = rP)
    (hΓjlen : Γj.length = cnP + cnF)
    (hcdomslen : cdoms.length = cnP + cnF)
    (hrdomslen : rdoms.length = rP)
    (htyw : tyA.hasFvar = false) (htyb : tyA.looseBVarsBounded 0 = true)
    (hCw : cvjty.hasFvar = false) (hCb : cvjty.looseBVarsBounded 0 = true)
    (hTVj0 : denote m₀.cval env₀ ψ 0 cvjty = some TVj)
    (htowerS : PiTele (rP + cnF) Tstmt Γs Rbody)
    (htowerJ : PiTele (cnP + cnF) TVj Γj Rj)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hbAnns : ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hleafS : ∀ l, (l ∈ ([] : List (Nat × Name × Expr)) ∨
        ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hLB : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) →
      Expr.LeavesBounded e)
    (hdomsS0' : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote m₀.cval env₀ ψ i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    (hxstakelen : (xs.take rP).length = rP)
    (hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF)
    (hzsget : ∀ p, p < rP + cnF →
      (xs.take rP ++ ys.drop cnP).getD p default =
        (if p < rP then xs.getD p default
         else ys.getD (cnP + (p - rP)) default))
    (hzstake : ∀ n, n ≤ rP →
      (xs.take rP ++ ys.drop cnP).take n = xs.take n)
    (hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF)
    (hspIdx : ∀ (q : Nat), q < cnP + cnF →
      ∃ nm t, (fvs.take cnP ++ fvs.drop rP)[q]? =
        some (Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm t))
    (hspFacts : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      (∃ i nm t, x = Expr.fvar i nm t) ∧ Expr.WScoped (rP + cnF) x ∧
        x.looseBVarsBounded 0 = true)
    (hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF)
    (hmixget : ∀ p, p < cnP + cnF →
      (xs.take cnP ++ ys.drop cnP).getD p default =
        (if p < cnP then xs.getD p default else ys.getD p default))
    (hstepsR : ∀ n, n < (xs.take rP).length →
      HasType Δ ((xs.take rP).getD n default)
        (VExpr.instSeq ((xs.take rP).take n) (n - 1)
          (ΓP.getD ((xs.take rP).length - 1 - n) default)))
    (hstepsMix : ∀ n, n < (xs.take cnP ++ ys.drop cnP).length →
      HasType Δ ((xs.take cnP ++ ys.drop cnP).getD n default)
        (VExpr.instSeq ((xs.take cnP ++ ys.drop cnP).take n) (n - 1)
          (Γj.getD ((xs.take cnP ++ ys.drop cnP).length - 1 - n)
            default)))
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f) =
      some (rdoms, rrest))
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvjty.renameConsts f) = some (cdoms, cres))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hPRdoms : ∀ (j : Nat) (x x' : Expr),
      (fvsP.map Expr.fvarTypeD)[j]? = some x →
      rdoms[j]? = some x' → RenEqT f x x')
    (hdomsP0' : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denote m₀.cval env₀ ψ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default)) :
    VTeleTyped Δ Tstmt (xs.take rP ++ ys.drop cnP)
    (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
      ((xs.take rP ++ ys.drop cnP).length - 1) Rbody) := by
  have hcl := m₀.cval_closed
  have hopenDeqG := openFrame_deq (Δ := Δ) (K := rP + cnF) m₀ ihd
  have hpadhit := padHit (K := rP + cnF)
  have htowerS' : PiTele (xs.take rP ++ ys.drop cnP).length Tstmt Γs
      Rbody := by
    rw [hzslen]
    exact htowerS
  refine VTeleTyped.ofPiTele htowerS' ?_
  intro n hn hpref
  rw [hzslen] at hn
  obtain ⟨mid, hmid⟩ := hpref
  obtain ⟨midS2, hpreS, -⟩ := PiTele.prefix htowerS n (by omega)
  have hztklen : ((xs.take rP ++ ys.drop cnP).take n).length = n := by
    rw [List.length_take, hzslen]
    omega
  have hcsZ : CtxSpine Δ (Γs.drop (rP + cnF - n))
      ((xs.take rP ++ ys.drop cnP).take n) := by
    refine hmid.toCtxSpine (Γ := Γs.drop (rP + cnF - n))
      (R := midS2) ?_
    rw [hztklen]
    exact hpreS
  -- the statement's n-th annotation
  have hnfvs : n < fvs.length := by omega
  obtain ⟨nmS, tyS, hfvsn⟩ := hshapeS n fvs[n]
    (List.getElem?_eq_getElem hnfvs)
  have hwtyS : Expr.WScoped n tyS := by
    have h1 := hwsFvs fvs[n] (List.getElem_mem hnfvs)
    rw [hfvsn] at h1
    exact ((by simpa [Expr.WScoped] using h1) :
      n < rP + cnF ∧ Expr.WScoped n tyS).2
  have hvaden : denote m₀.cval env₀ (ψ)
      (rP + cnF) tyS =
      some ((Γs.getD (rP + cnF - 1 - n) default).liftN
        (rP + cnF - n)) := by
    have h1 := hdomsS0' n fvs[n] (List.getElem?_eq_getElem hnfvs)
    rw [hfvsn] at h1
    rw [show Expr.fvarTypeD (Expr.fvar n nmS tyS) = tyS from rfl] at h1
    rw [denote_lift hcl hwtyS.fvarsBelow (rP + cnF) (by omega), h1]
    rfl
  have hlaS : ∀ l ∈ tyS.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l hl
    refine hleafS l (Or.inr ⟨fvs[n], List.getElem_mem hnfvs, ?_⟩)
    rw [hfvsn, Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  have hbaS : tyS.looseBVarsBounded 0 = true := by
    have h1 := hbAnns fvs[n] (List.getElem_mem hnfvs)
    rw [hfvsn] at h1
    exact h1
  by_cases hnrP : n < rP
  · -- a parameter/motive/minor position: the recursor's fitting,
    -- converted along the opened-domain agreement
    have haS : ((fvs.take rP).map Expr.fvarTypeD)[n]? = some tyS := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hnrP,
        List.getElem?_eq_getElem hnfvs, hfvsn]
      rfl
    have hbS : rdoms[n]? = some (rdoms.getD n default) := by
      simp [List.getD, List.getElem?_eq_getElem
        (show n < rdoms.length from by omega)]
    have hde := DefEqListOk.pointwise hdePre n haS hbS
    -- the renamed recursor domain denotes to the P-tower's entry
    have hwrd : Expr.WScoped n (rdoms.getD n default) := by
      have h1 := instPisAt_index_WScoped (d := 0) (fvs.take rP) hrinst
        (Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact htyw)) ?_ n (rdoms.getD n default) hbS
      · simpa using h1
      · intro i a ha
        have hia : i < rP := by
          rcases Nat.lt_or_ge i rP with h | h
          · exact h
          · rw [List.getElem?_eq_none (by
              rw [List.length_take, hfvslen]; omega)] at ha
            exact nomatch ha
        rw [List.getElem?_take_of_lt hia] at ha
        obtain ⟨nm1, ty1, rfl⟩ := hshapeS i a ha
        have h2 := hwsFvs (Expr.fvar i nm1 ty1) (List.mem_of_getElem? ha)
        have h3 : i < rP + cnF ∧ Expr.WScoped i ty1 := by
          simpa [Expr.WScoped] using h2
        show Expr.WScoped (0 + i + 1) (Expr.fvar i nm1 ty1)
        simp only [Expr.WScoped]
        exact ⟨by omega, h3.2⟩
    have hvbden : denote m₀.cval env₀ (ψ)
        (rP + cnF) (rdoms.getD n default) =
        some ((ΓP.getD (rP - 1 - n) default).liftN
          (rP + cnF - n)) := by
      have hjP : n < fvsP.length := by omega
      obtain ⟨nmP, tyP, hfvsPn⟩ := hshapeP n fvsP[n]
        (List.getElem?_eq_getElem hjP)
      have hre := hPRdoms n tyP (rdoms.getD n default)
        (by rw [List.getElem?_map, List.getElem?_eq_getElem hjP,
          hfvsPn]; rfl) hbS
      have h1 := hdomsP0' n fvsP[n] (List.getElem?_eq_getElem hjP)
      rw [hfvsPn] at h1
      rw [show Expr.fvarTypeD (Expr.fvar n nmP tyP) = tyP from rfl] at h1
      rw [denote_lift hcl hwrd.fvarsBelow (rP + cnF) (by omega),
        RenEqT.denote hro hre n, h1]
      rfl
    have hlbS : ∀ l ∈ (rdoms.getD n default).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
      intro l hl
      rcases instPisAt_leaves _ hrinst l
          (Or.inl ⟨rdoms.getD n default,
            List.mem_of_getElem? hbS, hl⟩) with h1 | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_renameConsts]; exact htyw)] at h1
        exact nomatch h1
      · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha, hla⟩)
    have hbbS : (rdoms.getD n default).looseBVarsBounded 0 = true := by
      have hspb : ∀ a ∈ fvs.take rP, a.looseBVarsBounded 0 = true := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
        obtain ⟨nm1, ty1, rfl⟩ := hshapeS q a hq
        rfl
      obtain ⟨h1, -⟩ := instPisAt_bounded (fvs.take rP) hrinst
        (by rw [Expr.looseBVarsBounded_renameConsts]; exact htyb) hspb
      exact h1 _ (List.mem_of_getElem? hbS)
    have hgen := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
      hdomsS0' tyS (rdoms.getD n default) n (by omega) (by omega) hde
      hlaS hlbS hwtyS hwrd hbaS hbbS (hLB _ hlaS) (hLB _ hlbS)
      hvaden hvbden hcsZ
    have habs1 := instSeq_append_absorb
      ((xs.take rP ++ ys.drop cnP).take n)
      (List.replicate (rP + cnF - n) dummyPropT)
      (Γs.getD (rP + cnF - 1 - n) default)
    have habs2 := instSeq_append_absorb
      ((xs.take rP ++ ys.drop cnP).take n)
      (List.replicate (rP + cnF - n) dummyPropT)
      (ΓP.getD (rP - 1 - n) default)
    rw [hztklen, List.length_replicate,
      show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega]
      at habs1 habs2
    rw [List.length_append, hztklen, List.length_replicate,
      show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega,
      habs1, habs2] at hgen
    -- the source typing, from the recursor's own fitting
    have hsrc := hstepsR n (by rw [hxstakelen]; omega)
    rw [hxstakelen, List.take_take, Nat.min_eq_left (by omega : n ≤ rP),
      show (xs.take rP).getD n default = xs.getD n default from by
        simp only [List.getD]
        rw [List.getElem?_take_of_lt hnrP]] at hsrc
    rw [show (xs.take rP ++ ys.drop cnP).getD n default =
        xs.getD n default from by
      rw [hzsget n (by omega), if_pos hnrP],
      show (xs.take rP ++ ys.drop cnP).length - 1 - n =
        rP + cnF - 1 - n from by rw [hzslen],
      hzstake n (by omega)]
    rw [hzstake n (by omega)] at hgen
    exact Deq.conv hsrc (Deq.symm hgen)
  · -- a field position: the mixed constructor fitting, converted
    -- through the scattered install run
    have hnnrP : rP ≤ n := by omega
    have hXlt : cnP + (n - rP) < cnP + cnF := by omega
    -- the install fact at this field
    have haF : ((fvs.drop rP).map Expr.fvarTypeD)[n - rP]? =
        some tyS := by
      rw [List.getElem?_map, List.getElem?_drop,
        show rP + (n - rP) = n from by omega,
        List.getElem?_eq_getElem hnfvs, hfvsn]
      rfl
    have hbF : (cdoms.drop cnP)[n - rP]? =
        some (cdoms.getD (cnP + (n - rP)) default) := by
      rw [List.getElem?_drop]
      simp [List.getD, List.getElem?_eq_getElem
        (show cnP + (n - rP) < cdoms.length from by omega)]
    have hde := DefEqListOk.pointwise hdeFld (n - rP) haF hbF
    -- the truncated scattered run and the field's domain
    obtain ⟨midE, htakeE, hdropE⟩ :=
      instPisAt_take (fvs.take cnP ++ fvs.drop rP)
        (cnP + (n - rP)) hcinst
    rw [List.drop_eq_getElem_cons (by rw [hsplen]; omega)] at hdropE
    match hmidE : midE, hdropE with
    | .forallE nmE domE bodyE mbE, hdropE => ?_
    simp only [Expr.instPisAt] at hdropE
    cases h1 : Expr.instPisAt
        ((fvs.take cnP ++ fvs.drop rP).drop (cnP + (n - rP) + 1))
        (bodyE.instantiate1
          (fvs.take cnP ++ fvs.drop rP)[cnP + (n - rP)]) with
    | none => rw [h1] at hdropE; exact nomatch hdropE
    | some pE => ?_
    rw [h1] at hdropE
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      at hdropE
    have hdomE' : cdoms.getD (cnP + (n - rP)) default = domE := by
      have h2 : (cdoms.drop (cnP + (n - rP)))[0]? = some domE := by
        rw [← hdropE.1]
        rfl
      rw [List.getElem?_drop, Nat.add_zero] at h2
      simp [List.getD, h2]
    rw [hdomE'] at hde
    -- the spine of the truncated run, scoped at n
    have hspTakeFacts : ∀ (q : Nat) (x : Expr),
        ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))[q]? =
          some x →
        (∃ i nm t, x = Expr.fvar i nm t) ∧
          Expr.WScoped (rP + cnF) x ∧
          x.looseBVarsBounded 0 = true := by
      intro q x hx
      have hq : q < cnP + (n - rP) := by
        rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take, hsplen]; omega)] at hx
          exact nomatch hx
      rw [List.getElem?_take_of_lt hq] at hx
      exact hspFacts q x hx
    have hspTakeWSn : ∀ a ∈ (fvs.take cnP ++ fvs.drop rP).take
        (cnP + (n - rP)), Expr.WScoped n a := by
      intro a ha
      obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      have hqlt : q < cnP + (n - rP) := by
        rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take, hsplen]; omega)] at hq
          exact nomatch hq
      rw [List.getElem?_take_of_lt hqlt] at hq
      obtain ⟨⟨i0, nm0, t0, rfl⟩, hwsK, -⟩ := hspFacts q a hq
      obtain ⟨nm1, t1, hq1⟩ := hspIdx q (by omega)
      have heq := Option.some.inj (hq.symm.trans hq1)
      injection heq with heqi heqn heqt
      have hidx : i0 < n := by
        rw [heqi]
        by_cases hqc : q < cnP
        · rw [if_pos hqc]
          omega
        · rw [if_neg hqc]
          omega
      have hK : i0 < rP + cnF ∧ Expr.WScoped i0 t0 := by
        simpa [Expr.WScoped] using hwsK
      simp only [Expr.WScoped]
      exact ⟨hidx, hK.2⟩
    -- the field domain's own facts
    have hdomEmem : cdoms.getD (cnP + (n - rP)) default ∈ cdoms := by
      refine List.mem_of_getElem? (i := cnP + (n - rP)) ?_
      simp [List.getD, List.getElem?_eq_getElem
        (show cnP + (n - rP) < cdoms.length from by omega)]
    have hwdomE : Expr.WScoped n domE := by
      obtain ⟨-, hmidW⟩ := instPisAt_WScoped (d := n)
        ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))
        (cvjty.renameConsts f) htakeE
        (Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hCw))
        hspTakeWSn
      exact ((by simpa [Expr.WScoped] using hmidW) :
        Expr.WScoped n domE ∧ Expr.WScoped n bodyE).1
    have hlbF : ∀ l ∈ domE.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
      intro l hl
      rw [← hdomE'] at hl
      rcases instPisAt_leaves _ hcinst l
          (Or.inl ⟨cdoms.getD (cnP + (n - rP)) default, hdomEmem, hl⟩)
        with h1 | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_renameConsts]; exact hCw)] at h1
        exact nomatch h1
      · rcases List.mem_append.mp ha with ha' | ha'
        · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha', hla⟩)
        · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_drop ha', hla⟩)
    have hbbF : domE.looseBVarsBounded 0 = true := by
      have hspb : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
          a.looseBVarsBounded 0 = true := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        exact (hspFacts q a hq).2.2
      obtain ⟨h1, -⟩ := instPisAt_bounded _ hcinst
        (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb) hspb
      rw [← hdomE']
      exact h1 _ hdomEmem
    -- the truncated run's residual denotes at the frame
    have hTVjK : denote m₀.cval env₀ (ψ)
        (rP + cnF) (cvjty.renameConsts f) = some TVj := by
      rw [denote_renameConsts hro,
        denote_depth_closed hcl hCw hCb (rP + cnF)]
      exact hTVj0
    obtain ⟨vMidE, hvMidE⟩ := instPisAt_fvar_denote_defined hcl _
      htakeE (fun q x hx => by
        obtain ⟨⟨i0, nm0, t0, rfl⟩, hw1, hb1⟩ := hspTakeFacts q x hx
        exact ⟨⟨VExpr.bvar (rP + cnF - 1 - i0), by rw [denote_fvar]⟩,
          hw1, hb1⟩)
      ((Expr.WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]; exact hCw)
        (d := rP + cnF)).fvarsBelow)
      (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
      hTVjK
    rw [denote_forallE] at hvMidE
    cases hAE : denote m₀.cval env₀ (ψ)
        (rP + cnF) domE with
    | none => rw [hAE] at hvMidE; exact nomatch hvMidE
    | some AE => ?_
    rw [hAE] at hvMidE
    cases hBE : denote m₀.cval env₀ (ψ)
        (rP + cnF + 1) (bodyE.instantiate1
          (.fvar (rP + cnF) nmE domE)) with
    | none => rw [hBE] at hvMidE; exact nomatch hvMidE
    | some BE => ?_
    rw [hBE] at hvMidE
    obtain rfl : vMidE = .pi AE BE := (Option.some.inj hvMidE).symm
    -- the workhorse: the statement's field domain against the run's
    have hgen := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
      hdomsS0' tyS domE n (by omega) (by omega) (hdomE' ▸ hde)
      hlaS hlbF hwtyS hwdomE hbaS hbbF (hLB _ hlaS) (hLB _ hlbF)
      hvaden hAE hcsZ
    have habsL := instSeq_append_absorb
      ((xs.take rP ++ ys.drop cnP).take n)
      (List.replicate (rP + cnF - n) dummyPropT)
      (Γs.getD (rP + cnF - 1 - n) default)
    rw [hztklen, List.length_replicate,
      show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega]
      at habsL
    rw [List.length_append, hztklen, List.length_replicate,
      show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega,
      habsL] at hgen
    -- the cross-frame identification
    have hvalslen : (((xs.take rP ++ ys.drop cnP).take n) ++
        List.replicate (rP + cnF - n) dummyPropT).length = rP + cnF := by
      simp only [List.length_append, List.length_replicate, hztklen]
      omega
    obtain ⟨midJ, hpreJ1, hpreJ2⟩ := PiTele.prefix htowerJ
      (cnP + (n - rP)) (by omega)
    have hTVjClosed : VExpr.Closed TVj :=
      denote_closed hcl hCw hCb hTVj0
    have hsptklen : ((fvs.take cnP ++ fvs.drop rP).take
        (cnP + (n - rP))).length = cnP + (n - rP) := by
      rw [List.length_take, hsplen]
      omega
    have htowerX : PiTele ((fvs.take cnP ++ fvs.drop rP).take
        (cnP + (n - rP))).length
        (VExpr.instSeq ((xs.take rP ++ ys.drop cnP).take n ++
          List.replicate (rP + cnF - n) dummyPropT) (rP + cnF - 1) TVj)
        (Γj.drop (cnP + cnF - (cnP + (n - rP)))) midJ := by
      rw [VExpr.instSeq_eq_self_of_closed hTVjClosed, hsptklen]
      exact hpreJ1
    have hwsXlen : ((xs.take cnP ++ ys.drop cnP).take
        (cnP + (n - rP))).length =
        ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP))).length := by
      rw [hsptklen, List.length_take, hmixlen]
      omega
    have hwsCond : ∀ (q i0 : Nat) (nm0 : Name) (t0 : Expr),
        ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))[q]? =
          some (Expr.fvar i0 nm0 t0) →
        ((xs.take cnP ++ ys.drop cnP).take (cnP + (n - rP)))[q]? =
          some (VExpr.instSeq ((xs.take rP ++ ys.drop cnP).take n ++
            List.replicate (rP + cnF - n) dummyPropT) (rP + cnF - 1)
            (.bvar (rP + cnF - 1 - i0))) := by
      intro q i0 nm0 t0 hq
      have hqlt : q < cnP + (n - rP) := by
        rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take, hsplen]; omega)] at hq
          exact nomatch hq
      rw [List.getElem?_take_of_lt hqlt] at hq
      obtain ⟨nm1, t1, hq1⟩ := hspIdx q (by omega)
      have heq := Option.some.inj (hq.symm.trans hq1)
      injection heq with heqi heqn heqt
      have hi0n : i0 < n := by
        rw [heqi]
        by_cases hqc : q < cnP
        · rw [if_pos hqc]
          omega
        · rw [if_neg hqc]
          omega
      rw [List.getElem?_take_of_lt hqlt,
        hpadhit n i0 ((xs.take rP ++ ys.drop cnP).take n) hi0n hztklen
          (by omega)]
      have hqm : q < cnP + cnF := by omega
      rw [List.getElem?_eq_getElem (show q < (xs.take cnP ++
        ys.drop cnP).length from by rw [hmixlen]; omega)]
      have hmixq : (xs.take cnP ++ ys.drop cnP)[q] =
          (xs.take cnP ++ ys.drop cnP).getD q default := by
        simp [List.getD, List.getElem?_eq_getElem
          (show q < (xs.take cnP ++ ys.drop cnP).length from by
            rw [hmixlen]; omega)]
      rw [hmixq, hmixget q hqm]
      -- align the selected value with the frame's
      have hzi0 : ((xs.take rP ++ ys.drop cnP).take n).getD i0 default =
          (xs.take rP ++ ys.drop cnP).getD i0 default := by
        simp only [List.getD]
        rw [List.getElem?_take_of_lt hi0n]
      rw [hzi0, hzsget i0 (by omega)]
      by_cases hqc : q < cnP
      · rw [if_pos hqc,
          show i0 = q from by rw [heqi, if_pos hqc],
          if_pos (show q < rP from by omega)]
      · rw [if_neg hqc,
          show i0 = rP + (q - cnP) from by rw [heqi, if_neg hqc],
          if_neg (show ¬ rP + (q - cnP) < rP from by omega),
          show cnP + (rP + (q - cnP) - rP) = q from by omega]
    have hvMidE2 : denote m₀.cval env₀ (ψ)
        (rP + cnF) (Expr.forallE nmE domE bodyE mbE) =
        some (.pi AE BE) := by
      rw [denote_forallE, hAE, hBE]
    have hcross := instPisAt_denote_cross hcl
      ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP))) htakeE
      hvalslen (fun j x hx => (hspTakeFacts j x hx).2)
      ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) (by
        rw [hasFvar_renameConsts]; exact hCw)).fvarsBelow)
      (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
      hTVjK hvMidE2 hwsXlen
      (fun j x hx => by
        obtain ⟨⟨i, nm, t, rfl⟩, -, -⟩ := hspTakeFacts j x hx
        exact ⟨VExpr.bvar (rP + cnF - 1 - i), by rw [denote_fvar],
          hwsCond j i nm t hx⟩)
      htowerX
    -- read the head domain off both sides
    rw [VExpr.instSeq_pi _ _ _ _ (by rw [hvalslen]; omega)] at hcross
    obtain ⟨SJ, hSJ⟩ : ∃ SJ, cnP + cnF - (cnP + (n - rP)) = SJ + 1 :=
      ⟨cnP + cnF - (cnP + (n - rP)) - 1, by omega⟩
    rw [hSJ] at hpreJ2
    obtain ⟨BJ, hmidJpi, -⟩ := hpreJ2.head
    rw [hmidJpi, VExpr.instSeq_pi _ _ _ _ (by
      rw [hwsXlen, hsptklen]; omega)] at hcross
    obtain ⟨hh1, -⟩ := (VExpr.pi.injEq _ _ _ _).mp hcross
    have hentry : (Γj.take (SJ + 1)).getD SJ default =
        Γj.getD SJ default := by
      simp only [List.getD]
      rw [List.getElem?_take_of_lt (by omega)]
    rw [hentry,
      show ((xs.take cnP ++ ys.drop cnP).take (cnP + (n - rP))).length
        = cnP + (n - rP) from by rw [List.length_take, hmixlen]; omega]
      at hh1
    rw [hh1] at hgen
    -- the source typing from the mixed fitting
    have hsrc := hstepsMix (cnP + (n - rP)) (by rw [hmixlen]; omega)
    rw [show (xs.take cnP ++ ys.drop cnP).length - 1 - (cnP + (n - rP))
        = SJ from by rw [hmixlen]; omega,
      show (xs.take cnP ++ ys.drop cnP).getD (cnP + (n - rP)) default
        = ys.getD (cnP + (n - rP)) default from by
        rw [hmixget _ (by omega), if_neg (by omega)]] at hsrc
    -- align the goal and close
    rw [show (xs.take rP ++ ys.drop cnP).getD n default =
        ys.getD (cnP + (n - rP)) default from by
      rw [hzsget n (by omega), if_neg (by omega)],
      show (xs.take rP ++ ys.drop cnP).length - 1 - n =
        rP + cnF - 1 - n from by rw [hzslen]]
    exact Deq.conv hsrc (Deq.symm hgen)

set_option maxHeartbeats 6400000 in
/-- The pointwise correspondence over the redex's spine (`hpt`,
Stage J): each position of the law's left spine is `Deq` to the
statement's, instantiated at the fired spine — prefix positions by
the frame, index positions through `IotaIndexPin` and the crossed
residual, the major through the parameter pin. -/
theorem pointStage {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat}
    {φ : Name → Nat} {lps : List Name} {us usj : List Level}
    {Δ : List VExpr}
    (ihd : DefEqClaimsTT m₀ (Level.substFn φ lps us) F)
    {f : Name → Name} (hro : RenameOkT m₀.cval env₀ f)
    {ctor : Name} {cvj : ConstantVal} {ciCm : ConstantInfo}
    (hfCmE : env₀.find? (f ctor) = some ciCm)
    (hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p = Level.substFn φ lps us p)
    {rP cnP cnF mI : Nat} {xs ys : List VExpr}
    {vHC restC : VExpr} {vLargs vCargs vArgsC : List VExpr}
    {fvs : List Expr} {lhsS : Expr} {Γs Γj : List VExpr}
    {cvjty cres : Expr} {cdoms : List Expr}
    (hplainLe : cnP ≤ rP) (hrPmI : rP ≤ mI)
    (hlenX : xs.length = mI) (hlenY : ys.length = cnP + cnF)
    (_hlenJ : usj.length = cvj.levelParams.length)
    (hfvslen : fvs.length = rP + cnF)
    (hΓslen : Γs.length = rP + cnF)
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hCw : cvjty.hasFvar = false)
    (hCb : cvjty.looseBVarsBounded 0 = true)
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvjty.renameConsts f) = some (cdoms, cres))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hpar : ∀ i, i < cnP → i < mI →
      Deq Δ (ys.getD i default) (xs.getD i default))
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hleafS : ∀ l, (l ∈ ([] : List (Nat × Name × Expr)) ∨
        ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hLB : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) →
      Expr.LeavesBounded e)
    (hdomsS0' : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote m₀.cval env₀ (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    (hctorE : env₀.find? ctor = some (.ctorInfo cvj cnP cnF))
    (hwsL : Expr.WScoped (rP + cnF) lhsS)
    (hbL : lhsS.looseBVarsBounded 0 = true)
    (hlfL : ∀ l ∈ lhsS.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hvLargslen : vLargs.length = mI + 1)
    (hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF)
    (hzsget : ∀ p, p < rP + cnF →
      (xs.take rP ++ ys.drop cnP).getD p default =
        (if p < rP then xs.getD p default
         else ys.getD (cnP + (p - rP)) default))
    (hzsel : ∀ q, q < rP + cnF →
      VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        (.bvar (rP + cnF - 1 - q)) =
        (xs.take rP ++ ys.drop cnP).getD q default)
    (hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF)
    (hspIdx : ∀ (q : Nat), q < cnP + cnF →
      ∃ nm t, (fvs.take cnP ++ fvs.drop rP)[q]? =
        some (Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm t))
    (hspFacts : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      (∃ i nm t, x = Expr.fvar i nm t) ∧ Expr.WScoped (rP + cnF) x ∧
        x.looseBVarsBounded 0 = true)
    (hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF)
    (hmixget : ∀ p, p < cnP + cnF →
      (xs.take cnP ++ ys.drop cnP).getD p default =
        (if p < cnP then xs.getD p default else ys.getD p default))
    (hcsC : CtxSpine Δ Γj ys)
    (hcsMix : CtxSpine Δ Γj (xs.take cnP ++ ys.drop cnP))
    (hcsZfull : CtxSpine Δ Γs (xs.take rP ++ ys.drop cnP))
    (hspL : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) lhsS.getAppArgs vLargs)
    (hargsAligned : vCargs.map (VExpr.instSeq
        (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)) =
      vArgsC.map (VExpr.instSeq (xs.take cnP ++ ys.drop cnP)
        (cnP + cnF - 1)))
    (hvCargslen : vCargs.length = cnP + (mI - rP))
    (harityC : vArgsC.length = cnP + (mI - rP))
    (hspC2 : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) cres.getAppArgs vCargs)
    (hidx : IotaIndexPin Δ restC cnP mI rP xs)
    {Rj' : VExpr}
    (hrestC : restC = VExpr.instSeq ys (ys.length - 1) Rj')
    (hRjdecomp : Rj' = VExpr.mkAppN vHC vArgsC) :
    ∀ i : Fin (xs ++ [VExpr.mkAppN
    (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).length,
    Deq Δ (xs ++ [VExpr.mkAppN
      (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])[i]
      ((vLargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1))).getD i default) := by
  have hcl := m₀.cval_closed
  have hopenDeqG := openFrame_deq (Δ := Δ) (K := rP + cnF) m₀ ihd
  obtain ⟨HH, cargs, hrestCdecomp, hlenDisj, hpinDeq⟩ := hidx
  have hrestCinst : restC = VExpr.mkAppN
      (VExpr.instSeq ys (cnP + cnF - 1) vHC)
      (vArgsC.map (VExpr.instSeq ys (cnP + cnF - 1))) := by
    rw [hrestC, hRjdecomp, VExpr.instSeq_mkAppN, hlenY]
  have hgetD : ∀ (L : List VExpr) (g : VExpr → VExpr) (q : Nat),
      q < L.length → (L.map g).getD q default = g (L.getD q default) := by
    intro L g q hq
    simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem hq]
  have hspLget := DenoteSpine.get hspL
  intro i
  have hilen : i.1 < mI + 1 := by
    have h0 := i.2
    simp only [List.length_append, List.length_cons,
      List.length_nil] at h0
    omega
  rw [Fin.getElem_fin, hgetD vLargs _ i.1 (by omega)]
  by_cases hirP : i.1 < rP
  · -- a prefix position: the frame's own variable, on both sides
    have htk := congrArg (fun l => l[i.1]?) hlpre
    simp only [List.getElem?_take_of_lt hirP] at htk
    obtain ⟨nm, t, hsh⟩ := hshapeS i.1 fvs[i.1]
      (List.getElem?_eq_getElem (show i.1 < fvs.length from by omega))
    have hden := hspLget ⟨i.1, by omega⟩
    simp only [Fin.getElem_fin] at hden
    rw [show lhsS.getAppArgs[i.1] = fvs[i.1] from by
        have h2 := htk
        rw [List.getElem?_eq_getElem
            (show i.1 < lhsS.getAppArgs.length from by omega),
          List.getElem?_eq_getElem
            (show i.1 < fvs.length from by omega)] at h2
        exact Option.some.inj h2,
      hsh, denote_fvar] at hden
    have hvLi : vLargs.getD i.1 default =
        VExpr.bvar (rP + cnF - 1 - i.1) := (Option.some.inj hden).symm
    rw [List.getElem_append_left (by omega : i.1 < xs.length),
      hvLi, hzsel i.1 (by omega), hzsget i.1 (by omega), if_pos hirP,
      show xs.getD i.1 default = xs[i.1] from by
        simp [List.getD, List.getElem?_eq_getElem
          (show i.1 < xs.length from by omega)]]
  · by_cases himI : i.1 < mI
    · -- an index position: through the canonical tuple
      have haI : ((lhsS.getAppArgs.drop rP).take (mI - rP))[i.1 - rP]? =
          some (lhsS.getAppArgs.getD i.1 default) := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
          show rP + (i.1 - rP) = i.1 from by omega]
        simp [List.getD, List.getElem?_eq_getElem
          (show i.1 < lhsS.getAppArgs.length from by omega)]
      have hbI : (cres.getAppArgs.drop cnP)[i.1 - rP]? =
          some (cres.getAppArgs.getD (cnP + (i.1 - rP)) default) := by
        rw [List.getElem?_drop]
        simp [List.getD, List.getElem?_eq_getElem
          (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
            rw [hclen]; omega)]
      have hdeI := DefEqListOk.pointwise hdeIdx (i.1 - rP) haI hbI
      -- the constructor residual's frame facts
      have hwscres : Expr.WScoped (rP + cnF) cres := by
        obtain ⟨-, h1⟩ := instPisAt_WScoped (d := rP + cnF) _ _ hcinst
          (Expr.WScoped.of_not_hasFvar (by
            rw [hasFvar_renameConsts]
            exact hCw))
          (fun a ha => by
            obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
            exact (hspFacts q a hq).2.1)
        exact h1
      have hbcres : cres.looseBVarsBounded 0 = true := by
        obtain ⟨-, h1⟩ := instPisAt_bounded _ hcinst
          (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
          (fun a ha => by
            obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
            exact (hspFacts q a hq).2.2)
        exact h1
      have hlfcres : ∀ l ∈ cres.fvarLeaves,
          Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
        intro l hl
        rcases instPisAt_leaves _ hcinst l (Or.inr hl)
          with h1 | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [hasFvar_renameConsts]; exact hCw)] at h1
          exact nomatch h1
        · rcases List.mem_append.mp ha with ha' | ha'
          · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha', hla⟩)
          · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_drop ha', hla⟩)
      -- the two compared arguments' facts
      have hmemLA : lhsS.getAppArgs.getD i.1 default ∈
          lhsS.getAppArgs := by
        refine List.mem_of_getElem? (i := i.1) ?_
        simp [List.getD, List.getElem?_eq_getElem
          (show i.1 < lhsS.getAppArgs.length from by omega)]
      have hmemCA : cres.getAppArgs.getD (cnP + (i.1 - rP)) default ∈
          cres.getAppArgs := by
        refine List.mem_of_getElem? (i := cnP + (i.1 - rP)) ?_
        simp [List.getD, List.getElem?_eq_getElem
          (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
            rw [hclen]; omega)]
      have hlfLA : ∀ l ∈ (lhsS.getAppArgs.getD i.1
          default).fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
        fun l hl => hlfL l (fvarLeaves_getAppArgs hmemLA l hl)
      have hlfCA : ∀ l ∈ (cres.getAppArgs.getD (cnP + (i.1 - rP))
          default).fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
        fun l hl => hlfcres l (fvarLeaves_getAppArgs hmemCA l hl)
      have hdenLA : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (lhsS.getAppArgs.getD i.1 default) =
          some (vLargs.getD i.1 default) := by
        have h1 := hspLget ⟨i.1, by omega⟩
        simp only [Fin.getElem_fin] at h1
        rw [show lhsS.getAppArgs.getD i.1 default =
          lhsS.getAppArgs[i.1] from by
          simp [List.getD, List.getElem?_eq_getElem
            (show i.1 < lhsS.getAppArgs.length from by omega)]]
        exact h1
      have hdenCA : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (cres.getAppArgs.getD (cnP + (i.1 - rP))
            default) = some (vCargs.getD (cnP + (i.1 - rP))
            default) := by
        have h1 := hspC2.get ⟨cnP + (i.1 - rP), by rw [hclen]; omega⟩
        simp only [Fin.getElem_fin] at h1
        rw [show cres.getAppArgs.getD (cnP + (i.1 - rP)) default =
          cres.getAppArgs[cnP + (i.1 - rP)] from by
          simp [List.getD, List.getElem?_eq_getElem
            (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
              rw [hclen]; omega)]]
        exact h1
      have hcsZ0 : CtxSpine Δ (Γs.drop (rP + cnF - (rP + cnF)))
          (xs.take rP ++ ys.drop cnP) := by
        rw [Nat.sub_self, List.drop_zero]
        exact hcsZfull
      have hgenI := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
        hdomsS0' (lhsS.getAppArgs.getD i.1 default)
        (cres.getAppArgs.getD (cnP + (i.1 - rP)) default)
        (rP + cnF) (Nat.le_refl _) (Nat.le_refl _) hdeI
        hlfLA hlfCA (hwsL.getAppArgs _ hmemLA)
        (hwscres.getAppArgs _ hmemCA)
        (looseBVarsBounded_getAppArgs hbL _ hmemLA)
        (looseBVarsBounded_getAppArgs hbcres _ hmemCA)
        (hLB _ hlfLA) (hLB _ hlfCA) hdenLA hdenCA hcsZ0
      rw [Nat.sub_self] at hgenI
      simp only [List.replicate, List.append_nil] at hgenI
      rw [hzslen] at hgenI
      -- move the compared component onto the constructor's walk
      have hcomp := congrArg
        (fun l => l.getD (cnP + (i.1 - rP)) default) hargsAligned
      rw [hgetD vCargs _ _ (by omega), hgetD vArgsC _ _ (by omega)]
        at hcomp
      rw [hcomp] at hgenI
      -- the walk at the fired constructor spine
      have hptMix : ∀ p : Fin (xs.take cnP ++ ys.drop cnP).length,
          Deq Δ (xs.take cnP ++ ys.drop cnP)[p] (ys.getD p default) := by
        intro p
        have hp2 := p.2
        have hpm : p.1 < cnP + cnF := by omega
        have hmp : (xs.take cnP ++ ys.drop cnP)[p.1] =
            (xs.take cnP ++ ys.drop cnP).getD p.1 default := by
          simp [List.getD, List.getElem?_eq_getElem hp2]
        rw [Fin.getElem_fin, hmp, hmixget p.1 hpm]
        by_cases hpc : p.1 < cnP
        · rw [if_pos hpc]
          exact (hpar p.1 hpc (by omega)).symm
        · rw [if_neg hpc]
      have hcongrI := CtxSpine.instSeq_congr hcsMix hcsC hptMix
        (vArgsC.getD (cnP + (i.1 - rP)) default)
      rw [hmixlen, hlenY] at hcongrI
      -- the pin's fact at this component
      rcases hlenDisj with hmIrP | hcargslen
      · omega
      have h3 := hrestCdecomp.symm.trans hrestCinst
      obtain ⟨-, hcargsEq⟩ := VExpr.mkAppN_inj h3
        (by rw [hcargslen, List.length_map, harityC])
      have hpinI := hpinDeq (i.1 - rP) (by omega)
      rw [hcargsEq, hgetD vArgsC _ _ (by omega),
        show rP + (i.1 - rP) = i.1 from by omega] at hpinI
      -- assemble
      rw [List.getElem_append_left (by omega : i.1 < xs.length),
        show xs[i.1] = xs.getD i.1 default from by
          simp [List.getD, List.getElem?_eq_getElem
            (show i.1 < xs.length from by omega)]]
      exact Deq.symm (Deq.trans hgenI (Deq.trans hcongrI hpinI))
    · -- the major premise: the constructor at parameters and fields
      have hieq : i.1 = mI := by omega
      -- the statement's last argument is the canonical spine
      have hlast : lhsS.getAppArgs.getD mI default =
          Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
            (fvs.take cnP ++ fvs.drop rP) := by
        rw [← hmaj, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
          hlarity, Nat.add_sub_cancel]
        simp [List.getD, List.getElem?_eq_getElem
          (show mI < lhsS.getAppArgs.length from by omega)]
      -- its denotation: the model constructor over the frame's bvars
      have hspden : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (fvs.take cnP ++ fvs.drop rP)
          ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
            (rP + cnF - 1 -
              (if q < cnP then q else rP + (q - cnP))))) := by
        refine DenoteSpine.of_getElem
          (by rw [hsplen, List.length_map, List.length_range]) ?_
        intro q hq
        rw [hsplen] at hq
        obtain ⟨nm, t, hq1⟩ := hspIdx q hq
        rw [show (fvs.take cnP ++ fvs.drop rP).getD q default =
            Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm t
            from by simp [List.getD, hq1],
          denote_fvar,
          show ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
            (rP + cnF - 1 - (if q < cnP then q else rP + (q - cnP))))
            ).getD q default = VExpr.bvar (rP + cnF - 1 -
              (if q < cnP then q else rP + (q - cnP))) from by
            simp [List.getD, List.getElem?_map, List.getElem?_range hq]]
      have hheadden : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (.const (f ctor) (cvj.levelParams.map .param)) =
          some (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) := by
        rw [denote_const, hfCmE]
        dsimp only
        rw [if_pos (by rw [List.length_map, hCmlps])]
        congr 1
        rw [hCmlps,
          show Level.substFn (Level.substFn φ lps us) cvj.levelParams
            (cvj.levelParams.map Level.param) =
            Level.substFn φ lps us from
          funext fun p => Level.substFn_map_param, hro.2.2]
        exact (m₀.val_params ctor _ hctorE _ _
          (fun p hp => hagree p hp)).symm
      have hmajden := hspLget ⟨mI, by omega⟩
      simp only [Fin.getElem_fin] at hmajden
      rw [show lhsS.getAppArgs[mI] =
          lhsS.getAppArgs.getD mI default from by
        simp [List.getD, List.getElem?_eq_getElem
          (show mI < lhsS.getAppArgs.length from by omega)],
        hlast, denote_mkAppN hspden hheadden] at hmajden
      have hvLmaj : vLargs.getD i.1 default =
          VExpr.mkAppN (m₀.cval ctor (Level.substFn φ cvj.levelParams
            usj)) ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
            (rP + cnF - 1 -
              (if q < cnP then q else rP + (q - cnP))))) := by
        rw [hieq]
        exact (Option.some.inj hmajden).symm
      have hmapmaj : ((List.range (cnP + cnF)).map
          (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) ∘
            fun q => VExpr.bvar (rP + cnF - 1 -
              (if q < cnP then q else rP + (q - cnP))))) =
          (List.range (cnP + cnF)).map (fun q =>
            if q < cnP then xs.getD q default
            else ys.getD q default) := by
        refine List.map_congr_left ?_
        intro q hq
        have hqm := List.mem_range.mp hq
        simp only [Function.comp_apply]
        by_cases hqc : q < cnP
        · rw [if_pos hqc, if_pos hqc, hzsel q (by omega),
            hzsget q (by omega), if_pos (by omega : q < rP)]
        · rw [if_neg hqc, if_neg hqc,
            hzsel (rP + (q - cnP)) (by omega),
            hzsget (rP + (q - cnP)) (by omega),
            if_neg (by omega : ¬ rP + (q - cnP) < rP),
            show cnP + (rP + (q - cnP) - rP) = q from by omega]
      rw [hvLmaj,
        show (xs ++ [VExpr.mkAppN (m₀.cval ctor
            (Level.substFn φ cvj.levelParams usj)) ys])[i.1]'(i.2) =
          VExpr.mkAppN (m₀.cval ctor
            (Level.substFn φ cvj.levelParams usj)) ys from by
          rw [List.getElem_append_right (by omega : xs.length ≤ i.1)]
          simp [show i.1 - xs.length = 0 from by omega]]
      rw [VExpr.instSeq_mkAppN,
        VExpr.instSeq_eq_self_of_closed (hcl _ _), List.map_map, hmapmaj]
      refine Deq.mkAppN Deq.refl ?_ ?_
      · rw [List.length_map, List.length_range, hlenY]
      · intro q
        have hq2 := q.2
        have hqm : q.1 < cnP + cnF := by omega
        rw [Fin.getElem_fin,
          show ys[q.1]'(hq2) = ys.getD q.1 default from by
            simp [List.getD],
          show ((List.range (cnP + cnF)).map (fun q =>
            if q < cnP then xs.getD q default else ys.getD q default)
            ).getD q.1 default = (if q.1 < cnP then xs.getD q.1 default
              else ys.getD q.1 default) from by
            simp [List.getD, List.getElem?_map, List.getElem?_range hqm]]
        by_cases hqc : q.1 < cnP
        · rw [if_pos hqc]
          exact hpar q.1 hqc (by omega)
        · rw [if_neg hqc]

end Setlec.TTVerify
