import Setlec.SetP.DirectRecPinsP

/-!
# The minor premise's space (task #175 W4c, P3 module 6, part 12)

`recMinor`: at a parameter valuation and a motive value, the minor
binder's reading interprets to `minorSp` — the Π-tower over the
constructor's field chain ending in the motive at the tuple.  The
field domains the checker opened (`Γm`) are pinned by `isDefEq` to the
constructor's, instantiated at the recursor's variables (`cdomsF`);
those read, at the field depths, to the constructor's field entries
lifted over the minor and motive slots (`liftDoms 2`).  The two
composite contexts — `Γm` above the padded slot, and the lifted field
entries above it — are identified by `frameIdent` over the defeq
claims, and the minor space follows by `interp_minorSp_of_tele`, its
core being the constructor leaf's fold (`directMkAV_fold`).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

theorem liftDoms_take (n : Nat) :
    ∀ (ds : List (Nat × Nat × AVExpr)) (k j : Nat),
      (liftDoms n k ds).take j = liftDoms n k (ds.take j)
  | [], _, _ => by simp [liftDoms]
  | _ :: ds, k, 0 => rfl
  | _ :: ds, k, j + 1 => by
    simp only [liftDoms, List.take_succ_cons, liftDoms_take n ds (k + 1) j]

/-- A fit of lifted domains is a fit of the domains at the shifted
frame. -/
theorem spineFit_liftDoms (n : Nat) :
    ∀ {ds : List (Nat × Nat × AVExpr)} {k : Nat} {σ : Nat → V} {as : List V},
      SpineFit σ ((liftDoms n k ds).map (·.2.2)) as ↔
        SpineFit (shiftE n k σ) (ds.map (·.2.2)) as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ds, k, σ, a :: as => by
    simp only [liftDoms, List.map_cons, SpineFit, interp2_liftN]
    rw [← shiftE_cons_succ']
    exact and_congr Iff.rfl (spineFit_liftDoms n)

theorem spineFit_append_inv :
    ∀ {Ds₁ Ds₂ : List AVExpr} {ρ : Nat → V} {as : List V},
      SpineFit ρ (Ds₁ ++ Ds₂) as →
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂
  | [], _, ρ, as, h => ⟨[], as, rfl, trivial, h⟩
  | _ :: _, _, _, [], h => h.elim
  | D :: Ds₁, Ds₂, ρ, a :: as, h => by
    obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_inv (Ds₁ := Ds₁) h.2
    exact ⟨a :: as₁, as₂, rfl, ⟨h.1, h1⟩, h2⟩

omit [SetTheory V] in
/-- A consed spine's entries below its length are the spine's, from the
top. -/
theorem consList_apply_lt :
    ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
      consList as σ k = (as[as.length - 1 - k]?).getD (σ 0)
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with h | h
    · rw [consList_apply_lt as (cons a σ) k h, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega), Option.getD_some,
        Option.getD_some]
    · obtain rfl : k = as.length := by simp at hk; omega
      have := consList_apply_add as (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, List.length_cons, show as.length + 1 - 1 - as.length = 0 from by omega,
        List.getElem?_cons_zero, Option.getD_some, cons_zero]

/-- The field variables, read at a consed field spine, are the spine. -/
theorem map_fieldBvars_interp {nF : Nat} {as : List V} (hlen : as.length = nF)
    (σ : Nat → V) :
    ((List.range nF).map fun k => (AVExpr.bvar (nF - 1 - k))).map (interp2 V (consList as σ))
      = as := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, interp2_bvar]
    have hi : i < nF := by simpa using h1
    rw [consList_apply_lt as σ (nF - 1 - i) (by omega), hlen,
      show nF - 1 - (nF - 1 - i) = i from by omega, List.getElem?_eq_getElem h2,
      Option.getD_some]

theorem stripPisAV_liftN_inv (n' c : Nat) :
    ∀ (n : Nat) {e : AVExpr} {gds : List (Nat × Nat × AVExpr)} {R : AVExpr},
      stripPisAV n (e.liftN n' c) = some (gds, R) →
      ∃ gds₀ R₀, stripPisAV n e = some (gds₀, R₀) ∧ gds = liftDoms n' c gds₀ ∧
        R = R₀.liftN n' (c + n)
  | 0, e, gds, R, h => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl, by simp⟩
  | n + 1, e, gds, R, h => by
    match e, h with
    | .pi u v A B, h =>
      simp only [AVExpr.liftN_pi, stripPisAV] at h
      cases h1 : stripPisAV n (B.liftN n' (c + 1)) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        obtain ⟨gds', R'⟩ := p
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨gds₀, R₀, hst, rfl, rfl⟩ := stripPisAV_liftN_inv n' (c + 1) n h1
        refine ⟨(u, v, A) :: gds₀, R₀, by simp [stripPisAV, hst], rfl, ?_⟩
        rw [show c + 1 + n = c + (n + 1) from by omega]
    | .bvar _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .eqE _ _ _, h | .proj _ _, h | .prf, h =>
      simp [AVExpr.liftN, stripPisAV] at h

theorem mem_take_of_le {α : Type _} {l : List α} {a : α} {n n' : Nat}
    (h : a ∈ l.take n) (hn : n ≤ n') : a ∈ l.take n' := by
  obtain ⟨q, hq⟩ := List.getElem?_of_mem h
  have hq' : q < n := by
    have := (List.getElem?_eq_some_iff.mp hq).1
    simp at this; omega
  rw [List.getElem?_take_of_lt hq'] at hq
  exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (i := q) (j := n') (by omega)]; exact hq)

omit [SetTheory V] in
/-- The consed reversed range at a shifted frame is the shift. -/
theorem consList_range_reverse_shift (j : Nat) (ρ : Nat → V) :
    consList ((List.range j).reverse.map ρ) (fun i => ρ (i + j + 2)) = shiftE 2 j ρ := by
  have h1 : (List.range j).reverse.map ρ = (List.range j).reverse.map (shiftE 2 j ρ) := by
    apply List.map_congr_left
    intro k hk
    have : k < j := by simpa using hk
    simp [shiftE, this]
  have h2 : (fun i => ρ (i + j + 2)) = fun i => shiftE 2 j ρ (i + j) := by
    funext i; simp only [shiftE]; rw [if_neg (by omega)]
  rw [h1, h2]
  exact consList_range_reverse j (shiftE 2 j ρ)

/-! ## The minor space -/

set_option maxHeartbeats 6400000 in
/-- **The opened field domains are the constructor's field entries, lifted
over the minor and motive slots**: the two composite contexts (`Γm`
above a minor-slot entry `E`, the lifted field entries above it) have
the same satisfying valuations at every field depth, and the entries
interpret alike under them — `frameIdent` over the field pins. -/
theorem minorFieldsIdent {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP nF : Nat} {tyR : Expr} {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + 3)
    {xFvs : List Expr} {minBody : Expr} {Γm : List AVExpr} {Rm : AVExpr}
    (comp : CompOpenedP m φ nP nF fvsR xFvs minBody Γr Γm Rm)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr} (hlenDs : ds.length = nP + nF)
    (hCok : ∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV ds bodyC))
    {crest : Expr} (hres : denoteP m.acval env φ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hwres : Expr.WScoped nP crest) (hbres : crest.looseBVarsBounded 0 = true)
    (hleafres : ∀ l ∈ crest.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧ l.2.2.looseBVarsBounded 0 = true)
    {cdomsF : List Expr} {crest2 : Expr}
    (hcf : Expr.instPisAt xFvs crest = some (cdomsF, crest2))
    (hpinsF : ∀ i, i < nF → ∃ a b, xFvs[i]? = some a ∧ cdomsF[i]? = some b ∧
      Setlec.isDefEqCore μ env F (nP + 2 + i) (Expr.fvarTypeD a) b = .ok true)
    (hiffP : ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ ↔
      Sat2 V (((ds.take nP).map (·.2.2)).reverse) ρ)
    (E : AVExpr) :
    (∀ j, j ≤ nF → ∀ ρ' : Nat → V,
      Sat2 V (compCtx Γm Γr nF E j) ρ' ↔
        Sat2 V ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
          (E :: Γr.drop 2)) ρ') ∧
    (∀ j, j < nF → ∀ ρ' : Nat → V, Sat2 V (compCtx Γm Γr nF E j) ρ' →
      interp2 V ρ' (Γm.getD (nF - 1 - j) default)
        = interp2 V ρ' (((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default).liftN 2 j)) := by
  have hlenR : Γr.length = nP + 3 := hR.len
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenFds : (ds.drop nP).length = nF := by simp [hlenDs]
  have hΓ₂len : ((((ds.take nP).map (·.2.2)).reverse)).length = nP := by simp [hlenDs]
  -- the constructor tower's gradings
  have hstC := stripPisAV_mkPisAV ds bodyC
  rw [hlenDs] at hstC
  obtain ⟨okΓc, -⟩ := piTeleP_graded (V := V) (piTeleP_of_stripPisAV hstC) (Δ₀ := [])
    (fun ρ _ => hCok ρ)
  simp only [List.append_nil] at okΓc
  have hΓc := reverse_map_take_drop ds nP
  -- the padded base frame
  -- the constructor's residual, lifted under the minor and the motive
  have hres2 : denoteP m.acval env φ (nP + 2) crest
      = some (mkPisAV (liftDoms 2 0 (ds.drop nP)) (bodyC.liftN 2 nF)) := by
    have h := denoteP_lift (env := env) (φ := φ) m.acval_closed hwres (nP + 2) (by omega)
    rw [hres, show nP + 2 - nP = 2 from by omega, Option.map_some, liftN_mkPisAV, Nat.zero_add,
      hlenFds] at h
    exact h
  have hstL := stripPisAV_mkPisAV (liftDoms 2 0 (ds.drop nP)) (bodyC.liftN 2 nF)
  rw [liftDoms_length, hlenFds] at hstL
  have hteleL := piTeleP_of_stripPisAV hstL
  have hidxX : ∀ (q : Nat) (x : Expr), xFvs[q]? = some x →
      ∃ nm t, x = Expr.fvar (nP + 2 + q) nm t := fun q x hx => (comp.varX q x hx).1
  have hdomsF := instPisAt_openerDomsP xFvs hcf hidxX hres2 (by rw [comp.lenX]; exact hteleL)
  rw [comp.lenX] at hdomsF
  -- the lifted field entries
  have hentL : ∀ q, q < nF →
      ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse)).getD (nF - 1 - q) default
        = ((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD q default).liftN 2 q := by
    intro q hq
    obtain ⟨d, hd⟩ : ∃ d, (ds.drop nP)[q]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hl : (liftDoms 2 0 (ds.drop nP))[q]? = some (d.1, d.2.1, d.2.2.liftN 2 q) := by
      rw [liftDoms_getElem?, hd, Nat.zero_add]; rfl
    rw [getD_reverse_of_peel (by rw [liftDoms_length, hlenFds]) hq hl,
      List.getD_eq_getElem?_getD, List.getElem?_map, hd]
    try rfl
  -- the two composite contexts
  have hΓ1len : (compCtx Γm Γr nF E nF).length = nP + 2 + nF :=
    compCtx_length comp.lenM hlenR (Nat.le_refl _)
  have hΓ2len : ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
      (E :: Γr.drop 2)).length = nP + 2 + nF := by
    simp [liftDoms_length, hlenFds, hlenR]; omega
  have hΓ2drop : ∀ j, j ≤ nF →
      (((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++ (E :: Γr.drop 2)).drop
          (nF - j))
        = (((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++ (E :: Γr.drop 2) := by
    intro j hj
    rw [List.drop_append_of_le_length
        (by rw [List.length_reverse, List.length_map, liftDoms_length, hlenFds]; exact Nat.sub_le _ _),
      List.drop_reverse, List.length_map, liftDoms_length, hlenFds,
      show nF - (nF - j) = j from by omega, ← List.map_take, liftDoms_take]
  -- the base frame's satisfaction, from any composite frame's
  have hbaseSat : ∀ (j : Nat) (ρ' : Nat → V), j ≤ nF →
      Sat2 V ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
        (E :: Γr.drop 2)) ρ' →
      Sat2 V (((ds.take nP).map (·.2.2)).reverse) (fun i => ρ' (i + j + 2)) ∧
      SpineFit (fun i => ρ' (i + j + 2)) (((ds.drop nP).map (·.2.2)).take j)
        ((List.range j).reverse.map ρ') := by
    intro j ρ' hj hs
    have hlenLj : ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)))).length = j := by
      simp [liftDoms_length]; omega
    have hsp := spineFit_of_sat2 (Δ₀ := E :: Γr.drop 2)
      (Ds := ((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2))) hs
    rw [hlenLj] at hsp
    have hsp' := (spineFit_liftDoms 2).mp hsp
    rw [shiftE_zero, List.map_take] at hsp'
    have e : (fun i => ρ' (i + 2 + j)) = fun i => ρ' (i + j + 2) := by
      funext i; congr 1; omega
    rw [e] at hsp'
    refine ⟨?_, hsp'⟩
    have hb := Sat2_drop hs j
    rw [List.drop_append_of_le_length (by simp [hlenLj]),
      List.drop_eq_nil_of_le (by simp [hlenLj]), List.nil_append] at hb
    have hb2 := Sat2_tail hb
    have hb3 := Sat2_drop hb2 1
    rw [List.drop_drop] at hb3
    have e : (fun i => ρ' (i + j + 2)) = fun j_1 => ρ' (j_1 + 1 + 1 + j) := by
      funext i; congr 1; omega
    refine (hiffP _).mp ?_
    rw [e]
    exact hb3
  -- a term's leaves over the constructor domains at the field frame
  have hleafX : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      ∀ l ∈ x.fvarLeaves,
        (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) ∧
        l.2.2.looseBVarsBounded 0 = true := by
    intro i x hx l hl
    obtain ⟨⟨nm, ty, rfl⟩, -, hb, -, hleaf⟩ := comp.varX i x hx
    simp only [Expr.fvarTypeD] at hb hleaf
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨Or.inr (List.mem_of_getElem? hx), hb⟩
    · refine ⟨hleaf l hl, ?_⟩
      rcases hleaf l hl with h | h
      · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
        have hq' : q < nP + 1 := by
          have := (List.getElem?_eq_some_iff.mp hq).1
          simp at this; omega
        rw [List.getElem?_take_of_lt hq'] at hq
        obtain ⟨-, -, hb', -, -⟩ := hR.var q _ hq
        obtain ⟨nm', ty', hx'⟩ := hidxR q _ hq
        obtain ⟨-, -, h3⟩ : l.1 = q ∧ l.2.1 = nm' ∧ l.2.2 = ty' := by
          injection hx' with a b c
          exact ⟨a, b, c⟩
        rw [hx'] at hb'
        rw [h3]
        simpa [Expr.fvarTypeD] using hb'
      · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
        obtain ⟨-, -, hb', -, -⟩ := comp.varX q _ hq
        obtain ⟨nm', ty', hx'⟩ := hidxX q _ hq
        obtain ⟨-, -, h3⟩ : l.1 = nP + 2 + q ∧ l.2.1 = nm' ∧ l.2.2 = ty' := by
          injection hx' with a b c
          exact ⟨a, b, c⟩
        rw [hx'] at hb'
        rw [h3]
        simpa [Expr.fvarTypeD] using hb'
  -- the index of a leaf among the first `nP + 1` recursor variables or
  -- the field variables is never the minor's
  have hnotMinor : ∀ l : Nat × Name × Expr,
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) →
      l.1 ≠ nP + 1 := by
    intro l hl
    rcases hl with h | h
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
      have hq' : q < nP + 1 := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        simp at this; omega
      rw [List.getElem?_take_of_lt hq'] at hq
      obtain ⟨nm', ty', hx'⟩ := hidxR q _ hq
      have : l.1 = q := by injection hx'
      omega
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
      obtain ⟨nm', ty', hx'⟩ := hidxX q _ hq
      have : l.1 = nP + 2 + q := by injection hx'
      omega
  have hleafCtx : ∀ l : Nat × Name × Expr,
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) →
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) ∧
      (l.1 = nP + 1 → E = Γr.getD 1 default) := by
    intro l hl
    refine ⟨?_, fun h => absurd h (hnotMinor l hl)⟩
    rcases hl with h | h
    · exact Or.inl (mem_take_of_le h (by omega))
    · exact Or.inr h
  -- the constructor domains' scoping
  have hspW : ∀ (i : Nat) (a : Expr), xFvs[i]? = some a → Expr.WScoped (nP + 2 + i + 1) a := by
    intro i a ha
    obtain ⟨⟨nm, ty, rfl⟩, hw, -, -, -⟩ := comp.varX i a ha
    simp only [Expr.fvarTypeD] at hw
    simp only [Expr.WScoped]
    exact ⟨by omega, hw⟩
  obtain ⟨hbdomsF, -⟩ := instPisAt_bounded xFvs hcf hbres (fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxX q a hq
    rfl)
  have hleavesRunF := instPisAt_leaves xFvs hcf
  -- **the pin at field `j`**: the opened domain and the constructor's,
  -- identified at every composite frame whose earlier fields are
  -- already identified
  have hagree : ∀ j, j < nF →
      (∀ ρ' : Nat → V, Sat2 V (compCtx Γm Γr nF E j) ρ' ↔
        Sat2 V ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
          (E :: Γr.drop 2)) ρ') →
      ∀ ρ' : Nat → V, Sat2 V (compCtx Γm Γr nF E j) ρ' →
        interp2 V ρ' (Γm.getD (nF - 1 - j) default)
          = interp2 V ρ' (((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default).liftN 2 j) := by
    intro j hj hiff ρ' hρ'
    obtain ⟨a, b, ha, hb, hdeq⟩ := hpinsF j hj
    -- the opened domain's side
    obtain ⟨-, hwa, hba, hLa, hleafa⟩ := comp.varX j a ha
    have hda := comp.domsX j a ha
    have hCa := comp.ctx E (Nat.le_of_lt hj) hwa (fun l hl => hleafCtx l (hleafa l hl))
    -- the constructor domain's side
    have hwb : Expr.WScoped (nP + 2 + j) b :=
      instPisAt_index_WScoped xFvs (d := nP + 2) hcf (Expr.WScoped.mono (by omega) hwres)
        hspW j b hb
    have hbb : b.looseBVarsBounded 0 = true := hbdomsF b (List.mem_of_getElem? hb)
    have hleafb : ∀ l ∈ b.fvarLeaves,
        (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) ∧
        l.2.2.looseBVarsBounded 0 = true := by
      intro l hl
      rcases hleavesRunF l (Or.inl ⟨b, List.mem_of_getElem? hb, hl⟩) with h | ⟨x, hx, hlx⟩
      · obtain ⟨h1, h2⟩ := hleafres l h
        exact ⟨Or.inl (mem_take_of_le h1 (by omega)), h2⟩
      · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
        exact hleafX q x hq l hlx
    have hLb : Expr.LeavesBounded b := fun l hl => (hleafb l hl).2
    have hCb := comp.ctx E (Nat.le_of_lt hj) hwb (fun l hl => hleafCtx l (hleafb l hl).1)
    have hdb : denoteP m.acval env φ (nP + 2 + j) b
        = some (((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default).liftN 2 j) := by
      have := hdomsF j hj
      rw [List.getD_eq_getElem?_getD (l := cdomsF), hb, Option.getD_some, hentL j hj] at this
      exact this
    -- the gradings
    have hoka := comp.okΓm E j hj
    have hokb : ∀ ρ'' : Nat → V, Sat2 V (compCtx Γm Γr nF E j) ρ'' →
        AnnotOkP V ρ'' (((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default).liftN 2 j) := by
      intro ρ'' hρ''
      obtain ⟨hsatΓ₂, hspF⟩ := hbaseSat j ρ'' (Nat.le_of_lt hj) ((hiff ρ'').mp hρ'')
      refine (AnnotOkP_liftN V 2 _ j ρ'').mpr ?_
      have hsatF := sat2_of_spineFit (Δ₀ := (((ds.take nP).map (·.2.2)).reverse)) hsatΓ₂ hspF
      rw [consList_range_reverse_shift] at hsatF
      have hdropC : (((ds.map (·.2.2)).reverse)).drop (nP + nF - (nP + j))
          = ((((ds.drop nP).map (·.2.2))).take j).reverse ++
            (((ds.take nP).map (·.2.2)).reverse) := by
        rw [hΓc, show nP + nF - (nP + j) = nF - j from by omega,
          List.drop_append_of_le_length
            (by rw [List.length_reverse, List.length_map, hlenFds]; exact Nat.sub_le _ _),
          List.drop_reverse, List.length_map, hlenFds, show nF - (nF - j) = j from by omega]
      have hentC : (((ds.map (·.2.2)).reverse)).getD (nP + nF - 1 - (nP + j)) default
          = (((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default := by
        rw [hΓc, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlenDs]; omega),
          List.getElem?_reverse (by simp [hlenDs]; omega), List.length_map, hlenFds,
          show nF - 1 - (nF - 1 - j) = j from by omega, ← List.getD_eq_getElem?_getD]
      have := okΓc (nP + j) (by omega) (shiftE 2 j ρ'') (by rw [hdropC]; exact hsatF)
      rw [hentC] at this
      exact this
    exact hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb hda hdb hoka hokb ρ' hρ'
  -- the identification of the two composite contexts
  have hequiv := frameIdent (V := V) hΓ1len hΓ2len (fun i hi hiff ρ' hρ' => by
    rcases Nat.lt_or_ge i (nP + 2) with hlt | hge
    · -- a base entry: the same on both sides
      have e1 : (compCtx Γm Γr nF E nF).getD (nP + 2 + nF - 1 - i) default
          = (E :: Γr.drop 2).getD (nP + 1 - i) default := by
        simp only [compCtx, Nat.sub_self, List.drop_zero]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [comp.lenM]; omega),
          comp.lenM, show nP + 2 + nF - 1 - i - nF = nP + 1 - i from by omega,
          ← List.getD_eq_getElem?_getD]
      have e2 : ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
            (E :: Γr.drop 2)).getD (nP + 2 + nF - 1 - i) default
          = (E :: Γr.drop 2).getD (nP + 1 - i) default := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp [liftDoms_length, hlenFds]; omega)]
        simp only [List.length_reverse, List.length_map, liftDoms_length, hlenFds]
        rw [show nP + 2 + nF - 1 - i - nF = nP + 1 - i from by omega,
          ← List.getD_eq_getElem?_getD]
      rw [e1, e2]
    · -- a field entry: the pin
      obtain ⟨j, rfl⟩ : ∃ j, i = nP + 2 + j := ⟨i - (nP + 2), by omega⟩
      have hj : j < nF := by omega
      have hdropΓ1 : (compCtx Γm Γr nF E nF).drop (nP + 2 + nF - (nP + 2 + j))
          = compCtx Γm Γr nF E j := by
        rw [show nP + 2 + nF - (nP + 2 + j) = nF - j from by omega]
        exact compCtx_drop_fields comp.lenM (Nat.le_of_lt hj) (Nat.le_refl _)
      have hdropΓ2 : ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
            (E :: Γr.drop 2)).drop (nP + 2 + nF - (nP + 2 + j))
          = (((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
            (E :: Γr.drop 2) := by
        rw [show nP + 2 + nF - (nP + 2 + j) = nF - j from by omega]
        exact hΓ2drop j (Nat.le_of_lt hj)
      rw [hdropΓ1] at hρ'
      rw [hdropΓ1, hdropΓ2] at hiff
      have e1 : (compCtx Γm Γr nF E nF).getD (nP + 2 + nF - 1 - (nP + 2 + j)) default
          = Γm.getD (nF - 1 - j) default := by
        rw [List.getD_eq_getElem?_getD, show nP + 2 + nF - 1 - (nP + 2 + j) = nF - 1 - j from by omega,
          compCtx_getElem?_field comp.lenM (Nat.le_refl _) hj]
        rfl
      have e2 : ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
            (E :: Γr.drop 2)).getD (nP + 2 + nF - 1 - (nP + 2 + j)) default
          = ((((ds.drop nP).map (fun d : Nat × Nat × AVExpr => d.2.2))).getD j default).liftN 2 j := by
        rw [List.getD_eq_getElem?_getD, show nP + 2 + nF - 1 - (nP + 2 + j) = nF - 1 - j from by omega,
          List.getElem?_append_left (by simp [liftDoms_length, hlenFds]; omega),
          ← List.getD_eq_getElem?_getD, hentL j hj]
      rw [e1, e2]
      exact hagree j hj hiff ρ' hρ')
  have hequiv' : ∀ j, j ≤ nF → ∀ ρ' : Nat → V,
      Sat2 V (compCtx Γm Γr nF E j) ρ' ↔
        Sat2 V ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
          (E :: Γr.drop 2)) ρ' := by
    intro j hj ρ'
    have := hequiv (nP + 2 + j) (by omega) ρ'
    rw [show nP + 2 + nF - (nP + 2 + j) = nF - j from by omega,
      compCtx_drop_fields comp.lenM hj (Nat.le_refl _), hΓ2drop j hj] at this
    exact this
  exact ⟨hequiv', fun j hj ρ' h => hagree j hj (hequiv' j (Nat.le_of_lt hj)) ρ' h⟩

set_option maxHeartbeats 6400000 in
/-- **The minor binder's reading is the minor space.** -/
theorem recMinor {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP nF : Nat} {tyR : Expr} {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + 3)
    {nmM : Name} {tyM : Expr}
    {nmm : Name} {tym : Expr} (hmin : fvsR[nP + 1]? = some (.fvar (nP + 1) nmm tym))
    {xFvs : List Expr} {minBody : Expr} {Γm : List AVExpr} {Rm : AVExpr}
    (comp : CompOpenedP m φ nP nF fvsR xFvs minBody Γr Γm Rm)
    {ℓ : Nat} (hPiBits : PiBitsOpen φ (ℓ = 0) nF (nP + 2) tym)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr} (hlenDs : ds.length = nP + nF)
    (hCok : ∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV ds bodyC))
    {C : Name} {lps : List Name} {cvCa : ConstantVal}
    (hfC : env.find? C = some (.ctorInfo cvCa nP nF)) (hlpsC : cvCa.levelParams = lps)
    {w : Nat} (hleafC : m.acval C φ = directMkAV w ds ((ds.drop nP).map (·.2.2)))
    {crest : Expr} (hres : denoteP m.acval env φ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hwres : Expr.WScoped nP crest) (hbres : crest.looseBVarsBounded 0 = true)
    (hleafres : ∀ l ∈ crest.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧ l.2.2.looseBVarsBounded 0 = true)
    {cdomsF : List Expr} {crest2 : Expr}
    (hcf : Expr.instPisAt xFvs crest = some (cdomsF, crest2))
    (hpinsF : ∀ i, i < nF → ∃ a b, xFvs[i]? = some a ∧ cdomsF[i]? = some b ∧
      Setlec.isDefEqCore μ env F (nP + 2 + i) (Expr.fvarTypeD a) b = .ok true)
    (hminBody : minBody = .app (.fvar nP nmM tyM)
      (Expr.mkAppN (.const C (lps.map .param)) (fvsR.take nP ++ xFvs)))
    (hiffP : ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ ↔
      Sat2 V (((ds.take nP).map (·.2.2)).reverse) ρ)
    (hfieldsB : ∀ ρ : Nat → V, Sat2 V (((ds.take nP).map (·.2.2)).reverse) ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2))) :
    ∀ ρp : Nat → V, Sat2 V (Γr.drop 3) ρp →
      ∀ M : V, M ∈ˢ interp2 V ρp (Γr.getD 2 default) →
        interp2 V (cons M ρp) (Γr.getD 1 default)
          = minorSp ℓ w M ((ds.drop nP).map (·.2.2)) ρp [] := by
  intro ρp hρp M hM
  have hlenR : Γr.length = nP + 3 := hR.len
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenFds : (ds.drop nP).length = nF := by simp [hlenDs]
  have hΓ₂len : ((((ds.take nP).map (·.2.2)).reverse)).length = nP := by simp [hlenDs]
  have hsatC := (hiffP ρp).mp hρp
  have hdrop2 : Γr.drop 2 = Γr.getD 2 default :: Γr.drop 3 := by
    have h := drop_succ_eq_getD_cons hlenR (i := nP) (by omega)
    rwa [show nP + 3 - (nP + 1) = 2 from by omega, show nP + 3 - 1 - nP = 2 from by omega,
      show nP + 3 - nP = 3 from by omega] at h
  have hsat0 : Sat2 V (.sort 0 :: Γr.drop 2) (cons unitSet (cons M ρp)) := by
    rw [hdrop2]
    exact Sat2_cons V (Sat2_cons V hρp hM) (unitSet_mem_univ 0)
  have hidxX : ∀ (q : Nat) (x : Expr), xFvs[q]? = some x →
      ∃ nm t, x = Expr.fvar (nP + 2 + q) nm t := fun q x hx => (comp.varX q x hx).1
  obtain ⟨hequiv', hagree'⟩ := minorFieldsIdent hc hR hidxR hlenF comp hlenDs hCok hres hwres
    hbres hleafres hcf hpinsF hiffP (.sort 0)
  -- the minor type's peel and its bits
  obtain ⟨gds, hst, hΓm⟩ := stripPisAV_of_piTeleP comp.tele
  obtain ⟨hTeq, hlenG⟩ := stripPisAV_eq_mkPis hst
  obtain ⟨-, hw1, -, -, -⟩ := hR.var (nP + 1) _ hmin
  simp only [Expr.fvarTypeD] at hw1
  have hread1 : denoteP m.acval env φ (nP + 1) tym = some (Γr.getD 1 default) := by
    have := hR.doms (nP + 1) _ hmin
    simp only [Expr.fvarTypeD] at this
    rwa [show nP + 3 - 1 - (nP + 1) = 1 from by omega] at this
  have hread2 : denoteP m.acval env φ (nP + 2) tym
      = some ((Γr.getD 1 default).liftN 1 0) := by
    rw [denoteP_lift m.acval_closed hw1 (nP + 2) (by omega), hread1,
      show nP + 2 - (nP + 1) = 1 from by omega]
    rfl
  have hbits : ∀ d ∈ gds, (ℓ = 0 ↔ d.2.1 = 0) := fun d hd =>
    (stripPisAV_bits nF hPiBits hread2 hst d hd).symm
  -- the minor's reading, one deeper
  have hlift : interp2 V (cons M ρp) (Γr.getD 1 default)
      = interp2 V (cons unitSet (cons M ρp)) ((Γr.getD 1 default).liftN 1 0) := by
    rw [interp2_liftN, shiftE_one_cons]
  rw [hlift, hTeq]
  refine interp_minorSp_of_tele (by rw [hlenG, hlenFs]) hbits ?_ ?_
  · -- the field domains agree along a fitting chain
    intro j as hj hsp
    rw [hlenFs] at hj
    have hlenAs : as.length = j := by
      rw [hsp.length_eq, List.length_take, hlenFs]; omega
    have hsatL : Sat2 V ((((liftDoms 2 0 ((ds.drop nP).take j)).map (·.2.2)).reverse) ++
        (.sort 0 :: Γr.drop 2)) (consList as (cons unitSet (cons M ρp))) := by
      refine sat2_of_spineFit hsat0 ?_
      rw [spineFit_liftDoms, shiftE_cons_cons, List.map_take]
      exact hsp
    have hsatComp := (hequiv' j (Nat.le_of_lt hj) _).mpr hsatL
    have hag := hagree' j hj _ hsatComp
    have hent : (gds.getD j default).2.2 = Γm.getD (nF - 1 - j) default := by
      obtain ⟨q, hq⟩ : ∃ q, gds[j]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenG]; exact hj)⟩
      rw [← hΓm, getD_reverse_of_peel hlenG hj hq, List.getD_eq_getElem?_getD, hq]
      rfl
    rw [hent, hag, interp2_liftN, ← hlenAs, shiftE_consList_len, shiftE_cons_cons]
  · -- the core: the motive at the constructor leaf's fold
    intro as hsp
    have hlenAs : as.length = nF := by rw [hsp.length_eq, hlenFs]
    have hRm := comp.body
    rw [hminBody] at hRm
    obtain ⟨fa, aa, hfa, haa, hRmeq⟩ := denoteP_app_inv hRm
    rw [denoteP_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    -- the constructor spine's reading
    have hlenT : (fvsR.take nP).length = nP := by simp [hlenF]
    have hspP := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := φ) (nP + 2 + nF)
      (fvsR.take nP) 0 (fun k x hx => by
        have hk : k < nP := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp at this; omega
        rw [List.getElem?_take_of_lt hk] at hx
        obtain ⟨nm, ty, h⟩ := hidxR k x hx
        exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩)
    have hspX := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := φ) (nP + 2 + nF)
      xFvs (nP + 2) hidxX
    rw [hlenT] at hspP
    rw [comp.lenX] at hspX
    have haa' := denoteP_mkAppN (hspP.append hspX) (f := .const C (lps.map .param))
      (fa := m.acval C φ) (by
        rw [denoteP_const hfC (by show (lps.map Level.param).length = cvCa.levelParams.length; simp [hlpsC])]
        show some (m.acval C (Level.substFn φ cvCa.levelParams (lps.map .param))) = _
        rw [hlpsC, Level.substFn_param_self])
    obtain rfl := Option.some.inj (haa.symm.trans haa')
    subst hRmeq
    -- the values
    have hMval : consList as (cons unitSet (cons M ρp)) (nP + 2 + nF - 1 - nP) = M := by
      rw [show nP + 2 + nF - 1 - nP = 1 + as.length from by omega, consList_apply_add]
      rfl
    have hP : ((List.range nP).map fun k => AVExpr.bvar (nP + 2 + nF - 1 - (0 + k)))
        = paramBvarsAt nP (nP + (2 + nF)) := by
      apply List.map_congr_left
      intro k _
      congr 1; omega
    have hX : ((List.range nF).map fun k => AVExpr.bvar (nP + 2 + nF - 1 - (nP + 2 + k)))
        = (List.range nF).map fun k => AVExpr.bvar (nF - 1 - k) := by
      apply List.map_congr_left
      intro k _
      congr 1; omega
    have hσ : ∀ j, consList as (cons unitSet (cons M ρp)) (j + (2 + nF)) = ρp j := by
      intro j
      rw [show j + (2 + nF) = (j + 2) + as.length from by omega, consList_apply_add]
      rfl
    have hleafC' : m.acval C φ
        = directMkAV w (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) := by
      rw [hleafC, List.take_append_drop]
    rw [interp2_app, interp2_bvar, hMval, interp2_mkAppN,
      ← List.foldl_map (f := interp2 V (consList as (cons unitSet (cons M ρp))))
        (g := SetTheory.app),
      List.map_append, hP, hX, map_paramBvarsAt_interp hσ, map_fieldBvars_interp hlenAs,
      interp2_closed (V := V) (m.cval_closedL C φ) _ (fun j => ρp (j + nP)), hleafC']
    have hlenP : ((ds.take nP).map (·.2.2)).length = nP := by simp [hlenDs]
    have hsp₁ := spineFit_of_sat2 (Δ₀ := []) (Ds := (ds.take nP).map (·.2.2))
      (by rw [List.append_nil]; exact hsatC)
    rw [hlenP] at hsp₁
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, directMkAV_zero, foldl_app_pt, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [directMkAV_fold hw hsp₁ (by rw [consList_range_reverse]; exact hsp)
        (by rw [consList_range_reverse]; exact (hfieldsB ρp hsatC).toBound hw), if_neg hw,
        List.nil_append]

end Setlec.SetR.Interp2
