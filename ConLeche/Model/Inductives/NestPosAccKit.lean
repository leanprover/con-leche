module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Annot.LfpAcc

public section

/-!
# Accessibility hole relations, truncated and extended (lane ACCMODEL, session 3)

The twins of `HoleRel.drop`, `HoleRel.dropBase` and `HoleRel.extendEmpty`
(`ContFrame.lean`) for the accessibility hole relation `HoleRelA`:

* `HoleRelA.drop`: the relation seen at a depth at or above every hole
  (a container instance's key depth), the frames kept;
* `HoleRelA.dropBase`: the relation seen at the block's own depth, the
  frames forgotten (a cached instantiation's parameters lie below every
  frame hole);
* `HoleRelA.extendEmpty`: a frameless relation at the block's own depth
  extended by enclosing frames holding `∅` on both sides — their holes are
  blind (`∅` applied is `∅`) and never hold `pt`, so richness there is
  vacuous.

The admissible items move with the positions (`holeQ_shift`,
`holeQ_nil`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The admissible items, moved -/

/-- The admissible items `k` positions further down. -/
theorem holeQ_shift {ctx : NestCtx} {prog : List NestHole} {d k i n : Nat}
    (h : HoleQ ctx prog d i n) : HoleQ ctx prog (d + k) (i + k) n := by
  rcases h with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, hk, hj, hlt, rfl, hn⟩
  · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
  · exact Or.inr ⟨j, hk, hj, by omega, by omega, hn⟩

/-- The member holes are admissible under any frames. -/
theorem holeQ_nil {ctx : NestCtx} {prog : List NestHole} {d i n : Nat}
    (h : HoleQ ctx [] d i n) : HoleQ ctx prog d i n := by
  rcases h with h | ⟨j, hk, hj, -⟩
  · exact Or.inl h
  · simp at hj

/-- An item of the frame `n` positions down is its item `n` positions up. -/
theorem holds_drop {ρ : Nat → V} {n : Nat} {o : Occ V} :
    Holds (fun i => ρ (i + n)) o ↔ Holds ρ (o.1 + n, o.2) := Iff.rfl

/-! ## Truncation -/

/-- **The accessibility hole relation, truncated** at a depth `h` at or
above every hole: the frame's walk sees the context below `h`. -/
theorem HoleRelA.drop {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (hR : HoleRelA m φ ctx prog d Δa R) {h : Nat}
    (hhi : ctx.hiAt prog.length ≤ h) (hle : h ≤ d) :
    HoleRelA m φ ctx prog h (Δa.drop (d - h)) (R.drop (d - h)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - h)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  frame := by
    rintro i key hk dsa hsp _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < h := by simp only [NestCtx.hiAt] at hhi ⊢; omega
    have hws : ∀ x ∈ key.key.ds, Expr.WScoped h x :=
      fun x hx => Expr.WScoped.mono hhi (hR.dsScoped i key hk x hx)
    have hsp' := DenoteMetaSpine.lift (m := m) (φ := φ) hle hws hsp
    have := hR.frame i key hk _ hsp' ρ ρ' hr is
    simp only [List.map_map, Function.comp_def, interp_liftN_drop] at this
    dsimp only
    rwa [show h - 1 - (ctx.hiAt 0 + i) + (d - h) = d - 1 - (ctx.hiAt 0 + i) by omega]
  dsScoped := hR.dsScoped
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  rich := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    have hQ' : HoleQ ctx prog d (i + (d - h)) vs.length := by
      have := holeQ_shift (k := d - h) hQ
      rwa [show h + (d - h) = d by omega] at this
    obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR.rich ρ ρ₀ hr (i + (d - h)) vs hQ' hpt
    refine ⟨fun j => ρ'' (j + (d - h)), ⟨ρ, ρ'', hr'', rfl, rfl⟩, fun o ho hH => ?_, z, hz, hzp⟩
    have hQo : HoleQ ctx prog d (o.1 + (d - h)) o.2.1.length := by
      have := holeQ_shift (k := d - h) ho
      rwa [show h + (d - h) = d by omega] at this
    exact hle'' (o.1 + (d - h), o.2) hQo hH
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

/-- **The accessibility hole relation seen at the block's own depth**, the
frames forgotten. -/
theorem HoleRelA.dropBase {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (hR : HoleRelA m φ ctx prog d Δa R) (hle : ctx.hiAt prog.length ≤ d) :
    HoleRelA m φ ctx [] (ctx.hiAt 0) (Δa.drop (d - ctx.hiAt 0)) (R.drop (d - ctx.hiAt 0)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - ctx.hiAt 0)) fun hp => hi ?_
    simp only [holeP, NestCtx.hiAt, List.length_nil] at hp hle ⊢
    omega
  frame := by
    intro i hk h
    simp at h
  dsScoped := by
    intro i hk h
    simp at h
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  rich := by
    have hle0 : ctx.hiAt 0 ≤ d := by simp only [NestCtx.hiAt] at hle ⊢; omega
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    have hQ' : HoleQ ctx prog d (i + (d - ctx.hiAt 0)) vs.length := by
      have := holeQ_nil (prog := prog) (holeQ_shift (k := d - ctx.hiAt 0) hQ)
      rwa [show ctx.hiAt 0 + (d - ctx.hiAt 0) = d by omega] at this
    obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR.rich ρ ρ₀ hr _ vs hQ' hpt
    refine ⟨fun j => ρ'' (j + (d - ctx.hiAt 0)), ⟨ρ, ρ'', hr'', rfl, rfl⟩, fun o ho hH => ?_,
      z, hz, hzp⟩
    have hQo : HoleQ ctx prog d (o.1 + (d - ctx.hiAt 0)) o.2.1.length := by
      have := holeQ_nil (prog := prog) (holeQ_shift (k := d - ctx.hiAt 0) ho)
      rwa [show ctx.hiAt 0 + (d - ctx.hiAt 0) = d by omega] at this
    exact hle'' (o.1 + (d - ctx.hiAt 0), o.2) hQo hH
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

/-! ## Empty enclosing frames -/

theorem consList_replicate_lt (n : Nat) (a : V) (σ : Nat → V) {i : Nat} (hi : i < n) :
    consList (List.replicate n a) σ i = a := by
  rw [consList_getD_of_lt _ _ _ (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, List.length_replicate]
  rw [if_pos (by omega)]
  rfl

/-- **Empty enclosing frames**: a frameless relation at the block's own
depth, extended by the enclosing frames of `prog` holding `∅` on both
sides (a `Sort 0` entry each). -/
theorem HoleRelA.extendEmpty {ctx : NestCtx} {Δ0 : List AnnotTerm} {R00 : FrameRel V}
    (hR : HoleRelA m φ ctx [] (ctx.hiAt 0) Δ0 R00) (prog : List NestHole)
    (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x) :
    HoleRelA m φ ctx prog (ctx.hiAt prog.length)
      (List.replicate prog.length (.sort 0) ++ Δ0)
      (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧ σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    have hsp : ∀ σ : Nat → V, SpineFit σ (List.replicate prog.length (AnnotTerm.sort 0))
        (List.replicate prog.length empty) := by
      intro σ
      induction prog.length generalizing σ with
      | zero => trivial
      | succ n ih =>
        exact ⟨by rw [interp_sort]; exact empty_mem_univ 0, ih _⟩
    have e := List.reverse_replicate (n := prog.length) (a := (AnnotTerm.sort 0))
    refine ⟨?_, ?_⟩
    · have := sat_of_spineFit h1 (hsp ρ); rwa [e] at this
    · have := sat_of_spineFit h2 (hsp ρ'); rwa [e] at this
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    by_cases hip : i < prog.length
    · exfalso; apply hi
      simp only [NestCtx.hiAt] at ⊢
      refine ⟨by omega, by omega, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + prog.length := ⟨i - prog.length, by omega⟩
    have e1 := consList_apply_add (List.replicate prog.length (empty : V)) ρ j
    have e2 := consList_apply_add (List.replicate prog.length (empty : V)) ρ' j
    rw [List.length_replicate] at e1 e2
    rw [e1, e2]
    refine hR.agree ρ ρ' hr j fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    simp only [NestCtx.hiAt, List.length_nil] at h1 h2 h3 ⊢
    refine ⟨by omega, by omega, by omega⟩
  frame := by
    rintro i hk hki dsa hsp _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hki).1
      simpa using this
    rw [consList_replicate_lt _ _ _ (by simp only [NestCtx.hiAt]; omega),
      foldlApp_empty, foldlApp_empty]
  dsScoped := hsc
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  rich := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    -- an item at an enclosing frame's hole never holds anything
    have hfr : ∀ (σ : Nat → V) (j : Nat) (us : List V), j < prog.length →
        ¬ ∃ y, y ∈ˢ us.foldl app (consList (List.replicate prog.length empty) σ j) := by
      rintro σ j us hj ⟨y, hy⟩
      rw [consList_replicate_lt _ _ _ hj, foldlApp_empty] at hy
      exact not_mem_empty y hy
    -- an admissible position at or beyond the enclosing frames is a member hole
    have hmem : ∀ j n, HoleQ ctx prog (ctx.hiAt prog.length) j n → prog.length ≤ j →
        HoleQ ctx [] (ctx.hiAt 0) (j - prog.length) n := by
      rintro j n (⟨t, ht, hlt, rfl, hn⟩ | ⟨jj, hk, hj, hlt, rfl, hn⟩) hge
      · refine Or.inl ⟨t, ht, ?_, ?_, hn⟩
        · simp only [NestCtx.hiAt] at hlt ⊢; omega
        · simp only [NestCtx.hiAt] at hge ⊢; omega
      · have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_reverse] at this
        simp only [NestCtx.hiAt] at hge; omega
    by_cases hip : i < prog.length
    · exact absurd ⟨pt, hpt⟩ (hfr ρ i vs hip)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + prog.length := ⟨i - prog.length, by omega⟩
    have hQ0 := hmem _ _ hQ (by omega)
    rw [show j + prog.length - prog.length = j by omega] at hQ0
    have ea : ∀ (σ : Nat → V) (k : Nat),
        consList (List.replicate prog.length (empty : V)) σ (k + prog.length) = σ k := fun σ k => by
      have := consList_apply_add (List.replicate prog.length (empty : V)) σ k
      rwa [List.length_replicate] at this
    rw [ea] at hpt
    obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR.rich ρ ρ₀ hr j vs hQ0 hpt
    refine ⟨consList (List.replicate prog.length empty) ρ'', ⟨ρ, ρ'', hr'', rfl, rfl⟩,
      fun o ho hH => ?_, z, by rw [ea]; exact hz, hzp⟩
    obtain ⟨oi, us, y⟩ := o
    by_cases hoi : oi < prog.length
    · exact absurd ⟨y, hH⟩ (hfr ρ oi us hoi)
    obtain ⟨oj, rfl⟩ : ∃ oj, oi = oj + prog.length := ⟨oi - prog.length, by omega⟩
    have hQo := hmem _ _ ho (by simp only; omega)
    simp only [show oj + prog.length - prog.length = oj by omega] at hQo
    show y ∈ˢ us.foldl app (consList (List.replicate prog.length empty) ρ'' (oj + prog.length))
    rw [ea]
    have hH' : y ∈ˢ us.foldl app (consList (List.replicate prog.length empty) ρ
      (oj + prog.length)) := hH
    rw [ea] at hH'
    exact hle'' (oj, us, y) hQo hH'
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

end ConLeche.Model
