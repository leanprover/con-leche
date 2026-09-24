module

public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Annot.BitInst
import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Graphs
import ConLeche.Model.Inductives.StructTele

public section

/-!
# The frame relation (lane CONTSEM, NESTPLAN L3 (iv))

A container frame (`nestFrame`) walks its constructors at the depth
`hi + g` (`hi = ctx.hiAt |prog|`, `g` the reached group's size): the
context TRUNCATED at `hi` — the key's parameters are scoped there — and
extended by one hole per reached group-mate.  The hole relation the walk
is proved along is built from the enclosing one in two moves:

* `HoleRel.drop` — the relation at depth `d` seen `d - h` positions down
  (every hole lies below `hi ≤ h`, so the truncated frames agree off the
  holes, the member holes and the frames' holes are the same values);
* `HoleRel.extend` — the relation at exactly `hi`, extended by the new
  frames' hole values (`consList`), given their context entries and the
  new holes' order at their keys' parameters (`HoleOnArgs`).
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

/-! ## Spines across depths -/

theorem DenoteMetaSpine.lift {h D : Nat} (hle : h ≤ D) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ x ∈ as, Expr.WScoped h x) →
      DenoteMetaSpine m.acval env φ h as vs →
      DenoteMetaSpine m.acval env φ D as (vs.map (AnnotTerm.liftN (D - h) · 0))
  | _, _, _, .nil => .nil
  | a :: as, v :: vs, hws, .cons ha h' => by
    refine .cons ?_ (DenoteMetaSpine.lift hle (fun x hx => hws x (List.mem_cons_of_mem _ hx)) h')
    rw [denoteMeta_lift m.acval_closed (hws a List.mem_cons_self) D hle, ha]
    rfl

theorem DenoteMetaSpine.unlift {h D : Nat} (hle : h ≤ D) :
    ∀ {as : List Expr} {vs' : List AnnotTerm}, (∀ x ∈ as, Expr.WScoped h x) →
      DenoteMetaSpine m.acval env φ D as vs' →
      ∃ vs, DenoteMetaSpine m.acval env φ h as vs ∧ vs' = vs.map (AnnotTerm.liftN (D - h) · 0)
  | _, _, _, .nil => ⟨[], .nil, rfl⟩
  | a :: as, _ :: _, hws, .cons ha h' => by
    obtain ⟨vs, hvs, rfl⟩ :=
      DenoteMetaSpine.unlift hle (fun x hx => hws x (List.mem_cons_of_mem _ hx)) h'
    rw [denoteMeta_lift m.acval_closed (hws a List.mem_cons_self) D hle] at ha
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨v :: vs, .cons hv hvs, rfl⟩

/-- A lifted reading, read below a spine of the lift's length. -/
theorem interp_liftN_consList (xs : List V) (ρ : Nat → V) (a : AnnotTerm) :
    interp V (consList xs ρ) (a.liftN xs.length 0) = interp V ρ a := by
  rw [interp_liftN, shiftE_consList]

/-- A lifted reading, read at a valuation seen `n` positions down. -/
theorem interp_liftN_drop (n : Nat) (ρ : Nat → V) (a : AnnotTerm) :
    interp V ρ (a.liftN n 0) = interp V (fun i => ρ (i + n)) a := by
  rw [interp_liftN]
  congr 1

/-! ## Truncation -/

/-- The relation of the valuations seen `n` positions down. -/
@[expose] def _root_.ConLeche.Semantics.FrameRel.drop (R : FrameRel V) (n : Nat) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ', R ρ ρ' ∧ σ = (fun i => ρ (i + n)) ∧ σ' = (fun i => ρ' (i + n))

theorem Sat_drop' {Δ : List AnnotTerm} {ρ : Nat → V} (h : Sat V Δ ρ)
    (n : Nat) : Sat V (Δ.drop n) (fun j => ρ (j + n)) := by
  intro i Aa hi
  rw [List.getElem?_drop] at hi
  have h1 := h (n + i) Aa hi
  show ρ (i + n) ∈ˢ interp V (fun j => ρ (j + i + 1 + n)) Aa
  have e : (fun j => ρ (j + i + 1 + n)) = fun j => ρ (j + (n + i) + 1) := by
    funext j; congr 1; omega
  rw [e, show i + n = n + i by omega]
  exact h1

/-- **The hole relation, truncated** at a depth `h` at or above every
hole: the frame's walk sees the context below `h`. -/
theorem HoleRel.drop {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (hR : HoleRel m φ ctx prog d Δa R) {h : Nat}
    (hhi : ctx.hiAt prog.length ≤ h) (hle : h ≤ d) :
    HoleRel m φ ctx prog h (Δa.drop (d - h)) (R.drop (d - h)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop' h1 _, Sat_drop' h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - h)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  member := by
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < h := by simp only [NestCtx.hiAt] at hhi; omega
    have := hR.member t ht ρ ρ' hr as has
    dsimp only
    rwa [show h - 1 - (ctx.nP + t) + (d - h) = d - 1 - (ctx.nP + t) by omega]
  frame := by
    rintro i key hk dsa hsp ni _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is his
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < h := by simp only [NestCtx.hiAt] at hhi ⊢; omega
    have hws : ∀ x ∈ key.key.ds, Expr.WScoped h x :=
      fun x hx => Expr.WScoped.mono hhi (hR.dsScoped i key hk x hx)
    have hsp' := DenoteMetaSpine.lift (m := m) (φ := φ) hle hws hsp
    have := hR.frame i key hk _ hsp' ni ρ ρ' hr is his
    simp only [List.map_map, Function.comp_def, interp_liftN_drop] at this
    dsimp only
    rwa [show h - 1 - (ctx.hiAt 0 + i) + (d - h) = d - 1 - (ctx.hiAt 0 + i) by omega]
  dsScoped := hR.dsScoped

/-! ## Extension by new frames -/

theorem consList_getElem_pos {xs : List V} {ρ : Nat → V} {g p : Nat} (hl : xs.length = g)
    (hp : p < g) : consList xs ρ (g - 1 - p) = xs[p]'(by rw [hl]; exact hp) := by
  subst hl
  rw [consList_getD_of_lt _ _ _ (by omega), show xs.length - 1 - (xs.length - 1 - p) = p by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]

/-- **The hole relation, extended by new frames** — the frames `news`
(the reached group of a container instantiation, each at the key's
parameters, scoped at `hi`), their holes holding `vS ρ ρ'` at the
smaller and `vL ρ ρ'` at the larger side of each related pair of the
relation at exactly `hi`.  The caller supplies the holes' context entries
(`hdom`) and their order at their keys' parameters (`hnew`). -/
theorem HoleRel.extend {ctx : NestCtx} {prog : List NestHole} {Δh : List AnnotTerm}
    {R₀ : FrameRel V} (hR₀ : HoleRel m φ ctx prog (ctx.hiAt prog.length) Δh R₀)
    (news : List NestHole)
    (hbase : ∀ x ∈ news, ∀ a ∈ x.key.ds, Expr.WScoped (ctx.hiAt prog.length) a)
    (Ts : List AnnotTerm) (vS vL : (Nat → V) → (Nat → V) → List V)
    (hvS : ∀ ρ ρ', (vS ρ ρ').length = news.length) (hvL : ∀ ρ ρ', (vL ρ ρ').length = news.length)
    (hdom : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (Ts ++ Δh) (consList (vS ρ ρ') ρ) ∧ Sat V (Ts ++ Δh) (consList (vL ρ ρ') ρ'))
    (hnew : ∀ ρ ρ', R₀ ρ ρ' → ∀ (p : Nat) (hk : NestHole), news[p]? = some hk →
      ∀ dsa, DenoteMetaSpine m.acval env φ (ctx.hiAt prog.length) hk.key.ds dsa →
      ∀ (hp : p < news.length) (is : List V),
      (dsa.map (interp V ρ) ++ is).foldl app ((vS ρ ρ')[p]'(by rw [hvS]; exact hp))
        ⊆ˢ (dsa.map (interp V ρ') ++ is).foldl app ((vL ρ ρ')[p]'(by rw [hvL]; exact hp))) :
    HoleRel m φ ctx (news.reverse ++ prog) (ctx.hiAt prog.length + news.length) (Ts ++ Δh)
      (fun σ σ' => ∃ ρ ρ', R₀ ρ ρ' ∧ σ = consList (vS ρ ρ') ρ ∧ σ' = consList (vL ρ ρ') ρ') where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact hdom ρ ρ' hr
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    have hlen : (news.reverse ++ prog).length = news.length + prog.length := by
      rw [List.length_append, List.length_reverse]
    rw [hlen] at hi
    by_cases hig : i < news.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, ?_⟩ <;> first | omega | (simp only [NestCtx.hiAt]; omega)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + news.length := ⟨i - news.length, by omega⟩
    have e1 := consList_apply_add (vS ρ ρ') ρ j
    have e2 := consList_apply_add (vL ρ ρ') ρ' j
    rw [hvS] at e1; rw [hvL] at e2
    rw [e1, e2]
    refine hR₀.agree ρ ρ' hr j fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, by omega, ?_⟩
    simp only [NestCtx.hiAt] at h3 ⊢; omega
  member := by
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < ctx.hiAt prog.length := by simp only [NestCtx.hiAt]; omega
    have e1 := consList_apply_add (vS ρ ρ') ρ (ctx.hiAt prog.length - 1 - (ctx.nP + t))
    have e2 := consList_apply_add (vL ρ ρ') ρ' (ctx.hiAt prog.length - 1 - (ctx.nP + t))
    rw [hvS] at e1; rw [hvL] at e2
    rw [show ctx.hiAt prog.length + news.length - 1 - (ctx.nP + t)
      = ctx.hiAt prog.length - 1 - (ctx.nP + t) + news.length by omega, e1, e2]
    exact hR₀.member t ht ρ ρ' hr as has
  frame := by
    rintro i key hk dsa hsp ni _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is his
    rw [List.reverse_append, List.reverse_reverse] at hk
    have hws : ∀ x ∈ key.key.ds, Expr.WScoped (ctx.hiAt prog.length) x := by
      by_cases hi : i < prog.reverse.length
      · rw [List.getElem?_append_left hi] at hk
        exact hR₀.dsScoped i key hk
      · rw [List.getElem?_append_right (by omega)] at hk
        exact hbase key (List.mem_of_getElem? hk)
    obtain ⟨dsa₀, hsp₀, rfl⟩ :=
      DenoteMetaSpine.unlift (m := m) (φ := φ) (Nat.le_add_right _ news.length) hws hsp
    rw [show ctx.hiAt prog.length + news.length - ctx.hiAt prog.length = news.length by omega]
    have hmS : ∀ σ xs, xs.length = news.length →
        (dsa₀.map (AnnotTerm.liftN news.length · 0)).map (interp V (consList xs σ))
          = dsa₀.map (interp V σ) := by
      intro σ xs hx
      rw [List.map_map]
      refine List.map_congr_left fun a _ => ?_
      show interp V (consList xs σ) (a.liftN news.length 0) = _
      rw [← hx, interp_liftN_consList]
    rw [hmS ρ _ (hvS ρ ρ'), hmS ρ' _ (hvL ρ ρ')]
    by_cases hi : i < prog.reverse.length
    · -- an enclosing frame: the relation at `hi`, below the new holes
      rw [List.getElem?_append_left hi] at hk
      have hlt : i < prog.length := by simpa using hi
      have := hR₀.frame i key hk dsa₀ hsp₀ ni ρ ρ' hr is his
      have e1 := consList_apply_add (vS ρ ρ') ρ (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))
      have e2 := consList_apply_add (vL ρ ρ') ρ' (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))
      rw [hvS] at e1; rw [hvL] at e2
      rw [show ctx.hiAt prog.length + news.length - 1 - (ctx.hiAt 0 + i)
        = ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i) + news.length by
          simp only [NestCtx.hiAt]; omega, e1, e2]
      exact this
    · -- a new frame: its hole value
      rw [List.getElem?_append_right (by omega), List.length_reverse] at hk
      obtain ⟨p, hpdef⟩ : ∃ p, p = i - prog.length := ⟨_, rfl⟩
      rw [← hpdef] at hk
      have hp : p < news.length := (List.getElem?_eq_some_iff.mp hk).1
      have hpos : ctx.hiAt prog.length + news.length - 1 - (ctx.hiAt 0 + i)
          = news.length - 1 - p := by
        simp only [NestCtx.hiAt, List.length_reverse] at hi ⊢; omega
      rw [hpos]
      rw [consList_getElem_pos (hvS ρ ρ') hp, consList_getElem_pos (hvL ρ ρ') hp]
      exact hnew ρ ρ' hr p key hk dsa₀ hsp₀ hp is
  dsScoped := by
    intro i key hk x hx
    have hlen : (news.reverse ++ prog).length = news.length + prog.length := by
      rw [List.length_append, List.length_reverse]
    rw [hlen]
    rw [List.reverse_append, List.reverse_reverse] at hk
    refine Expr.WScoped.mono (show ctx.hiAt prog.length ≤ ctx.hiAt (news.length + prog.length) by
      simp only [NestCtx.hiAt]; omega) ?_
    by_cases hi : i < prog.reverse.length
    · rw [List.getElem?_append_left hi] at hk
      exact hR₀.dsScoped i key hk x hx
    · rw [List.getElem?_append_right (by omega)] at hk
      exact hbase key (List.mem_of_getElem? hk) x hx

/-! ## Forgetting the frames, and empty frames -/

/-- **The hole relation seen at the block's own depth**, the frames
forgotten (a cached instantiation's parameters lie below every frame
hole). -/
theorem HoleRel.dropBase {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (hR : HoleRel m φ ctx prog d Δa R) (hle : ctx.hiAt prog.length ≤ d) :
    HoleRel m φ ctx [] (ctx.hiAt 0) (Δa.drop (d - ctx.hiAt 0)) (R.drop (d - ctx.hiAt 0)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop' h1 _, Sat_drop' h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - ctx.hiAt 0)) fun hp => hi ?_
    simp only [holeP, NestCtx.hiAt, List.length_nil] at hp hle ⊢
    omega
  member := by
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
    have hle' : ctx.hiAt 0 ≤ d := by simp only [NestCtx.hiAt] at hle ⊢; omega
    have := hR.member t ht ρ ρ' hr as has
    dsimp only
    rwa [show ctx.hiAt 0 - 1 - (ctx.nP + t) + (d - ctx.hiAt 0) = d - 1 - (ctx.nP + t) by omega]
  frame := by
    intro i hk h
    simp at h
  dsScoped := by
    intro i hk h
    simp at h

theorem foldl_app_empty : ∀ (as : List V), as.foldl app (empty : V) = empty
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_empty, foldl_app_empty as]

/-- **Empty enclosing frames**: a relation at the block's own depth,
extended by the enclosing frames of `prog` holding the empty set on both
sides (a `Sort 0` entry each) — their holes' order is then trivial. -/
theorem HoleRel.extendEmpty {ctx : NestCtx} {Δ0 : List AnnotTerm} {R00 : FrameRel V}
    (hR : HoleRel m φ ctx [] (ctx.hiAt 0) Δ0 R00) (prog : List NestHole)
    (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x) :
    HoleRel m φ ctx prog (ctx.hiAt prog.length)
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
  member := by
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
    have e1 := consList_apply_add (List.replicate prog.length (empty : V)) ρ
      (ctx.hiAt 0 - 1 - (ctx.nP + t))
    have e2 := consList_apply_add (List.replicate prog.length (empty : V)) ρ'
      (ctx.hiAt 0 - 1 - (ctx.nP + t))
    rw [List.length_replicate] at e1 e2
    rw [show ctx.hiAt prog.length - 1 - (ctx.nP + t)
      = ctx.hiAt 0 - 1 - (ctx.nP + t) + prog.length by simp only [NestCtx.hiAt] at hlt ⊢; omega,
      e1, e2]
    have := hR.member t ht ρ ρ' hr as has
    simpa using this
  frame := by
    rintro i hk hki dsa hsp ni _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is his
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hki).1
      simpa using this
    have hpos : ∀ σ : Nat → V,
        consList (List.replicate prog.length (empty : V)) σ
          (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i)) = empty := by
      intro σ
      rw [consList_getD_of_lt _ _ _ (by simp only [List.length_replicate, NestCtx.hiAt]; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, List.length_replicate]
      rw [if_pos (by omega)]
      rfl
    rw [hpos ρ, hpos ρ', foldl_app_empty, foldl_app_empty]
    exact Subset.refl _
  dsScoped := hsc

end ConLeche.Model
