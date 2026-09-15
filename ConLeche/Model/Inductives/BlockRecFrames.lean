module

public import ConLeche.Model.Inductives.MutualRecRead
public import ConLeche.Model.Inductives.SumData
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.FixChains
public section

/-!
# The block's recursor frames, read at `k` motives (task #315, M3)

The uniform route's candidate recursor (`BlockRecCand.lean`) is
typed at the `k`-motive recursor type's reading `mutualRecDataAV`
(`MutualRecRead.lean`) through the kit's obligations; the obligations
read the frame's minors, whose types are `minorAVAtRM` — `FixRecFrames.lean`'s
readings with the motive of the constructor's own member and, per
inductive hypothesis, the motive of the member the field targets.
This file is those readings at a frame `(p⃗, M⃗, m⃗)` with the `k`
motives a LIST (`FixRecFrames.lean` has one motive `M`):

* `spineFit_of_wellDenoted_mkAppN_pis`: an application chain graded
  against a graph-regime Π-tower has its arguments fitting the tower's
  domains — how the recursor type's `WellDenoted` (the run's
  `MutualRecData.okTy`) yields the index readings' FITS (DESIGN §U.5);
* `interp_formerApp`: a former at the block's parameter variables and
  an index spine, under `D` further binders;
* `interp_ihDomAVM`: the ih domain at motive `mot` reads to the nested
  product over the field's telescope at the field's own frame;
* `ihPisAVM_fold_mem`: the ih binders folded along values in their
  domains, the `WellDenoted` premise threaded through (the domains'
  gradings are what the values' memberships are proved from);
* `interp_minorConcAVM`: the minor's conclusion at motive `mot`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Fits from gradings against a Π-tower -/

/-- **A graded application chain against a graph-regime Π-tower fits
its domains**: each application node's package puts the argument in
the domain of the function's graph, and a graph's domain is rigid
(`spineFit_of_wellDenoted_lams` at a Π-tower membership). -/
theorem spineFit_of_wellDenoted_mkAppN_pis {C : AnnotTerm} :
    ∀ {args : List AnnotTerm} {ds : List (Nat × Nat × AnnotTerm)} {σ ρ : Nat → V}
      {f : AnnotTerm} {fv : V},
      (∀ d ∈ ds, d.2.1 ≠ 0) → args.length ≤ ds.length →
      WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = fv → fv ∈ˢ interp V σ (mkPisAV ds C) →
      SpineFit σ ((ds.take args.length).map (·.2.2)) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: args, d :: ds, σ, ρ, f, fv, hnz, hlen, hok, hf, hfv => by
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hd : d.2.1 ≠ 0 := hnz d List.mem_cons_self
    have hfv' : fv ∈ˢ piR d.2.1 (interp V σ d.2.2) fun x => interp V (cons x σ) (mkPisAV ds C) := hfv
    obtain ⟨hgr, -, -, hne⟩ := mem_piR_pos hd hfv'
    rw [hf] at hfm
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0] at hfm
      exact hne (eq_pt_of_mem_piR_zero hfm)
    rw [piR_pos hv, ← hgr] at hfm
    have hmem : interp V ρ a ∈ˢ interp V σ d.2.2 := graph_dom_of_mem_piSet hfm _ ham
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    refine ⟨hmem, ?_⟩
    refine spineFit_of_wellDenoted_mkAppN_pis (C := C) (args := args) (ds := ds)
      (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd')) (by simpa using hlen) hok ?_
      (app_mem_piR_pos hd hfv' hmem)
    rw [interp_app, hf]

/-! ## The former at the block's variables -/

/-- **A former at the parameter variables and an index spine**, under
`D` binders between the parameters and the index binders, reads to
the leaf's fold along the parameters' values and the spine. -/
theorem interp_formerApp {nP nIdx : Nat} {ρp : Nat → V} {as₀ is : List V} (hlen : is.length = nIdx)
    (L : AnnotTerm) (hcl : Term.bvarsBelow 0 L.erase) :
    interp V (consList is (consList as₀ ρp))
        (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx))
      = (((List.range nP).reverse.map ρp) ++ is).foldl SetTheory.app
          (interp V (fun j => ρp (j + nP)) L) := by
  have hσ : ∀ j, consList is (consList as₀ ρp) (j + (as₀.length + nIdx)) = ρp j := by
    intro j
    rw [show j + (as₀.length + nIdx) = (j + as₀.length) + is.length from by omega,
      consList_apply_add, consList_apply_add]
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList is (consList as₀ ρp)))
    (g := SetTheory.app), List.map_append, map_paramBvarsAt_interp hσ,
    show fieldBvars nIdx = (List.range nIdx).map (fun k => AnnotTerm.bvar (nIdx - 1 - k)) from rfl,
    map_fieldBvars_interp hlen, interp_closed (V := V) hcl _ (fun j => ρp (j + nP))]

/-- **A former at the parameter variables and index EXPRESSIONS**,
under `D` binders between the parameters and the frame: the leaf's
fold along the parameters' values and the expressions' readings. -/
theorem interp_formerApp' {nP : Nat} {ρp : Nat → V} {as₀ : List V}
    (L : AnnotTerm) (hcl : Term.bvarsBelow 0 L.erase) (Eis : List AnnotTerm) :
    interp V (consList as₀ ρp) (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + as₀.length) ++ Eis))
      = (((List.range nP).reverse.map ρp) ++ Eis.map (interp V (consList as₀ ρp))).foldl
          SetTheory.app (interp V (fun j => ρp (j + nP)) L) := by
  have hσ : ∀ j, consList as₀ ρp (j + as₀.length) = ρp j := fun j => consList_apply_add as₀ ρp j
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList as₀ ρp)) (g := SetTheory.app),
    List.map_append, map_paramBvarsAt_interp hσ, interp_closed (V := V) hcl _ (fun j => ρp (j + nP))]

/-! ## `Prop`-regime introductions -/

/-- The point inhabits a `Prop`-regime Π-tower with at least one
binder once the conclusion is inhabited at every fitting spine. -/
theorem pt_mem_mkPisAV_zero_of {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, ds ≠ [] → (∀ d ∈ ds, d.2.1 = 0) →
      (∀ xs, SpineFit ρ (ds.map (·.2.2)) xs → ∃ y, y ∈ˢ interp V (consList xs ρ) C) →
      (pt : V) ∈ˢ interp V ρ (mkPisAV ds C)
  | [], _, hne, _, _ => absurd rfl hne
  | d :: ds, ρ, _, hz, hinh => by
    show (pt : V) ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun x => interp V (cons x ρ) (mkPisAV ds C)
    rw [hz d List.mem_cons_self]
    refine pt_mem_piR_zero fun x hx => ?_
    cases ds with
    | nil =>
      show ∃ y, y ∈ˢ interp V (cons x ρ) C
      have := hinh [x] ⟨hx, trivial⟩
      rwa [consList_cons, consList_nil] at this
    | cons d' ds' =>
      refine ⟨pt, pt_mem_mkPisAV_zero_of (List.cons_ne_nil _ _)
        (fun d'' hd'' => hz d'' (List.mem_cons_of_mem _ hd'')) fun xs hxs => ?_⟩
      have := hinh (x :: xs) ⟨hx, hxs⟩
      rwa [consList_cons] at this

/-- The point inhabits a `Prop`-regime nested product over truth
values once the bound is inhabited at every fitting spine. -/
theorem pt_mem_piTele_zero_of {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) ∈ˢ (univZero : V)) →
      (∀ as, FitsS T as → ∃ y, y ∈ˢ B (acc ++ as)) → (pt : V) ∈ˢ piTele 0 T B acc
  | _, .nil, acc, h0, h => by
    obtain ⟨y, hy⟩ := h [] trivial
    have hz := h0 [] trivial
    rw [List.append_nil] at hy hz
    show (pt : V) ∈ˢ B acc
    rw [← eq_pt_of_mem_univZero hz hy]
    exact hy
  | _, .cons A T, acc, h0, h => by
    show (pt : V) ∈ˢ piR 0 A fun a => piTele 0 (T a) B (acc ++ [a])
    refine pt_mem_piR_zero fun a ha => ⟨pt, pt_mem_piTele_zero_of (fun as has => ?_) fun as has => ?_⟩
    · have := h0 (a :: as) ⟨ha, has⟩
      rwa [List.append_cons] at this
    · have := h (a :: as) ⟨ha, has⟩
      rwa [List.append_cons] at this

/-! ## The ih domain at motive `mot` -/

omit [SetTheory V] in
/-- The frame `(p⃗, M⃗, m⃗)` with the motives a list is the single-motive
frame at the first motive with the remaining motives among the
minors. -/
theorem consList_motives_cons (M0 : V) (Msl' msl : List V) (ρp : Nat → V) :
    consList msl (consList (M0 :: Msl') ρp) = consList (Msl' ++ msl) (cons M0 ρp) := by
  rw [consList_cons, consList_append]

/-- The ih domain's body under `as` telescope values at motive `mot`:
motive `mot` at the field's index values (under those values) at the
field applied to them (`interp_ihDomBody` with the motives a list). -/
theorem interp_ihDomBodyM {nF o i l mot : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hmot : mot < Msl.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF) (as : List V) (Eis : List AnnotTerm) :
    interp V (consList as (consList ihs (consList fs (consList msl (consList Msl ρp)))))
        (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + as.length - mot))
          (Eis.map (ihIdxAtM nF o i l as.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + as.length)) (teleVarsAV as.length)]))
      = SetTheory.app
          ((Eis.map (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app
            (Msl.getD mot pt))
          (as.foldl SetTheory.app (fs.getD i pt)) := by
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hmot (Nat.not_lt_zero _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hfr := consList_motives_cons M0 Msl' msl ρp
  have hms : (Msl' ++ msl).length + 1 = o := by
    rw [List.length_append]; simp only [List.length_cons] at ho; omega
  rw [AnnotTerm.mkAppN_append_one, interp_app, interp_mkAppN,
    interp_bvar, interp_mkAppN, interp_bvar,
    ← List.foldl_map (f := interp V (consList as (consList ihs (consList fs (consList msl
      (consList (M0 :: Msl') ρp)))))) (g := SetTheory.app) (l := Eis.map (ihIdxAtM nF o i l as.length)),
    ← List.foldl_map (f := interp V (consList as (consList ihs (consList fs (consList msl
      (consList (M0 :: Msl') ρp)))))) (g := SetTheory.app) (l := teleVarsAV as.length), List.map_map]
  have hM : consList as (consList ihs (consList fs (consList msl (consList (M0 :: Msl') ρp))))
      (nF + o - 1 + l + as.length - mot) = (M0 :: Msl').getD mot pt := by
    rw [show nF + o - 1 + l + as.length - mot
        = ((((M0 :: Msl').length - 1 - mot) + msl.length) + fs.length + ihs.length) + as.length from by
          simp only [List.length_cons] at ho hmot ⊢; omega,
      consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add,
      consList_apply_lt' _ _ (by simp only [List.length_cons] at hmot ⊢; omega),
      show (M0 :: Msl').length - 1 - ((M0 :: Msl').length - 1 - mot) = mot from by
        simp only [List.length_cons] at hmot ⊢; omega]
  have hf : consList as (consList ihs (consList fs (consList msl (consList (M0 :: Msl') ρp))))
      (nF - 1 - i + l + as.length) = fs.getD i pt := by
    rw [consList_apply_add, show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega,
      consList_apply_add, consList_apply_lt' fs _ (by omega),
      show fs.length - 1 - (nF - 1 - i) = i from by omega]
  have hvars : (teleVarsAV as.length).map
      (interp V (consList as (consList ihs (consList fs (consList msl (consList (M0 :: Msl') ρp)))))) = as :=
    map_fieldBvars_interp rfl _
  rw [hM, hf, hvars]
  congr 2
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  rw [hfr]
  exact interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi) as E

/-- **The ih domain at motive `mot`** reads to the nested product over
the field's telescope, at the field's own frame, of motive `mot` at
the field's index values and the field applied to the telescope's
values (`interp_ihDomAV` with the motives a list). -/
theorem interp_ihDomAVM {ℓ nF o i l mot : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hmot : mot < Msl.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, (d.2.1 = 0 ↔ ℓ = 0))
    (Eis : List AnnotTerm) :
    interp V (consList ihs (consList fs (consList msl (consList Msl ρp)))) (ihDomAVM mot nF o i l tl Eis)
      = piTele ℓ (teleOfFields (consList (fs.take i) ρp) (tl.map (·.2.2)))
          (fun as => SetTheory.app
            ((Eis.map (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app
              (Msl.getD mot pt))
            (as.foldl SetTheory.app (fs.getD i pt))) [] := by
  unfold ihDomAVM
  rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := ℓ) (acc := [])
    (B := fun as => SetTheory.app
      ((Eis.map (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app
        (Msl.getD mot pt))
      (as.foldl SetTheory.app (fs.getD i pt)))]
  · obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
      cases Msl with
      | nil => exact absurd hmot (Nat.not_lt_zero _)
      | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
    have hms : (Msl' ++ msl).length + 1 = o := by
      rw [List.length_append]; simp only [List.length_cons] at ho; omega
    rw [consList_motives_cons]
    have hT := piTele_ihTeleAtGo (v := ℓ) (M := M0) (ρp := ρp)
      (B := fun as => SetTheory.app
        ((Eis.map (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app
          ((M0 :: Msl').getD mot pt))
        (as.foldl SetTheory.app (fs.getD i pt))) hms hfs hihs (Nat.le_of_lt hi) tl [] []
    simp only [List.length_nil, consList] at hT
    exact hT
  · intro d hd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact hbits d' hd'
  · intro as hsp
    have hlen : as.length = tl.length := by
      rw [hsp.length_eq, List.length_map, ihTeleAtR_length]
    rw [List.nil_append, ← hlen]
    exact interp_ihDomBodyM ho hmot hfs hihs hi as Eis

/-! ## The ih chain, folded -/

/-- At a zero bit the ih binders' reading is a truth value, given the
body is one at every ih spine of the right length. -/
theorem ihPisAVM_zero_univZero {b nF o : Nat} {moti : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} (hb : b = 0) :
    ∀ (is : List Nat) (l : Nat) (frame : Nat → V) (body : AnnotTerm),
      (∀ ihs : List V, ihs.length = is.length → interp V (consList ihs frame) body ∈ˢ (univZero : V)) →
      interp V frame (ihPisAVM moti nF o b tls Eiss is l body) ∈ˢ (univZero : V)
  | [], _, frame, body, h => by
    show interp V frame body ∈ˢ (univZero : V)
    exact h [] rfl
  | _ :: _, _, _, _, _ => by
    simp only [ihPisAVM, interp_pi]
    rw [hb]
    exact piR_zero_mem_univZero

/-- **The ih binders folded along values in their domains**: the result
is in the body's reading at the ih frame.  At a zero bit the body must
be a truth value at every ih spine of the right length (the
`Prop`-regime side condition of each application). -/
theorem ihPisAVM_fold_mem {b nF o : Nat} {moti : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    ∀ (is : List Nat) (l₀ : Nat) (vs : List V) (frame : Nat → V) (body : AnnotTerm) (x : V),
      vs.length = is.length →
      x ∈ˢ interp V frame (ihPisAVM moti nF o b tls Eiss is l₀ body) →
      (b = 0 → ∀ ihs : List V, ihs.length = is.length →
        interp V (consList ihs frame) body ∈ˢ (univZero : V)) →
      (∀ l, l < is.length →
        vs.getD l pt ∈ˢ interp V (consList (vs.take l) frame)
          (ihDomAVM (moti (is.getD l 0)) nF o (is.getD l 0) (l₀ + l)
            (rebit b (tls.getD (is.getD l 0) [])) (Eiss.getD (is.getD l 0) []))) →
      vs.foldl SetTheory.app x ∈ˢ interp V (consList vs frame) body
  | [], _, [], _, _, _, _, hx, _, _ => hx
  | [], _, _ :: _, _, _, _, hlen, _, _, _ => nomatch hlen
  | _ :: _, _, [], _, _, _, hlen, _, _, _ => nomatch hlen
  | i :: is, l₀, v :: vs, frame, body, x, hlen, hx, hb0, hvs => by
    simp only [ihPisAVM, interp_pi] at hx
    have hv := hvs 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, consList_nil, Nat.add_zero] at hv
    have hxv : SetTheory.app x v
        ∈ˢ interp V (cons v frame) (ihPisAVM moti nF o b tls Eiss is (l₀ + 1) body) := by
      refine app_mem_piR hx hv fun hb y _ => ?_
      exact ihPisAVM_zero_univZero hb is (l₀ + 1) (cons y frame) body fun ihs hl => by
        have := hb0 hb (y :: ihs) (by simp [hl])
        rwa [consList_cons] at this
    rw [List.foldl_cons, consList_cons]
    refine ihPisAVM_fold_mem is (l₀ + 1) vs (cons v frame) body (SetTheory.app x v)
      (by simpa using hlen) hxv ?_ ?_
    · intro hb ihs hl
      have := hb0 hb (v :: ihs) (by simp [hl])
      rwa [consList_cons] at this
    · intro l hl
      have := hvs (l + 1) (by simpa using hl)
      simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons] at this
      rw [show l₀ + (l + 1) = l₀ + 1 + l from by omega] at this
      exact this

/-! ## The minor's conclusion at motive `mot` -/

/-- **The minor's conclusion at motive `mot`** — the motive at the
constructor's index readings and the constructor at the block's
variables — at a field spine over the frame `(p⃗, M⃗, m⃗)`. -/
theorem interp_minorConcAVM {nP nF o mot : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hmot : mot < Msl.length) {fs : List V} (hfs : fs.length = nF)
    (Es : List AnnotTerm) (C : AnnotTerm) (hcl : Term.bvarsBelow 0 C.erase) :
    interp V (consList fs (consList msl (consList Msl ρp)))
        (AnnotTerm.mkAppN (.bvar (nF + o - 1 - mot))
          ((Es.map fun E => E.liftN o nF) ++
            [AnnotTerm.mkAppN C (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)]))
      = SetTheory.app ((Es.map (interp V (consList fs ρp))).foldl SetTheory.app (Msl.getD mot pt))
          ((((List.range nP).reverse.map ρp) ++ fs).foldl SetTheory.app
            (interp V (fun j => ρp (j + nP)) C)) := by
  have hsh : shiftE o 0 (consList msl (consList Msl ρp)) = ρp := by
    rw [← consList_append, ← ho, ← List.length_append, shiftE_consList]
  have hM : consList fs (consList msl (consList Msl ρp)) (nF + o - 1 - mot) = Msl.getD mot pt := by
    rw [show nF + o - 1 - mot = ((Msl.length - 1 - mot) + msl.length) + fs.length from by omega,
      consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega),
      show Msl.length - 1 - (Msl.length - 1 - mot) = mot from by omega]
  rw [AnnotTerm.mkAppN_append_one, interp_app, interp_mkAppN, interp_bvar, hM,
    ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl ρp))))
      (g := SetTheory.app), List.map_map]
  have hidx : Es.map ((interp V (consList fs (consList msl (consList Msl ρp)))) ∘
      fun E => E.liftN o nF) = Es.map (interp V (consList fs ρp)) := by
    apply List.map_congr_left
    intro E _
    simp only [Function.comp]
    rw [interp_liftN, ← hfs, shiftE_consList_len, hsh]
  rw [hidx]
  congr 1
  rw [show consList fs (consList msl (consList Msl ρp)) = consList fs (consList (Msl ++ msl) ρp) from by
      rw [consList_append],
    show nP + o + nF = nP + ((Msl ++ msl).length + nF) from by rw [List.length_append]; omega]
  exact interp_formerApp hfs C hcl

/-! ## The frames' variables, read -/

/-- The motive variable of the ih domain's body at the frame
`(p⃗, M⃗, m⃗, f⃗, ih⃗, a⃗)`: motive `mot` of the list. -/
theorem consList_ih_motive_var {nF o l mot : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hmot : mot < Msl.length) {fs ihs as : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) :
    consList as (consList ihs (consList fs (consList msl (consList Msl ρp))))
      (nF + o - 1 + l + as.length - mot) = Msl.getD mot pt := by
  rw [show nF + o - 1 + l + as.length - mot
      = (((Msl.length - 1 - mot) + msl.length) + fs.length + ihs.length) + as.length from by omega,
    consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add,
    consList_apply_lt' _ _ (by omega), show Msl.length - 1 - (Msl.length - 1 - mot) = mot from by omega]

/-- The motive variable of the minor's conclusion at the frame
`(p⃗, M⃗, m⃗, f⃗)`: motive `mot` of the list. -/
theorem consList_motive_var {nF o mot : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hmot : mot < Msl.length) {fs : List V}
    (hfs : fs.length = nF) :
    consList fs (consList msl (consList Msl ρp)) (nF + o - 1 - mot) = Msl.getD mot pt := by
  rw [show nF + o - 1 - mot = ((Msl.length - 1 - mot) + msl.length) + fs.length from by omega,
    consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega),
    show Msl.length - 1 - (Msl.length - 1 - mot) = mot from by omega]

/-- The moved index expressions read at the ih body's frame as the
expressions at the field's own frame. -/
theorem map_ihIdxAtM_interp {nF o i l : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hne : 0 < Msl.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i ≤ nF) (as : List V) (Eis : List AnnotTerm) :
    (Eis.map (ihIdxAtM nF o i l as.length)).map
        (interp V (consList as (consList ihs (consList fs (consList msl (consList Msl ρp))))))
      = Eis.map (interp V (consList as (consList (fs.take i) ρp))) := by
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hne (Nat.not_lt_zero _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hms : (Msl' ++ msl).length + 1 = o := by
    rw [List.length_append]; simp only [List.length_cons] at ho; omega
  rw [List.map_map]
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  rw [consList_motives_cons]
  exact interp_ihIdxAtM hms hfs hihs hi as E

/-- The lifted index readings of the minor's conclusion read at the
frame `(p⃗, M⃗, m⃗, f⃗)` as the readings at the parameter frame under the
fields. -/
theorem map_liftN_interp {nF o : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) {fs : List V} (hfs : fs.length = nF) (Es : List AnnotTerm) :
    (Es.map fun E => E.liftN o nF).map (interp V (consList fs (consList msl (consList Msl ρp))))
      = Es.map (interp V (consList fs ρp)) := by
  have hsh : shiftE o 0 (consList msl (consList Msl ρp)) = ρp := by
    rw [← consList_append, ← ho, ← List.length_append, shiftE_consList]
  rw [List.map_map]
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  rw [interp_liftN, ← hfs, shiftE_consList_len, hsh]

/-- A spine fits the moved telescope at the ih frame exactly when it
fits the telescope at the field's own frame. -/
theorem spineFit_ihTeleAtGo {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as bs : List V),
      SpineFit (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          ((ihTeleAtGo nF o i l as.length tl).map (·.2.2)) bs ↔
        SpineFit (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | d :: tl, as, b :: bs => by
    show (b ∈ˢ interp V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length d.2.2) ∧
      SpineFit (cons b (consList as (consList ihs (consList fs (consList ms (cons M ρp))))))
        ((ihTeleAtGo nF o i l (as.length + 1) tl).map (·.2.2)) bs) ↔
      (b ∈ˢ interp V (consList as (consList (fs.take i) ρp)) d.2.2 ∧
        SpineFit (cons b (consList as (consList (fs.take i) ρp))) (tl.map (·.2.2)) bs)
    rw [interp_ihIdxAtM hms hfs hihs hi as d.2.2]
    refine and_congr Iff.rfl ?_
    have := spineFit_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [b]) bs
    rw [consList_append, consList_append, List.length_append, List.length_singleton] at this
    exact this

/-- `spineFit_ihTeleAtGo` at the frame with the motives a list, at the
whole telescope. -/
theorem spineFit_ihTeleAtR_M {nF o i l : Nat} {ρp : Nat → V} {Msl msl : List V}
    (ho : Msl.length + msl.length = o) (hne : 0 < Msl.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i ≤ nF)
    (tl : List (Nat × Nat × AnnotTerm)) (bs : List V) :
    SpineFit (consList ihs (consList fs (consList msl (consList Msl ρp))))
        ((ihTeleAtR nF o i l tl).map (·.2.2)) bs ↔
      SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs := by
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hne (Nat.not_lt_zero _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hms : (Msl' ++ msl).length + 1 = o := by
    rw [List.length_append]; simp only [List.length_cons] at ho; omega
  rw [consList_motives_cons]
  have := spineFit_ihTeleAtGo (M := M0) (ρp := ρp) hms hfs hihs hi tl [] bs
  simpa only [List.length_nil, consList_nil, ihTeleAtR] using this

end ConLeche.Model
