module

public import ConLeche.Model.Inductives.RecFold
public import ConLeche.Model.Steps.IotaKit
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.FixRuleKit
public section

/-!
# A fold at a motive/minor CHOICE (task #279 M-B′ step 3b)

`RecFold.lean` types and fires a fold `⟦R_t⟧ p⃗ M⃗ m⃗` from a
represented block's recursor, given the spine's fit.  This module
supplies the spine for the ONE shape every nested-route fold has
(DESIGN §M.3): per member `t` a TARGET family `Tg t` — a reading, at
the fold's frame, of a function on the member's index telescope into
the elimination universe — and per constructor `J` a REBUILD leaf
`RC J` — a reading of a function over the constructor's fields with
every recursive field's domain replaced by the target at the field's
index readings, into the target at the constructor's index readings.
The motive of member `t` is then `λ ı⃗ x, Tg t ı⃗` (constant in the
major) and the minor of constructor `J` is `λ f⃗ ih⃗, RC J (f⃗ with every
recursive field replaced by its hypothesis)`.

`ψ⁻¹_m` (the aux recursor at the containers at the pins) and `ψ_A`
(the container's recursor at the copies) are both instances; what
differs is the choice of `Tg`/`RC` and how the two FACTS about them
are discharged.

This half: the motive choice and its membership in the tower's motive
binder (`motChoiceAV_mem`), over the tower's own binder data at the
parameter spine `ps` (`AnnotTerm.instSeq` puts the value at the fold's
frame; the tower's grading supplies the binders' grading).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Generic tower lemmas -/

omit [SetTheory V] in
/-- The `never` datum's bit is one (`PropWhen.holds_never`). -/
theorem pwBit_never_eq (ψ : Name → Nat) : pwBit ψ ConLeche.PropWhen.never = 1 := by
  unfold pwBit
  rw [ConLeche.PropWhen.holds_never]
  rfl

/-- `spineFit_getElem?`'s converse: positional memberships make a fit. -/
theorem spineFit_of_getElem? {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {vs : List V}, vs.length = Fs.length →
      (∀ (n : Nat) (v : V) (F : AnnotTerm), vs[n]? = some v → Fs[n]? = some F →
        v ∈ˢ interp V (consList (vs.take n) ρ) F) →
      SpineFit ρ Fs vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | F :: Fs, v :: vs, hlen, h => by
    refine ⟨?_, spineFit_of_getElem? (by simpa using hlen) fun n v' F' hv hF => ?_⟩
    · have := h 0 v F rfl rfl
      simpa using this
    · have := h (n + 1) v' F' (by simpa using hv) (by simpa using hF)
      rw [List.take_succ_cons, consList_cons] at this
      exact this

/-- `UnderTowerOk` from the Π-tower's grading and the leaf condition at
every fitting spine. -/
theorem underTowerOk_of_wellDenoted {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV ds T) →
      (∀ as, SpineFit σ (ds.map (·.2.2)) as →
        WellDenoted V (consList as σ) b ∧
        interp V (consList as σ) b ∈ˢ interp V (consList as σ) T ∧
        (m = 0 → interp V (consList as σ) T ∈ˢ (univZero : V))) →
      UnderTowerOk m σ b T ds
  | [], σ, _, h => by
    have := h [] trivial
    simpa [UnderTowerOk] using this
  | d :: ds, σ, hwd, h => by
    simp only [mkPisAV, WellDenoted_pi] at hwd
    refine ⟨hwd.1, fun a ha => underTowerOk_of_wellDenoted (hwd.2 a ha) fun as hsp => ?_⟩
    have := h (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A graded Π-tower's binder domain, at a fitting prefix. -/
theorem wellDenoted_mkPisAV_dom {T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV ds T) →
      ∀ (as : List V) (n : Nat) (d : Nat × Nat × AnnotTerm), ds[n]? = some d →
        SpineFit σ ((ds.take n).map (·.2.2)) as →
        WellDenoted V (consList as σ) d.2.2
  | [], _, _, _, _, _, h, _ => nomatch h
  | d :: ds, σ, hwd, as, 0, d', hd, hsp => by
    obtain rfl := Option.some.inj hd
    obtain rfl : as = [] := by
      cases as with
      | nil => rfl
      | cons _ _ => exact hsp.elim
    simp only [mkPisAV, WellDenoted_pi] at hwd
    exact hwd.1
  | d :: ds, σ, hwd, as, n + 1, d', hd, hsp => by
    simp only [mkPisAV, WellDenoted_pi] at hwd
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      rw [List.take_succ_cons, List.map_cons] at hsp
      rw [consList_cons]
      exact wellDenoted_mkPisAV_dom (hwd.2 a hsp.1) as n d' (by simpa using hd) hsp.2

/-- A Π-tower's body is graded at every fitting spine. -/
theorem wellDenoted_mkPisAV_body {T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV ds T) →
      ∀ as, SpineFit σ (ds.map (·.2.2)) as → WellDenoted V (consList as σ) T
  | [], _, h, [], _ => h
  | [], _, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, [], hsp => hsp.elim
  | d :: ds, σ, hwd, a :: as, hsp => by
    simp only [mkPisAV, WellDenoted_pi] at hwd
    rw [consList_cons]
    exact wellDenoted_mkPisAV_body (hwd.2 a hsp.1) as hsp.2

/-- **Graded readings applied along a fitting spine are graded, and the
application lands in the tower's body at the spine's frame** — the
`SpineFit` form of `wellDenotedV_mkAppN_of_fitA`. -/
theorem wellDenotedV_mkAppN_of_spineFit {σ : Nat → V} {ds : List (Nat × Nat × AnnotTerm)}
    {C f : AnnotTerm} {as : List AnnotTerm}
    (hT : WellDenotedV V σ (mkPisAV ds C)) (hf : WellDenotedV V σ f)
    (has : ∀ a ∈ as, WellDenotedV V σ a) (hmem : interp V σ f ∈ˢ interp V σ (mkPisAV ds C))
    (hfit : SpineFit σ (ds.map (·.2.2)) (as.map (interp V σ))) :
    WellDenotedV V σ (AnnotTerm.mkAppN f as) ∧
      interp V σ (AnnotTerm.mkAppN f as) ∈ˢ interp V (consList (as.map (interp V σ)) σ) C := by
  have h := wellDenotedV_mkAppN_of_fitA as hT hf has hmem (teleFitPA_of_spineFit (C := C) hfit)
  have hlen : as.length = ds.length := by
    have := SpineFit.length_eq hfit
    simpa using this
  rw [← hlen, interp_instSeq_consList] at h
  exact h

/-- Replacing a graded tower's body by a sort keeps it graded. -/
theorem wellDenoted_mkPisAV_of_body {T : AnnotTerm} {u : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV ds T) → WellDenoted V σ (mkPisAV ds (.sort u))
  | [], _, _ => trivial
  | d :: ds, σ, h => by
    simp only [mkPisAV, WellDenoted_pi] at h ⊢
    exact ⟨h.1, fun x hx => wellDenoted_mkPisAV_of_body (h.2 x hx)⟩

/-- At nonzero bits, replacing a bit-valid tower's body by a sort keeps
it bit-valid. -/
theorem annotValid_mkPisAV_of_body {T : AnnotTerm} {u b : Nat} (hb : b ≠ 0) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ ds, d.2.1 = b) → AnnotValid V σ (mkPisAV ds T) → AnnotValid V σ (mkPisAV ds (.sort u))
  | [], _, _, _ => trivial
  | d :: ds, σ, hz, h => by
    simp only [mkPisAV, AnnotValid_pi] at h ⊢
    refine ⟨h.1, fun x hx => annotValid_mkPisAV_of_body hb (fun d' hd' => hz d' (.tail _ hd'))
      (h.2.1 x hx), fun h0 => absurd ?_ hb⟩
    rw [← hz d (.head _)]
    exact h0

/-! ## The motive choice -/

namespace IndRepData

variable (d : IndRepData V)

/-- Member `t`'s motive binder data, as one list: its index telescope
(never-bit) and its family at the pins (`motiveAVP` is the Π-tower
over it ending in the elimination sort). -/
@[expose] def motDataAV (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    List (Nat × Nat × AnnotTerm) :=
  rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []) ++
    [(0, pwBit ψ ConLeche.PropWhen.never,
      famAppAV ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) d.nP (d.nP + d.nIdxs.getD t 0)
        (d.nIdxs.getD t 0))]

/-- Member `t`'s motive domain in the tower is the Π-tower over the
motive binder data ending in the elimination sort. -/
theorem motiveAVP_eq (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    motiveAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) ψ d.nP (d.nIdxs.getD t 0) d.elimL
        ((d.ipss ψ).getD t [])
      = mkPisAV (d.motDataAV m ψ t) (.sort (d.elimL.eval ψ)) := by
  unfold motiveAVP motDataAV
  rw [mkPisAV_append]
  rfl

/-- Every motive binder carries the never-bit. -/
theorem mem_motDataAV {m : EnvModel V env} {ψ : Name → Nat} {t : Nat}
    {x : Nat × Nat × AnnotTerm} (hx : x ∈ d.motDataAV m ψ t) :
    x.2.1 = pwBit ψ ConLeche.PropWhen.never := by
  simp only [motDataAV, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | rfl
  · exact mem_rebit h
  · rfl

/-- **The motive value of member `t` at the target choice `Tg`**:
`λ ı⃗ x, Tg t ı⃗` — constant in the major — spelled over the tower's own
motive binder data, at the fold's frame through the parameter spine
`ps` (the binder data are at the block's parameter frame; `instSeq`
substitutes the spine for the parameter variables). -/
@[expose] def motChoiceAV (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (Tg : Nat → AnnotTerm) (t : Nat) : AnnotTerm :=
  ConLeche.Model.AnnotTerm.instSeq ps (d.nP - 1)
    (mkLamsAV ((d.motDataAV m ψ t).map fun x => (x.2.1, x.2.2))
      (AnnotTerm.mkAppN ((Tg t).liftN (d.nP + d.nIdxs.getD t 0 + 1) 0)
        (idxVarsAV (d.nIdxs.getD t 0) 1)))

/-- **The motive value inhabits the tower's motive binder**, at the
parameter frame of the spine, from: the tower's motive domain graded
there, and the target a graded function on the member's index
telescope into the elimination universe. -/
theorem motChoiceAV_mem (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {t : Nat} {ρ : Nat → V} (hps : ps.length = d.nP)
    (hips : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    (hwd : WellDenotedV V (consList (ps.map (interp V ρ)) ρ)
      (motiveAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) ψ d.nP (d.nIdxs.getD t 0) d.elimL
        ((d.ipss ψ).getD t [])))
    (hTg : WellDenotedV V ρ (Tg t) ∧
      interp V ρ (Tg t) ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ)
        (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
          (.sort (d.elimL.eval ψ)))) :
    interp V ρ (d.motChoiceAV m ψ ps Tg t)
      ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ)
          (motiveAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) ψ d.nP (d.nIdxs.getD t 0) d.elimL
            ((d.ipss ψ).getD t [])) := by
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  rw [d.motiveAVP_eq] at hwd ⊢
  unfold motChoiceAV
  rw [← hps, interp_instSeq_consList, hps]
  -- the parameter frame
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ at hwd hTg ⊢
  have hσlen : ∀ (as : List V), as.length = d.nIdxs.getD t 0 + 1 →
      shiftE (d.nP + d.nIdxs.getD t 0 + 1) 0 (consList as σ) = ρ := by
    intro as has
    rw [← hσ, ← consList_append,
      show d.nP + d.nIdxs.getD t 0 + 1 = (ps.map (interp V ρ) ++ as).length from by
        simp [hps, has]; omega,
      shiftE_consList]
  refine mkLamsAV_bits_mem (m := pwBit ψ ConLeche.PropWhen.never)
    (fun x hx => by rw [d.mem_motDataAV hx]) ?_
  refine underTowerOk_of_wellDenoted hwd.1 fun as hsp => ?_
  -- the spine: the indices, then the major
  have hsplit : (d.motDataAV m ψ t).map (·.2.2)
      = (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2) ++
        [famAppAV ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) d.nP (d.nP + d.nIdxs.getD t 0)
          (d.nIdxs.getD t 0)] := by
    simp [motDataAV]
  rw [hsplit] at hsp
  obtain ⟨is, xs, rfl, hfitI, hfitX⟩ := spineFit_append_inv hsp
  have hlenI : is.length = d.nIdxs.getD t 0 := by
    rw [SpineFit.length_eq hfitI, List.length_map, rebit_length, hips]
  obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
    match xs, hfitX with
    | [x], _ => exact ⟨x, rfl⟩
  have hlenAs : (is ++ [x]).length = d.nIdxs.getD t 0 + 1 := by simp [hlenI]
  -- the frame at the leaf and its two shifts
  have hshiftTg : shiftE (d.nP + d.nIdxs.getD t 0 + 1) 0 (consList (is ++ [x]) σ) = ρ :=
    hσlen _ hlenAs
  have hleaf : consList (is ++ [x]) σ = cons x (consList is σ) := by
    rw [consList_append, consList_cons, consList_nil]
  have hshift1 : shiftE 1 0 (consList (is ++ [x]) σ) = consList is σ := by
    rw [hleaf]
    funext i
    simp [shiftE]
  -- the index variables read the index values
  have hidx : (idxVarsAV (d.nIdxs.getD t 0) 1).map (interp V (consList (is ++ [x]) σ)) = is := by
    rw [map_idxVarsAV_interp (ρ₀ := consList is σ) hshift1, ← hlenI, frameIdx_consList']
  -- the lifted target reads the target
  have hTgL : interp V (consList (is ++ [x]) σ) ((Tg t).liftN (d.nP + d.nIdxs.getD t 0 + 1) 0)
      = interp V ρ (Tg t) := by
    rw [interp_liftN, hshiftTg]
  -- the target's tower, lifted under the indices and the major
  have hTow : interp V (consList (is ++ [x]) σ)
      ((mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
        (.sort (d.elimL.eval ψ))).liftN (d.nIdxs.getD t 0 + 1) 0)
      = interp V σ (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
          (.sort (d.elimL.eval ψ))) := by
    rw [interp_liftN, ← hlenAs, shiftE_consList]
  have hfitL : SpineFit (consList (is ++ [x]) σ)
      ((liftDoms (d.nIdxs.getD t 0 + 1) 0
        (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))).map (·.2.2))
      ((idxVarsAV (d.nIdxs.getD t 0) 1).map (interp V (consList (is ++ [x]) σ))) := by
    rw [hidx, spineFit_liftDoms, ← hlenAs, shiftE_consList]
    exact hfitI
  -- the target's tower is graded at the leaf frame: its domains are the
  -- motive's, its body a sort
  have hwdP : WellDenotedV V σ
      (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
        (.sort (d.elimL.eval ψ))) := by
    have h := hwd
    unfold motDataAV at h
    rw [mkPisAV_append] at h
    exact ⟨wellDenoted_mkPisAV_of_body h.1,
      annotValid_mkPisAV_of_body hb (fun x hx => mem_rebit hx) h.2⟩
  have hTowWD : WellDenotedV V (consList (is ++ [x]) σ)
      (mkPisAV (liftDoms (d.nIdxs.getD t 0 + 1) 0
        (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])))
        (.sort (d.elimL.eval ψ))) := by
    have h : WellDenotedV V (consList (is ++ [x]) σ)
        ((mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
          (.sort (d.elimL.eval ψ))).liftN (d.nIdxs.getD t 0 + 1) 0) := by
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_liftN, ← hlenAs, shiftE_consList]; exact hwdP.1
      · rw [AnnotValid_liftN, ← hlenAs, shiftE_consList]; exact hwdP.2
    rw [liftN_mkPisAV, AnnotTerm.liftN_sort] at h
    exact h
  have hmem' : interp V ρ (Tg t) ∈ˢ interp V (consList (is ++ [x]) σ)
      (mkPisAV (liftDoms (d.nIdxs.getD t 0 + 1) 0
        (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])))
        (.sort (d.elimL.eval ψ))) := by
    rw [liftN_mkPisAV, AnnotTerm.liftN_sort] at hTow
    rw [hTow]
    exact hTg.2
  have hfTg : WellDenotedV V (consList (is ++ [x]) σ)
      ((Tg t).liftN (d.nP + d.nIdxs.getD t 0 + 1) 0) := by
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_liftN, hshiftTg]; exact hTg.1.1
    · rw [AnnotValid_liftN, hshiftTg]; exact hTg.1.2
  refine ⟨?_, ?_, fun h0 => absurd h0 hb⟩
  · -- the body is graded
    exact (wellDenotedV_mkAppN_of_spineFit hTowWD hfTg
      (fun a ha => by
        simp only [idxVarsAV, List.mem_map] at ha
        obtain ⟨l, -, rfl⟩ := ha
        exact ⟨trivial, trivial⟩)
      (by rw [hTgL]; exact hmem') hfitL).1.1
  · -- the body's value: the target at the index values, in the universe
    rw [interp_mkAppN_map, hidx, hTgL]
    have := mkPisAV_fold_mem (m := pwBit ψ ConLeche.PropWhen.never)
      (fun x hx => by rw [mem_rebit hx]) (fun h0 => absurd h0 hb) hTg.2 hfitI
    rw [hleaf, interp_sort]
    simpa using this

/-- **The motive value's β**: applied to index values and a major
fitting the motive's binders, the motive value is the target at the
index values (the major is ignored). -/
theorem motChoiceAV_fold (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {t : Nat} {ρ : Nat → V} (hps : ps.length = d.nP)
    (hips : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0) {is : List V} {x : V}
    (hfit : SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV m ψ t).map (·.2.2))
      (is ++ [x])) :
    (is ++ [x]).foldl SetTheory.app (interp V ρ (d.motChoiceAV m ψ ps Tg t))
      = is.foldl SetTheory.app (interp V ρ (Tg t)) := by
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  unfold motChoiceAV
  rw [← hps, interp_instSeq_consList, hps]
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ at hfit ⊢
  have hlenAs : (is ++ [x]).length = d.nIdxs.getD t 0 + 1 := by
    have := SpineFit.length_eq hfit
    rw [this, List.length_map]
    unfold motDataAV
    rw [List.length_append, rebit_length, List.length_singleton, hips]
  have hlenI : is.length = d.nIdxs.getD t 0 := by
    simp at hlenAs; exact hlenAs
  have hfit' : SpineFit σ (((d.motDataAV m ψ t).map fun x => (x.2.1, x.2.2)).map (·.2)) (is ++ [x]) := by
    rw [List.map_map]; exact hfit
  rw [mkLamsAV_fold (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      show y.2.1 ≠ 0
      rw [d.mem_motDataAV hy]; exact hb) hfit']
  have hleaf : consList (is ++ [x]) σ = cons x (consList is σ) := by
    rw [consList_append, consList_cons, consList_nil]
  have hshift1 : shiftE 1 0 (consList (is ++ [x]) σ) = consList is σ := by
    rw [hleaf]; funext i; simp [shiftE]
  have hshiftTg : shiftE (d.nP + d.nIdxs.getD t 0 + 1) 0 (consList (is ++ [x]) σ) = ρ := by
    rw [← hσ, ← consList_append,
      show d.nP + d.nIdxs.getD t 0 + 1 = (ps.map (interp V ρ) ++ (is ++ [x])).length from by
        simp [hps, hlenI]; omega,
      shiftE_consList]
  rw [interp_mkAppN_map, map_idxVarsAV_interp (ρ₀ := consList is σ) hshift1, ← hlenI,
    frameIdx_consList', interp_liftN, hlenI, hshiftTg]

end IndRepData

/-! ## The minor's binder data -/

/-- The ih binders of a minor, as binder data (`ihPisAVM` is the
Π-tower over them). -/
@[expose] def ihDataAVM (moti : Nat → Nat) (nF o b : Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eiss : List (List AnnotTerm)) : List Nat → Nat → List (Nat × Nat × AnnotTerm)
  | [], _ => []
  | i :: is, l =>
    (0, b, ihDomAVM (moti i) nF o i l (rebit b (tls.getD i [])) (Eiss.getD i [])) ::
      ihDataAVM moti nF o b tls Eiss is (l + 1)

omit [SetTheory V] in
theorem ihPisAVM_eq_mkPisAV (moti : Nat → Nat) (nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    ∀ (is : List Nat) (l : Nat) (body : AnnotTerm),
      ihPisAVM moti nF o b tls Eiss is l body = mkPisAV (ihDataAVM moti nF o b tls Eiss is l) body
  | [], _, _ => rfl
  | i :: is, l, body => by
    simp only [ihPisAVM, ihDataAVM, mkPisAV, ihPisAVM_eq_mkPisAV moti nF o b tls Eiss is (l + 1) body]

omit [SetTheory V] in
theorem ihDataAVM_length (moti : Nat → Nat) (nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    ∀ (is : List Nat) (l : Nat), (ihDataAVM moti nF o b tls Eiss is l).length = is.length
  | [], _ => rfl
  | i :: is, l => by simp [ihDataAVM, ihDataAVM_length moti nF o b tls Eiss is (l + 1)]

omit [SetTheory V] in
theorem mem_ihDataAVM {moti : Nat → Nat} {nF o b : Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eiss : List (List AnnotTerm)} :
    ∀ {is : List Nat} {l : Nat} {x : Nat × Nat × AnnotTerm},
      x ∈ ihDataAVM moti nF o b tls Eiss is l → x.2.1 = b
  | [], _, _, h => nomatch h
  | i :: is, l, x, h => by
    simp only [ihDataAVM, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_ihDataAVM h

omit [SetTheory V] in
/-- The ih binders, positionally: ih `n` is over recursive field
`is[n]` at ih position `l + n`. -/
theorem ihDataAVM_getElem? (moti : Nat → Nat) (nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    ∀ (is : List Nat) (l n : Nat),
      (ihDataAVM moti nF o b tls Eiss is l)[n]?
        = (is[n]?).map fun i =>
            (0, b, ihDomAVM (moti i) nF o i (l + n) (rebit b (tls.getD i [])) (Eiss.getD i []))
  | [], _, _ => rfl
  | i :: is, l, 0 => by simp [ihDataAVM]
  | i :: is, l, n + 1 => by
    simp only [ihDataAVM, List.getElem?_cons_succ]
    rw [ihDataAVM_getElem? moti nF o b tls Eiss is (l + 1) n]
    congr 2
    funext i'
    rw [show l + 1 + n = l + (n + 1) from by omega]

/-- A minor's binder data: the fields lifted under the `o` earlier
binders, then the ih binders. -/
@[expose] def minorDataAV (moti : Nat → Nat) (nP nF b o : Nat) (ds : List (Nat × Nat × AnnotTerm))
    (recIdx : List Nat) (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    List (Nat × Nat × AnnotTerm) :=
  rebit b (liftDoms o 0 (ds.drop nP)) ++ ihDataAVM moti nF o b tls Eiss recIdx 0

/-- A minor's conclusion: the constructor's member's motive at the
index readings and the constructor at the fields, under the ih
binders. -/
@[expose] def minorConcAV (mot : Nat) (m : EnvModel V env) (C : Name) (pinsC : List AnnotTerm)
    (ψ : Name → Nat) (nP nF o : Nat) (Es : List AnnotTerm) (nIh : Nat) : AnnotTerm :=
  (AnnotTerm.mkAppN (.bvar (nF + o - 1 - mot))
    ((Es.map fun E => E.liftN o nF) ++
      [famAppAV (m.acval C ψ) pinsC nP (nP + o + nF) nF])).liftN nIh 0

/-- The tower's minor domain is the Π-tower over the minor's binder
data ending in its conclusion. -/
theorem minorAVAtRMP_eq {mot : Nat} {moti : Nat → Nat} {m : EnvModel V env} {C : Name}
    {pinsC : List AnnotTerm} {ψ : Name → Nat} {nP nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Es : List AnnotTerm} {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eiss : List (List AnnotTerm)} :
    minorAVAtRMP mot moti m C pinsC ψ nP nF b o ds Es recIdx tls Eiss
      = mkPisAV (minorDataAV moti nP nF b o ds recIdx tls Eiss)
          (minorConcAV mot m C pinsC ψ nP nF o Es recIdx.length) := by
  unfold minorAVAtRMP minorDataAV minorConcAV
  rw [mkPisAV_append, ihPisAVM_eq_mkPisAV]

theorem mem_minorDataAV {moti : Nat → Nat} {nP nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    {x : Nat × Nat × AnnotTerm} (hx : x ∈ minorDataAV moti nP nF b o ds recIdx tls Eiss) :
    x.2.1 = b := by
  simp only [minorDataAV, List.mem_append] at hx
  rcases hx with h | h
  · exact mem_rebit h
  · exact mem_ihDataAVM h

/-- The minor entries at pins, positionally. -/
theorem fixMinorsDataMP_getElem? {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (pinsOf : Nat → List AnnotTerm)
      (cds : List CtorDatumR) (o j : Nat),
      (fixMinorsDataMP mots tgts pinsOf m ψ nP b cds o)[j]?
        = (cds[j]?).map fun cd => (0, b, minorAVAtRMP (mots j) (tgts j) m cd.1 (pinsOf j) ψ nP
            cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
  | _, _, _, [], _, _ => rfl
  | mots, tgts, pinsOf, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, 0 => by
    simp [fixMinorsDataMP]
  | mots, tgts, pinsOf, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, j + 1 => by
    simp only [fixMinorsDataMP, List.getElem?_cons_succ]
    rw [fixMinorsDataMP_getElem? (fun J => mots (J + 1)) (fun J => tgts (J + 1))
      (fun J => pinsOf (J + 1)) cs (o + 1) j]
    congr 2
    funext cd
    rw [show o + 1 + j = o + (j + 1) from by omega]

omit [SetTheory V] in
/-- The motive entries at pins, positionally. -/
theorem motivesDataGoP_getElem? (Lof : Nat → AnnotTerm) (pinsOf : Nat → List AnnotTerm)
    (nIdxOf : Nat → Nat) (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat)
    (ℓ : Level) (b : Nat) :
    ∀ (k i t : Nat), t < k →
      (motivesDataGoP Lof pinsOf nIdxOf ipsOf ψ nP ℓ b k i)[t]?
        = some (0, b, (motiveAVP (Lof t) (pinsOf t) ψ nP (nIdxOf t) ℓ (ipsOf t)).liftN (i + t) 0)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, 0, _ => by simp [motivesDataGoP]
  | k + 1, i, t + 1, h => by
    simp only [motivesDataGoP, List.getElem?_cons_succ]
    rw [motivesDataGoP_getElem? (fun t => Lof (t + 1)) (fun t => pinsOf (t + 1))
      (fun t => nIdxOf (t + 1)) (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1) t (by omega),
      show i + 1 + t = i + (t + 1) from by omega]

/-! ## The ih domain in target form -/

/-- **The ih domain of recursive field `i` in TARGET form**: the Π-tower
over the field's telescope (moved to the ih frame) of the target of
the field's member at the field's index readings — what a hypothesis
value is when the motive is `λ ı⃗ x, Tg ı⃗`. -/
@[expose] def tgIhDomAV (Tg : Nat → AnnotTerm) (tgt nP nF o i l : Nat)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) : AnnotTerm :=
  mkPisAV (ihTeleAtR nF o i l tl)
    (AnnotTerm.mkAppN ((Tg tgt).liftN (nP + o + nF + l + tl.length) 0)
      (Eis.map (ihIdxAtM nF o i l tl.length)))

/-- The target-form ih domain reads, at the ih frame, to the nested
product over the field's telescope at the field's own frame of the
target at the field's index values. -/
theorem interp_tgIhDomAV {b nP nF o i l : Nat} {ρ : Nat → V} {ps Ms ms : List V}
    (hps : ps.length = nP) (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length)
    {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, (d.2.1 = 0 ↔ b = 0))
    (Tg : Nat → AnnotTerm) (tgt : Nat) (Eis : List AnnotTerm) :
    interp V (consList ihs (consList fs (consList ms (consList Ms (consList ps ρ)))))
        (tgIhDomAV Tg tgt nP nF o i l tl Eis)
      = piTele b (teleOfFields (consList (fs.take i) (consList ps ρ)) (tl.map (·.2.2)))
          (fun as => (Eis.map (interp V (consList as (consList (fs.take i) (consList ps ρ))))).foldl
            SetTheory.app (interp V ρ (Tg tgt))) [] := by
  unfold tgIhDomAV
  rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := b) (acc := [])
    (B := fun as => (Eis.map (interp V (consList as (consList (fs.take i) (consList ps ρ))))).foldl
      SetTheory.app (interp V ρ (Tg tgt)))]
  · have hT := piTele_ihTeleAtGoK (v := b) (ρp := consList ps ρ)
      (B := fun as => (Eis.map (interp V (consList as (consList (fs.take i) (consList ps ρ))))).foldl
        SetTheory.app (interp V ρ (Tg tgt))) hms hk hfs hihs (Nat.le_of_lt hi) tl [] []
    simp only [List.length_nil, consList] at hT
    exact hT
  · intro d hd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact hbits d' hd'
  · intro as hsp
    have hlen : as.length = tl.length := by
      rw [hsp.length_eq, List.length_map, ihTeleAtR_length]
    rw [List.nil_append, interp_mkAppN_map, List.map_map]
    have hE : Eis.map (interp V (consList as (consList ihs (consList fs (consList ms
        (consList Ms (consList ps ρ)))))) ∘ ihIdxAtM nF o i l tl.length)
        = Eis.map (interp V (consList as (consList (fs.take i) (consList ps ρ)))) := by
      apply List.map_congr_left
      intro E _
      simp only [Function.comp_def]
      rw [← hlen]
      exact interp_ihIdxAtMK hms hk hfs hihs (Nat.le_of_lt hi) as E
    rw [hE, interp_liftN]
    congr 1
    rw [← consList_append, ← consList_append, ← consList_append, ← consList_append,
      ← consList_append,
      show nP + o + nF + l + tl.length
        = (ps ++ (Ms ++ (ms ++ (fs ++ (ihs ++ as))))).length from by
          simp [hps, hfs, hihs, hlen]; omega,
      shiftE_consList]

/-- The ih binders in target form: `ihDataAVM` with each hypothesis
domain in target form. -/
@[expose] def ihDataTg (Tg : Nat → AnnotTerm) (moti : Nat → Nat) (nP nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    List Nat → Nat → List (Nat × Nat × AnnotTerm)
  | [], _ => []
  | i :: is, l =>
    (0, b, tgIhDomAV Tg (moti i) nP nF o i l (rebit b (tls.getD i [])) (Eiss.getD i [])) ::
      ihDataTg Tg moti nP nF o b tls Eiss is (l + 1)

/-- A minor's binder data in target form: the fields, then the ih
binders in target form. -/
@[expose] def minorDataTg (Tg : Nat → AnnotTerm) (moti : Nat → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    List (Nat × Nat × AnnotTerm) :=
  rebit b (liftDoms o 0 (ds.drop nP)) ++ ihDataTg Tg moti nP nF o b tls Eiss recIdx 0

/-- Nested products over one telescope agree when their bodies agree
at fitting tuples (`piTele_congr_body`, restated here). -/
theorem piTele_congr_body' {v : Nat} {B B' : List V → V} :
    ∀ {n : Nat} {T : TeleS V n} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) = B' (acc ++ as)) →
      piTele v T B acc = piTele v T B' acc
  | _, .nil, acc, h => by
    have := h [] trivial
    simpa [piTele] using this
  | _, .cons A T, acc, h => by
    simp only [piTele]
    refine piR_congr fun a ha => ?_
    refine piTele_congr_body' fun as hfit => ?_
    have := h (a :: as) ⟨ha, hfit⟩
    rwa [List.append_cons] at this

namespace IndRepData

variable (d : IndRepData V)

/-- The motive spine of the choice. -/
@[expose] def motChoiceAVs (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (Tg : Nat → AnnotTerm) : List AnnotTerm :=
  (List.range d.k).map (d.motChoiceAV m ψ ps Tg)

theorem motChoiceAVs_length (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (Tg : Nat → AnnotTerm) : (d.motChoiceAVs m ψ ps Tg).length = d.k := by
  simp [motChoiceAVs]

theorem motChoiceAVs_getD (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (Tg : Nat → AnnotTerm) (ρ : Nat → V) {t : Nat} (ht : t < d.k) :
    ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)).getD t pt
      = interp V ρ (d.motChoiceAV m ψ ps Tg t) := by
  simp [motChoiceAVs, List.getD_eq_getElem?_getD, List.getElem?_range ht]

/-- **The tower's ih domain at the choice's motives reads as the
target-form ih domain**: the motive's β at the field's index values
and the field along the telescope, pointwise under the nested product.
`hfield` is the field's own typing — its value along the telescope
lands in its member's family at the index readings, which fit the
member's index telescope. -/
theorem interp_ihDom_choice (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {ρ : Nat → V} (hps : ps.length = d.nP) {tgt : Nat} (htgt : tgt < d.k)
    (hips : ((d.ipss ψ).getD tgt []).length = d.nIdxs.getD tgt 0)
    {ms : List V} {o nF i l : Nat} (hms : ms.length + d.k = o) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm)
    (hfield : ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        (tl.map (·.2.2)) as →
      SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD tgt [])).map (·.2.2))
          (Eis.map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
        as.foldl SetTheory.app (fs.getD i pt)
          ∈ˢ interp V (consList
              (Eis.map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
              (consList (ps.map (interp V ρ)) ρ))
            (famAppAV ((d.Ls m ψ).getD tgt default) (d.pinsOf ψ tgt) d.nP
              (d.nP + d.nIdxs.getD tgt 0) (d.nIdxs.getD tgt 0))) :
    interp V (consList ihs (consList fs (consList ms
        (consList ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))))
        (ihDomAVM tgt nF o i l (rebit (d.bb ψ) tl) Eis)
      = interp V (consList ihs (consList fs (consList ms
          (consList ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))))
          (tgIhDomAV Tg tgt d.nP nF o i l (rebit (d.bb ψ) tl) Eis) := by
  have hMs : ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)).length = d.k := by
    simp [motChoiceAVs]
  have hk : 0 < ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)).length := by rw [hMs]; omega
  have hms' : ms.length + ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)).length = o := by
    rw [hMs]; exact hms
  have hpsv : (ps.map (interp V ρ)).length = d.nP := by rw [List.length_map, hps]
  rw [interp_ihDomAVM (ℓ := d.bb ψ) hms' (by rw [hMs]; exact htgt) hfs hihs hi
      (fun x hx => by rw [mem_rebit hx]) Eis,
    interp_tgIhDomAV (b := d.bb ψ) hpsv hms' hk hfs hihs hi (fun x hx => by rw [mem_rebit hx])
      Tg tgt Eis, rebit_map_dom]
  refine piTele_congr_body' fun as hfit => ?_
  rw [List.nil_append]
  obtain ⟨hE, hx⟩ := hfield as (fitsS_teleOfFields.mp hfit)
  rw [d.motChoiceAVs_getD m ψ ps Tg ρ htgt]
  have hsplit : (d.motDataAV m ψ tgt).map (·.2.2)
      = (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD tgt [])).map (·.2.2) ++
        [famAppAV ((d.Ls m ψ).getD tgt default) (d.pinsOf ψ tgt) d.nP (d.nP + d.nIdxs.getD tgt 0)
          (d.nIdxs.getD tgt 0)] := by
    simp [motDataAV]
  have := d.motChoiceAV_fold m (Tg := Tg) hps hips (is := Eis.map (interp V (consList as
      (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
    (x := as.foldl SetTheory.app (fs.getD i pt))
    (by rw [hsplit]; exact SpineFit.append hE ⟨hx, trivial⟩)
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at this
  exact this

/-- **The ih fits transfer to target form**: at the choice's motives, a
spine of hypothesis values fits the tower's ih binders iff it fits
the target-form ih binders — `interp_ihDom_choice` at every position.
`hfields` is every recursive field's own typing (`interp_ihDom_choice`'s
`hfield`). -/
theorem spineFit_ihData_tg (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {ρ : Nat → V} (hps : ps.length = d.nP)
    (hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    {ms : List V} {o nF : Nat} (hms : ms.length + d.k = o) {fs : List V} (hfs : fs.length = nF)
    {moti : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    ∀ (is : List Nat) (l : Nat) (ihs0 : List V), ihs0.length = l →
      (∀ i ∈ is, i < nF ∧ moti i < d.k ∧
        ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
            ((tls.getD i []).map (·.2.2)) as →
          SpineFit (consList (ps.map (interp V ρ)) ρ)
              ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (moti i) [])).map (·.2.2))
              ((Eiss.getD i []).map
                (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
            as.foldl SetTheory.app (fs.getD i pt)
              ∈ˢ interp V (consList ((Eiss.getD i []).map
                  (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
                  (consList (ps.map (interp V ρ)) ρ))
                (famAppAV ((d.Ls m ψ).getD (moti i) default) (d.pinsOf ψ (moti i)) d.nP
                  (d.nP + d.nIdxs.getD (moti i) 0) (d.nIdxs.getD (moti i) 0))) →
      ∀ ihs : List V,
        (SpineFit (consList ihs0 (consList fs (consList ms
            (consList ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))))
          ((ihDataAVM moti nF o (d.bb ψ) tls Eiss is l).map (·.2.2)) ihs ↔
        SpineFit (consList ihs0 (consList fs (consList ms
            (consList ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))))
          ((ihDataTg Tg moti d.nP nF o (d.bb ψ) tls Eiss is l).map (·.2.2)) ihs)
  | [], _, _, _, _, _ => Iff.rfl
  | i :: is, l, ihs0, hl, hfields, ihs => by
    cases ihs with
    | nil => exact Iff.rfl
    | cons v vs =>
      simp only [ihDataAVM, ihDataTg, List.map_cons, SpineFit]
      obtain ⟨hi, hmoti, hfield⟩ := hfields i List.mem_cons_self
      rw [d.interp_ihDom_choice m hps hmoti (hipsLen _ hmoti) hms hfs hl hi (tls.getD i [])
        (Eiss.getD i []) hfield]
      refine and_congr Iff.rfl ?_
      rw [consList_snoc']
      exact spineFit_ihData_tg m hps hipsLen hms hfs is (l + 1) (ihs0 ++ [v]) (by simp [hl])
        (fun i' hi' => hfields i' (List.mem_cons_of_mem _ hi')) vs

/-! ## The minor choice -/

/-- **The minor value of constructor `J` at a body**: the λ-tower over
the tower's own minor binder data with the consumer's `body` (its
rebuild, at the minor's leaf frame: the parameters, the motives, the
earlier minors, the fields and the hypotheses), at the fold's frame
through the parameters, the motives and the earlier minors. -/
@[expose] def minChoiceAV (ψ : Name → Nat) (ps Ms prior : List AnnotTerm)
    (J : Nat) (body : AnnotTerm) : AnnotTerm :=
  ConLeche.Model.AnnotTerm.instSeq (ps ++ Ms ++ prior) (d.nP + d.k + J - 1)
    (mkLamsAV ((minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1).map
      fun x => (x.2.1, x.2.2)) body)

/-- **The minor value inhabits the tower's minor binder** — at the
frame of the parameters, the choice's motives and the earlier minors —
from: the binder graded there (`hwd`), every recursive field's own
typing (`hfield`), the constructor's own typing (`hEs`: its index
readings fit its member's telescope and the constructor at the fields
lands in the family), and the BODY's fact (`hleaf`): at every spine of
fields and target-form hypotheses, the body is graded and lands in the
member's target at the constructor's index readings (a truth value at
the zero bit). -/
theorem minChoiceAV_mem (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {ρ : Nat → V} (hps : ps.length = d.nP) (hk : 0 < d.k)
    (hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    {J : Nat} {C : Name} {nF : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdx : List Nat} {Eiss : List (List AnnotTerm)} {tls : List (List (Nat × Nat × AnnotTerm))}
    (hcd : (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls))
    (hds : ds.length = d.nP + nF) (hmot : d.mems J < d.k)
    (hrec : ∀ i ∈ recIdx, i < nF ∧ d.tgtsR J i < d.k)
    {prior : List AnnotTerm} (hprior : prior.length = J) {body : AnnotTerm}
    (hwd : WellDenotedV V (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ)
      (minorAVAtRMP (d.mems J) (d.tgtsR J) m C (d.pinsOf ψ (d.mems J)) ψ d.nP nF (d.bb ψ) (d.k + J)
        ds Es recIdx tls Eiss))
    (hfield : ∀ i ∈ recIdx, ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
          ((tls.getD i []).map (·.2.2)) as →
        SpineFit (consList (ps.map (interp V ρ)) ρ)
            ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR J i) [])).map (·.2.2))
            ((Eiss.getD i []).map
              (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
          as.foldl SetTheory.app (fs.getD i pt)
            ∈ˢ interp V (consList ((Eiss.getD i []).map
                (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
                (consList (ps.map (interp V ρ)) ρ))
              (famAppAV ((d.Ls m ψ).getD (d.tgtsR J i) default) (d.pinsOf ψ (d.tgtsR J i)) d.nP
                (d.nP + d.nIdxs.getD (d.tgtsR J i) 0) (d.nIdxs.getD (d.tgtsR J i) 0)))
    (hEs : ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2))
          (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))) ∧
        fs.foldl SetTheory.app
            (interp V (consList (ps.map (interp V ρ)) ρ)
              (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J))))
          ∈ˢ interp V (consList (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))))
              (consList (ps.map (interp V ρ)) ρ))
            (famAppAV ((d.Ls m ψ).getD (d.mems J) default) (d.pinsOf ψ (d.mems J)) d.nP
              (d.nP + d.nIdxs.getD (d.mems J) 0) (d.nIdxs.getD (d.mems J) 0)))
    (hleaf : ∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
      SpineFit (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ)
        ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
        (fs ++ ihs) →
      WellDenotedV V (consList (fs ++ ihs)
          (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ)) body ∧
        interp V (consList (fs ++ ihs)
            (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ)) body
          ∈ˢ (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
              SetTheory.app (interp V ρ (Tg (d.mems J))) ∧
        (d.bb ψ = 0 →
          (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
              SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V))) :
    interp V ρ (d.minChoiceAV ψ ps (d.motChoiceAVs m ψ ps Tg) prior J body)
      ∈ˢ interp V (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ)
          (minorAVAtRMP (d.mems J) (d.tgtsR J) m C (d.pinsOf ψ (d.mems J)) ψ d.nP nF (d.bb ψ)
            (d.k + J) ds Es recIdx tls Eiss) := by
  -- the datum at `J`
  have hget : (d.cdsR ψ).getD J default = (C, nF, ds, Es, recIdx, Eiss, tls) := by
    rw [List.getD_eq_getElem?_getD, hcd]; rfl
  unfold minChoiceAV
  rw [hget]
  -- the frames
  have hlen : (ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).length = d.nP + d.k + J := by
    rw [List.length_append, List.length_append, hps, motChoiceAVs_length, hprior]
  rw [← hlen, interp_instSeq_consList]
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ at hfield hEs hleaf ⊢
  have hσJ : consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++ prior).map (interp V ρ)) ρ
      = consList (prior.map (interp V ρ))
          (consList ((d.motChoiceAVs m ψ ps Tg).map (interp V ρ)) σ) := by
    rw [List.map_append, List.map_append, consList_append, consList_append, hσ]
  rw [hσJ] at hwd hleaf ⊢
  generalize hMsv : (d.motChoiceAVs m ψ ps Tg).map (interp V ρ) = Msv at hwd hleaf ⊢
  generalize hpriorv : prior.map (interp V ρ) = priorv at hwd hleaf ⊢
  have hMsvLen : Msv.length = d.k := by rw [← hMsv]; simp [motChoiceAVs]
  have hpriorvLen : priorv.length = J := by rw [← hpriorv, List.length_map, hprior]
  have hms : priorv.length + d.k = d.k + J := by rw [hpriorvLen]; omega
  rw [minorAVAtRMP_eq] at hwd ⊢
  refine mkLamsAV_bits_mem (m := d.bb ψ) (fun x hx => by rw [mem_minorDataAV hx]) ?_
  refine underTowerOk_of_wellDenoted hwd.1 fun as hsp => ?_
  -- the spine: the fields, then the hypotheses
  have hsplitD : (minorDataAV (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2)
      = (rebit (d.bb ψ) (liftDoms (d.k + J) 0 (ds.drop d.nP))).map (·.2.2) ++
        (ihDataAVM (d.tgtsR J) nF (d.k + J) (d.bb ψ) tls Eiss recIdx 0).map (·.2.2) := by
    simp [minorDataAV]
  rw [hsplitD] at hsp
  obtain ⟨fs, ihs, rfl, hfitF, hfitI⟩ := spineFit_append_inv hsp
  have hfs : fs.length = nF := by
    rw [SpineFit.length_eq hfitF, List.length_map, rebit_length, liftDoms_length, List.length_drop,
      hds]
    omega
  have hihs : ihs.length = recIdx.length := by
    rw [SpineFit.length_eq hfitI, List.length_map, ihDataAVM_length]
  -- the fields fit at the parameter frame
  have hshiftO : shiftE (d.k + J) 0 (consList priorv (consList Msv σ)) = σ := by
    rw [← consList_append, show d.k + J = (Msv ++ priorv).length from by
      rw [List.length_append, hMsvLen, hpriorvLen], shiftE_consList]
  have hfitF' : SpineFit σ ((ds.drop d.nP).map (·.2.2)) fs := by
    rw [rebit_map_dom, spineFit_liftDoms, hshiftO] at hfitF
    exact hfitF
  -- the hypotheses fit in target form
  have hfitI' : SpineFit (consList fs (consList priorv (consList Msv σ)))
      ((ihDataTg Tg (d.tgtsR J) d.nP nF (d.k + J) (d.bb ψ) tls Eiss recIdx 0).map (·.2.2)) ihs := by
    have h := d.spineFit_ihData_tg m (Tg := Tg) (ms := priorv) (fs := fs) hps hipsLen hms hfs
      recIdx 0 [] rfl
      (fun i hi => ⟨(hrec i hi).1, (hrec i hi).2, fun as has => by
        rw [hσ]
        rw [hσ] at has
        exact hfield i hi fs hfitF' as has⟩) ihs
    rw [hMsv, hσ, consList_nil] at h
    exact h.mp hfitI
  have hfitTg : SpineFit (consList priorv (consList Msv σ))
      ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
      (fs ++ ihs) := by
    unfold minorDataTg
    rw [List.map_append]
    exact SpineFit.append hfitF hfitI'
  obtain ⟨hwdB, hmemB, h0B⟩ := hleaf fs ihs hfs hihs hfitTg
  -- the conclusion at the leaf frame: the motive at the index readings
  -- and the constructor at the fields, β-reduced to the target
  have hconc : interp V (consList (fs ++ ihs) (consList priorv (consList Msv σ)))
      (minorConcAV (d.mems J) m C (d.pinsOf ψ (d.mems J)) ψ d.nP nF (d.k + J) Es recIdx.length)
      = (Es.map (interp V (consList fs σ))).foldl SetTheory.app (interp V ρ (Tg (d.mems J))) := by
    unfold minorConcAV
    rw [consList_append, interp_liftN, ← hihs, shiftE_consList, interp_mkAppN_map, List.map_append,
      List.map_map, List.map_cons, List.map_nil, interp_bvar]
    -- the motive
    have hmotv : consList fs (consList priorv (consList Msv σ)) (nF + (d.k + J) - 1 - d.mems J)
        = interp V ρ (d.motChoiceAV m ψ ps Tg (d.mems J)) := by
      rw [← consList_append,
        show nF + (d.k + J) - 1 - d.mems J = (priorv ++ fs).length + Msv.length - 1 - d.mems J from by
          rw [List.length_append, hpriorvLen, hfs, hMsvLen]; omega,
        consList_motive_apply (by rw [hMsvLen]; exact hmot), ← hMsv,
        d.motChoiceAVs_getD m ψ ps Tg ρ hmot]
    -- the index readings
    have hEsv : Es.map (interp V (consList fs (consList priorv (consList Msv σ))) ∘
        fun E => E.liftN (d.k + J) nF) = Es.map (interp V (consList fs σ)) := by
      apply List.map_congr_left
      intro E _
      simp only [Function.comp_def]
      rw [interp_liftN, ← hfs, shiftE_consList_len, hshiftO]
    -- the constructor at the fields
    have hctor : interp V (consList fs (consList priorv (consList Msv σ)))
        (famAppAV (m.acval C ψ) (d.pinsOf ψ (d.mems J)) d.nP (d.nP + (d.k + J) + nF) nF)
        = fs.foldl SetTheory.app
            (interp V σ (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J)))) := by
      unfold famAppAV
      rw [interp_mkAppN_map, interp_mkAppN_map, List.map_append, List.foldl_append,
        show d.nP + (d.k + J) + nF - d.nP = d.k + J + nF from by omega, List.map_map,
        show fieldBvars nF = (List.range nF).map (fun q => AnnotTerm.bvar (nF - 1 - q)) from rfl,
        map_fieldBvars_interp hfs, interp_closed (V := V) (m.cval_closedL C ψ) _ σ]
      congr 2
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_def]
      rw [interp_liftN, ← consList_append, ← consList_append,
        show d.k + J + nF = (Msv ++ (priorv ++ fs)).length from by
          rw [List.length_append, List.length_append, hMsvLen, hpriorvLen, hfs]; omega,
        shiftE_consList]
    rw [hmotv, hEsv, hctor, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hE, hx⟩ := hEs fs hfitF'
    have hsplitM : (d.motDataAV m ψ (d.mems J)).map (·.2.2)
        = (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2) ++
          [famAppAV ((d.Ls m ψ).getD (d.mems J) default) (d.pinsOf ψ (d.mems J)) d.nP
            (d.nP + d.nIdxs.getD (d.mems J) 0) (d.nIdxs.getD (d.mems J) 0)] := by
      simp [motDataAV]
    have := d.motChoiceAV_fold m (Tg := Tg) hps (hipsLen _ hmot)
      (is := Es.map (interp V (consList fs σ)))
      (x := fs.foldl SetTheory.app
        (interp V σ (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J)))))
      (by rw [hσ, hsplitM]; exact SpineFit.append hE ⟨hx, trivial⟩)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at this
    exact this
  rw [hconc]
  exact ⟨hwdB.1, hmemB, h0B⟩

/-! ## The minor spine -/

/-- The minor spine of the choice at the bodies, by position: minor
`J`'s value is over the earlier minors. -/
@[expose] def minChoiceAVs (ψ : Name → Nat) (ps Ms : List AnnotTerm) (bodies : Nat → AnnotTerm) :
    Nat → List AnnotTerm
  | 0 => []
  | J + 1 =>
    minChoiceAVs ψ ps Ms bodies J ++
      [d.minChoiceAV ψ ps Ms (minChoiceAVs ψ ps Ms bodies J) J (bodies J)]

omit [SetTheory V] in
theorem minChoiceAVs_length (ψ : Name → Nat) (ps Ms : List AnnotTerm) (bodies : Nat → AnnotTerm) :
    ∀ n, (d.minChoiceAVs ψ ps Ms bodies n).length = n
  | 0 => rfl
  | n + 1 => by simp [minChoiceAVs, minChoiceAVs_length ψ ps Ms bodies n]

omit [SetTheory V] in
theorem minChoiceAVs_take (ψ : Name → Nat) (ps Ms : List AnnotTerm) (bodies : Nat → AnnotTerm) :
    ∀ n J, J ≤ n → (d.minChoiceAVs ψ ps Ms bodies n).take J = d.minChoiceAVs ψ ps Ms bodies J
  | 0, J, h => by
    obtain rfl : J = 0 := Nat.le_zero.mp h
    rfl
  | n + 1, J, h => by
    rcases Nat.lt_or_ge J (n + 1) with h' | h'
    · simp only [minChoiceAVs]
      rw [List.take_append_of_le_length (by rw [d.minChoiceAVs_length]; omega)]
      exact minChoiceAVs_take ψ ps Ms bodies n J (by omega)
    · obtain rfl : J = n + 1 := by omega
      rw [List.take_of_length_le (by rw [d.minChoiceAVs_length]; exact Nat.le_refl _)]

omit [SetTheory V] in
theorem minChoiceAVs_getElem? (ψ : Name → Nat) (ps Ms : List AnnotTerm) (bodies : Nat → AnnotTerm) :
    ∀ n J, J < n →
      (d.minChoiceAVs ψ ps Ms bodies n)[J]?
        = some (d.minChoiceAV ψ ps Ms (d.minChoiceAVs ψ ps Ms bodies J) J (bodies J))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, J, h => by
    rcases Nat.lt_or_ge J n with h' | h'
    · simp only [minChoiceAVs]
      rw [List.getElem?_append_left (by rw [d.minChoiceAVs_length]; exact h')]
      exact minChoiceAVs_getElem? ψ ps Ms bodies n J h'
    · obtain rfl : J = n := by omega
      simp only [minChoiceAVs]
      rw [List.getElem?_append_right (by rw [d.minChoiceAVs_length]; exact Nat.le_refl _),
        d.minChoiceAVs_length]
      simp

end IndRepData

/-- A bit-valid Π-tower's binder domain, at a fitting prefix. -/
theorem annotValid_mkPisAV_dom {T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV ds T) →
      ∀ (as : List V) (n : Nat) (d : Nat × Nat × AnnotTerm), ds[n]? = some d →
        SpineFit σ ((ds.take n).map (·.2.2)) as →
        AnnotValid V (consList as σ) d.2.2
  | [], _, _, _, _, _, h, _ => nomatch h
  | d :: ds, σ, hv, as, 0, d', hd, hsp => by
    obtain rfl := Option.some.inj hd
    obtain rfl : as = [] := by
      cases as with
      | nil => rfl
      | cons _ _ => exact hsp.elim
    simp only [mkPisAV, AnnotValid_pi] at hv
    exact hv.1
  | d :: ds, σ, hv, as, n + 1, d', hd, hsp => by
    simp only [mkPisAV, AnnotValid_pi] at hv
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      rw [List.take_succ_cons, List.map_cons] at hsp
      rw [consList_cons]
      exact annotValid_mkPisAV_dom (hv.2.1 a hsp.1) as n d' (by simpa using hd) hsp.2

/-- A fit of the first `n` entries extends by entry `n`. -/
theorem spineFit_take_succ {ρ : Nat → V} {Fs : List AnnotTerm} {vs : List V} {n : Nat}
    {F : AnnotTerm} {v : V} (hF : Fs[n]? = some F) (hv : vs[n]? = some v)
    (h : SpineFit ρ (Fs.take n) (vs.take n)) (hmem : v ∈ˢ interp V (consList (vs.take n) ρ) F) :
    SpineFit ρ (Fs.take (n + 1)) (vs.take (n + 1)) := by
  rw [List.take_add_one, List.take_add_one, hF, hv]
  exact SpineFit.append h ⟨hmem, trivial⟩

namespace IndRepData

variable (d : IndRepData V)

/-- **The choice's prefix spine fits the tower**: the parameters (the
consumer's fit), the motives (`motChoiceAV_mem`) and the minors
(`minChoiceAV_mem`), each binder's grading read off ONE member's
recursor tower at the fit of the entries before it.  `hmin` bundles
the per-constructor facts `minChoiceAV_mem` takes, at the earlier
minors of the spine. -/
theorem choice_prefix_fit (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {ρ : Nat → V} (bodies : Nat → AnnotTerm) (hps : ps.length = d.nP)
    (hk : 0 < d.k) (hpps : ((d.ppsM 0 ψ).take d.nP).length = d.nP)
    (hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    {t₀ : Nat} (hTower : WellDenotedV V ρ
      (mkPisAV (d.recDataAV m ψ t₀) (mutualConcAV d.k d.nAll (d.nIdxAt t₀) t₀)))
    (hparams : SpineFit ρ ((rebit (d.bb ψ) ((d.ppsM 0 ψ).take d.nP)).map (·.2.2))
      (ps.map (interp V ρ)))
    (hTg : ∀ t, t < d.k → WellDenotedV V ρ (Tg t) ∧
      interp V ρ (Tg t) ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ)
        (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
          (.sort (d.elimL.eval ψ))))
    (hmin : ∀ J, J < d.nAll → ∀ (C : Name) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm))
      (Es : List AnnotTerm) (recIdx : List Nat) (Eiss : List (List AnnotTerm))
      (tls : List (List (Nat × Nat × AnnotTerm))),
      (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls) →
      ds.length = d.nP + nF ∧ d.mems J < d.k ∧ (∀ i ∈ recIdx, i < nF ∧ d.tgtsR J i < d.k) ∧
      (∀ i ∈ recIdx, ∀ fs : List V,
        SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
        ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
            ((tls.getD i []).map (·.2.2)) as →
          SpineFit (consList (ps.map (interp V ρ)) ρ)
              ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR J i) [])).map (·.2.2))
              ((Eiss.getD i []).map
                (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
            as.foldl SetTheory.app (fs.getD i pt)
              ∈ˢ interp V (consList ((Eiss.getD i []).map
                  (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
                  (consList (ps.map (interp V ρ)) ρ))
                (famAppAV ((d.Ls m ψ).getD (d.tgtsR J i) default) (d.pinsOf ψ (d.tgtsR J i)) d.nP
                  (d.nP + d.nIdxs.getD (d.tgtsR J i) 0) (d.nIdxs.getD (d.tgtsR J i) 0))) ∧
      (∀ fs : List V,
        SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
        SpineFit (consList (ps.map (interp V ρ)) ρ)
            ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2))
            (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))) ∧
          fs.foldl SetTheory.app
              (interp V (consList (ps.map (interp V ρ)) ρ)
                (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J))))
            ∈ˢ interp V (consList (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))))
                (consList (ps.map (interp V ρ)) ρ))
              (famAppAV ((d.Ls m ψ).getD (d.mems J) default) (d.pinsOf ψ (d.mems J)) d.nP
                (d.nP + d.nIdxs.getD (d.mems J) 0) (d.nIdxs.getD (d.mems J) 0))) ∧
      (∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
        SpineFit (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
            d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ)
          ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
          (fs ++ ihs) →
        WellDenotedV V (consList (fs ++ ihs)
            (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
              d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ))
            (bodies J) ∧
          interp V (consList (fs ++ ihs)
              (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
                d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ))
              (bodies J)
            ∈ˢ (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
                SetTheory.app (interp V ρ (Tg (d.mems J))) ∧
          (d.bb ψ = 0 →
            (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
                SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)))) :
    SpineFit ρ ((d.recPrefixAV m ψ).map (·.2.2))
      ((ps ++ d.motChoiceAVs m ψ ps Tg ++
        d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies d.nAll).map (interp V ρ)) := by
  -- the three segments and their lengths
  generalize hMs : d.motChoiceAVs m ψ ps Tg = Ms at hmin ⊢
  have hMsLen : Ms.length = d.k := by rw [← hMs]; exact d.motChoiceAVs_length m ψ ps Tg
  have hNsLen : (d.minChoiceAVs ψ ps Ms bodies d.nAll).length = d.nAll :=
    d.minChoiceAVs_length ψ ps Ms bodies d.nAll
  have hpreLen : (d.recPrefixAV m ψ).length = d.nP + d.k + d.nAll := d.recPrefixAV_length m ψ hpps
  have hvalsLen : ((ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ)).length
      = d.nP + d.k + d.nAll := by
    rw [List.length_map, List.length_append, List.length_append, hps, hMsLen, hNsLen]
  -- the tower's binder data are the prefix followed by the trailer
  have hsplit := d.recDataAV_split m ψ t₀
  -- the prefix, positionally
  have hpreGet : ∀ n, n < d.nP + d.k + d.nAll →
      (d.recPrefixAV m ψ)[n]? =
        if n < d.nP then (rebit (d.bb ψ) ((d.ppsM 0 ψ).take d.nP))[n]?
        else if n < d.nP + d.k then
          some (0, d.bb ψ, (motiveAVP ((d.Ls m ψ).getD (n - d.nP) default) (d.pinsOf ψ (n - d.nP)) ψ
            d.nP (d.nIdxs.getD (n - d.nP) 0) d.elimL ((d.ipss ψ).getD (n - d.nP) [])).liftN (n - d.nP) 0)
        else ((d.cdsR ψ)[n - (d.nP + d.k)]?).map fun cd =>
          (0, d.bb ψ, minorAVAtRMP (d.mems (n - (d.nP + d.k))) (d.tgtsR (n - (d.nP + d.k))) m cd.1
            (d.pinsOf ψ (d.mems (n - (d.nP + d.k)))) ψ d.nP cd.2.1 (d.bb ψ) (d.k + (n - (d.nP + d.k)))
            cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) := by
    intro n hn
    unfold recPrefixAV
    split
    · next h =>
      rw [List.getElem?_append_left (by rw [List.length_append, rebit_length, hpps]; omega),
        List.getElem?_append_left (by rw [rebit_length, hpps]; exact h)]
    · next h =>
      split
      · next h' =>
        rw [List.getElem?_append_left (by
            rw [List.length_append, rebit_length, hpps, motivesDataGoP_length, d.Ls_length]; exact h'),
          List.getElem?_append_right (by rw [rebit_length, hpps]; omega), rebit_length, hpps,
          motivesDataGoP_getElem? _ _ _ _ _ _ _ _ _ _ _ (by rw [d.Ls_length]; omega), Nat.zero_add]
      · next h' =>
        rw [List.getElem?_append_right (by
            rw [List.length_append, rebit_length, hpps, motivesDataGoP_length, d.Ls_length]; omega),
          List.length_append, rebit_length, hpps, motivesDataGoP_length, d.Ls_length,
          fixMinorsDataMP_getElem?]
  -- the values, positionally
  have hvalGet : ∀ n, n < d.nP + d.k + d.nAll →
      ((ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ))[n]? =
        if n < d.nP then (ps.map (interp V ρ))[n]?
        else if n < d.nP + d.k then (Ms.map (interp V ρ))[n - d.nP]?
        else some (interp V ρ (d.minChoiceAV ψ ps Ms (d.minChoiceAVs ψ ps Ms bodies (n - (d.nP + d.k)))
          (n - (d.nP + d.k)) (bodies (n - (d.nP + d.k))))) := by
    intro n hn
    rw [List.map_append, List.map_append]
    split
    · next h =>
      rw [List.getElem?_append_left (by rw [List.length_append, List.length_map, List.length_map, hps]; omega),
        List.getElem?_append_left (by rw [List.length_map, hps]; exact h)]
    · next h =>
      split
      · next h' =>
        rw [List.getElem?_append_left (by
            rw [List.length_append, List.length_map, List.length_map, hps, hMsLen]; exact h'),
          List.getElem?_append_right (by rw [List.length_map, hps]; omega), List.length_map, hps]
      · next h' =>
        rw [List.getElem?_append_right (by
            rw [List.length_append, List.length_map, List.length_map, hps, hMsLen]; omega),
          List.length_append, List.length_map, List.length_map, hps, hMsLen, List.getElem?_map,
          d.minChoiceAVs_getElem? ψ ps Ms bodies d.nAll _ (by omega)]
        rfl
  -- the prefixes of the values
  have hvalTakeP : ∀ n, n ≤ d.nP →
      ((ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ)).take n
        = (ps.map (interp V ρ)).take n := by
    intro n hn
    rw [List.map_append, List.map_append, List.take_append_of_le_length (by
      rw [List.length_append, List.length_map, hps]; omega),
      List.take_append_of_le_length (by rw [List.length_map, hps]; exact hn)]
  have hvalTakeM : ∀ t, t ≤ d.k →
      ((ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ)).take (d.nP + t)
        = ps.map (interp V ρ) ++ (Ms.map (interp V ρ)).take t := by
    intro t ht
    rw [List.map_append, List.map_append, List.append_assoc,
      show d.nP + t = (ps.map (interp V ρ)).length + t from by rw [List.length_map, hps],
      List.take_length_add_append, List.take_append_of_le_length (by
        rw [List.length_map, hMsLen]; exact ht)]
  have hvalTakeN : ∀ J, J ≤ d.nAll →
      ((ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ)).take (d.nP + d.k + J)
        = (ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies J).map (interp V ρ) := by
    intro J hJ
    rw [List.map_append, List.map_append, List.map_append, List.map_append,
      show d.nP + d.k + J = (ps.map (interp V ρ) ++ Ms.map (interp V ρ)).length + J from by
        rw [List.length_append, List.length_map, List.length_map, hps, hMsLen],
      List.take_length_add_append, ← List.map_take, d.minChoiceAVs_take ψ ps Ms bodies d.nAll J hJ]
  generalize hvals : (ps ++ Ms ++ d.minChoiceAVs ψ ps Ms bodies d.nAll).map (interp V ρ) = vals
    at hvalsLen hvalGet hvalTakeP hvalTakeM hvalTakeN ⊢
  -- the induction over the positions
  have hupto : ∀ n, n ≤ d.nP + d.k + d.nAll →
      SpineFit ρ (((d.recPrefixAV m ψ).map (·.2.2)).take n) (vals.take n) := by
    intro n
    induction n with
    | zero => intro _; exact trivial
    | succ n ih =>
      intro hn
      have hfit := ih (by omega)
      -- the binder's grading at the fit
      have hgr : ∀ D, (d.recPrefixAV m ψ)[n]? = some D →
          WellDenotedV V (consList (vals.take n) ρ) D.2.2 := by
        intro D hD
        have hD' : (d.recDataAV m ψ t₀)[n]? = some D := by
          rw [hsplit, List.getElem?_append_left (by rw [hpreLen]; omega)]; exact hD
        have hfit' : SpineFit ρ (((d.recDataAV m ψ t₀).take n).map (·.2.2)) (vals.take n) := by
          rw [hsplit, List.take_append_of_le_length (by rw [hpreLen]; omega), List.map_take]
          exact hfit
        exact ⟨wellDenoted_mkPisAV_dom hTower.1 _ n D hD' hfit',
          annotValid_mkPisAV_dom hTower.2 _ n D hD' hfit'⟩
      rcases Nat.lt_or_ge n d.nP with h | h
      · -- a parameter
        obtain ⟨D, hD⟩ : ∃ D, (rebit (d.bb ψ) ((d.ppsM 0 ψ).take d.nP))[n]? = some D :=
          ⟨_, List.getElem?_eq_getElem (by rw [rebit_length, hpps]; exact h)⟩
        obtain ⟨v, hv⟩ : ∃ v, (ps.map (interp V ρ))[n]? = some v :=
          ⟨_, List.getElem?_eq_getElem (by rw [List.length_map, hps]; exact h)⟩
        refine spineFit_take_succ (F := D.2.2) (v := v) ?_ ?_ hfit ?_
        · rw [List.getElem?_map, hpreGet n (by omega), if_pos h, hD]; rfl
        · rw [hvalGet n (by omega), if_pos h, hv]
        · rw [hvalTakeP n (by omega)]
          exact spineFit_getElem? hparams n v D.2.2 hv (by rw [List.getElem?_map, hD]; rfl)
      · rcases Nat.lt_or_ge n (d.nP + d.k) with h' | h'
        · -- a motive
          obtain ⟨t, rfl⟩ : ∃ t, n = d.nP + t := ⟨n - d.nP, by omega⟩
          have ht : t < d.k := by omega
          have hpre' : (d.recPrefixAV m ψ)[d.nP + t]? = some (0, d.bb ψ,
              (motiveAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) ψ d.nP (d.nIdxs.getD t 0)
                d.elimL ((d.ipss ψ).getD t [])).liftN t 0) := by
            rw [hpreGet _ (by omega), if_neg (by omega), if_pos h', Nat.add_sub_cancel_left]
          have hvt : (Ms.map (interp V ρ))[t]? = some (interp V ρ (d.motChoiceAV m ψ ps Tg t)) := by
            rw [← hMs]; simp [motChoiceAVs, List.getElem?_range ht]
          have hval' : vals[d.nP + t]? = some (interp V ρ (d.motChoiceAV m ψ ps Tg t)) := by
            rw [hvalGet _ (by omega), if_neg (by omega), if_pos h', Nat.add_sub_cancel_left, hvt]
          refine spineFit_take_succ (F := (motiveAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) ψ
              d.nP (d.nIdxs.getD t 0) d.elimL ((d.ipss ψ).getD t [])).liftN t 0) ?_ hval' hfit ?_
          · rw [List.getElem?_map, hpre']; rfl
          · have hsh : shiftE t 0 (consList ((Ms.map (interp V ρ)).take t)
                (consList (ps.map (interp V ρ)) ρ)) = consList (ps.map (interp V ρ)) ρ := by
              have hlt : ((Ms.map (interp V ρ)).take t).length = t := by
                rw [List.length_take, List.length_map, hMsLen]; omega
              have := shiftE_consList ((Ms.map (interp V ρ)).take t) (consList (ps.map (interp V ρ)) ρ)
              rw [hlt] at this
              exact this
            have hwd := hgr _ hpre'
            rw [hvalTakeM t (by omega), consList_append] at hwd ⊢
            rw [interp_liftN, hsh]
            obtain ⟨hwd1, hwd2⟩ := hwd
            rw [WellDenoted_liftN, hsh] at hwd1
            rw [AnnotValid_liftN, hsh] at hwd2
            exact d.motChoiceAV_mem m hps (hipsLen t ht) ⟨hwd1, hwd2⟩ (hTg t ht)
        · -- a minor
          obtain ⟨J, rfl⟩ : ∃ J, n = d.nP + d.k + J := ⟨n - (d.nP + d.k), by omega⟩
          have hJ : J < d.nAll := by omega
          obtain ⟨cd, hcd⟩ : ∃ cd, (d.cdsR ψ)[J]? = some cd :=
            ⟨_, List.getElem?_eq_getElem (by rw [d.cdsR_length]; exact hJ)⟩
          obtain ⟨C, nF, ds, Es, recIdx, Eiss, tls⟩ := cd
          have hpre' : (d.recPrefixAV m ψ)[d.nP + d.k + J]? = some (0, d.bb ψ,
              minorAVAtRMP (d.mems J) (d.tgtsR J) m C (d.pinsOf ψ (d.mems J)) ψ d.nP nF (d.bb ψ)
                (d.k + J) ds Es recIdx tls Eiss) := by
            rw [hpreGet _ (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
              hcd]
            rfl
          have hval' : vals[d.nP + d.k + J]? = some (interp V ρ (d.minChoiceAV ψ ps Ms
              (d.minChoiceAVs ψ ps Ms bodies J) J (bodies J))) := by
            rw [hvalGet _ (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
          obtain ⟨hds, hmot, hrec, hfield, hEs, hleaf⟩ := hmin J hJ C nF ds Es recIdx Eiss tls hcd
          refine spineFit_take_succ (F := minorAVAtRMP (d.mems J) (d.tgtsR J) m C
              (d.pinsOf ψ (d.mems J)) ψ d.nP nF (d.bb ψ) (d.k + J) ds Es recIdx tls Eiss)
            ?_ hval' hfit ?_
          · rw [List.getElem?_map, hpre']; rfl
          · have hwd := hgr _ hpre'
            rw [hvalTakeN J (by omega)] at hwd ⊢
            rw [← hMs] at hwd hleaf ⊢
            exact d.minChoiceAV_mem m hps hk hipsLen hcd hds hmot hrec
              (d.minChoiceAVs_length ψ ps _ bodies J) hwd hfield hEs hleaf
  have := hupto (d.nP + d.k + d.nAll) (Nat.le_refl _)
  rw [List.take_of_length_le (by rw [List.length_map, hpreLen]; exact Nat.le_refl _),
    List.take_of_length_le (by rw [hvalsLen]; exact Nat.le_refl _)] at this
  exact this

end IndRepData

end ConLeche.Model
