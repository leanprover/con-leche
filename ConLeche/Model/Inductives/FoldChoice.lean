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

open ConLeche.Term ConLeche.Verify SetTheory
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

end ConLeche.Model
