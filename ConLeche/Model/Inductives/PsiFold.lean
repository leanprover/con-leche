module

public import ConLeche.Model.Inductives.FoldChoice
import ConLeche.Model.Inductives.FixRecFrames
public section

/-!
# The forward fold `ψ`: the transport entry (task #279 M-B′ step 3f)

`ψ_A` (DESIGN §M.3, §M.22) is the container's recursor at the pins,
folded at the choice whose targets are the copies' carriers and whose
bodies rebuild with the copies' constructors.  The bodies' spines have
three kinds of entry, decided per field by the AUX kind of the copy's
constructor against the container's recursor view:

* the FIELD variable (aux-ordinary);
* the kit's HYPOTHESIS (a field recursive in the container's view —
  `ψ⁻¹`'s `useIh` case, `InvFold.mixedVarsAV`);
* the TRANSPORT `λ a⃗, Ψ e⃗ (x a⃗)` — a `J`-ordinary field that is
  aux-recursive into another copy `A'`: the term `Ψ` built for `A'`
  earlier along the order (`Verify/Inductives/NestedOrder.lean`,
  `orderFold`), at the field's index readings, applied to the field
  under its own (reflexive) telescope.

The first two are the ψ⁻¹ instance's; this module spells the third
(`viaEntryAV`) at the kit's ih frame — the parameter frame, the
motives, the earlier minors, the fields and the hypotheses, in the
same re-indexing the kit uses for the ih DOMAINS (`ihDomAVM`:
`ihTeleAtR`, `ihIdxAtM`) — reads it at the field's own frame as a
`lamTower` (`interp_viaEntryAV`), and types it into the target-form
product the copy's constructor binder expects (`viaEntry_mem`): from
the ONE fact `ψ` consumes of `Ψ` — at every telescope spine the
application lands in the target at the index values.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The entry -/

/-- The transport's BODY under `m` telescope binders at the ih frame:
`Ψ` (at the parameter frame, lifted over the motives, the earlier
minors, the fields, the hypotheses and the telescope) at the field's
index readings (moved as the ih domain moves them) and the field
variable applied to the telescope variables. -/
@[expose] def viaBodyAV (Ψ : AnnotTerm) (nF o i l m : Nat) (Eis : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (Ψ.liftN (o + nF + l + m) 0)
    (Eis.map (ihIdxAtM nF o i l m) ++
      [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + m)) (teleVarsAV m)])

/-- **The transport entry** `λ a⃗, Ψ e⃗ (x a⃗)` over the field's telescope
`tl` (its codomain bits already the elimination's, as the kit's
`rebit b`), moved to the ih frame as `ihDomAVM` moves the ih domain's
telescope. -/
@[expose] def viaEntryAV (Ψ : AnnotTerm) (nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) : AnnotTerm :=
  mkLamsAV ((ihTeleAtR nF o i l tl).map fun d => (d.2.1, d.2.2)) (viaBodyAV Ψ nF o i l tl.length Eis)

/-! ## Reading it -/

/-- A λ-tower over binder data whose codomain bits are all `b` reads
as `lamTower b`. -/
theorem interp_mkLamsAV_lamTower {b : Nat} {body : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}, (∀ d ∈ ds, d.2.1 = b) →
      interp V σ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) body)
        = lamTower b σ ds fun σ' => interp V σ' body
  | [], _, _ => rfl
  | d :: ds, σ, hb => by
    simp only [List.map_cons, mkLamsAV, lamTower, interp_lam]
    rw [hb d (List.mem_cons_self ..)]
    congr 1
    funext a
    exact interp_mkLamsAV_lamTower fun d' hd' => hb d' (List.mem_cons_of_mem _ hd')

omit [SetTheory V] in
/-- The ih frame shifted past the telescope, the hypotheses, the fields,
the minors and the motives is the parameter frame. -/
theorem shiftE_ihFrame {o nF l : Nat} {ρp : Nat → V} {Ms ms fs ihs as : List V}
    (hms : ms.length + Ms.length = o) (hfs : fs.length = nF) (hihs : ihs.length = l) :
    shiftE (o + nF + l + as.length) 0
        (consList as (consList ihs (consList fs (consList ms (consList Ms ρp)))))
      = ρp := by
  have hfr : consList as (consList ihs (consList fs (consList ms (consList Ms ρp))))
      = consList (Ms ++ ms ++ fs ++ ihs ++ as) ρp := by
    simp only [consList_append]
  rw [hfr, show o + nF + l + as.length = (Ms ++ ms ++ fs ++ ihs ++ as).length from by
    simp only [List.length_append]; omega]
  exact shiftE_consList _ _

/-- **The transport body reads** (under `as` telescope values at the ih
frame) as `Ψ` at the parameter frame applied to the field's index
values at the field's own frame and to the field at `as`. -/
theorem interp_viaBodyAV {nF o i l : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF) (as : List V)
    (Ψ : AnnotTerm) (Eis : List AnnotTerm) :
    interp V (consList as (consList ihs (consList fs (consList ms (consList Ms ρp)))))
        (viaBodyAV Ψ nF o i l as.length Eis)
      = (Eis.map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (interp V ρp Ψ) := by
  unfold viaBodyAV
  rw [interp_mkAppN_map, List.map_append, List.map_map, List.map_singleton, interp_mkAppN_map,
    interp_bvar, interp_liftN, shiftE_ihFrame hms hfs hihs]
  have hf : consList as (consList ihs (consList fs (consList ms (consList Ms ρp))))
      (nF - 1 - i + l + as.length) = fs.getD i pt := by
    rw [consList_apply_add, show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega,
      consList_apply_add, consList_apply_lt' fs _ (by omega),
      show fs.length - 1 - (nF - 1 - i) = i from by omega]
  have hvars : (teleVarsAV as.length).map
      (interp V (consList as (consList ihs (consList fs (consList ms (consList Ms ρp)))))) = as :=
    map_fieldBvars_interp rfl _
  rw [hf, hvars]
  congr 2
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  exact interp_ihIdxAtMK hms hk hfs hihs (Nat.le_of_lt hi) as E

/-- **The transport entry reads** at the ih frame as the λ-tower over
the field's telescope at the field's own frame of the transport body:
`Ψ` at the index values and the field at the telescope's values —
the shape of the kit's target-fold hypotheses (`choice_fold_iota`). -/
theorem interp_viaEntryAV {b nF o i l : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, d.2.1 = b)
    (Ψ : AnnotTerm) (Eis : List AnnotTerm) :
    interp V (consList ihs (consList fs (consList ms (consList Ms ρp)))) (viaEntryAV Ψ nF o i l tl Eis)
      = lamTower b (consList (fs.take i) ρp) tl fun σ' =>
          (Eis.map (interp V σ') ++
            [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app (interp V ρp Ψ) := by
  unfold viaEntryAV ihTeleAtR
  rw [interp_mkLamsAV_lamTower (b := b) (fun d hd => by
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact hbits d' hd')]
  -- the two towers, binder by binder: the moved telescope at the ih
  -- frame under `as` values is the telescope at the field's frame
  suffices h : ∀ (as : List V) (tl' : List (Nat × Nat × AnnotTerm)),
      as.length + tl'.length = tl.length →
      lamTower b (consList as (consList ihs (consList fs (consList ms (consList Ms ρp)))))
          (ihTeleAtGo nF o i l as.length tl')
          (fun σ' => interp V σ' (viaBodyAV Ψ nF o i l tl.length Eis))
        = lamTower b (consList as (consList (fs.take i) ρp)) tl' fun σ' =>
          (Eis.map (interp V σ') ++
            [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app (interp V ρp Ψ) by
    have := h [] tl (by simp)
    simpa only [consList_nil, List.length_nil] using this
  intro as tl' hlen
  induction tl' generalizing as with
  | nil =>
    simp only [ihTeleAtGo, lamTower]
    have hlen' : as.length = tl.length := by simpa using hlen
    rw [← hlen', interp_viaBodyAV hms hk hfs hihs hi as Ψ Eis, frameIdx_consList' as]
  | cons d tl' ih =>
    simp only [ihTeleAtGo, lamTower]
    rw [interp_ihIdxAtMK hms hk hfs hihs (Nat.le_of_lt hi) as d.2.2]
    congr 1
    funext a
    have h1 : cons a (consList as (consList ihs (consList fs (consList ms (consList Ms ρp)))))
        = consList (as ++ [a]) (consList ihs (consList fs (consList ms (consList Ms ρp)))) := by
      rw [consList_append, consList_cons, consList_nil]
    have h2 : cons a (consList as (consList (fs.take i) ρp))
        = consList (as ++ [a]) (consList (fs.take i) ρp) := by
      rw [consList_append, consList_cons, consList_nil]
    rw [h1, h2]
    have := ih (as ++ [a]) (by rw [List.length_append, List.length_singleton]; simp at hlen; omega)
    rw [List.length_append, List.length_singleton] at this
    exact this

/-! ## Typing it -/

/-- **The transport entry is typed**: at the ih frame it inhabits the
nested product over the field's telescope (at the field's own frame)
of a body `B` — the copy's target at the field's index values, when
the caller so chooses — from the ONE fact `ψ` consumes of `Ψ`: at
every spine fitting the telescope, `Ψ` at the index values and the
field at the spine lands in `B`.  The caller derives that fact from
`Ψ`'s own typing (the earlier copy's `ψ`) and the field's fit against
its domain read in target form (a `J`-ordinary field's domain is the
target's pin applied to the index readings, DESIGN §M.22). -/
theorem viaEntry_mem {b nF o i l : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length) {fs ihs : List V}
    (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, d.2.1 = b)
    (Ψ : AnnotTerm) (Eis : List AnnotTerm) {B : List V → V}
    (hΨ : ∀ as : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) as →
      (Eis.map (interp V (consList as (consList (fs.take i) ρp))) ++
        [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (interp V ρp Ψ) ∈ˢ B as) :
    interp V (consList ihs (consList fs (consList ms (consList Ms ρp)))) (viaEntryAV Ψ nF o i l tl Eis)
      ∈ˢ piTele b (teleOfFields (consList (fs.take i) ρp) (tl.map (·.2.2))) B [] := by
  rw [interp_viaEntryAV hms hk hfs hihs hi hbits Ψ Eis]
  refine lamTower_mem_piTele fun as hfit => ?_
  rw [List.nil_append]
  have hfit' := fitsS_teleOfFields.mp hfit
  have hlen : as.length = tl.length := by rw [hfit'.length_eq, List.length_map]
  rw [← hlen, frameIdx_consList' as]
  exact hΨ as hfit'

end ConLeche.Model
