module

public import ConLeche.SetModel.HoleOp
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# The closed tuple of a FLAT hole-operator block (lane NESTW-KIT)

(W) at `w ≠ 0` for a HOLEOP block datum (`UBlock`, `SetModel/HoleOp.lean`)
whose every constructor's fields are presented FLAT (`FlatCtor`): each
field is either ORDINARY (a hole-free type read at the frame) or
RECURSIVE (`RTel`: a Π-tower of hole-free domains, nonzero codomain bits,
over a member hole at a hole-free index tuple).  This is the shape of the
TRANSIENT WIDE operator of a nested block (`SetModel/NestWide.lean`):
every nested occurrence is a plain hole at its key, so the wide datum is
flat.  It is the set-level twin of the Model tier's
`LfpDatum.closed_of_flat` (`Model/Annot/LfpHoleWitness.lean`).

**R3's caveat, as a named premise: `HoleUnread`** — no field type (an
ordinary field's type, a recursive field's Π-domains or its hole's index
tuple) reads the value of a RECURSIVE field.  The kernel supplies it:
`nestPos`'s U4 decline ("no later field and no result index uses a
recursive or reflexive field", `Kernel/Inductives/Positivity.lean`).
The result-index half of U4 is NOT needed here: a shape is cut from the
fibre at its own index.

The container presentation (`tupleContainer_closed_exists`):
* a SHAPE is the member tag, the constructor tag and the SHADOW of an
  element's spine — the recursive values replaced by `pt` — among the
  shadows of the fibre's elements at SOME tuple of the space; by
  `HoleUnread` the shadow fits the shadow telescope (`shTele`: the
  ordinary types at the shadow frame, `{pt}` at a recursive field), so
  the shape set is a member of the universe;
* its POSITIONS are the recursive fields' Π-spines, tagged by the
  field's position (`posSet`), read at the shadow frame;
* a position's TARGET is the member its hole names at the hole's index
  reading (`tgtAt`);
* the BUILDER (`rebuild`) puts the shadow's ordinary values back and
  curries the function on positions into each recursive slot.
-/

namespace ConLeche.SetTheory

open Tower
open ConLeche.SetModel

universe u

variable {V : Type u} [SetTheory V]

/-! ## Universe facts -/

/-- Application stays inside a positive universe. -/
theorem app_mem_univ_pos {w : Nat} (hw : w ≠ 0) {g : V} (hg : g ∈ˢ (univ w : V)) (p : V) :
    app g p ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold app
  split
  · exact hU.pt_mem hg
  · exact hU.sUnion_mem (hU.sep_mem (hU.sUnion_mem (hU.sUnion_mem hg)))

theorem mkTower_mem_univ_pos {w : Nat} (hw : w ≠ 0) :
    ∀ {fs : List V}, (∀ y, y ∈ fs → y ∈ˢ (univ w : V)) → mkTower fs ∈ˢ (univ w : V)
  | [], _ => (univ_isTGUniverse hw).transitive (unitSet_mem_univ w) pt_mem_unitSet
  | y :: fs, h => by
    show spair y (mkTower fs) ∈ˢ _
    rw [spair_eq_kpair]
    exact (univ_isTGUniverse hw).kpair_mem (unitSet_mem_univ w) (h y List.mem_cons_self)
      (mkTower_mem_univ_pos hw fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem uinj_mem_univ_pos {w : Nat} (hw : w ≠ 0) (j : Nat) {fs : List V}
    (h : ∀ y, y ∈ fs → y ∈ˢ (univ w : V)) : uinj w j fs ∈ˢ (univ w : V) := by
  rw [uinj_pos hw]
  show spair (vnat j) (mkTower fs) ∈ˢ _
  rw [spair_eq_kpair]
  exact (univ_isTGUniverse hw).kpair_mem (unitSet_mem_univ w) (vnat_mem_univ_pos hw j)
    (mkTower_mem_univ_pos hw h)

/-! ## Recursive field types: Π-towers over a member hole -/

/-- **A recursive field's type**, flat: a Π-tower of hole-free domains
over member `m`'s hole at a hole-free index tuple. -/
inductive RTel (V : Type u) : Type u
  /-- `T_m ⟨es⟩` -/
  | hole (m : Nat) (es : (Nat → V) → V)
  /-- `Π (a : A), B` at codomain bit `v` -/
  | pi (v : Nat) (A : (Nat → V) → V) (B : RTel V)

namespace RTel

/-- The field type's reading at a frame and a hole tuple. -/
noncomputable def read : RTel V → (Nat → V) → (Nat → V) → V
  | hole m es, ρ, X => app (X m) (es ρ)
  | pi v A B, ρ, X => piR v (A ρ) fun a => B.read (fcons a ρ) X

/-- Well-formed at width `K` and level `w`: the hole names a component,
the bits are nonzero, the domains are sets of the level. -/
def WF (w K : Nat) : RTel V → Prop
  | hole m _ => m < K
  | pi v A B => v ≠ 0 ∧ (∀ ρ, A ρ ∈ˢ (univ w : V)) ∧ B.WF w K

/-- The Π-spines (the positions of one field). -/
noncomputable def spines (w : Nat) : RTel V → (Nat → V) → V
  | hole _ _, _ => unitSet
  | pi _ A B, ρ => sigmaSet w (A ρ) fun a => B.spines w (fcons a ρ)

/-- The member a spine targets. -/
noncomputable def tgtM : RTel V → V → Nat
  | hole m _, _ => m
  | pi _ _ B, s => B.tgtM (ssnd s)

/-- The index tuple a spine targets. -/
noncomputable def tgtI : RTel V → (Nat → V) → V → V
  | hole _ es, ρ, _ => es ρ
  | pi _ _ B, ρ, s => B.tgtI (fcons (sfst s) ρ) (ssnd s)

/-- A function value read along a spine. -/
noncomputable def evalAt : RTel V → V → V → V
  | hole _ _, f, _ => f
  | pi _ _ B, f, s => B.evalAt (app f (sfst s)) (ssnd s)

/-- The curried function of a function on spines. -/
noncomputable def curry : RTel V → (Nat → V) → (V → V) → V
  | hole _ _, _, G => G pt
  | pi _ A B, ρ, G => graph (fun a => B.curry (fcons a ρ) fun s => G (kpair a s)) (A ρ)

/-- Two frames the field type reads alike. -/
def Agree : RTel V → (Nat → V) → (Nat → V) → Prop
  | hole _ es, ρ, ρ' => es ρ = es ρ'
  | pi _ A B, ρ, ρ' => A ρ = A ρ' ∧ ∀ a, B.Agree (fcons a ρ) (fcons a ρ')

theorem read_agree : ∀ (r : RTel V) {ρ ρ' : Nat → V}, r.Agree ρ ρ' → ∀ X, r.read ρ X = r.read ρ' X
  | hole _ _, _, _, h, _ => by simp only [read]; rw [show _ = _ from h]
  | pi _ _ B, _, _, h, X => by
    simp only [read]
    rw [h.1]
    congr 1
    funext a
    exact read_agree B (h.2 a) X

theorem spines_agree (w : Nat) : ∀ (r : RTel V) {ρ ρ' : Nat → V}, r.Agree ρ ρ' →
    r.spines w ρ = r.spines w ρ'
  | hole _ _, _, _, _ => rfl
  | pi _ _ B, _, _, h => by
    simp only [spines]
    rw [h.1]
    congr 1
    funext a
    exact spines_agree w B (h.2 a)

theorem tgtI_agree : ∀ (r : RTel V) {ρ ρ' : Nat → V}, r.Agree ρ ρ' → ∀ s, r.tgtI ρ s = r.tgtI ρ' s
  | hole _ _, _, _, h, _ => h
  | pi _ _ B, _, _, h, s => tgtI_agree B (h.2 (sfst s)) (ssnd s)

theorem curry_agree : ∀ (r : RTel V) {ρ ρ' : Nat → V}, r.Agree ρ ρ' → ∀ G, r.curry ρ G = r.curry ρ' G
  | hole _ _, _, _, _, _ => rfl
  | pi _ _ B, _, _, h, G => by
    simp only [curry]
    rw [h.1]
    congr 1
    funext a
    exact curry_agree B (h.2 a) _

theorem tgtM_lt {w K : Nat} : ∀ (r : RTel V), r.WF w K → ∀ s, r.tgtM s < K
  | hole _ _, h, _ => h
  | pi _ _ B, h, s => tgtM_lt B h.2.2 (ssnd s)

variable {w : Nat}

/-- A function value along a spine lands in the targeted fibre. -/
theorem evalAt_mem (hw : w ≠ 0) {K : Nat} : ∀ (r : RTel V), r.WF w K → ∀ {ρ X : Nat → V} {f s : V},
    f ∈ˢ r.read ρ X → s ∈ˢ r.spines w ρ → r.evalAt f s ∈ˢ app (X (r.tgtM s)) (r.tgtI ρ s)
  | hole _ _, _, _, _, _, _, hf, _ => hf
  | pi _ _ B, hwf, ρ, X, f, s, hf, hs => by
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hs
    obtain rfl := hpos hw
    have hfa := (mem_piR_pos hwf.1 hf).2.1 a ha
    simp only [evalAt, tgtM, tgtI, sfst_spair, ssnd_spair]
    exact evalAt_mem hw B hwf.2.2 hfa hb

/-- The curried spine-reading of a function value is the value. -/
theorem curry_eta (hw : w ≠ 0) {K : Nat} : ∀ (r : RTel V), r.WF w K → ∀ {ρ X : Nat → V} {f : V},
    f ∈ˢ r.read ρ X → r.curry ρ (r.evalAt f) = f
  | hole _ _, _, _, _, _, _ => rfl
  | pi v A B, hwf, ρ, X, f, hf => by
    obtain ⟨hg, hfa, -, -⟩ := mem_piR_pos hwf.1 hf
    simp only [curry]
    refine Eq.trans (graph_congr fun a ha => ?_) hg
    have : (fun s => (pi v A B).evalAt f (kpair a s)) = B.evalAt (app f a) := by
      funext s; simp only [evalAt, sfst_kpair, ssnd_kpair]
    rw [this]
    exact curry_eta hw B hwf.2.2 (hfa a ha)

/-- The curried function reads its argument on the spines only. -/
theorem curry_congr (hw : w ≠ 0) : ∀ (r : RTel V) {ρ : Nat → V} {G G' : V → V},
    (∀ s, s ∈ˢ r.spines w ρ → G s = G' s) → r.curry ρ G = r.curry ρ G'
  | hole _ _, _, _, _, h => h pt pt_mem_unitSet
  | pi _ _ B, _, _, _, h => by
    simp only [curry]
    refine graph_congr fun a ha => curry_congr hw B fun s hs => h _ ?_
    rw [← spair_eq_kpair]
    exact spair_mem hw ha hs

theorem graph_mem_univ (hw : w ≠ 0) {F : V → V} {A : V} (hA : A ∈ˢ (univ w : V))
    (hF : ∀ a, a ∈ˢ A → F a ∈ˢ (univ w : V)) : graph F A ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  exact hU.transitive (hU.piSet_mem (B := fun a => sing (F a)) hA fun a ha => hU.sing_mem hA (hF a ha))
    (graph_mem_piSet fun a _ => mem_sing.mpr rfl)

theorem curry_mem_univ (hw : w ≠ 0) {K : Nat} : ∀ (r : RTel V), r.WF w K → ∀ {ρ : Nat → V} {G : V → V},
    (∀ s, G s ∈ˢ (univ w : V)) → r.curry ρ G ∈ˢ (univ w : V)
  | hole _ _, _, _, _, h => h pt
  | pi _ _ B, hwf, ρ, _, h => by
    simp only [curry]
    exact graph_mem_univ hw (hwf.2.1 ρ) fun a _ => curry_mem_univ hw B hwf.2.2 fun s => h _

theorem spines_mem_univ (hw : w ≠ 0) {K : Nat} : ∀ (r : RTel V), r.WF w K → ∀ ρ : Nat → V,
    r.spines w ρ ∈ˢ (univ w : V)
  | hole _ _, _, _ => unitSet_mem_univ w
  | pi _ _ B, hwf, ρ => by
    simp only [spines]
    have h := sigma_mem_univ (u := w) (v := w) (hwf.2.1 ρ) fun a _ => spines_mem_univ hw B hwf.2.2 (fcons a ρ)
    rwa [show Nat.max w w = w from Nat.max_self w] at h

end RTel

/-! ## Flat fields and constructors -/

/-- **A flat field**: ordinary (hole-free) or recursive. -/
inductive FField (V : Type u) : Type u
  /-- a hole-free type read at the frame -/
  | plain (A : (Nat → V) → V)
  /-- a recursive field -/
  | recur (r : RTel V)

namespace FField

/-- The field type's reading. -/
noncomputable def read : FField V → (Nat → V) → (Nat → V) → V
  | plain A, ρ, _ => A ρ
  | recur r, ρ, X => r.read ρ X

/-- The shadow of a value: the point at a recursive field. -/
noncomputable def shv : FField V → V → V
  | plain _, x => x
  | recur _, _ => pt

/-- The shadow domain: `{pt}` at a recursive field. -/
noncomputable def shDom : FField V → (Nat → V) → V
  | plain A, ρ => A ρ
  | recur _, _ => unitSet

/-- Well-formed at width `K` and level `w`. -/
def WF (w K : Nat) : FField V → Prop
  | plain A => ∀ ρ, A ρ ∈ˢ (univ w : V)
  | recur r => r.WF w K

/-- Two frames the field type reads alike. -/
def Agree : FField V → (Nat → V) → (Nat → V) → Prop
  | plain A, ρ, ρ' => A ρ = A ρ'
  | recur r, ρ, ρ' => r.Agree ρ ρ'

end FField

/-- A spine fits a flat field telescope. -/
def FitsF : List (FField V) → (Nat → V) → (Nat → V) → List V → Prop
  | [], _, _, [] => True
  | f :: ffs, ρ, X, x :: xs => x ∈ˢ f.read ρ X ∧ FitsF ffs (fcons x ρ) X xs
  | _, _, _, _ => False

/-- The shadow of a spine. -/
noncomputable def shadowL : List (FField V) → List V → List V
  | f :: ffs, x :: xs => f.shv x :: shadowL ffs xs
  | _, _ => []

/-- The shadow telescope. -/
noncomputable def shTele : (ffs : List (FField V)) → (Nat → V) → TeleS V ffs.length
  | [], _ => .nil
  | f :: ffs, ρ => .cons (f.shDom ρ) fun a => shTele ffs (fcons a ρ)

/-- **R3's caveat (U4), the named premise**: no field type reads the
value of a recursive field — the fields read alike at a frame and at
its shadow (`ρ` the frame of the values, `ρ'` of their shadows).
Supplied by `nestPos`'s U4 decline. -/
def HoleUnread : List (FField V) → (Nat → V) → (Nat → V) → Prop
  | [], _, _ => True
  | f :: ffs, ρ, ρ' => f.Agree ρ ρ' ∧ ∀ x, HoleUnread ffs (fcons x ρ) (fcons (f.shv x) ρ')

/-- The constructor's fields read as the flat fields, at the parameter
`α`, at every frame and hole tuple. -/
def ReadsAs (α : V) : List ((Nat → V) → (Nat → V) → V → V) → List (FField V) → Prop
  | [], [] => True
  | F :: Fs, f :: ffs => (∀ ρ' X, F ρ' X α = f.read ρ' X) ∧ ReadsAs α Fs ffs
  | _, _ => False

theorem ReadsAs.length_eq {α : V} : ∀ {Fs : List ((Nat → V) → (Nat → V) → V → V)} {ffs : List (FField V)},
    ReadsAs α Fs ffs → Fs.length = ffs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons]; rw [ReadsAs.length_eq h.2]

/-- **A constructor presented flat** at the parameter `α`: its fields
read as the flat fields at every frame and tuple, well-formed, and
reading no recursive value. -/
structure FlatCtor (w K : Nat) (ρ : Nat → V) (α : V) (ct : UCtor V w K) (ffs : List (FField V)) :
    Prop where
  reads : ReadsAs α ct.fields ffs
  wf : ∀ f ∈ ffs, f.WF w K
  unread : HoleUnread ffs ρ ρ

/-- **A block presented flat** at the frame `ρ` and the parameter `α`. -/
def UBlock.FlatAt {w K : Nat} (d : UBlock V w K) (ρ : Nat → V) (α : V) : Prop :=
  ∀ c, c < K → ∀ (j : Nat) (ct : UCtor V w K), (d.ctors c)[j]? = some ct →
    ∃ ffs, FlatCtor w K ρ α ct ffs

section Tele

variable {w K : Nat}

theorem fitsS_teleOf_iff {α : V} {X : Nat → V} :
    ∀ {Fs : List ((Nat → V) → (Nat → V) → V → V)} {ffs : List (FField V)},
    ReadsAs α Fs ffs → ∀ {ρ : Nat → V} {xs : List V}, FitsS (teleOf Fs ρ X α) xs ↔ FitsF ffs ρ X xs
  | [], [], _, _, [] => Iff.rfl
  | [], [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _ :: _, _, _, [] => Iff.rfl
  | F :: Fs, f :: ffs, h, ρ, x :: xs => by
    show x ∈ˢ F ρ X α ∧ FitsS (teleOf Fs (fcons x ρ) X α) xs ↔ x ∈ˢ f.read ρ X ∧ FitsF ffs (fcons x ρ) X xs
    rw [h.1, fitsS_teleOf_iff h.2]

theorem boundS_shTele : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) → ∀ ρ : Nat → V,
    BoundS w (shTele ffs ρ)
  | [], _, _ => trivial
  | f :: ffs, h, ρ => by
    refine ⟨?_, fun a _ => boundS_shTele ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) _⟩
    have hf := h f List.mem_cons_self
    cases f with
    | plain A => exact hf ρ
    | recur r => exact unitSet_mem_univ w

/-- **The shadow fits the shadow telescope** — `HoleUnread`'s use. -/
theorem shadow_fits : ∀ (ffs : List (FField V)) {ρ ρ' X : Nat → V} {xs : List V},
    HoleUnread ffs ρ ρ' → FitsF ffs ρ X xs → FitsS (shTele ffs ρ') (shadowL ffs xs)
  | [], _, _, _, [], _, _ => trivial
  | f :: ffs, ρ, ρ', X, x :: xs, hU, hf => by
    refine ⟨?_, shadow_fits ffs (hU.2 x) hf.2⟩
    cases f with
    | plain A => show x ∈ˢ A ρ'; rw [← show A ρ = A ρ' from hU.1]; exact hf.1
    | recur r => exact pt_mem_unitSet

theorem shadowL_length : ∀ (ffs : List (FField V)) (xs : List V), xs.length = ffs.length →
    (shadowL ffs xs).length = ffs.length
  | [], [], _ => rfl
  | _ :: ffs, _ :: xs, h => by
    simp only [shadowL, List.length_cons]
    rw [shadowL_length ffs xs (by simpa using h)]

end Tele

/-! ## Positions, targets, the builder -/

section Positions

variable {w K : Nat}

/-- The positions: the recursive fields' spines, tagged by the field's
position `l`, at the shadow frame. -/
noncomputable def posSet (w : Nat) : List (FField V) → (Nat → V) → List V → Nat → V
  | [], _, _, _ => empty
  | .plain _ :: ffs, ρ, x :: xs, l => posSet w ffs (fcons x ρ) xs (l + 1)
  | .recur r :: ffs, ρ, x :: xs, l =>
    binUnion (image (fun s => kpair (vnat l) s) (r.spines w ρ)) (posSet w ffs (fcons x ρ) xs (l + 1))
  | _ :: _, _, [], _ => empty

open Classical in
/-- A position's target (member, index tuple). -/
noncomputable def tgtAt : List (FField V) → (Nat → V) → List V → Nat → V → Nat × V
  | [], _, _, _, _ => (0, empty)
  | .plain _ :: ffs, ρ, x :: xs, l, p => tgtAt ffs (fcons x ρ) xs (l + 1) p
  | .recur r :: ffs, ρ, x :: xs, l, p =>
    if sfst p = vnat l then (r.tgtM (ssnd p), r.tgtI ρ (ssnd p)) else tgtAt ffs (fcons x ρ) xs (l + 1) p
  | _ :: _, _, [], _, _ => (0, empty)

open Classical in
/-- A position's value in a spine. -/
noncomputable def valAt : List (FField V) → List V → Nat → V → V
  | [], _, _, _ => empty
  | .plain _ :: ffs, _ :: xs, l, p => valAt ffs xs (l + 1) p
  | .recur r :: ffs, x :: xs, l, p => if sfst p = vnat l then r.evalAt x (ssnd p) else valAt ffs xs (l + 1) p
  | _ :: _, [], _, _ => empty

/-- The builder: the shadow's ordinary values, each recursive slot the
curried function on its positions. -/
noncomputable def rebuild : List (FField V) → (Nat → V) → List V → Nat → (V → V) → List V
  | [], _, _, _, _ => []
  | .plain _ :: ffs, ρ, x :: xs, l, G => x :: rebuild ffs (fcons x ρ) xs (l + 1) G
  | .recur r :: ffs, ρ, x :: xs, l, G =>
    r.curry ρ (fun s => G (kpair (vnat l) s)) :: rebuild ffs (fcons x ρ) xs (l + 1) G
  | _ :: _, _, [], _, _ => []

theorem mem_posSet_tag : ∀ (ffs : List (FField V)) {ρ : Nat → V} {xs : List V} {l : Nat} {p : V},
    p ∈ˢ posSet w ffs ρ xs l → ∃ l' s, l ≤ l' ∧ p = kpair (vnat l') s
  | [], _, _, _, _, hp => (not_mem_empty _ hp).elim
  | .plain _ :: _, _, [], _, _, hp => (not_mem_empty _ hp).elim
  | .recur _ :: _, _, [], _, _, hp => (not_mem_empty _ hp).elim
  | .plain _ :: ffs, _, _ :: _, _, _, hp => by
    obtain ⟨l', s, hl, rfl⟩ := mem_posSet_tag ffs hp
    exact ⟨l', s, by omega, rfl⟩
  | .recur _ :: ffs, _, _ :: _, _, _, hp => by
    rcases mem_binUnion.mp hp with hp | hp
    · obtain ⟨s, -, rfl⟩ := mem_image.mp hp
      exact ⟨_, s, Nat.le_refl _, rfl⟩
    · obtain ⟨l', s, hl, rfl⟩ := mem_posSet_tag ffs hp
      exact ⟨l', s, by omega, rfl⟩

theorem sfst_ne_of_posSet {ffs : List (FField V)} {ρ : Nat → V} {xs : List V} {l : Nat} {p : V}
    (hp : p ∈ˢ posSet w ffs ρ xs (l + 1)) : sfst p ≠ vnat l := by
  obtain ⟨l', s, hl, rfl⟩ := mem_posSet_tag ffs hp
  rw [sfst_kpair]
  intro h
  have := vnat_inj h
  omega

theorem posSet_mem_univ (hw : w ≠ 0) : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) →
    ∀ (ρ : Nat → V) (xs : List V) (l : Nat), posSet w ffs ρ xs l ∈ˢ (univ w : V)
  | [], _, _, _, _ => empty_mem_univ w
  | .plain _ :: _, _, _, [], _ => empty_mem_univ w
  | .recur _ :: _, _, _, [], _ => empty_mem_univ w
  | .plain _ :: ffs, h, ρ, x :: xs, l =>
    posSet_mem_univ hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) _ xs _
  | .recur r :: ffs, h, ρ, x :: xs, l => by
    have hU := univ_isTGUniverse (V := V) hw
    have hr : r.WF w K := h _ List.mem_cons_self
    have hS := RTel.spines_mem_univ hw r hr ρ
    refine hU.binUnion_mem (unitSet_mem_univ w)
      (hU.image_mem hS fun s hs => hU.kpair_mem hS (vnat_mem_univ_pos hw l) (hU.transitive hS hs))
      (posSet_mem_univ hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) _ xs _)

theorem tgtAt_fst_lt : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) →
    ∀ {ρ : Nat → V} {xs : List V} {l : Nat} {p : V},
    p ∈ˢ posSet w ffs ρ xs l → (tgtAt ffs ρ xs l p).1 < K
  | [], _, _, _, _, _, hp => (not_mem_empty _ hp).elim
  | .plain _ :: _, _, _, [], _, _, hp => (not_mem_empty _ hp).elim
  | .recur _ :: _, _, _, [], _, _, hp => (not_mem_empty _ hp).elim
  | .plain _ :: ffs, h, _, _ :: _, _, _, hp =>
    tgtAt_fst_lt ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hp
  | .recur r :: ffs, h, _, _ :: _, l, p, hp => by
    simp only [tgtAt]
    split
    · exact RTel.tgtM_lt r (h _ List.mem_cons_self) _
    · rcases mem_binUnion.mp hp with hp' | hp'
      · obtain ⟨s, -, rfl⟩ := mem_image.mp hp'
        next hne => exact (hne (sfst_kpair _ _)).elim
      · exact tgtAt_fst_lt ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hp'

/-- **A position's value lands in its target's fibre** (the container's
elimination, one field at a time), at the shadow frame. -/
theorem valAt_mem (hw : w ≠ 0) : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) →
    ∀ {ρ ρ' X : Nat → V} {xs : List V} {l : Nat} {p : V},
    HoleUnread ffs ρ ρ' → FitsF ffs ρ X xs → p ∈ˢ posSet w ffs ρ' (shadowL ffs xs) l →
    valAt ffs xs l p ∈ˢ app (X (tgtAt ffs ρ' (shadowL ffs xs) l p).1) (tgtAt ffs ρ' (shadowL ffs xs) l p).2
  | [], _, _, _, _, [], _, _, _, _, hp => (not_mem_empty _ hp).elim
  | .plain A :: ffs, h, ρ, ρ', X, x :: xs, l, p, hU, hf, hp =>
    valAt_mem hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) (hU.2 x) hf.2 hp
  | .recur r :: ffs, h, ρ, ρ', X, x :: xs, l, p, hU, hf, hp => by
    have hr : r.WF w K := h _ List.mem_cons_self
    have hag : r.Agree ρ ρ' := hU.1
    simp only [shadowL, FField.shv, posSet] at hp
    simp only [shadowL, FField.shv, tgtAt, valAt]
    rcases mem_binUnion.mp hp with hp' | hp'
    · obtain ⟨s, hs, rfl⟩ := mem_image.mp hp'
      rw [if_pos (sfst_kpair _ _), if_pos (sfst_kpair _ _), ssnd_kpair, ← RTel.tgtI_agree r hag]
      rw [← RTel.spines_agree w r hag] at hs
      exact RTel.evalAt_mem hw r hr hf.1 hs
    · rw [if_neg (sfst_ne_of_posSet hp'), if_neg (sfst_ne_of_posSet hp')]
      exact valAt_mem hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) (hU.2 x) hf.2 hp'

/-- **The builder rebuilds the spine** from its shadow and its values
at the positions. -/
theorem rebuild_eq (hw : w ≠ 0) : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) →
    ∀ {ρ ρ' X : Nat → V} {xs : List V} {l : Nat} {G : V → V},
    HoleUnread ffs ρ ρ' → FitsF ffs ρ X xs →
    (∀ p, p ∈ˢ posSet w ffs ρ' (shadowL ffs xs) l → G p = valAt ffs xs l p) →
    rebuild ffs ρ' (shadowL ffs xs) l G = xs
  | [], _, _, _, _, [], _, _, _, _, _ => rfl
  | .plain A :: ffs, h, ρ, ρ', X, x :: xs, l, G, hU, hf, hG => by
    simp only [shadowL, FField.shv, rebuild]
    congr 1
    exact rebuild_eq hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) (hU.2 x) hf.2 hG
  | .recur r :: ffs, h, ρ, ρ', X, x :: xs, l, G, hU, hf, hG => by
    have hr : r.WF w K := h _ List.mem_cons_self
    have hag : r.Agree ρ ρ' := hU.1
    simp only [shadowL, FField.shv, rebuild]
    simp only [shadowL, FField.shv, posSet, valAt] at hG
    congr 1
    · rw [RTel.curry_congr hw r (G' := r.evalAt x) fun s hs => by
          rw [hG _ (mem_binUnion.mpr (Or.inl (mem_image.mpr ⟨s, hs, rfl⟩))), if_pos (sfst_kpair _ _),
            ssnd_kpair],
        ← RTel.curry_agree r hag]
      exact RTel.curry_eta hw r hr hf.1
    · refine rebuild_eq hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) (hU.2 x) hf.2 fun p hp => ?_
      rw [hG p (mem_binUnion.mpr (Or.inr hp)), if_neg (sfst_ne_of_posSet hp)]

theorem rebuild_mem_univ (hw : w ≠ 0) : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.WF w K) →
    ∀ {ρ : Nat → V} {sh : List V} {l : Nat} {G : V → V},
    FitsS (shTele ffs ρ) sh → (∀ p, G p ∈ˢ (univ w : V)) →
    ∀ y, y ∈ rebuild ffs ρ sh l G → y ∈ˢ (univ w : V)
  | [], _, _, [], _, _, _, _, _, hy => by simp [rebuild] at hy
  | .plain A :: ffs, h, ρ, x :: xs, l, G, hf, hG, y, hy => by
    simp only [rebuild, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact (univ_isTGUniverse hw).transitive ((h _ List.mem_cons_self : ∀ ρ, A ρ ∈ˢ _) ρ) hf.1
    · exact rebuild_mem_univ hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hf.2 hG y hy
  | .recur r :: ffs, h, ρ, x :: xs, l, G, hf, hG, y, hy => by
    simp only [rebuild, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact RTel.curry_mem_univ hw r (h _ List.mem_cons_self) fun s => hG _
    · exact rebuild_mem_univ hw ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hf.2 hG y hy

end Positions

/-! ## The closed tuple -/

section Closed

variable {w K : Nat}

open Classical in
/-- A numeral's number (`0` off the numerals). -/
noncomputable def natOf (x : V) : Nat := if h : ∃ n, x = vnat n then h.choose else 0

theorem natOf_vnat (n : Nat) : natOf (vnat n : V) = n := by
  unfold natOf
  have h : ∃ m, (vnat n : V) = vnat m := ⟨n, rfl⟩
  rw [dif_pos h]
  exact (vnat_inj h.choose_spec).symm

open Classical in
/-- The chosen flat presentation of component `c`'s constructor `j`. -/
noncomputable def flatOf (d : UBlock V w K) (ρ : Nat → V) (α : V) (c j : Nat) : List (FField V) :=
  match (d.ctors c)[j]? with
  | some ct => if h : ∃ ffs, FlatCtor w K ρ α ct ffs then h.choose else []
  | none => []

theorem flatOf_spec {d : UBlock V w K} {ρ : Nat → V} {α : V} (hflat : d.FlatAt ρ α) {c : Nat} (hc : c < K)
    {j : Nat} {ct : UCtor V w K} (hct : (d.ctors c)[j]? = some ct) :
    FlatCtor w K ρ α ct (flatOf d ρ α c j) := by
  have h := hflat c hc j ct hct
  unfold flatOf
  rw [hct]
  dsimp only
  rw [dif_pos h]
  exact h.choose_spec

theorem flatOf_wf {d : UBlock V w K} {ρ : Nat → V} {α : V} (hflat : d.FlatAt ρ α) {c : Nat} (hc : c < K)
    (j : Nat) : ∀ f ∈ flatOf d ρ α c j, f.WF w K := by
  cases hct : (d.ctors c)[j]? with
  | some ct => exact (flatOf_spec hflat hc hct).wf
  | none => unfold flatOf; rw [hct]; intro f hf; exact absurd hf List.not_mem_nil

/-- The shape of a spine of component `c`'s constructor `j`. -/
noncomputable def shapeOf (d : UBlock V w K) (ρ : Nat → V) (α : V) (c j : Nat) (fs : List V) : V :=
  kpair (vnat c) (inj j (mkTower (shadowL (flatOf d ρ α c j) fs)))

/-- The shapes of component `c` at the index `t`. -/
noncomputable def shapeSet (d : UBlock V w K) (ρ : Nat → V) (α : V) (c : Nat) (t : V) : V :=
  image (fun x => kpair (vnat c) x) (sep (sumSet w fun j => towerSet w (shTele (flatOf d ρ α c j) ρ))
    fun a => ∃ X, InTupleSpace w K d.Is X ∧ ∃ j ct fs, (d.ctors c)[j]? = some ct ∧
      FitsS (teleOf ct.fields ρ X α) fs ∧ ct.idx (fconsList fs ρ) = t ∧
      a = inj j (mkTower (shadowL (flatOf d ρ α c j) fs)))

/-- A shape's member, constructor, flat fields and shadow. -/
noncomputable def sC (a : V) : Nat := natOf (sfst a)
noncomputable def sJ (a : V) : Nat := natOf (sfst (ssnd a))
noncomputable def sFF (d : UBlock V w K) (ρ : Nat → V) (α : V) (a : V) : List (FField V) :=
  flatOf d ρ α (sC a) (sJ a)
noncomputable def sSh (d : UBlock V w K) (ρ : Nat → V) (α : V) (a : V) : List V :=
  projList (sFF d ρ α a).length (ssnd (ssnd a))

theorem shape_read (d : UBlock V w K) (ρ : Nat → V) (α : V) (c j : Nat) {fs : List V}
    (hlen : fs.length = (flatOf d ρ α c j).length) :
    sC (shapeOf d ρ α c j fs) = c ∧ sJ (shapeOf d ρ α c j fs) = j ∧
      sFF d ρ α (shapeOf d ρ α c j fs) = flatOf d ρ α c j ∧
      sSh d ρ α (shapeOf d ρ α c j fs) = shadowL (flatOf d ρ α c j) fs := by
  have hC : sC (shapeOf d ρ α c j fs) = c := by
    unfold sC shapeOf; rw [sfst_kpair, natOf_vnat]
  have hJ : sJ (shapeOf d ρ α c j fs) = j := by
    unfold sJ shapeOf; rw [ssnd_kpair, sfst_inj, natOf_vnat]
  have hF : sFF d ρ α (shapeOf d ρ α c j fs) = flatOf d ρ α c j := by
    unfold sFF; rw [hC, hJ]
  refine ⟨hC, hJ, hF, ?_⟩
  unfold sSh
  rw [hF]
  unfold shapeOf
  rw [ssnd_kpair, ssnd_inj, projList_mkTower _ _ (shadowL_length _ _ hlen)]

theorem mem_shapeSet {d : UBlock V w K} {ρ : Nat → V} {α : V} {c : Nat} {t a : V}
    (ha : a ∈ˢ shapeSet d ρ α c t) :
    ∃ X, InTupleSpace w K d.Is X ∧ ∃ j ct fs, (d.ctors c)[j]? = some ct ∧
      FitsS (teleOf ct.fields ρ X α) fs ∧ ct.idx (fconsList fs ρ) = t ∧ a = shapeOf d ρ α c j fs := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  obtain ⟨-, X, hX, j, ct, fs, hct, hf, hi, rfl⟩ := mem_sep.mp hb
  exact ⟨X, hX, j, ct, fs, hct, hf, hi, rfl⟩

/-- **(W) for a flat block** at `w ≠ 0`: the hole operator of a block
whose constructors are presented flat (`UBlock.FlatAt`, including
`HoleUnread`) has a closed tuple. -/
theorem UBlock.closed_of_flat (hw : w ≠ 0) (d : UBlock V w K) (ρ : Nat → V) (α : V)
    (hflat : d.FlatAt ρ α) : d.Closed ρ α := by
  have hU := univ_isTGUniverse (V := V) hw
  -- the facts a shape carries
  have hwit : ∀ {c : Nat}, c < K → ∀ {t a : V}, a ∈ˢ shapeSet d ρ α c t →
      ∃ X, InTupleSpace w K d.Is X ∧ ∃ j ct fs, (d.ctors c)[j]? = some ct ∧
        FlatCtor w K ρ α ct (flatOf d ρ α c j) ∧ FitsF (flatOf d ρ α c j) ρ X fs ∧
        sJ a = j ∧ sFF d ρ α a = flatOf d ρ α c j ∧ sSh d ρ α a = shadowL (flatOf d ρ α c j) fs := by
    intro c hc t a ha
    obtain ⟨X, hX, j, ct, fs, hct, hf, -, rfl⟩ := mem_shapeSet ha
    have hF := flatOf_spec hflat hc hct
    have hff := (fitsS_teleOf_iff hF.reads).mp hf
    have hlen : fs.length = (flatOf d ρ α c j).length := by
      rw [← hF.reads.length_eq, ← hf.length_eq]
    obtain ⟨-, hJ, hFF, hSh⟩ := shape_read d ρ α c j hlen
    exact ⟨X, hX, j, ct, fs, hct, hF, hff, hJ, hFF, hSh⟩
  refine tupleContainer_closed_exists hw (Is := d.Is) (uPhi d ρ α) (shapeSet d ρ α)
    (fun a => posSet w (sFF d ρ α a) ρ (sSh d ρ α a) 0)
    (fun a p => (tgtAt (sFF d ρ α a) ρ (sSh d ρ α a) 0 p).1)
    (fun a p => (tgtAt (sFF d ρ α a) ρ (sSh d ρ α a) 0 p).2)
    (fun _ a g => uinj w (sJ a) (rebuild (sFF d ρ α a) ρ (sSh d ρ α a) 0 (app g))) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro c hc t _
    have hS : sumSet w (fun j => towerSet w (shTele (flatOf d ρ α c j) ρ)) ∈ˢ (univ w : V) :=
      sumSet_mem_univ hw fun j => towerSet_mem_univ _ (boundS_shTele _ (flatOf_wf hflat hc j) ρ)
    exact hU.image_mem (hU.sep_mem hS) fun x hx =>
      hU.kpair_mem hS (vnat_mem_univ_pos hw c) (hU.transitive hS (mem_sep.mp hx).1)
  case hB =>
    intro c hc t a _ ha
    obtain ⟨X, -, j, ct, fs, -, -, -, -, hFF, -⟩ := hwit hc ha
    rw [hFF]
    exact posSet_mem_univ hw _ (flatOf_wf hflat hc j) _ _ _
  case htgt =>
    intro c hc t a p _ ha hp
    obtain ⟨X, hX, j, ct, fs, -, hF, hff, -, hFF, hSh⟩ := hwit hc ha
    rw [hFF, hSh] at hp ⊢
    have hlt := tgtAt_fst_lt _ hF.wf hp
    refine ⟨hlt, ?_⟩
    have hv := valAt_mem hw _ hF.wf hF.unread hff hp
    by_cases hin : (tgtAt (flatOf d ρ α c j) ρ (shadowL (flatOf d ρ α c j) fs) 0 p).2 ∈ˢ
        d.Is (tgtAt (flatOf d ρ α c j) ρ (shadowL (flatOf d ρ α c j) fs) 0 p).1
    · exact hin
    · rw [app_off_dom_of_mem_piSet (hX _ hlt) hin] at hv
      exact (not_mem_empty _ hv).elim
  case hmkU =>
    intro c hc t a g _ ha hg
    obtain ⟨X, hX, j, ct, fs, -, hF, hff, -, hFF, hSh⟩ := hwit hc ha
    refine uinj_mem_univ_pos hw _ fun y hy => ?_
    rw [hFF, hSh] at hy
    exact rebuild_mem_univ hw _ hF.wf (shadow_fits _ hF.unread hff) (fun p => app_mem_univ_pos hw hg p) y hy
  case helim =>
    intro X hX c hc t ht x hx
    obtain ⟨j, fs, ct, hct, hf, hi, rfl⟩ := (mem_uPhi d ρ α X ht).mp hx
    have hF := flatOf_spec hflat hc hct
    have hff := (fitsS_teleOf_iff hF.reads).mp hf
    have hlen : fs.length = (flatOf d ρ α c j).length := by
      rw [← hF.reads.length_eq, ← hf.length_eq]
    obtain ⟨-, hJ, hFF, hSh⟩ := shape_read d ρ α c j hlen
    have ha : shapeOf d ρ α c j fs ∈ˢ shapeSet d ρ α c t := by
      refine mem_image.mpr ⟨_, mem_sep.mpr ⟨inj_mem hw (mkTower_mem hw (shadow_fits _ hF.unread hff)),
        X, hX, j, ct, fs, hct, hf, hi, rfl⟩, rfl⟩
    refine ⟨_, ha, graph (valAt (flatOf d ρ α c j) fs 0) (posSet w (flatOf d ρ α c j) ρ
      (shadowL (flatOf d ρ α c j) fs) 0), ?_, ?_⟩
    · rw [hFF, hSh]
      exact graph_mem_piSet fun p hp => valAt_mem hw _ hF.wf hF.unread hff hp
    · rw [hJ, hFF, hSh, rebuild_eq hw _ hF.wf hF.unread hff fun p hp => app_graph hp]

end Closed

/-! ## Presenting a block flat, and comparing hole operators -/

section Present

variable {w K : Nat}

/-- A flat field whose type reads no frame slot at all. -/
def FField.Blind (f : FField V) : Prop := ∀ ρ ρ' : Nat → V, f.Agree ρ ρ'

/-- Fields that read no frame slot read no recursive value. -/
theorem holeUnread_of_blind : ∀ (ffs : List (FField V)), (∀ f ∈ ffs, f.Blind) →
    ∀ ρ ρ' : Nat → V, HoleUnread ffs ρ ρ'
  | [], _, _, _ => trivial
  | f :: ffs, h, ρ, ρ' => ⟨h f List.mem_cons_self ρ ρ', fun _ =>
      holeUnread_of_blind ffs (fun g hg => h g (List.mem_cons_of_mem _ hg)) _ _⟩

/-- A flat presentation from blind well-formed fields. -/
theorem FlatCtor.of_blind {ρ : Nat → V} {α : V} {ct : UCtor V w K} {ffs : List (FField V)}
    (hr : ReadsAs α ct.fields ffs) (hwf : ∀ f ∈ ffs, f.WF w K) (hb : ∀ f ∈ ffs, f.Blind) :
    FlatCtor w K ρ α ct ffs :=
  ⟨hr, hwf, holeUnread_of_blind ffs hb ρ ρ⟩

/-- A component's constructors, presented flat one by one. -/
def FlatCtors (w K : Nat) (ρ : Nat → V) (α : V) : List (UCtor V w K) → List (List (FField V)) → Prop
  | [], _ => True
  | ct :: cts, ffs :: fl => FlatCtor w K ρ α ct ffs ∧ FlatCtors w K ρ α cts fl
  | _ :: _, [] => False

theorem flatCtors_get {ρ : Nat → V} {α : V} : ∀ {cts : List (UCtor V w K)} {fl : List (List (FField V))},
    FlatCtors w K ρ α cts fl → ∀ (j : Nat) (ct : UCtor V w K), cts[j]? = some ct →
    ∃ ffs, FlatCtor w K ρ α ct ffs
  | [], _, _, _, _, hct => by simp at hct
  | _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, ffs :: _, h, 0, _, hct => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hct
    subst hct
    exact ⟨ffs, h.1⟩
  | _ :: _, _ :: _, h, j + 1, ct, hct => flatCtors_get h.2 j ct (by simpa using hct)

theorem UBlock.flatAt_of {d : UBlock V w K} {ρ : Nat → V} {α : V}
    (h : ∀ c, c < K → ∃ fl, FlatCtors w K ρ α (d.ctors c) fl) : d.FlatAt ρ α := by
  intro c hc j ct hct
  obtain ⟨fl, hfl⟩ := h c hc
  exact flatCtors_get hfl j ct hct

/-- **(W) for a flat block at every level**: free at `Prop`, the flat
kit above. -/
theorem UBlock.closed_of_flatAll (d : UBlock V w K) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V))
    (hflat : w ≠ 0 → d.FlatAt ρ α) : d.Closed ρ α := by
  by_cases hw : w = 0
  · subst hw; exact uPhi_closed_zero d ρ hα
  · exact UBlock.closed_of_flat hw d ρ α (hflat hw)

/-- **Two hole operators compared through their fibre laws**: a
component's fibre lies below another's when every spine fitting one of
the first's constructors fits the second's constructor at the same tag
with the same result index. -/
theorem uPhi_famLe {K' : Nat} (d : UBlock V w K) (d' : UBlock V w K') (ρ ρ' : Nat → V) (α α' : V)
    (X X' : Nat → V) {c c' : Nat} (hIs : d.Is c = d'.Is c')
    (h : ∀ t, t ∈ˢ d.Is c → ∀ (j : Nat) (fs : List V) (ct : UCtor V w K), (d.ctors c)[j]? = some ct →
      FitsS (teleOf ct.fields ρ X α) fs → ct.idx (fconsList fs ρ) = t →
      ∃ ct' : UCtor V w K', (d'.ctors c')[j]? = some ct' ∧ FitsS (teleOf ct'.fields ρ' X' α') fs ∧
        ct'.idx (fconsList fs ρ') = t) :
    FamLe (d.Is c) (uPhi d ρ α X c) (uPhi d' ρ' α' X' c') := by
  intro t ht x hx
  obtain ⟨j, fs, ct, hct, hf, hi, rfl⟩ := (mem_uPhi d ρ α X ht).mp hx
  obtain ⟨ct', hct', hf', hi'⟩ := h t ht j fs ct hct hf hi
  exact (mem_uPhi d' ρ' α' X' (hIs ▸ ht)).mpr ⟨j, fs, ct', hct', hf', hi', rfl⟩

end Present

end ConLeche.SetTheory
