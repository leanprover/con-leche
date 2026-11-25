module

public import ConLeche.SetTheory.Derive.Pair

@[expose] public section

/-!
# Grothendieck universes: closure laws from SGA4

Recovers the Grothendieck-universe closure laws from the four
first-order SGA4 clauses of `IsGrothendieck` (`Core.lean`) — applied
downstream to the chain members `univChain n`.

* `transitive`, `upair_mem`, `power_mem` follow directly from the
  first three clauses.
* `mem_of_subset_mem` follows in one line from `power_mem` and
  `transitive`.
* `sUnion_mem`, `famUnion_mem`, and `image_mem` use SGA4 clause 4
  (indexed union over an internal function graph `IsFunGraph Mem g I U`).
  Notably, `image_mem` and `famUnion_mem` require a graph witness
  `HasImage (fun x => kpair x (F x)) A` (or `DefFunOn A F`), since in
  a countable first-order model mere existence of the image set does
  not supply an internal function graph.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section IsGrothendieck

variable {U : V} (hU : IsGrothendieck (Mem (V := V)) U)

include hU

theorem _root_.ConLeche.IsGrothendieck.transitive : ∀ {y z : V}, y ∈ˢ U → z ∈ˢ y → z ∈ˢ U :=
  fun {y z} hy hz => hU.transitivity y z hy hz

theorem _root_.ConLeche.IsGrothendieck.subset_of_mem {y : V} (hy : y ∈ˢ U) : y ⊆ˢ U :=
  fun _ hz => hU.transitive hy hz

theorem _root_.ConLeche.IsGrothendieck.upair_mem {a b : V} (ha : a ∈ˢ U) (hb : b ∈ˢ U) :
    upair a b ∈ˢ U := by
  obtain ⟨p, hp, hup⟩ := hU.pairing a b ha hb
  rw [isUpair_iff] at hup
  exact hup ▸ hp

theorem _root_.ConLeche.IsGrothendieck.power_mem {y : V} (hy : y ∈ˢ U) : power y ∈ˢ U := by
  obtain ⟨p, hp, hsub⟩ := hU.powerSet y hy
  have heq : p = power y := ext fun z => (hsub z).trans mem_power.symm
  exact heq ▸ hp

theorem _root_.ConLeche.IsGrothendieck.mem_of_subset_mem :
    ∀ {y z : V}, y ∈ˢ U → z ⊆ˢ y → z ∈ˢ U :=
  fun {_y _z} hy hz => hU.transitive (hU.power_mem hy) (mem_power.mpr hz)

theorem _root_.ConLeche.IsGrothendieck.empty_mem {y : V} (hy : y ∈ˢ U) :
    (empty : V) ∈ˢ U :=
  hU.mem_of_subset_mem hy (empty_subset y)

theorem _root_.ConLeche.IsGrothendieck.sing_mem {a : V} (ha : a ∈ˢ U) : sing a ∈ˢ U :=
  hU.upair_mem ha ha

theorem _root_.ConLeche.IsGrothendieck.kpair_mem {a b : V} (ha : a ∈ˢ U) (hb : b ∈ˢ U) :
    kpair a b ∈ˢ U :=
  hU.upair_mem (hU.sing_mem ha) (hU.upair_mem ha hb)

theorem _root_.ConLeche.IsGrothendieck.sep_mem {a : V} {p : V → Prop}
    (ha : a ∈ˢ U) (h : HasSep a p) : sep a p h ∈ˢ U :=
  hU.mem_of_subset_mem ha sep_subset

/-- `⋃` closure, via the identity function graph `y ↦ ⟨y, y⟩` on `s`
and SGA4 clause 4. -/
theorem _root_.ConLeche.IsGrothendieck.sUnion_mem {s : V} (hs : s ∈ˢ U) :
    sUnion s ∈ˢ U := by
  have himg : HasImage (fun y : V => kpair y y) s := by
    fo_def [DefFun.kpair_apply]
  let g := image (fun y => kpair y y) s himg
  have hfg : IsFunGraph (Mem (V := V)) g s U := by
    constructor
    · intro p hp
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
      exact ⟨y, y, hy, hU.transitive hs hy, isKPair_kpair y y⟩
    · intro x hx
      refine ⟨x, ⟨hU.transitive hs hx, kpair x x,
        mem_image.mpr ⟨x, hx, rfl⟩, isKPair_kpair x x⟩, ?_⟩
      rintro y ⟨_, p, hp, hkp⟩
      obtain ⟨w, _, rfl⟩ := mem_image.mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      rfl
  obtain ⟨w, hw, hzw⟩ := hU.indexedUnion s g hs hfg
  have heq : w = sUnion s := ext fun z => by
    rw [hzw z, mem_sUnion]
    constructor
    · rintro ⟨i, y, p, hi, _, hp, hkp, hzy⟩
      obtain ⟨u, _, rfl⟩ := mem_image.mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      exact ⟨u, hi, hzy⟩
    · rintro ⟨y, hy, hzy⟩
      exact ⟨y, y, kpair y y, hy, hU.transitive hs hy,
        mem_image.mpr ⟨y, hy, rfl⟩, isKPair_kpair y y, hzy⟩
  exact heq ▸ hw

theorem _root_.ConLeche.IsGrothendieck.binUnion_mem {a b : V}
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : binUnion a b ∈ˢ U :=
  hU.sUnion_mem (hU.upair_mem ha hb)

/-- Union of a member-indexed family of members, given a set-level
function graph witness `HasImage (fun x => kpair x (F x)) A`. -/
theorem _root_.ConLeche.IsGrothendieck.famUnion_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U)
    (hImg : HasImage F A) (hG : HasImage (fun x => kpair x (F x)) A) :
    sUnion (image F A hImg) ∈ˢ U := by
  let g := image (fun x => kpair x (F x)) A hG
  have hfg : IsFunGraph (Mem (V := V)) g A U := by
    constructor
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
      exact ⟨x, F x, hx, hF x hx, isKPair_kpair x (F x)⟩
    · intro x hx
      refine ⟨F x, ⟨hF x hx, kpair x (F x),
        mem_image.mpr ⟨x, hx, rfl⟩, isKPair_kpair x (F x)⟩, ?_⟩
      rintro y ⟨_, p, hp, hkp⟩
      obtain ⟨w, _, rfl⟩ := mem_image.mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      rfl
  obtain ⟨w, hw, hzw⟩ := hU.indexedUnion A g hA hfg
  have heq : w = sUnion (image F A hImg) := ext fun z => by
    rw [hzw z, mem_sUnion]
    constructor
    · rintro ⟨i, y, p, hi, _, hp, hkp, hzy⟩
      obtain ⟨x, _, rfl⟩ := mem_image.mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      exact ⟨F x, mem_image.mpr ⟨x, hi, rfl⟩, hzy⟩
    · rintro ⟨y, hy, hzy⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      exact ⟨i, F i, kpair i (F i), hi, hF i hi,
        mem_image.mpr ⟨i, hi, rfl⟩, isKPair_kpair i (F i), hzy⟩
  exact heq ▸ hw

/-- Convenience form of `famUnion_mem` when `F` is `DefFunOn A F`. -/
theorem _root_.ConLeche.IsGrothendieck.famUnion_mem_of_def {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U)
    (hImg : HasImage F A) (hDef : DefFunOn A F) :
    sUnion (image F A hImg) ∈ˢ U :=
  hU.famUnion_mem hA hF hImg (hasImage_kpair hDef)

open Classical in
/-- Replacement closure: the image of a member under a fibre-wise
member-valued function is a member, given a set-level graph witness
`HasImage (fun x => kpair x (F x)) A`. -/
theorem _root_.ConLeche.IsGrothendieck.image_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U)
    (hImg : HasImage F A) (hG : HasImage (fun x => kpair x (F x)) A) :
    image F A hImg ∈ˢ U := by
  let R : V → (Fin 1 → V) → Prop := fun z v =>
    ∃ x y, v 0 = kpair x y ∧ z = kpair x (sing y)
  have hR : DefRel (1 + 1) fun w => R (w 0) (ftail w) := by
    fo_def [DefFun.kpair_apply, DefFun.sing_apply]
  let transform : V → V := fun p =>
    if h : ExistsUnique fun z => R z (fcons p Fin.elim0) then Classical.choose h
    else empty
  have htransDef : DefFun 1 fun v => transform (v 0) := by
    have huc := DefFun.uniqueChoice_curry hR
    refine huc.congr fun v => ?_
    have heqv : fcons (v 0) Fin.elim0 = v := by
      funext ⟨i, hi⟩
      match i with
      | 0 => rfl
    dsimp only [transform]
    simp only [heqv]
  have htrans_eq : ∀ x y : V, transform (kpair x y) = kpair x (sing y) := by
    intro x y
    have hex : ExistsUnique fun z => R z (fcons (kpair x y) Fin.elim0) := by
      refine ⟨kpair x (sing y), ⟨x, y, rfl, rfl⟩, ?_⟩
      rintro z ⟨x', y', hxy, rfl⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj hxy
      rfl
    have heq : transform (kpair x y) = Classical.choose hex := dite_eq_left hex
    rw [heq]
    obtain ⟨x', y', hxy, hchoose⟩ := (Classical.choose_spec hex).1
    obtain ⟨rfl, rfl⟩ := kpair_inj hxy
    exact hchoose
  let g₀ := image (fun x => kpair x (F x)) A hG
  have hgImg : HasImage transform g₀ := hasImage_of_defFun1 htransDef g₀
  let g := image transform g₀ hgImg
  have hg_mem : ∀ p, p ∈ˢ g ↔ ∃ x, x ∈ˢ A ∧ p = kpair x (sing (F x)) := by
    intro p
    rw [mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
      exact ⟨x, hx, htrans_eq x (F x)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨kpair x (F x), mem_image.mpr ⟨x, hx, rfl⟩, (htrans_eq x (F x)).symm⟩
  have hfg : IsFunGraph (Mem (V := V)) g A U := by
    constructor
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := (hg_mem p).mp hp
      exact ⟨x, sing (F x), hx, hU.sing_mem (hF x hx), isKPair_kpair x (sing (F x))⟩
    · intro x hx
      refine ⟨sing (F x), ⟨hU.sing_mem (hF x hx), kpair x (sing (F x)),
        (hg_mem _).mpr ⟨x, hx, rfl⟩, isKPair_kpair x (sing (F x))⟩, ?_⟩
      rintro y ⟨_, p, hp, hkp⟩
      obtain ⟨w, _, rfl⟩ := (hg_mem p).mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      rfl
  obtain ⟨w, hw, hzw⟩ := hU.indexedUnion A g hA hfg
  have heq : w = image F A hImg := ext fun z => by
    rw [hzw z, mem_image]
    constructor
    · rintro ⟨i, y, p, hi, _, hp, hkp, hzy⟩
      obtain ⟨x, _, rfl⟩ := (hg_mem p).mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      exact ⟨x, hi, mem_sing.mp hzy⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, sing (F i), kpair i (sing (F i)), hi, hU.sing_mem (hF i hi),
        (hg_mem _).mpr ⟨i, hi, rfl⟩, isKPair_kpair i (sing (F i)), mem_sing.mpr rfl⟩
  exact heq ▸ hw

/-- Convenience form of `image_mem` when `F` is `DefFunOn A F`. -/
theorem _root_.ConLeche.IsGrothendieck.image_mem_of_def {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U)
    (hImg : HasImage F A) (hDef : DefFunOn A F) :
    image F A hImg ∈ˢ U :=
  hU.image_mem hA hF hImg (hasImage_kpair hDef)

end IsGrothendieck

/-- Chain membership generalizes along the ordering, by transitivity
of the higher universe. -/
theorem univChain_mem_of_lt {m n : Nat} (h : m < n) :
    (univChain m : V) ∈ˢ univChain n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact (univChain_grothendieck (n + 1)).transitive (univChain_mem n) (ih h')
    · exact univChain_mem m

end ConLeche.SetTheory
