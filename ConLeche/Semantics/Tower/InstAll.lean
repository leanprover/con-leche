module

public import ConLeche.Semantics.Tower.SumRecCase
import ConLeche.Semantics.Tower.FixIhI

@[expose] public section

/-!
# Iterated parameter instantiation under binders (task #315 M6 s5)

The instantiation law behind the nested route's PIN IDENTIFICATION: a
copy's constructor is the container's with the container's parameters
instantiated at the pin's components `Ds`, and the copy's field
readings are the container's with `Ds` substituted UNDER the earlier
fields' binders (DESIGN §U.14 (e) 2–4).  This module is the pure
term-level half:

* `AnnotTerm.instAll ds k e` substitutes the parameter list `ds` — the
  OUTERMOST parameter first, at the highest cut — for the `ds.length`
  binders sitting at depth `k` in `e` (the `k` binders below the cut
  are the earlier fields, which stay);
* `instTele ds c ts` instantiates a telescope, entry `m` at cut `c + m`;
* **`interp_instAll`**: at a frame holding `k` field values above the
  base `ρ`, the instantiated term reads as the original at the frame
  holding the fields above the parameters' VALUES at `ρ` — the copy's
  reading at the block's frame is the container's at the pin's frame;
* `towerSet_instTele` and `piTele_instTele` are the same law along a
  telescope, at the tower set and the nested product.
-/

namespace ConLeche.Semantics

open ConLeche.Term SetTheory ConLeche.SetModel SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-- The parameter list `ds` substituted for the `ds.length` binders at
depth `k` — the outermost parameter first, at cut `k + (ds.length - 1)`,
down to the innermost at cut `k`.  `inst` lifts each substituted term
past the cut, so `ds` are stated at the BASE context. -/
def AnnotTerm.instAll : List AnnotTerm → Nat → AnnotTerm → AnnotTerm
  | [], _, e => e
  | d :: ds, k, e => instAll ds k (e.inst d (k + ds.length))

/-- A telescope instantiated: entry `m` at cut `c + m` (each entry
sits under the earlier ones). -/
def instTele (ds : List AnnotTerm) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | c, t :: ts => AnnotTerm.instAll ds c t :: instTele ds (c + 1) ts

omit [SetTheory V] in
theorem instTele_length (ds : List AnnotTerm) :
    ∀ (c : Nat) (ts : List AnnotTerm), (instTele ds c ts).length = ts.length
  | _, [] => rfl
  | c, _ :: ts => by simp only [instTele, List.length_cons, instTele_length ds (c + 1) ts]

omit [SetTheory V] in
theorem instTele_getD (ds : List AnnotTerm) :
    ∀ (c : Nat) (ts : List AnnotTerm) (m : Nat), m < ts.length →
      (instTele ds c ts).getD m default = AnnotTerm.instAll ds (c + m) (ts.getD m default)
  | _, [], _, h => by simp at h
  | c, t :: ts, 0, _ => by simp [instTele]
  | c, t :: ts, m + 1, h => by
    simp only [instTele, List.getD_cons_succ]
    rw [instTele_getD ds (c + 1) ts m (by simpa using h), Nat.add_assoc, Nat.add_comm 1 m]

/-- **The instantiation law at a frame**: with `fs` field values above
the base `ρ`, the term with `ds` substituted at the fields' depth reads
as the original at the frame holding `fs` above the values of `ds` at
`ρ`. -/
theorem interp_instAll :
    ∀ (ds : List AnnotTerm) (fs : List V) (ρ : Nat → V) (e : AnnotTerm),
      interp V (consList fs ρ) (AnnotTerm.instAll ds fs.length e)
        = interp V (consList fs (consList (ds.map (interp V ρ)) ρ)) e
  | [], fs, ρ, e => rfl
  | d :: ds, fs, ρ, e => by
    simp only [AnnotTerm.instAll, List.map_cons, consList_cons]
    rw [interp_instAll ds fs ρ, interp_inst]
    have hsh : shiftE (fs.length + ds.length) 0 (consList fs (consList (ds.map (interp V ρ)) ρ))
        = ρ := by
      have := shiftE_consList (ds.map (interp V ρ)) ρ
      rw [List.length_map] at this
      rw [shiftE_consList_add, this]
    have hin := instE_consList (interp V ρ d) fs (ds.map (interp V ρ)).length
      (consList (ds.map (interp V ρ)) ρ)
    rw [instE_consList', List.length_map] at hin
    rw [hsh, hin]

/-- `sigmaSet` reads its universe only through `= 0`. -/
theorem sigmaSet_zero_agree {w w' : Nat} (hz : w = 0 ↔ w' = 0) (A : V) (B : V → V) :
    sigmaSet w A B = sigmaSet w' A B := by
  by_cases hw : w = 0
  · rw [hw, hz.mp hw]
  · have hw' : w' ≠ 0 := fun h => hw (hz.mpr h)
    rw [sigmaSet_pos hw, sigmaSet_pos hw']

/-- **The bound law**: the hereditary bound over a telescope instantiated
at the fields' depth, at the fields' frame, is the bound over the
original telescope at the pin's frame (`interp_instAll` along the
telescope; task #315 L-A, the pins' index telescopes at the squash
regime). -/
theorem fieldsBound_instTele (w : Nat) (ds : List AnnotTerm) (ρ : Nat → V) :
    ∀ (ts : List AnnotTerm) (fs : List V),
      FieldsBound w (consList fs ρ) (instTele ds fs.length ts)
        ↔ FieldsBound w (consList fs (consList (ds.map (interp V ρ)) ρ)) ts
  | [], _ => Iff.rfl
  | t :: ts, fs => by
    simp only [instTele, FieldsBound]
    rw [interp_instAll ds fs ρ t]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr_right fun _ => ?_)
    have := fieldsBound_instTele w ds ρ ts (fs ++ [a])
    rw [List.length_append, List.length_singleton] at this
    simpa only [consList_append, consList_cons, consList_nil] using this

/-- **The tower law**: the tower set over a telescope instantiated at
the fields' depth, at the fields' frame, is the tower set over the
original telescope at the pin's frame — in either regime whenever the
two universes agree on `= 0`. -/
theorem towerSet_instTele {w w' : Nat} (hz : w = 0 ↔ w' = 0) (ds : List AnnotTerm) (ρ : Nat → V) :
    ∀ (ts : List AnnotTerm) (fs : List V),
      towerSet w (teleOfFields (consList fs ρ) (instTele ds fs.length ts))
        = towerSet w' (teleOfFields (consList fs (consList (ds.map (interp V ρ)) ρ)) ts)
  | [], fs => rfl
  | t :: ts, fs => by
    simp only [instTele, teleOfFields_cons, towerSet]
    rw [interp_instAll ds fs ρ t, sigmaSet_zero_agree hz]
    refine sigma_congr fun a _ => ?_
    have := towerSet_instTele hz ds ρ ts (fs ++ [a])
    rw [List.length_append, List.length_singleton] at this
    simpa only [consList_append, consList_cons, consList_nil] using this

/-- **The product law**: the nested product over a telescope
instantiated at the fields' depth, at the fields' frame, is the
product over the original at the pin's frame, when the bodies agree at
every fitting spine and the universes agree on `= 0`. -/
theorem piTele_instTele {w w' : Nat} (hz : w = 0 ↔ w' = 0) (ds : List AnnotTerm) (ρ : Nat → V)
    {B B' : List V → V} :
    ∀ (ts : List AnnotTerm) (fs : List V) (acc : List V),
      (∀ bs : List V, SpineFit (consList fs (consList (ds.map (interp V ρ)) ρ)) ts bs →
        B (acc ++ bs) = B' (acc ++ bs)) →
      piTele w (teleOfFields (consList fs ρ) (instTele ds fs.length ts)) B acc
        = piTele w' (teleOfFields (consList fs (consList (ds.map (interp V ρ)) ρ)) ts) B' acc
  | [], fs, acc, hB => by
    simp only [instTele, teleOfFields_nil, piTele]
    simpa using hB [] trivial
  | t :: ts, fs, acc, hB => by
    simp only [instTele, teleOfFields_cons, piTele]
    rw [interp_instAll ds fs ρ t]
    refine piR_zero_agree hz fun a ha => ?_
    have := piTele_instTele hz ds ρ ts (fs ++ [a]) (acc ++ [a]) fun bs hbs => by
      have h := hB (a :: bs) ⟨ha, by
        simpa only [consList_append, consList_cons, consList_nil] using hbs⟩
      simpa only [List.append_assoc, List.singleton_append] using h
    rw [List.length_append, List.length_singleton] at this
    simpa only [consList_append, consList_cons, consList_nil] using this


/-- **A spine fits an instantiated telescope at the block's frame iff it
fits the telescope at the pin's frame** (`interp_instAll` along the
telescope). -/
theorem spineFit_instTele (Ds : List AnnotTerm) (ρ' : Nat → V) :
    ∀ (Ids : List AnnotTerm) (fs₁ is : List V),
      SpineFit (consList fs₁ ρ') (instTele Ds fs₁.length Ids) is ↔
        SpineFit (consList fs₁ (consList (Ds.map (interp V ρ')) ρ')) Ids is
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | T :: Ids, fs₁, a :: is => by
    show (a ∈ˢ interp V (consList fs₁ ρ') (AnnotTerm.instAll Ds fs₁.length T) ∧
        SpineFit (cons a (consList fs₁ ρ')) (instTele Ds (fs₁.length + 1) Ids) is) ↔
      (a ∈ˢ interp V (consList fs₁ (consList (Ds.map (interp V ρ')) ρ')) T ∧
        SpineFit (cons a (consList fs₁ (consList (Ds.map (interp V ρ')) ρ'))) Ids is)
    rw [interp_instAll]
    have h := spineFit_instTele Ds ρ' Ids (fs₁ ++ [a]) is
    rw [List.length_append, List.length_singleton, consList_append, consList_append] at h
    exact and_congr Iff.rfl h

end ConLeche.Semantics
