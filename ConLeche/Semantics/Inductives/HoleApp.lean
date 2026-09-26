module

public import ConLeche.Semantics.Tower.TowerIntro

@[expose] public section

/-!
# Holes occur only applied to the block's own parameters (lane CONTSEM, M3)

A block's fields with holes (`LfpDatum.fields`, `Model/Annot/BlockLfp.lean`)
read member `m` at the variable `nP + m`, whose value in the hole frame
is the member's family CURRIED OVER THE PARAMETERS AND BLIND IN THEM
(`LfpDatum.holeVal`).  A container's instantiation reads the fields at
a frame whose member slots hold something else — a group-mate's former
(its own value, a function of its parameters), or a frame hole — which
agrees with the hole value only APPLIED TO THE FRAME'S OWN PARAMETERS.
So the substitution law of the container case (`nestPos`'s `contApp`,
NESTPLAN L3 (i)) needs the syntactic fact that every hole occurrence is
such an application (R23's M3): `HoleApp`.

`HoleApp k nP lo e`: the positions `lo ..< lo + k` are the holes and
`lo + k ..< lo + k + nP` the parameters (at local depth: `lo` rises under
every binder); every occurrence of a hole heads a spine whose first `nP`
arguments are the parameters, in order (`holeParams`), the rest
arbitrary (themselves `HoleApp`).

`interp_congr_holeApp`: such a term reads the same at two frames that
agree off the holes and whose hole values agree whenever applied to the
frame's parameter values followed by ANY arguments.
-/

namespace ConLeche.Semantics

open SetTheory

universe uv

/-- The parameter variables at local depth `lo` (holes `lo ..< lo + k`,
parameters above them), in order: parameter `p` is the variable
`nP - 1 - p` below the holes' top. -/
def holeParams (k nP lo : Nat) : List AnnotTerm :=
  (List.range nP).map fun p => .bvar (lo + k + nP - 1 - p)

/-- **Every hole occurrence is applied to the parameters** (see the module
docstring). -/
inductive HoleApp (k nP : Nat) : Nat → AnnotTerm → Prop
  | bvar {lo i : Nat} : ¬ (lo ≤ i ∧ i < lo + k) → HoleApp k nP lo (.bvar i)
  | sort {lo u : Nat} : HoleApp k nP lo (.sort u)
  | const {lo : Nat} {c : ConLeche.Term.BConst} {us : List Nat} : HoleApp k nP lo (.const c us)
  | app {lo : Nat} {f a : AnnotTerm} : HoleApp k nP lo f → HoleApp k nP lo a →
      HoleApp k nP lo (.app f a)
  | lam {lo u : Nat} {A b : AnnotTerm} : HoleApp k nP lo A → HoleApp k nP (lo + 1) b →
      HoleApp k nP lo (.lam u A b)
  | pi {lo u v : Nat} {A B : AnnotTerm} : HoleApp k nP lo A → HoleApp k nP (lo + 1) B →
      HoleApp k nP lo (.pi u v A B)
  | eqE {lo : Nat} {a b : AnnotTerm} : HoleApp k nP lo a → HoleApp k nP lo b →
      HoleApp k nP lo (.eqE a b)
  | fst {lo : Nat} {e : AnnotTerm} : HoleApp k nP lo e → HoleApp k nP lo (.fst e)
  | snd {lo : Nat} {e : AnnotTerm} : HoleApp k nP lo e → HoleApp k nP lo (.snd e)
  | prf {lo : Nat} : HoleApp k nP lo .prf
  /-- a hole, applied to the parameters and then anything -/
  | hole {lo h : Nat} {rest : List AnnotTerm} : lo ≤ h → h < lo + k →
      (∀ r ∈ rest, HoleApp k nP lo r) →
      HoleApp k nP lo (AnnotTerm.mkAppN (.bvar h) (holeParams k nP lo ++ rest))

variable {V : Type uv} [SetTheory V]

/-- The values at the parameter positions of `holeParams`. -/
def holeParamVals (k nP lo : Nat) (σ : Nat → V) : List V :=
  (List.range nP).map fun p => σ (lo + k + nP - 1 - p)

theorem map_interp_holeParams (k nP lo : Nat) (σ : Nat → V) :
    (holeParams k nP lo).map (interp V σ) = holeParamVals k nP lo σ := by
  simp [holeParams, holeParamVals, List.map_map, Function.comp_def]

omit [SetTheory V] in
theorem holeParamVals_cons (k nP lo : Nat) (x : V) (σ : Nat → V) :
    holeParamVals k nP (lo + 1) (cons x σ) = holeParamVals k nP lo σ := by
  unfold holeParamVals
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  show cons x σ (lo + 1 + k + nP - 1 - p) = σ (lo + k + nP - 1 - p)
  rw [show lo + 1 + k + nP - 1 - p = (lo + k + nP - 1 - p) + 1 by omega]
  rfl

/-- **Frames related at the holes**: they agree off `lo ..< lo + k`, and
each hole's values agree applied to the parameter values and any
further arguments. -/
def HoleAgree (k nP lo : Nat) (σ σ' : Nat → V) : Prop :=
  (∀ i, ¬ (lo ≤ i ∧ i < lo + k) → σ i = σ' i) ∧
  ∀ h, lo ≤ h → h < lo + k → ∀ is : List V,
    (holeParamVals k nP lo σ ++ is).foldl app (σ h)
      = (holeParamVals k nP lo σ ++ is).foldl app (σ' h)

theorem HoleAgree.cons {k nP lo : Nat} {σ σ' : Nat → V} (h : HoleAgree k nP lo σ σ') (x : V) :
    HoleAgree k nP (lo + 1) (cons x σ) (cons x σ') := by
  refine ⟨fun i hi => ?_, fun hh h1 h2 is => ?_⟩
  · cases i with
    | zero => rfl
    | succ i => exact h.1 i fun ⟨a, b⟩ => hi ⟨by omega, by omega⟩
  · obtain ⟨hh, rfl⟩ : ∃ h', hh = h' + 1 := ⟨hh - 1, by omega⟩
    rw [holeParamVals_cons]
    exact h.2 hh (by omega) (by omega) is

theorem holeParamVals_congr {k nP lo : Nat} {σ σ' : Nat → V} (h : HoleAgree k nP lo σ σ') :
    holeParamVals k nP lo σ = holeParamVals k nP lo σ' := by
  unfold holeParamVals
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  exact h.1 _ fun ⟨_, b⟩ => by omega

/-- **The applied-hole agreement** (R23's step `htailC`/`htailH`,
generalised): a term whose holes occur only applied to the parameters
reads the same at frames related at the holes. -/
theorem interp_congr_holeApp {k nP : Nat} :
    ∀ {lo : Nat} {e : AnnotTerm}, HoleApp k nP lo e →
      ∀ {σ σ' : Nat → V}, HoleAgree k nP lo σ σ' → interp V σ e = interp V σ' e := by
  intro lo e he
  induction he with
  | bvar hi => intro σ σ' h; exact h.1 _ hi
  | sort => intros; rfl
  | const => intros; rfl
  | app _ _ ihf iha => intro σ σ' h; simp only [interp_app, ihf h, iha h]
  | lam _ _ ihA ihb =>
    intro σ σ' h
    simp only [interp_lam, ihA h]
    congr 1; funext x; exact ihb (h.cons x)
  | pi _ _ ihA ihB =>
    intro σ σ' h
    simp only [interp_pi, ihA h]
    congr 1; funext x; exact ihB (h.cons x)
  | eqE _ _ iha ihb => intro σ σ' h; simp only [interp_eqE, iha h, ihb h]
  | fst _ ih => intro σ σ' h; simp only [interp_fst, ih h]
  | snd _ ih => intro σ σ' h; simp only [interp_snd, ih h]
  | prf => intros; rfl
  | @hole lo hh rest h1 h2 _ ih =>
    intro σ σ' h
    rw [interp_mkAppN_foldl, interp_mkAppN_foldl, List.map_append, List.map_append,
      map_interp_holeParams, map_interp_holeParams, ← holeParamVals_congr h, interp_bvar,
      interp_bvar]
    have hrest : rest.map (interp V σ) = rest.map (interp V σ') :=
      List.map_congr_left fun r hr => ih r hr h
    rw [hrest]
    exact h.2 hh h1 h2 _

/-- **A term not mentioning the holes** at all is `HoleApp` (the lifted
readings of hole-free fields and indices: `liftN k lo` skips the holes'
positions). -/
theorem holeApp_liftN (k nP : Nat) :
    ∀ (e : AnnotTerm) (lo : Nat), HoleApp k nP lo (e.liftN k lo) := by
  intro e
  induction e with
  | bvar i =>
    intro lo
    simp only [AnnotTerm.liftN_bvar]
    split
    · exact .bvar fun ⟨a, _⟩ => by omega
    · exact .bvar fun ⟨a, _⟩ => by omega
  | sort u => intro lo; exact .sort
  | const c us => intro lo; exact .const
  | app f a ihf iha => intro lo; exact .app (ihf lo) (iha lo)
  | lam u A b ihA ihb => intro lo; exact .lam (ihA lo) (ihb (lo + 1))
  | pi u v A B ihA ihB => intro lo; exact .pi (ihA lo) (ihB (lo + 1))
  | eqE a b iha ihb => intro lo; exact .eqE (iha lo) (ihb lo)
  | fst e ih => intro lo; exact .fst (ih lo)
  | snd e ih => intro lo; exact .snd (ih lo)
  | prf => intro lo; exact .prf

/-- **A telescope whose holes occur only applied to the parameters** —
field `l` at local depth `lo + l` — fits the same spines at frames
related at the holes. -/
theorem spineFit_congr_holeApp {k nP : Nat} :
    ∀ (Fs : List AnnotTerm) {lo : Nat},
      (∀ l F, Fs[l]? = some F → HoleApp k nP (lo + l) F) →
      ∀ {σ σ' : Nat → V}, HoleAgree k nP lo σ σ' →
        ∀ fs : List V, SpineFit σ Fs fs ↔ SpineFit σ' Fs fs
  | [], _, _, _, _, _, [] => Iff.rfl
  | [], _, _, _, _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, _, _, _, [] => Iff.rfl
  | F :: Fs, lo, hF, σ, σ', h, a :: as => by
    have h0 : HoleApp k nP lo F := by simpa using hF 0 F rfl
    have ht : ∀ l F', Fs[l]? = some F' → HoleApp k nP (lo + 1 + l) F' := by
      intro l F' hl
      have := hF (l + 1) F' (by simpa using hl)
      rwa [show lo + (l + 1) = lo + 1 + l by omega] at this
    show (a ∈ˢ interp V σ F ∧ SpineFit (cons a σ) Fs as) ↔
      (a ∈ˢ interp V σ' F ∧ SpineFit (cons a σ') Fs as)
    rw [interp_congr_holeApp h0 h, spineFit_congr_holeApp Fs ht (h.cons a) as]

/-- Frames related at the holes stay related below a common spine. -/
theorem HoleAgree.consList {k nP lo : Nat} :
    ∀ (fs : List V) {σ σ' : Nat → V}, HoleAgree k nP lo σ σ' →
      HoleAgree k nP (lo + fs.length) (consList fs σ) (consList fs σ')
  | [], _, _, h => h
  | a :: fs, _, _, h => by
    have := HoleAgree.consList (lo := lo + 1) fs (h.cons a)
    rwa [show lo + 1 + fs.length = lo + (a :: fs).length by simp; omega] at this

end ConLeche.Semantics
