import Lech.Semantics.Tower.TowerRec
import Lech.Semantics.Denote2Closed

/-!
# The direct-structure leaves' syntactic battery (task #175 wiring, W4)

The wiring checklist's item 1: the `hAclosed` row of an install-step
leaf is `AVExpr.liftN 1 (leaf) k = leaf`, and by
`AVExpr.liftN_eq_self` (`SetBase/Denote2Closed.lean`) that is exactly
boundedness of the leaf's **erasure** — annotations are inert, only
bvars move.  So this module is a bvar-bound walk per leaf
constructor, plus the peel lemma that produces the binder-data bounds
from the (closed) type reading the wiring strips
(`stripPisAV_below`).

Everything is a structural induction over the leaf formers of
`SetBase/Tower{Leaf,Mk,Rec}.lean`; no semantics, no `V`.

The `hAparams` row needs nothing from here: every leaf is a *plain
function* of its computed numerals and binder data
(`directTyAV`/`directMkAV`/`directRecAV`), so level-parameter
congruence at the install site is congruence of the inputs — the
readings' own `denoteP` congruence, discharged where the readings are
made.
-/

namespace Lech.Semantics
open Lech.SetModel

open Lech.TT

/-! ## Bound-variable bounds, at the erasure -/

/-- The domains of a λ-frame, each bounded at its own depth
(`(u, dom)` pairs — `mkLamsAV`'s data). -/
def LamDomsBelow (k : Nat) : List (Nat × AVExpr) → Prop
  | [] => True
  | d :: ds => VExpr.bvarsBelow k d.2.erase ∧ LamDomsBelow (k + 1) ds

/-- The binder triples of a Π-frame, each domain bounded at its own
depth (`(u, v, dom)` triples — `mkPisAV`/`mkLamsC`'s data). -/
def DomsBelow (k : Nat) : List (Nat × Nat × AVExpr) → Prop
  | [] => True
  | d :: ds => VExpr.bvarsBelow k d.2.2.erase ∧ DomsBelow (k + 1) ds

/-- A field-domain chain, each domain bounded at its own depth. -/
def FieldsBelow (k : Nat) : List AVExpr → Prop
  | [] => True
  | F :: Fs => VExpr.bvarsBelow k F.erase ∧ FieldsBelow (k + 1) Fs

/-- The domains' closedness, entry by entry. -/
theorem DomsBelow.getD_below {K : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)}, DomsBelow K ds → ∀ k, k < ds.length →
      VExpr.bvarsBelow (K + k) (ds.getD k default).2.2.erase
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | d :: ds, h, 0, _ => by simpa using h.1
  | d :: ds, h, k + 1, hk => by
    simp only [List.getD_cons_succ]
    have := DomsBelow.getD_below (K := K + 1) (ds := ds) h.2 k (by simpa using hk)
    rwa [show K + 1 + k = K + (k + 1) from by omega] at this

theorem domsBelow_of_getD {K : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)},
      (∀ k, k < ds.length → VExpr.bvarsBelow (K + k) (ds.getD k default).2.2.erase) → DomsBelow K ds
  | [], _ => trivial
  | d :: ds, h => by
    refine ⟨by simpa using h 0 (by simp), domsBelow_of_getD (K := K + 1) (ds := ds) fun k hk => ?_⟩
    have := h (k + 1) (by simpa using hk)
    simpa [show K + (k + 1) = K + 1 + k from by omega] using this

theorem DomsBelow.map {k : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)}, DomsBelow k ds →
      LamDomsBelow k (ds.map fun d => (d.1, d.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.map h.2⟩

theorem DomsBelow.mapC {m k : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)}, DomsBelow k ds →
      LamDomsBelow k (ds.map fun d => (m, d.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.mapC h.2⟩

theorem DomsBelow.fields {k : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)}, DomsBelow k ds →
      FieldsBelow k (ds.map (·.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.fields h.2⟩

/-! ## The `VExpr`-side helpers -/

namespace VExprAux

open Lech.TT.VExpr

/-- Lifting raises a bound by exactly the inserted count, at any
cut. -/
theorem bvarsBelow_liftN (n : Nat) :
    ∀ (v : VExpr) (m k : Nat), VExpr.bvarsBelow m v →
      VExpr.bvarsBelow (m + n) (VExpr.liftN n v k) := by
  intro v
  induction v with
  | bvar i =>
    intro m k h
    show VExpr.bvarsBelow (m + n) (.bvar (if i < k then i else i + n))
    by_cases hik : i < k
    · rw [if_pos hik]
      exact Nat.lt_of_lt_of_le (show i < m from h) (Nat.le_add_right m n)
    · rw [if_neg hik]
      exact Nat.add_lt_add_right (show i < m from h) n
  | sort u => intro _ _ _; trivial
  | const c us => intro _ _ _; trivial
  | prf => intro _ _ _; trivial
  | app f a ihf iha =>
    intro m k h
    exact ⟨ihf m k h.1, iha m k h.2⟩
  | lam A b ihA ihb =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihb (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | pi A B ihA ihB =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihB (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | letE T v b ihT ihv ihb =>
    intro m k h
    refine ⟨ihT m k h.1, ihv m k h.2.1, ?_⟩
    have := ihb (m + 1) (k + 1) h.2.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | eqE T a b ihT iha ihb =>
    intro m k h
    exact ⟨ihT m k h.1, iha m k h.2.1, ihb m k h.2.2⟩
  | proj i e ihe =>
    intro m k h
    exact ihe m k h

/-- Application spines preserve a bound. -/
theorem bvarsBelow_mkAppN :
    ∀ {as : List VExpr} {f : VExpr} {k : Nat}, VExpr.bvarsBelow k f →
      (∀ a ∈ as, VExpr.bvarsBelow k a) →
      VExpr.bvarsBelow k (VExpr.mkAppN f as)
  | [], _, _, hf, _ => hf
  | a :: as, f, k, hf, has => by
    rw [VExpr.mkAppN_cons]
    exact bvarsBelow_mkAppN ⟨hf, has a (.head _)⟩
      fun a' ha' => has a' (.tail _ ha')

end VExprAux

/-! ## The leaf constructors' bounds -/

/-- The carrier body (graph regime): bounded from the field chain's
own bounds. -/
theorem towerBodyAVPos_below {w : Nat} :
    ∀ {Fs : List AVExpr} {k : Nat}, FieldsBelow k Fs →
      VExpr.bvarsBelow k (towerBodyAVPos w Fs).erase
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨trivial, h.1⟩, h.1, towerBodyAVPos_below h.2⟩

/-- The carrier body (squash regime): bounded from the field chain's
own bounds. -/
theorem sqBodyAV_below :
    ∀ {Fs : List AVExpr} {k : Nat}, FieldsBelow k Fs →
      VExpr.bvarsBelow k (sqBodyAV Fs).erase
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨h.1, sqBodyAV_below h.2, trivial⟩, trivial⟩

/-- The carrier body, both regimes. -/
theorem towerBodyAV_below {w : Nat} {Fs : List AVExpr} {k : Nat}
    (h : FieldsBelow k Fs) :
    VExpr.bvarsBelow k (towerBodyAV w Fs).erase := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_below h
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_below h

/-- The uniform projection spelling adds no variables. -/
theorem projAV_below :
    ∀ {i : Nat} {e : AVExpr} {k : Nat}, VExpr.bvarsBelow k e.erase →
      VExpr.bvarsBelow k (projAV i e).erase
  | 0, _, _, h => h
  | i + 1, e, _, h => projAV_below (i := i) (e := .proj 1 e) h

/-- The recursor body mentions only the minor (`.bvar 1`) and the
major (`.bvar 0`). -/
theorem recBodyAV_below {nF k : Nat} (h2 : 2 ≤ k) :
    VExpr.bvarsBelow k (recBodyAV nF).erase := by
  rw [recBodyAV, AVExpr.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show 1 < k by omega) ?_
  intro a ha
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hea
  exact projAV_below (show (0 : Nat) < k by omega)

/-- The tupler (graph regime): bounded at the full field frame. -/
theorem mkTowerGoPos_below {w : Nat} :
    ∀ {Fs : List AVExpr} {k : Nat}, FieldsBelow k Fs →
      VExpr.bvarsBelow (k + Fs.length) (mkTowerGoPos w Fs).erase
  | [], _, _ => trivial
  | F :: Fs, k, h => by
    have hF : VExpr.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)).erase := by
      rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F.erase k 0 h.1
      exact this
    have hbody : VExpr.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w Fs).liftN (Fs.length + 1) 1).erase := by
      rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w Fs).erase (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : VExpr.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoPos w Fs).erase := by
      have := mkTowerGoPos_below (w := w) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The tupler, both regimes. -/
theorem mkTowerGo_below {w : Nat} {Fs : List AVExpr} {k : Nat}
    (h : FieldsBelow k Fs) :
    VExpr.bvarsBelow (k + Fs.length) (mkTowerGo w Fs).erase := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_below h

/-- The λ-tower former: bounded from the frame's own bounds and the
body's at the full depth. -/
theorem mkLamsAV_below :
    ∀ {ds : List (Nat × AVExpr)} {b : AVExpr} {k : Nat},
      LamDomsBelow k ds →
      VExpr.bvarsBelow (k + ds.length) b.erase →
      VExpr.bvarsBelow k (mkLamsAV ds b).erase
  | [], _, _, _, hb => hb
  | d :: ds, b, k, h, hb =>
    ⟨h.1, mkLamsAV_below h.2 (by
      rw [show k + 1 + ds.length = k + (ds.length + 1) by omega]
      exact hb)⟩

/-- The constant-bit tower, over Π-frame data. -/
theorem mkLamsC_below {m : Nat} {ds : List (Nat × Nat × AVExpr)}
    {b : AVExpr} {k : Nat} (h : DomsBelow k ds)
    (hb : VExpr.bvarsBelow (k + ds.length) b.erase) :
    VExpr.bvarsBelow k (mkLamsC m ds b).erase :=
  mkLamsAV_below h.mapC (by
    rw [List.length_map]; exact hb)

/-! ## The peel: bounds off a bounded reading -/

/-- A successful `stripPisAV` of a bounded reading bounds every binder
domain at its own depth and the residual at the full depth. -/
theorem stripPisAV_below :
    ∀ {n : Nat} {e : AVExpr} {ps : List (Nat × Nat × AVExpr)}
      {b : AVExpr} {k : Nat},
      stripPisAV n e = some (ps, b) →
      VExpr.bvarsBelow k e.erase →
      DomsBelow k ps ∧ VExpr.bvarsBelow (k + n) b.erase
  | 0, e, ps, b, k, h, he => by
    obtain ⟨rfl, rfl⟩ : ps = [] ∧ b = e := by
      simpa [stripPisAV] using h.symm
    exact ⟨trivial, he⟩
  | n + 1, .pi u v A B, ps, b, k, h, he => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps', b'⟩, hstrip, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : (u, v, A) :: ps' = ps ∧ b' = b := by
      simpa using heq
    obtain ⟨hds, hb⟩ := stripPisAV_below hstrip he.2
    exact ⟨⟨he.1, hds⟩, by
      rw [show k + (n + 1) = k + 1 + n by omega]
      exact hb⟩

/-! ## The three leaves -/

/-- **The type-former leaf is bounded** from the parameter frame's
and the field chain's bounds. -/
theorem directTyAV_below {w : Nat} {pps : List (Nat × Nat × AVExpr)}
    {Fs : List AVExpr} {k : Nat} (hp : DomsBelow k pps)
    (hF : FieldsBelow (k + pps.length) Fs) :
    VExpr.bvarsBelow k (directTyAV w pps Fs).erase :=
  mkLamsAV_below hp.mapC (by
    rw [List.length_map]
    exact towerBodyAV_below hF)

/-- **The constructor leaf is bounded**: the binder frame is the
parameter+field frame and the tupler sits at its top.  `hlen` is the
frame accounting the wiring computes (`ds = pds ++ fds`,
`Fs = fds.map (·.2.2)`, so the tupler's own frame ends exactly at the
binder tower's). -/
theorem directMkAV_below {w : Nat} {ds : List (Nat × Nat × AVExpr)}
    {Fs : List AVExpr} {k j : Nat} (hd : DomsBelow k ds)
    (hF : FieldsBelow (k + j) Fs)
    (hlen : j + Fs.length = ds.length) :
    VExpr.bvarsBelow k (directMkAV w ds Fs).erase :=
  mkLamsC_below hd (by
    have := mkTowerGo_below (w := w) hF
    rw [show k + j + Fs.length = k + ds.length by omega] at this
    exact this)

/-- **The recursor leaf is bounded**: the body reads only the minor
and the major, which sit inside any frame of length ≥ 2. -/
theorem directRecAV_below {ℓ : Nat} {ds : List (Nat × Nat × AVExpr)}
    {nF : Nat} {k : Nat} (hd : DomsBelow k ds)
    (h2 : 2 ≤ ds.length) :
    VExpr.bvarsBelow k (directRecAV ℓ ds nF).erase :=
  mkLamsC_below hd (recBodyAV_below (by omega))

/-! ## The `hAclosed` packages

The install rows want `AVExpr.liftN 1 (leaf) k = leaf` for every cut
`k`; a leaf bounded at `0` is bounded at every cut
(`VExpr.bvarsBelow.mono`), and a lift below the bound is the identity
(`AVExpr.liftN_eq_self`). -/

/-- A closed leaf is `liftN`-invariant at every cut. -/
theorem liftN_eq_self_of_closed {e : AVExpr}
    (h : VExpr.bvarsBelow 0 e.erase) (k n : Nat) :
    AVExpr.liftN n e k = e :=
  AVExpr.liftN_eq_self e (VExpr.bvarsBelow.mono (Nat.zero_le k) h) n

end Lech.Semantics
