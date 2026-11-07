module

public import ConLeche.Model.Modular.Instance
import ConLeche.Model.Modular.Valid

public section

/-!
# The modular theorem at con-leche's models

A development of modules (`ConLeche.Modular.Module`) is a development over the instance
(`toDev`): a module's context and own environment expose every name, its sources are every
earlier module's own environment exposing what the module reads alike from it
(`ConLeche.Modular.readsAlike`), and its keys are the module's.  A module passing the local checks
(`LocalOk`) is a valid one (`toDev_valid`): its
context is assembled from the sources (`reading`, `Valid.lean`), one copy of each name holds by the
views' exposure, its records are accepted from the context, and a new name is its own or a flagged
proof.  The generic theorem (`Development.modular`) then gives the compatible family of models
(`modularModels`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Cached
open ConLeche.Term (Term)

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet}

/-- The view module `i` reads of module `b`: `b`'s own environment, exposing what `i` reads alike
from it. -/
@[expose] def viewOf (dev : Nat → Module) (i b : Nat) : XEnv :=
  ((dev b).own, fun n => ((dev i).context.find? n).isSome = true ∧ (dev i).key n = (dev b).key n)

variable (V pins) in
/-- **A development of modules over the instance.** -/
@[expose] noncomputable def toDev (dev : Nat → Module) :
    Development (conlecheSemantics V pins) Stmt where
  ctx j := ((dev j).context, fun _ => True)
  decls j := ((dev j).decls, (dev j).proofs)
  own j := ((dev j).own, fun _ => True)
  sources j := (List.range j).map fun b => (b, viewOf dev j b)
  key j := (dev j).key

/-- **A module passing the local checks is valid.** -/
theorem toDev_valid {dev : Nat → Module} {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) :
    (toDev V pins dev).Valid i := by
  classical
  have hK := (hok i (Nat.le_refl i)).importOk
  refine ⟨fun x hx => ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩
  · -- a source is an earlier module's own environment, exposing fewer names
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact ⟨List.mem_range.mp hb, AssembledX.self PUnit.unit rfl fun _ _ _ => trivial⟩
  · -- the context, assembled from the sources
    let srcOf : Name → Option ((toDev V pins dev).Src i) := fun n =>
      if h : ((dev i).context.find? n).isSome = true then
        some ⟨((dev i).src n, viewOf dev i ((dev i).src n)),
          List.mem_map.mpr ⟨(dev i).src n, List.mem_range.mpr (hK.src_lt n h), rfl⟩⟩
      else none
    have hsE : srcEnv (fun x : (toDev V pins dev).Src i => x.1.2) srcOf = srcOwn dev i := by
      funext n
      by_cases h : ((dev i).context.find? n).isSome = true
      · simp [srcEnv, srcOf, srcOwn, h, viewOf]
      · simp [srcEnv, srcOf, srcOwn, h]
    refine AssembledX.reads srcOf (srcReads dev i) (fun _ => trivial)
      (fun n h => by
        change ((dev i).context.find? n).isSome = true at h
        simp only [srcOf, dite_eq_left h]; rfl)
      (fun n x hx d hd => ?_) (hsE ▸ reading hok)
    · -- what a source exposes is what is read alike from it
      by_cases h : ((dev i).context.find? n).isSome = true
      · simp only [srcOf, dite_eq_left h] at hx
        obtain rfl := Option.some.inj hx
        show ((dev i).context.find? d).isSome = true ∧ (dev i).key d = (dev ((dev i).src n)).key d
        simp only [srcReads, h, ↓reduceIte] at hd
        rw [readsAlike_find?] at hd
        split at hd
        · next hc => exact hc
        · exact nomatch hd
      · simp [srcOf, h] at hx
  · -- one copy: a source exposes only what is read alike
    intro n _ x hx hs
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact Development.interchangeable_iff.mpr hs.2.2
  · -- the own records, accepted from the context with their flags
    obtain ⟨q, hq⟩ := hK.accepted
    exact ⟨rfl, ⟨_, q, hq⟩, hK.flags⟩
  · -- a new name is the module's own, or a flagged proof
    intro n hn hC
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn.1
    have hCn : (dev i).context.find? n = none := by
      cases h : (dev i).context.find? n with
      | none => rfl
      | some _ => exact absurd ⟨show ((dev i).context.find? n).isSome = true by rw [h]; rfl, trivial⟩ hC
    have hkey := hK.key_own n ci hci hCn
    unfold Module.ownKey at hkey
    by_cases hp : (dev i).proofs n = true
    · rw [ite_eq_left hp] at hkey
      rcases own_find?_cases hK hci with h | ⟨-, d, hd, hcd⟩
      · rw [h] at hCn; exact nomatch hCn
      · refine .inr ⟨⟨_, hkey⟩, hp, d, hd, ?_⟩
        exact List.mem_map.mpr ⟨ci, hcd, ConLeche.Env.find?_name hci⟩
    · rw [ite_eq_right hp] at hkey
      exact .inl hkey

/-- **The compatible family of models**, over the instance. -/
theorem modularModels {dev : Nat → Module} {i : Nat}
    (hok : ∀ j ≤ i, LocalOk .verified pins dev j) :
    ∃ m : (j : Nat) → j < i + 1 → MMod V ((dev j).own, fun _ => True),
      (toDev V pins dev).Compatible (i + 1) m :=
  (toDev V pins dev).modular (i + 1) fun j hj =>
    toDev_valid fun k hk => hok k (by omega)

end ConLeche.Model.Modular
