module

public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Annot.BitLevels
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# The container substitution law

A container frame (`nestCtors`, `Kernel/Inductives/Positivity.lean`)
walks a stored constructor type `e` of the container's block at the
instantiation `(us, ds)`: `instPisWith ds ((e.instantiateLevelParams lps
us).replaceConsts sub)`, the reached group's members replaced by the
frame's holes (`sub`).  The record reads the same constructor
member-abstracted at the canonical variables (M2): `instPisWith params
(nestAbstract ctx holes e)` at depth `nP + k`, as the Π-tower over the
clause's fields with holes.

**The law** (`frameCrest_read`): when every member occurrence of `e` is
at the block's levels (M2′, which the kernel checks at every
install), the frame's constructor type reads, at the frame's depth, as
the recorded reading at the levels `us` with its parameter and hole
positions substituted — by the readings of the key's parameters, and of
the frame's holes (the reached group) or of the members' formers (the
rest) — ALL AT ONCE (`AnnotTerm.substAV`).  So a field spine fits the
frame's walked telescope exactly when it fits the recorded fields at the
valuation holding those values (`spineFit_substTele`): the parameter
frame `⟦ds⟧`, and at each member slot the frame's hole value or the
member's former.  The Expr half is `Expr.frameCrest_eq`
(`Verify/SubstFvars.lean`), the reading half `denoteMeta_substFvars`
(`Model/Annot/BitSubstFvars.lean`), the levels `denotePInstLevels`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx nestAbstract instPisWith)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- The level parameters, instantiated at a list of their own length, are
that list (the block's own levels at the key's). -/
theorem map_param_subst : ∀ {lps : List Name} {us : List Level}, lps.Nodup →
    us.length = lps.length → (lps.map Level.param).map (Level.subst lps us) = us
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | k :: ks, v :: vs, hnd, hlen => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    have hrest := map_param_subst (lps := ks) (us := vs) (List.nodup_cons.mp hnd).2
      (by simpa using hlen)
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨by simp [Level.subst, Level.subst.go], ?_⟩
    have hcongr : (ks.map Level.param).map (Level.subst (k :: ks) (v :: vs))
        = (ks.map Level.param).map (Level.subst ks vs) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro n hn
      have hne : k ≠ n := fun h => hk (h ▸ hn)
      simp [Level.subst, Level.subst.go, hne]
    rw [hcongr, hrest]

theorem fvarsBelow_instantiateLevelParams (ks : List Name) (us : List Level) {d : Nat} :
    ∀ {e : Expr}, Expr.fvarsBelow d e → Expr.fvarsBelow d (e.instantiateLevelParams ks us) := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.fvarsBelow, Expr.instantiateLevelParams]

/-- **The container substitution law, reading side** (see the module
docstring): the frame's constructor type reads as the recorded Π-tower
with its parameter and hole positions substituted. -/
theorem frameCrest_read (m : EnvModel V env) {φ : Name → Nat} {ctx : NestCtx}
    {holes : List Expr} {us : List Level} {sub : Name → List Level → Option Expr}
    {ds : List Expr} {D' : Nat} {s : Nat → Expr} {x : Nat → AnnotTerm}
    (hholes : ∀ mm, mm < ctx.names.length → ∃ ty, holes[mm]? = some (.fvar (ctx.nP + mm) ty))
    (hnd : ctx.lps.Nodup) (hul : us.length = ctx.lps.length)
    (hnP : ctx.params.length = ctx.nP)
    (hmem : ∀ mm, mm < ctx.names.length →
      s (ctx.nP + mm) = ((sub (ctx.names.getD mm .anonymous) us).getD
        (.const (ctx.names.getD mm .anonymous) us)))
    (hout : ∀ n vs, ctx.names.contains n = false → sub n vs = none)
    (hpar : ∀ i, i < ctx.nP → s i = ds.getD i default)
    (hpv : ∀ i, i < ctx.nP → ∃ ty, ctx.params[i]? = some (.fvar i ty))
    (hdlen : ds.length = ctx.nP)
    (hs : ∀ i, i < ctx.nP + ctx.names.length → Expr.WScoped D' (s i) ∧
      (s i).looseBVarsBounded 0 = true ∧ denoteMeta m.acval env φ D' (s i) = some (x i))
    {e A : Expr} (he : e.hasFvar = false) (hAw : Expr.WScoped (ctx.nP + ctx.names.length) A)
    (hocc : (nestAbstract ctx holes e).nestOcc ctx.names 0 0 = false)
    (hA : instPisWith ctx.params (nestAbstract ctx holes e) = some A)
    {ab : List (Nat × Nat × AnnotTerm)} {res : AnnotTerm}
    (hread : denoteMeta m.acval env (Level.substFn φ ctx.lps us) (ctx.nP + ctx.names.length) A
      = some (mkPisAV ab res)) :
    ∃ crest, instPisWith ds ((e.instantiateLevelParams ctx.lps us).replaceConsts sub) = some crest ∧
      denoteMeta m.acval env φ D' crest
        = some (mkPisAV (AnnotTerm.substTele (substTau (ctx.nP + ctx.names.length) D' x) 0 ab)
            (AnnotTerm.substAV (substTau (ctx.nP + ctx.names.length) D' x) res ab.length)) := by
  refine ⟨_, Expr.frameCrest_eq (b := ctx.nP + ctx.names.length) (D := D') hholes
    (map_param_subst hnd hul) (Nat.le_refl _) hmem hout
    (fun i hi => hpar i (by omega)) (fun i hi => hpv i (by omega)) (by omega) (by omega)
    (fun i hi => (hs i hi).2.1) he hocc hA, ?_⟩
  -- `A` is scoped at `nP + k`: the parameters and holes are its only variables
  have hAf : Expr.fvarsBelow (ctx.nP + ctx.names.length + 0) (A.instantiateLevelParams ctx.lps us) := by
    rw [Nat.add_zero]
    exact fvarsBelow_instantiateLevelParams _ _ hAw.fvarsBelow
  have h := denoteMeta_substFvars (φ := φ) m (b := ctx.nP + ctx.names.length) (D := D') (s := s)
    (x := x) hs (A.instantiateLevelParams ctx.lps us) 0 hAf
  rw [Nat.add_zero, Nat.add_zero, denotePInstLevels m φ ctx.lps us, hread] at h
  rw [h, Option.map_some, AnnotTerm.substAV_mkPisAV, Nat.zero_add]

/-- **The valuation the substituted reading is read at**: the member
slots (last member innermost) over the parameter frame, the rest of the
frame's valuation above them. -/
theorem substE_substTau {nP k D' : Nat} (x : Nat → AnnotTerm) (σ : Nat → V) :
    substE V (substTau (nP + k) D' x) 0 σ
      = consList ((List.range k).map fun mm => interp V σ (x (nP + mm)))
          (fun q => if q < nP then interp V σ (x (nP - 1 - q)) else σ (q - nP + D')) := by
  funext i
  have hlen : ((List.range k).map fun mm => interp V σ (x (nP + mm))).length = k := by simp
  simp only [substE, Nat.not_lt_zero, if_false, shiftE_zero_zero, Nat.sub_zero, substTau]
  rcases Nat.lt_or_ge i k with hik | hik
  · rw [consList_getD_of_lt _ _ _ (by rw [hlen]; exact hik), if_pos (by omega), hlen,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some, show nP + k - 1 - i = nP + (k - 1 - i) by omega]
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + k := ⟨i - k, by omega⟩
    rw [show q + k = q + ((List.range k).map fun mm => interp V σ (x (nP + mm))).length by
      rw [hlen], consList_apply_add, hlen]
    by_cases hq : q < nP
    · rw [if_pos (by omega), if_pos hq, show nP + k - 1 - (q + k) = nP - 1 - q by omega]
    · rw [if_neg (by omega), if_neg hq, interp_bvar,
        show q + k - (nP + k) + D' = q - nP + D' by omega]

end ConLeche.Model
