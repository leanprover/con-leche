module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Inductives.HoleKit
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.CtxOkP
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Semantics.Frame
import ConLeche.Verify.InferLemmas

public section

/-!
# The hole relation of the positivity derivation

The HOLE RELATION (`HoleRel`: related frames satisfy the context, agree
off the holes, and every member and frame hole grows) the positivity
theorem is proved along; the generic vocabulary under it (`holeP`,
hole-free readings, spines, `PiPosThen`/`ResultAt`/`ResultIdxConst`)
is `HoleKit.lean`.  The theorem itself — every judgment of the
positivity DERIVATION reads monotonically — is proved by induction on
the derivation (`PosDerivMono.lean`); the run is inverted once
(`Verify/Inductives/PosDerivInv.lean`).

The holes are the free variables `nP ..< hiAt |prog|`: the members, then
one per frame (`nestPos`'s own layout).  A hole at variable `i` reads,
at depth `d`, as the bound position `d - 1 - i` (`holeP`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **The hole relation** at depth `d` under the frames `prog`: related
frames satisfy the context, agree off the hole positions, the member
holes grow (at their full arity), and every frame's hole grows at its
instantiation's own parameters (`HoleOnArgs`: the key's parameter terms,
read at the depth, then the indices, at the member's FULL arity — the
kernel's `frameHole` rule checks `nestArity`: a frame hole holding a tuple BELOW its container's carrier grows only at
full arity, a partial application being a graph). -/
structure HoleRel (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  member : ∀ t, t < ctx.names.length →
    HoleOn R (d - 1 - (ctx.nP + t)) (ctx.nP + ctx.nIdxs.getD t 0)
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ dsa,
    DenoteMetaSpine m.acval env φ d hk.key.ds dsa → ∀ ni,
    ni + hk.key.ds.length = ConLeche.nestArity ctx hk.key.cname →
    HoleOnArgs R (d - 1 - (ctx.hiAt 0 + i)) dsa ni
  /-- the frames' parameter terms are scoped below the frames' holes (the
  kernel checks `fvarB ≤ hiAt` at each frame's entry) -/
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

/-- **Under a positive binder** (a hole-free domain, or an earlier field)
the relation is the same one level deeper. -/
theorem HoleRel.under {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRel m φ ctx prog d Δa R) (hd : ctx.hiAt prog.length ≤ d)
    {ta : AnnotTerm} (hA : MonoOn R ta) :
    HoleRel m φ ctx prog (d + 1) (ta :: Δa) (R.under ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 (hA ρ ρ' hR x hx)⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.under ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  member := by
    intro t ht
    have hlt : ctx.nP + t < d := by
      simp only [NestCtx.hiAt] at hd; omega
    rw [show d + 1 - 1 - (ctx.nP + t) = d - 1 - (ctx.nP + t) + 1 by omega]
    exact (h.member t ht).under ta
  frame := by
    intro i key hk dsa' hsp ni har
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < d := by
      simp only [NestCtx.hiAt] at hd ⊢; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped i key hk x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + i) = d - 1 - (ctx.hiAt 0 + i) + 1 by omega]
    exact (h.frame i key hk dsa hdsa ni har).under ta
  dsScoped := h.dsScoped

end ConLeche.Model
