import Setlec.SetR.Install.IndStagesS
import Setlec.Verify.InstSpine

/-!
# The nested fire's pin bridge (task #148, T5 c3)

The one place where a `.nested` rule differs from a `.plain` one, once
the bottom stages are parameter-spine-generic (`IndStagesS.lean`): the
constructor's parameter slots hold the stored **pins**, instantiated
at the statement frame's prefix openers, rather than the openers
themselves.

`pinCrossS` is the bridge.  The checker's comparand is
`instSpine (fvs.take rP) (rP - 1) (pin.renameConsts f)`; the rule's
value-quantified premise speaks of `instRevChain (xs.take rP) vp` with
`vp = ⟦openRev 0 rP pin⟧` at depth `rP` — the §8.1-corrected shape,
quantified over the pin's **value**, never over an expression.  The
identity is `denote_openRev` (the real-argument instantiation read
through the reverse opening) composed with `denote_openRev_base` (the
opened denotation is base-independent) and `nestedChain` (the reverse
chain rides the fired spine).  It is an identity of `VExpr`s, so no
interpretation-level agreement lemma is needed.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The nested pin bridge**: a stored pin, instantiated at the
statement frame's prefix openers and denoted at the frame depth,
instantiates along the fired statement spine to the pin's own
canonical denotation applied in reverse along the fired prefix. -/
theorem pinCrossS {cval : TConstVal} {env : Env} {ψ' : Name → Nat}
    (hcl : ∀ n ψ'', VExpr.Closed (cval n ψ''))
    {f : Name → Name} (hro : RenameOkT cval env f)
    {rP cnF : Nat} {fvs : List Expr}
    (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hbFvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true)
    {p : Expr} (hpw : p.hasFvar = false)
    (hpb : p.looseBVarsBounded rP = true)
    {vp : VExpr}
    (hvpden : denote cval env ψ' rP (openRev 0 rP p) = some vp)
    {xs zs : List VExpr}
    (hxtlen : (xs.take rP).length = rP)
    (hzslen : zs.length = rP + cnF)
    (hzspre : zs.take rP = xs.take rP) :
    ∃ w0, denote cval env ψ' (rP + cnF)
        (Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f))
        = some w0 ∧
      VExpr.instSeq zs (rP + cnF - 1) w0
        = VExpr.instRevChain (xs.take rP) vp := by
  have htklen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvslen]
    omega
  -- the frame's prefix openers denote to the canonical bvar spine
  have hbvslen : ((List.range rP).map
      (fun j => VExpr.bvar (rP + cnF - 1 - j))).length = rP := by
    rw [List.length_map, List.length_range]
  have hsp : DenoteSpine cval env ψ' (rP + cnF) (fvs.take rP)
      ((List.range rP).map (fun j => VExpr.bvar (rP + cnF - 1 - j))) := by
    refine DenoteSpine.of_getElem (by rw [htklen, hbvslen]) ?_
    intro q hq
    rw [htklen] at hq
    rcases hx : fvs[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx
      omega
    obtain ⟨nm, ty, rfl⟩ := hshapeS q x hx
    have h1 : (fvs.take rP).getD q default = Expr.fvar q nm ty := by
      rw [List.getD, List.getElem?_take_of_lt hq, hx]
      rfl
    have h2 : ((List.range rP).map
        (fun j => VExpr.bvar (rP + cnF - 1 - j))).getD q default
        = VExpr.bvar (rP + cnF - 1 - q) := by
      rw [List.getD, List.getElem?_map, List.getElem?_range hq]
      rfl
    rw [h1, h2]
    exact denote_fvar cval env ψ' (rP + cnF) q nm ty
  -- the renamed pin's frame facts
  have hpwR : (p.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hpw
  have hpbR : (p.renameConsts f).looseBVarsBounded rP = true := by
    rw [looseBVarsBounded_renameConsts]
    exact hpb
  -- the instantiation, read through the reverse opening
  have hkey := denote_openRev (cval := cval) (env := env) (φ := ψ')
    hcl (fvs.take rP) (e := p.renameConsts f) (d := rP + cnF)
    (fun a ha => by
      refine ⟨hwsFvs a (List.mem_of_mem_take ha),
        hbFvs a (List.mem_of_mem_take ha), ?_⟩
      exact (hwsFvs a (List.mem_of_mem_take ha)).fvarsBelow)
    (Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpwR] at hl
      exact nomatch hl))
    (by rw [htklen]; exact hpbR) hsp
  rw [htklen] at hkey
  -- the opened denotation is base-independent, and renaming-invariant
  have hbase := denote_openRev_base (cval := cval) (env := env)
    (φ := ψ') hcl hpwR hpbR (rP + cnF)
  have hren : openRev 0 rP (p.renameConsts f)
      = (openRev 0 rP p).renameConsts f := openRev_renameConsts f 0 rP p
  have hvpR : denote cval env ψ' rP (openRev 0 rP (p.renameConsts f))
      = some vp := by
    rw [hren, denote_renameConsts hro]
    exact hvpden
  rw [hbase, hvpR] at hkey
  refine ⟨_, by rw [Expr.instSpine_eq_instSeq]; exact hkey, ?_⟩
  -- the chain rides the fired spine
  have hbv : VExpr.bvarsBelow rP vp := by
    refine denote_bvarsBelow hcl rP (openRev 0 rP p) ?_ ?_ hvpden
    · have h := openRev_WScoped (d := 0)
        (Expr.WScoped.of_not_hasFvar hpw) rP
      rwa [Nat.zero_add] at h
    · exact openRev_bounded rP 0 (by simpa using hpb)
  have hchain := nestedChain (rP := rP) (cnF := cnF) (xs := xs) hxtlen
    zs (rP + cnF) vp hzslen (Nat.le_refl _) (by omega) hzspre hbv
  rw [show rP + cnF - (rP + cnF) = 0 from by omega,
    List.replicate_zero, List.append_nil] at hchain
  exact hchain

end Setlec.SetR
