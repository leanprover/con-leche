module

public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Kernel.Inductives.PositivityK
public import ConLeche.Verify.Inductives.UseSynK
import ConLeche.Model.Inductives.ContFrame

public section

/-!
# The hole relation at a key-named layout (PRIMREC / NESTKN-M2)

`HoleRelK` is `HoleRel` (`NestPosMono.lean`) at a LAYOUT of the key-named
positivity check (`Kernel/Inductives/PositivityK.lean`, variant E) instead of
a stack of path frames.  A layout `L` has, above the members, its FLEXIBLE
families `hiAt0 ..< hiAt0 + L.nF` (each a family over its indices) and then
its own group's holes `hiAt0 + L.nF ..< L.hi` (today's frame holes, applied
to the layout's `DsF`).  Along a relation:

* the member holes grow at their full arity (as today);
* a flexible family grows at its index count — only where the node MET it
  (`met`): an unmet family is unconstrained (PROOFPLAN R1: its binding at a
  use site need not be positive, and the node never reads it positively);
* an own hole grows at `DsF` (`HoleOnArgs`, today's frame clause).

`layoutBaseK` is the node's base: its families only, at depth
`hiAt0 + L.nF` — the frame the node's own group is iterated over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole LayoutK)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **A layout's base**: its flexible families only — the frame depth
`hiAt0 + L.nF` the node's own group is iterated over. -/
@[expose] def layoutBaseK (ctx : NestCtx) (L : LayoutK) : LayoutK :=
  { L with grp := [], hi := ctx.hiAt 0 + L.nF }

@[simp] theorem layoutBaseK_nF (ctx : NestCtx) (L : LayoutK) : (layoutBaseK ctx L).nF = L.nF := rfl
@[simp] theorem layoutBaseK_fams (ctx : NestCtx) (L : LayoutK) :
    (layoutBaseK ctx L).fams = L.fams := rfl
@[simp] theorem layoutBaseK_grp (ctx : NestCtx) (L : LayoutK) : (layoutBaseK ctx L).grp = [] := rfl
@[simp] theorem layoutBaseK_dsF (ctx : NestCtx) (L : LayoutK) :
    (layoutBaseK ctx L).dsF = L.dsF := rfl
@[simp] theorem layoutBaseK_hi (ctx : NestCtx) (L : LayoutK) :
    (layoutBaseK ctx L).hi = ctx.hiAt 0 + L.nF := rfl

/-- **The hole relation at a layout** (see the module docstring): at depth
`d`, related frames satisfy the context, agree off the holes
`nP ..< L.hi`, the members grow at full arity, every MET flexible family
at its index count, every own hole at the layout's `DsF`. -/
structure HoleRelK (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (L : LayoutK)
    (met : List Nat) (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  /-- the layout's shape: families, then the own group -/
  hiEq : L.hi = ctx.hiAt 0 + L.nF + L.grp.length
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP L.hi)
  member : ∀ t, t < ctx.names.length →
    HoleOn R (d - 1 - (ctx.nP + t)) (ctx.nP + ctx.nIdxs.getD t 0)
  fam : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < L.nF → L.fams[j]? = some (key, nI) →
    j ∈ met → HoleOn R (d - 1 - (ctx.hiAt 0 + j)) nI
  own : ∀ (g : Nat) (n : Name), L.grp[g]? = some n → ∀ dsa,
    DenoteMetaSpine m.acval env φ d L.dsF dsa → ∀ ni,
    ni + L.dsF.length = ConLeche.nestArity ctx n →
    HoleOnArgs R (d - 1 - (ctx.hiAt 0 + L.nF + g)) dsa ni
  /-- the layout's parameters are scoped below its holes -/
  dsScoped : ∀ x ∈ L.dsF, Expr.WScoped L.hi x

/-- **Under a positive binder** the relation is the same one level deeper. -/
theorem HoleRelK.under {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (h : HoleRelK m φ ctx L met d Δa R) (hd : L.hi ≤ d)
    {ta : AnnotTerm} (hA : MonoOn R ta) :
    HoleRelK m φ ctx L met (d + 1) (ta :: Δa) (R.under ta) where
  hiEq := h.hiEq
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
      have := h.hiEq
      simp only [NestCtx.hiAt] at this; omega
    rw [show d + 1 - 1 - (ctx.nP + t) = d - 1 - (ctx.nP + t) + 1 by omega]
    exact (h.member t ht).under ta
  fam := by
    intro j key nI hj hk hmet
    have hlt : ctx.hiAt 0 + j < d := by have := h.hiEq; omega
    rw [show d + 1 - 1 - (ctx.hiAt 0 + j) = d - 1 - (ctx.hiAt 0 + j) + 1 by omega]
    exact (h.fam j key nI hj hk hmet).under ta
  own := by
    intro g n hg dsa' hsp ni har
    have hglt : g < L.grp.length := (List.getElem?_eq_some_iff.mp hg).1
    have hlt : ctx.hiAt 0 + L.nF + g < d := by have := h.hiEq; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + L.nF + g) = d - 1 - (ctx.hiAt 0 + L.nF + g) + 1 by omega]
    exact (h.own g n hg dsa hdsa ni har).under ta
  dsScoped := h.dsScoped

/-- **The root layout's hole relation is the frameless one** (a member
constructor's walk). -/
theorem holeRelK_root {ctx : NestCtx} {met : List Nat} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRel m φ ctx [] d Δa R) :
    HoleRelK m φ ctx (ConLeche.rootLayoutK ctx) met d Δa R where
  hiEq := by simp [ConLeche.rootLayoutK]
  dom := h.dom
  agree := by simpa [ConLeche.rootLayoutK] using h.agree
  member := h.member
  fam := by intro j _ _ hj; simp [ConLeche.rootLayoutK] at hj
  own := by intro g n hg; simp [ConLeche.rootLayoutK] at hg
  dsScoped := by intro x hx; simp [ConLeche.rootLayoutK] at hx

/-! ## The layout's own material at a site -/

/-- **A context discipline survives new top entries** (`CtxOkP.extend` with
every leaf old). -/
theorem CtxOkP.weaken {h g : Nat} {Δ Ts : List AnnotTerm} {e : Expr} (hC : CtxOkP m φ h Δ e)
    (hTs : Ts.length = g) : CtxOkP m φ (h + g) (Ts ++ Δ) e :=
  CtxOkP.extend hTs hC.1 fun l hl => Or.inl (hC.2 l hl)

/-- **What a use needs of its user's layout** (beside the hole relation):
the layout's own syntactic material is well formed at the site — its
flexible families' keys (concrete: scoped at the members, bvar-closed,
readable, leaves in the context), its parameters `DsF` (leaves in the
context), its families' types syntactically good (`LayGoodK`, PRIMREC /
NESTKN-M3B) and its families' variables in the context (a binding may be a
family of the user, K2's inner bindings). -/
structure LaySiteK (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (L : LayoutK) (d : Nat)
    (Δa : List AnnotTerm) : Prop where
  keys : ∀ p ∈ L.fams, ∀ x ∈ p.1.ds, Expr.WScoped (ctx.hiAt 0) x ∧
    x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x ∧
    ∃ xa, denoteMeta m.acval env φ (ctx.hiAt 0) x = some xa
  dsF : ∀ x ∈ L.dsF, CtxOkP m φ d Δa x
  syn : ConLeche.LayGoodK ctx L
  famC : ∀ x (hx : x < L.famTys.length), CtxOkP m φ d Δa (.fvar (ctx.hiAt 0 + x) L.famTys[x])

theorem LaySiteK.weaken {ctx : NestCtx} {L : LayoutK} {d : Nat} {Δa Ts : List AnnotTerm}
    (h : LaySiteK m φ ctx L d Δa) {g : Nat} (hTs : Ts.length = g) :
    LaySiteK m φ ctx L (d + g) (Ts ++ Δa) where
  keys p hp x hx := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.keys p hp x hx
    exact ⟨h1, h2, h3, h4.weaken hTs, h5⟩
  dsF x hx := (h.dsF x hx).weaken hTs
  syn := h.syn
  famC x hx := (h.famC x hx).weaken hTs

theorem LaySiteK.under {ctx : NestCtx} {L : LayoutK} {d : Nat} {Δa : List AnnotTerm}
    (h : LaySiteK m φ ctx L d Δa) (ta : AnnotTerm) : LaySiteK m φ ctx L (d + 1) (ta :: Δa) :=
  h.weaken (Ts := [ta]) rfl

/-- The root layout has no material. -/
theorem laySiteK_root {ctx : NestCtx} {d : Nat} {Δa : List AnnotTerm} :
    LaySiteK m φ ctx (ConLeche.rootLayoutK ctx) d Δa where
  keys p hp := by simp [ConLeche.rootLayoutK] at hp
  dsF x hx := by simp [ConLeche.rootLayoutK] at hx
  syn := ⟨rfl, rfl, fun j hj => by simp [ConLeche.rootLayoutK] at hj,
    fun p hp => by simp [ConLeche.rootLayoutK] at hp⟩
  famC x hx := by simp [ConLeche.rootLayoutK] at hx

/-- A layout's base has its material. -/
theorem LaySiteK.base {ctx : NestCtx} {L : LayoutK} {d : Nat} {Δa : List AnnotTerm}
    (h : LaySiteK m φ ctx (layoutBaseK ctx L) d Δa) : LaySiteK m φ ctx L d Δa where
  keys := h.keys
  dsF := h.dsF
  syn := h.syn
  famC := h.famC

end ConLeche.Model
