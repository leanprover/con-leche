module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift
public import ConLeche.Verify.Inductives.ScopeKit
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves

public section

/-!
# The positivity walk's scoping

What the cached simulation (`Verify/Cached/NestPosC.lean`) and the
model's consumer (`Model/Inductives/BlockPosRun.lean`) need of the walk
beyond the generic scoping kit (`ScopeKit.lean`): a context whose stored
constants are closed (`NestCtxOk`) makes the member holes well-scoped
variables, and a seed's key is well scoped at the walk's depth.
-/

namespace ConLeche

open Expr

/-- A context whose stored constants are closed. -/
@[expose] def NestCtxOk (ctx : NestCtx) : Prop :=
  (∀ ci ∈ ctx.consts, ci.toConstantVal.type.hasFvar = false) ∧
  (∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.hasFvar = false)

/-- The member holes are variables, well scoped above them. -/
theorem nestHoles_ok {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
  intro x hx
  obtain ⟨mm, hmm, hf⟩ := option_mapM_mem h x hx
  have hmm' := List.mem_range.mp hmm
  split at hf
  · next cv caps hfind =>
    simp only [Option.some.injEq] at hf
    subst hf
    refine ⟨?_, _, _, rfl⟩
    simp only [WScoped, NestCtx.hiAt]
    exact ⟨by omega, WScoped.of_not_hasFvar (hc.2 _ _ hfind)⟩
  · exact nomatch hf

/-! ## The seeds: their keys

A seed (`nestSeedKey?`) is read off a closed recursor type in the walk's
representation: its parameters are arguments of a binder domain of the
member-abstracted type instantiated at the canonical parameters, so their
leaves are the canonical variables' and the holes', and they are well
scoped at the walk's depth. -/

/-- A binder domain of a stripped `Π`-telescope: its leaves are the
term's, and it is well scoped where the term is. -/
theorem stripPis_dom {d : Nat} :
    ∀ (n : Nat) (e : Expr) (bs : List (Expr × BinderMeta)) (r : Expr),
      e.stripPis n = some (bs, r) → ∀ b ∈ bs,
        (∀ l ∈ b.1.fvarLeaves, l ∈ e.fvarLeaves) ∧ (WScoped d e → WScoped d b.1)
  | 0, e, bs, r, h, b, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact nomatch hb
  | n + 1, .forallE ty body m, bs, r, h, b, hb => by
    simp only [Expr.stripPis] at h
    obtain ⟨⟨bs', r'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨fun l hl => by simp only [fvarLeaves, List.mem_append]; exact Or.inl hl,
        fun hw => by simp only [WScoped] at hw; exact hw.1⟩
    · obtain ⟨h1, h2⟩ := stripPis_dom n body bs' _ h' b hb
      exact ⟨fun l hl => by simp only [fvarLeaves, List.mem_append]; exact Or.inr (h1 l hl),
        fun hw => by simp only [WScoped] at hw; exact h2 hw.2⟩
  | _ + 1, .bvar _, _, _, h, _, _ | _ + 1, .fvar .., _, _, h, _, _
  | _ + 1, .sort _, _, _, h, _, _ | _ + 1, .const .., _, _, h, _, _
  | _ + 1, .app .., _, _, h, _, _ | _ + 1, .lam .., _, _, h, _, _
  | _ + 1, .letE .., _, _, h, _, _ | _ + 1, .proj .., _, _, h, _, _
  | _ + 1, .lit _, _, _, h, _, _ => by simp [Expr.stripPis] at h

/-- **A seed's key** (`nestSeedKey?`): no member and not `Quot`, a stored
container at its parameter count, its parameters without loose bound
variables, their leaves the canonical variables' and the holes', and well
scoped at the walk's depth where the canonical variables and the holes
are. -/
theorem nestSeedKey?_spec {ctx : NestCtx} {holes : List Expr} {nB : Nat} {ty : Expr}
    {key : NestKey} {nPc : Nat} (h : nestSeedKey? ctx holes nB ty = some (key, nPc)) :
    ctx.names.contains key.cname = false ∧ key.cname ≠ quotName ∧
      (∃ L, nestContainer ctx key.cname = some (nPc, L)) ∧ key.ds.length = nPc ∧
      (∀ x ∈ key.ds, x.bvarB = 0 ∧ ∀ l ∈ x.fvarLeaves, ∃ a ∈ ctx.params ++ holes, l ∈ a.fvarLeaves) ∧
      ((∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) →
        (∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) → ∀ x ∈ key.ds, WScoped (ctx.hiAt 0) x) := by
  unfold nestSeedKey? at h
  split at h
  · exact nomatch h
  rename_i hty
  have hcl : ty.hasFvar = false := by simpa using hty
  split at h
  · exact nomatch h
  rename_i body hbody
  split at h
  · exact nomatch h
  rename_i bs r hstrip
  split at h
  · exact nomatch h
  rename_i mdom mm hlast
  have hmem : (mdom, mm) ∈ bs := List.mem_of_getLast? hlast
  obtain ⟨hleafD, hwD⟩ := stripPis_dom (d := ctx.hiAt 0) nB body bs r hstrip _ hmem
  split at h
  · rename_i I us hfn
    split at h
    · exact nomatch h
    rename_i hnq
    split at h
    · exact nomatch h
    rename_i nPc' L hC
    dsimp only at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hnq
      have hargs : ∀ x ∈ mdom.getAppArgs.take nPc', x ∈ mdom.getAppArgs :=
        fun x hx => List.mem_of_mem_take hx
      refine ⟨by simpa using hnq.1, hnq.2, ⟨L, hC⟩, hok.1, fun x hx => ⟨by simpa using hok.2 x hx,
        fun l hl => ?_⟩, fun hholes hpar x hx => ?_⟩
      · have hl' := hleafD l (fvarLeaves_getAppArgs (hargs x hx) l hl)
        rcases fvarLeaves_instPisWith hbody l hl' with hl'' | ⟨a, ha, hla⟩
        · obtain ⟨c, us', r', hr', hlr⟩ := fvarLeaves_replaceConsts_closed _ hcl l hl''
          refine ⟨r', List.mem_append_right _ ?_, hlr⟩
          split at hr'
          · split at hr'
            · exact List.mem_of_getElem? hr'
            · exact nomatch hr'
          · exact nomatch hr'
        · exact ⟨a, List.mem_append_left _ ha, hla⟩
      · exact Expr.WScoped.getAppArgs (hwD (memberCrest_wscoped hholes hpar hcl hbody)) x
          (hargs x hx)
    · exact nomatch h
  · exact nomatch h

end ConLeche
