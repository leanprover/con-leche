module

public import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Verify.ProjSlots

public section

/-!
# The recursor stage, assembled at the run (task #315, M5, model half)

`blockRecStaged_of` (`Model/Inductives/BlockStageRec.lean`) is the
recursor stage's cons, stated at eighteen premises; `declBlock`
(`Model/Inductives/DeclBlock.lean`) consumes it through the named
`BlockRecStaged`.  This module is the seam between them: it discharges
from the CHECK'S OWN RUN every premise that is a syntactic fact about
the stored recursors, so that what is left of the Model half is the
two SEMANTIC seams — the family premise (`BlockRecPre`, lane RM3's
regimes) and the rule data (`BlockRuleDataAt`, lane RM6's `hnew`).

What the run supplies, and where it comes from:

| premise | source |
|---|---|
| `hty`, `hrhs` | `checkBlockRecK_facts` (lane V2) |
| `hresRec` | `checkBlockRecK_reserved` (lane K2) |
| `hfr`, `hnres`, `hpsh` | `checkConstantVal_inv` at the per-recursor run `checkBlockRecK_tyShape` names |
| `hnoTy` | `annotateCore_noProjAt` at the SAME run |
| `hrd` | `hrd_of_pre` (lane RM4), at the family premise |
| `hrecP` | `hrecP_of` (lane RM6), at the rule data |

and the generated guarded call's freedom from free variables
(`hnofv`, which `ihNodeVal_blockRec` asks for) is here too, beside the
other facts about the generated forms.
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape BlockParts
  consBlockRecs)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The generated guarded call carries no free variable

`ihNodeVal_blockRec` (`Model/Inductives/BlockRecRule.lean`, lane RM3)
asks for `hnofv`: the Π-tower `blockIhSpinePis` builds has
`hasFvar = false`.  It is a one-level computation — the tower's binder
domains are `structIdxAt`-lifts of the constructor's own field
telescope, the spine is the rule's prefix `bvar`s, the field's index
expressions (again `structIdxAt`-lifted) and one applied `bvar`, and
the head is a `.const` — so it needs nothing of the constructor beyond
its type's own freedom from free variables. -/

/-- `Expr.mkPisOf` keeps `hasFvar = false` when every binder domain and
the body do. -/
theorem hasFvar_mkPisOf : ∀ {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr},
    (∀ b ∈ bs, b.1.hasFvar = false) → body.hasFvar = false →
    (Expr.mkPisOf bs body).hasFvar = false
  | [], _, _, hb => hb
  | (ty, mt) :: bs, body, hbs, hb => by
    simp only [Expr.mkPisOf, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨hbs (ty, mt) List.mem_cons_self,
      hasFvar_mkPisOf (fun b hbm => hbs b (List.mem_cons_of_mem _ hbm)) hb⟩

/-- `structIdxAt` is two `liftLooseBVars`, and neither introduces a
free variable. -/
theorem hasFvar_structIdxAt {nF o i l m : Nat} {e : Expr} (he : e.hasFvar = false) :
    (ConLeche.structIdxAt nF o i l m e).hasFvar = false := by
  simp only [ConLeche.structIdxAt, hasFvar_liftLooseBVars, he]

/-- The moved telescope's domains carry no free variable when the
original's do. -/
theorem hasFvar_structTeleAt {nF o i l : Nat} {pw : ConLeche.PropWhen}
    {tele : List (Expr × ConLeche.BinderMeta)} (ht : ∀ b ∈ tele, b.1.hasFvar = false) :
    ∀ b ∈ ConLeche.structTeleAt nF o i l pw tele, b.1.hasFvar = false := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
  refine hasFvar_structIdxAt ?_
  exact ht _ (getD_mem _ (by simpa using List.mem_range.mp hk))

/-- The prefix and telescope variables are `bvar`s. -/
theorem hasFvar_bvars {L : List Nat} : ∀ e ∈ L.map (Expr.bvar ·), e.hasFvar = false := by
  intro e he
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp he
  rfl

/-- **`hnofv`**: the generated guarded call's Π-tower has no free
variable. -/
theorem hasFvar_blockIhSpinePis {nm : Name} {rlvls : List Level} {pw : ConLeche.PropWhen}
    {nP rP nF i d : Nat} {tele : List (Expr × ConLeche.BinderMeta)} {idx : List Expr}
    (ht : ∀ b ∈ tele, b.1.hasFvar = false) (hidx : ∀ e ∈ idx, e.hasFvar = false) :
    (ConLeche.blockIhSpinePis nm rlvls pw nP rP nF i d tele idx).hasFvar = false := by
  refine hasFvar_mkPisOf (hasFvar_structTeleAt ht) (hasFvar_mkAppN rfl ?_)
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      rfl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact hasFvar_structIdxAt (hidx e he)
  · obtain rfl := List.mem_singleton.mp ha
    refine hasFvar_mkAppN rfl (fun x hx => ?_)
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    rfl

/-- The constructor type's field telescope and index expressions carry
no free variable — at EVERY field index, the out-of-range ones being
empty. -/
theorem structFieldParts_hasFvar {cty : Expr} {nP nF i : Nat}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) :
    (∀ b ∈ ConLeche.structFieldTeleOf cty nP nF i, b.1.hasFvar = false) ∧
      ∀ e ∈ ConLeche.structFieldIdxOf cty nP nF i, e.hasFvar = false := by
  by_cases hi : i < nF
  · obtain ⟨htl, hix⟩ := structFieldTele_props (nP := nP) hCf hCb hstripC hi
    exact ⟨fun b hb => by
        obtain ⟨k, hk⟩ := List.getElem?_of_mem hb
        exact (htl k b hk).1,
      fun e he => (hix e he).1⟩
  · obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
    have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
    have hdef : cbs.getD (nP + i) default = default :=
      getD_of_le _ (by omega)
    have htl : ConLeche.structFieldTeleOf cty nP nF i = [] := by
      simp only [ConLeche.structFieldTeleOf, hs, hdef]
      rfl
    have hix : ConLeche.structFieldIdxOf cty nP nF i = [] := by
      simp only [ConLeche.structFieldIdxOf, hs, hdef]
      show List.drop nP (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = []
      rw [show (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = [] from rfl,
        List.drop_nil]
    rw [htl, hix]
    exact ⟨fun b hb => absurd hb List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩

end ConLeche.Model
