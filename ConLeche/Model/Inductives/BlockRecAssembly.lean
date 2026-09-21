module

public import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockRecInv

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

/-! ## 2. The stored recursors' NAMES

The `k` recursors are checked at ONE environment — the constructors' —
so `checkConstantVal`'s freshness says each is fresh THERE and says
nothing about the `k` names being pairwise distinct.  That is the
NAME-SET check's (`blockRecNameSetOk`, lane K2): the stored names are,
as a set, exactly `{T.rec : T a member}`, and there are as many of them
as there are members.  With the members' own names distinct, a
pigeonhole closes it. -/

/-- **The pigeonhole**: a list as long as a `Nodup` list it covers is
itself `Nodup`. -/
theorem nodup_of_subset_length {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {L M : List α}, M.Nodup → M ⊆ L → L.length ≤ M.length → L.Nodup
  | [], _, _, _, _ => List.nodup_nil
  | a :: L', M, hM, hML, hlen => by
    have hdup : a ∉ L' := by
      intro ha
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact ha
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega
    refine List.nodup_cons.mpr ⟨hdup, ?_⟩
    by_cases hmem : a ∈ M
    · refine nodup_of_subset_length (M := M.erase a) (List.Nodup.erase a hM) ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp (hML (List.mem_of_mem_erase hx)) with rfl | h
        · exact absurd hx (List.Nodup.not_mem_erase hM)
        · exact h
      · rw [List.length_erase_of_mem hmem]
        simp only [List.length_cons] at hlen
        omega
    · exfalso
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact absurd hx hmem
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega

/-- The members' recursor names are distinct because the members' are. -/
theorem nodup_recNames_of_members {ms : List ConLeche.MemberShape}
    (h : (ms.map (·.cvT.name)).Nodup) : (ms.map (fun m => m.cvT.name.str "rec")).Nodup := by
  have : (ms.map (fun m => m.cvT.name.str "rec"))
      = (ms.map (·.cvT.name)).map (fun n => n.str "rec") := by
    rw [List.map_map]; rfl
  rw [this]
  refine List.Pairwise.map _ (fun x y hxy hh => ?_) h
  exact hxy (by injection hh)

/-! ## 3. The stage, inverted at the NAMES and the per-recursor run -/

/-- **The recursor stage's per-index facts**: the name-set check ran,
there is one stored recursor per RECORD, and each stored recursor is
that record's constant, CHECKED at the constructors' environment. -/
theorem checkBlockRecK_recNames {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ConLeche.checkBlockRecPins (m := ConLeche.CheckM) p = .ok () ∧
    rs.length = p.recs.length ∧
    ∀ i, i < p.recs.length → ∃ rc r, p.recs[i]? = some rc ∧ rs[i]? = some r ∧
      r.1.name = rc.cvR.name ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) envC rc.cvR = .ok r.1 := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkBlockRecsRules_facts h
  refine ⟨by cases u; exact hpins, hlenR, ?_⟩
  intro i hil
  obtain ⟨rc, r, hrc, hr, hcvRa, -⟩ := hallR i hil
  obtain ⟨rc'', cvRi, nIdx, u', hrc'', hcu, hcv⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have hq := hcvRa
    rw [Nat.zero_add] at hq
    exact congrArg Prod.fst (Option.some.inj (hq.symm.trans hcvRa'))
  exact ⟨rc, r, hrc, hr, by rw [hr1, (ConLeche.checkConstantVal_lps hcv).1],
    by rw [hr1]; exact hcv⟩

/-- **`blockRecStaged_of`'s three NAME premises and `hnoTy`**, from the
per-recursor `checkConstantVal` run: freshness at the constructors'
environment, the two name guards, and — because the stored type is the
ANNOTATED one — every `.proj` node of it sits at a stored table slot,
so an EMPTY slot is not mentioned. -/
theorem checkBlockRecK_cvFacts {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs,
      envC.find? r.1.name = none ∧
      ConLeche.reservedBasisNames.contains r.1.name = false ∧
      r.1.name.isProjFnShape = false ∧
      ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i r.1.type := by
  obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hname, hcv⟩ := hall i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨hfresh, hres, hpsh, -, -, hfv, type, -, -, hann, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have htype : r.1.type = type := by rw [hcv']
  refine ⟨by rw [hname]; exact hfresh, by rw [hname]; exact hres,
    by rw [hname]; exact hpsh, fun T i hslot => ?_⟩
  rw [htype]
  exact ConLeche.annotateCore_noProjAt μ hann hfv hslot

/-- **`blockRecStaged_of`'s `hnd`**: the `k` stored recursor names are
pairwise distinct.  The per-recursor `checkConstantVal` runs all take
place at ONE environment and say nothing about it; what does is the
NAME-SET check — the stored names are exactly the members' `T.rec`,
and there are as many of them as there are members. -/
theorem checkBlockRecK_nodup {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hndM : p.toBlockShape.memberNames.Nodup) : (rs.map (·.1.name)).Nodup := by
  obtain ⟨hpins, hlenR, hall⟩ := checkBlockRecK_recNames h
  obtain ⟨hlenRM, hgot, hwant⟩ := ConLeche.checkBlockRecPins_names hpins
  -- the stored names ARE the records' names, positionally
  have hmap : rs.map (·.1.name) = p.recs.map (·.cvR.name) := by
    refine List.ext_getElem? (fun i => ?_)
    by_cases hi : i < p.recs.length
    · obtain ⟨rc, r, hrc, hr, hname, -⟩ := hall i hi
      simp only [List.getElem?_map, hrc, hr, Option.map_some]
      rw [hname]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, hlenR]; omega),
        List.getElem?_eq_none (by simp only [List.length_map]; omega)]
  rw [hmap]
  refine nodup_of_subset_length
    (M := p.toBlockShape.members.map (fun m => m.cvT.name.str "rec"))
    (nodup_recNames_of_members hndM) (fun y hy => ?_) ?_
  · obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hy
    obtain ⟨rc, hrc, hn⟩ := hwant ms hms
    exact hn ▸ List.mem_map_of_mem hrc
  · simp only [List.length_map, hlenR, hlenRM]
    exact Nat.le_refl _

end ConLeche.Model
