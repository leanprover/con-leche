module

public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockRecLaw
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
open ConLeche.Term
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
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) envC rc.cvR = .ok r.1 ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt i ∧
      ∃ nIdx, p.toBlockShape.majorIdxAt i = p.toBlockShape.rulePrefixAt i + nIdx := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkBlockRecsRules_facts h
  refine ⟨by cases u; exact hpins, hlenR, ?_⟩
  intro i hil
  obtain ⟨rc, r, hrc, hr, hcvRa, -⟩ := hallR i hil
  obtain ⟨rc'', cvRi, nIdx, u', hrc'', hcu, hcv, hle, hsum⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have hq := hcvRa
    rw [Nat.zero_add] at hq
    exact congrArg Prod.fst (Option.some.inj (hq.symm.trans hcvRa'))
  refine ⟨rc, r, hrc, hr, by rw [hr1, (ConLeche.checkConstantVal_lps hcv).1],
    by rw [hr1]; exact hcv, ?_, ?_⟩
  · rw [Nat.zero_add] at hle; exact hle
  · rw [Nat.zero_add] at hsum
    exact ⟨nIdx, hsum⟩

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
  obtain ⟨rc, r', hrc, hr', hname, hcv, -, -⟩ := hall i hil
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
    · obtain ⟨rc, r, hrc, hr, hname, -, -, -⟩ := hall i hi
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
  · simp only [List.length_map, hlenRM]
    exact Nat.le_refl _

/-! ## 4. The stored RULES are annotated, and therefore mention no
empty slot

`hnoRhs` is `hnoTy`'s twin one stage down: a stored right-hand side is
`annotateCore`'s output at the BARE-`k` environment, whose `findProj?`
is the constructors' (`findProj?_consBlockRecsBare`).  The Verify
tier's inversions keep the scoping facts and drop the annotation run,
so the three peels are repeated here for that one witness. -/

section Annot

open ConLeche (checkBlockRule checkBlockRules checkBlockRecsRules annotateCore fueledOps
  RecShape BlockFieldKind exceptBind_ok)

local macro "close_throw " h:term : tactic =>
  `(tactic| first
      | exact nomatch $h
      | exact absurd $h (by
          simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          exact fun hh => nomatch hh)
      | exact absurd $h
          (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- **Stage (c), at ONE rule, inverted at the ANNOTATION**: the stored
right-hand side is `annotateCore`'s output at the rule environment,
and the stream's own is free-variable-free. -/
theorem checkBlockRule_annot {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind}
    {rhs out : Expr} {F : Nat}
    (h : checkBlockRule (fueledOps μ F) envR (fueledOps μ F) envT p recNames rlvls
      recTys mIs rPs recTgts ri cvR cA ks rhs = .ok out) :
    annotateCore μ envR F 0 rhs = .ok out ∧ rhs.hasFvar = false := by
  unfold checkBlockRule at h
  obtain ⟨recTy, _, h⟩ := exceptBind_ok h
  by_cases hbv : Expr.looseBVarsBounded 0 rhs = true
  case neg => rw [if_neg hbv] at h; close_throw h
  rw [if_pos hbv] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  obtain ⟨rhsA, hann, h⟩ := exceptBind_ok h
  by_cases hlp : Expr.allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : Expr.constsResolve envR rhsA = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  obtain ⟨x1, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x1
  obtain ⟨x2, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x2
  obtain ⟨x3, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x3
  obtain ⟨x4, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x4
  obtain ⟨x5, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x5
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨x9, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x9
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨b, _, h⟩ := exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  rw [if_pos hd] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨hann, Bool.not_eq_true _ |>.mp hfv⟩

/-- One recursor's rules, at the annotation. -/
theorem checkBlockRules_annot {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {F : Nat} :
    ∀ {cs : List ((ConstantVal × Nat) × List BlockFieldKind)} {rhss out : List Expr},
      checkBlockRules (fueledOps μ F) envR (fueledOps μ F) envT p recNames rlvls
        recTys mIs rPs recTgts ri cvR cs rhss = .ok out →
      ∀ rhsA ∈ out, ∃ rhs : Expr, annotateCore μ envR F 0 rhs = .ok rhsA ∧ rhs.hasFvar = false
  | [], [], out, h => by
    simp only [checkBlockRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro rhsA hrhsA
    simp at hrhsA
  | (cA, ks) :: cs, rhs0 :: rhss, out, h => by
    unfold checkBlockRules at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro rhsA hrhsA
    rcases List.mem_cons.mp hrhsA with rfl | hmem
    · exact ⟨rhs0, checkBlockRule_annot hr⟩
    · exact checkBlockRules_annot hrest rhsA hmem
  | [], _ :: _, out, h => by
    simp only [checkBlockRules] at h
    close_throw h
  | _ :: _, [], out, h => by
    simp only [checkBlockRules] at h
    close_throw h

/-- Stage (c) at every recursor, at the annotation. -/
theorem checkBlockRecsRules_annot {envR envT : Env} {p : BlockParts} {recNames : List Name}
    {rlvls : List Level} {cvRas : List (ConstantVal × Nat)}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat}
      {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))},
      checkBlockRecsRules (fueledOps μ F) envR (fueledOps μ F) envT p recNames rlvls
        cvRas ctorsAs recs ri = .ok rs →
      ∀ r ∈ rs, ∀ rhsA ∈ r.2.1,
        ∃ rhs : Expr, annotateCore μ envR F 0 rhs = .ok rhsA ∧ rhs.hasFvar = false
  | [], _, rs, h => by
    simp only [checkBlockRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro r hr
    simp at hr
  | rc :: rest, ri, rs, h => by
    unfold checkBlockRecsRules at h
    obtain ⟨ms, _, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, _, h⟩ := exceptBind_ok h
    obtain ⟨kss, _, h⟩ := exceptBind_ok h
    obtain ⟨cvRn, _, h⟩ := exceptBind_ok h
    obtain ⟨cvRa, nIdx⟩ := cvRn
    try simp only at h
    by_cases hlen : (ctorsA.length == ms.ctors.length) = true
    case neg => rw [if_neg hlen] at h; close_throw h
    rw [if_pos hlen] at h
    obtain ⟨rhss, hrules, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hmem
    · exact fun rhsA hrhsA => checkBlockRules_annot hrules rhsA hrhsA
    · exact checkBlockRecsRules_annot hrest r hmem

/-- **`blockRecStaged_of`'s `hnoRhs`**: a stored rule's right-hand side
mentions no EMPTY projection slot of the constructors' environment.
It is `annotateCore_noProjAt` at the environment the stage annotates
in — the BARE-`k` one, whose `findProj?` is `envC`'s, because no
recursor's name is projection-shaped. -/
theorem checkBlockRecK_rhsNoProj {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, ∀ rhsA ∈ r.2.1, ∀ (T : Name) (i : Nat),
      envC.findProj? T i = none → Expr.NoProjAt T i rhsA := by
  have hq := h
  unfold ConLeche.checkBlockRecK at hq
  obtain ⟨-, -, hq⟩ := ConLeche.exceptBind_ok hq
  obtain ⟨cvRus, htys, hq⟩ := ConLeche.exceptBind_ok hq
  obtain ⟨-, -, hq⟩ := ConLeche.exceptBind_ok hq
  obtain ⟨hlenT, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  -- no rule-less recursor's name is projection-shaped, so the bare
  -- environment's slots are the constructors' environment's
  have hpsh : ∀ x ∈ cvRus.map (fun q => (q.1, q.2.1)),
      x.1.name.isProjFnShape = false := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
    have hil : i < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
    obtain ⟨rc, cvRi, nIdx, u, -, hcu, hcv, -, -⟩ := hallT i hil
    obtain rfl := Option.some.inj (hi.symm.trans hcu)
    obtain ⟨-, -, hps, -⟩ := ConLeche.checkConstantVal_inv hcv
    rw [(ConLeche.checkConstantVal_lps hcv).1]
    exact hps
  intro r hr rhsA hrhsA T i hslot
  obtain ⟨rhs, hann, hfv⟩ := checkBlockRecsRules_annot hq r hr rhsA hrhsA
  refine ConLeche.annotateCore_noProjAt μ hann hfv ?_
  rw [findProj?_consBlockRecsBare hpsh]
  exact hslot

end Annot

/-! ## 5. The stage's VALUATION

`blockRecStaged_of` takes the post-cons carrier's valuation `acv` as a
parameter with six facts about it.  The recursor lane CHOOSES it —
the `i`-th stored recursor's leaf is the `i`-th projection of the
family's chosen tuple and every other name reads as before — so it is
defined here and three of the six facts (`hag`, the valuation
spelling, and the arity) come with the definition.  The other three
are about the LEAF and belong beside `blockRecAV_facts`. -/

/-- **The recursors' cons's valuation**: the block's recursors read as
the family's leaves, everything else as the constructors' environment
reads it. -/
@[expose] noncomputable def blockRecAcvOf (base : Name → (Name → Nat) → AnnotTerm)
    (names : List Name) (leaf : (Name → Nat) → Nat → AnnotTerm) :
    Name → (Name → Nat) → AnnotTerm :=
  fun n ψ =>
    match names.findIdx? (· == n) with
    | some i => leaf ψ i
    | none => base n ψ

/-- Off the block's recursors the valuation is the constructors'. -/
theorem blockRecAcvOf_of_ne {base : Name → (Name → Nat) → AnnotTerm} {names : List Name}
    {leaf : (Name → Nat) → Nat → AnnotTerm} {n : Name} (hne : ∀ m ∈ names, n ≠ m) :
    blockRecAcvOf base names leaf n = base n := by
  have h : names.findIdx? (· == n) = none :=
    List.findIdx?_eq_none_iff.mpr (fun x hx => by
      simpa using fun hh => hne x hx hh.symm)
  funext ψ
  simp only [blockRecAcvOf, h]

/-- At the `i`-th stored recursor the valuation IS the `i`-th leaf —
the names being pairwise distinct is what makes the lookup land on
`i`. -/
theorem blockRecAcvOf_at {base : Name → (Name → Nat) → AnnotTerm} {names : List Name}
    {leaf : (Name → Nat) → Nat → AnnotTerm} (hnd : names.Nodup) {i : Nat} {n : Name}
    (hi : names[i]? = some n) :
    blockRecAcvOf base names leaf n = fun ψ => leaf ψ i := by
  have hlt : i < names.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : names[i] = n := by
    rw [List.getElem?_eq_getElem hlt] at hi
    exact Option.some.inj hi
  have h : names.findIdx? (· == n) = some i := by
    rw [← hn]
    refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hlt, by simp, fun j hji hp => ?_⟩
    have hjl : j < names.length := by omega
    have : names[j] = names[i] := by simpa using hp
    exact absurd ((List.getElem_inj hnd).mp this) (by omega)
  funext ψ
  simp [blockRecAcvOf, h]

/-! ## 6. The stage, assembled

`blockRecStaged_run` is `blockRecStaged_of` with every SYNTACTIC
premise read off the run and the VALUATION defined rather than
assumed, in the shape `declBlock` consumes (`BlockRecStaged`).  The
recursor types' readings are the run's too (`checkBlockRecK_tyPis`),
so `RecTy` is not a parameter but the named spelling `blockRecTyAV`.

What is left is: the LEAF's four structural facts and its
ψ-dependence (beside `blockRecAV_facts`, the semantics tier's), and
the two SEMANTIC seams — the family premise `BlockRecPre` (the
regimes) and the rule data `hnew` (`hrecP_of`). -/

/-- The `i`-th recursor's LEAF at `ψ`: the `i`-th projection of the
family's chosen tuple, at the recursor types the run reads.

**The family's level `s` is a FUNCTION of `ψ`**, as it is at `k = 1`
(`fixLeafAV`'s `sAV : (Name → Nat) → Nat`): a large eliminator carries
its own level parameter, so a block's recursor types are sets of a
level that MOVES with the valuation, and `BlockRecPre.hTy` is stated
at `univ (s ψ)`. -/
@[expose] noncomputable def blockRecLeafAV (acval : Name → (Name → Nat) → AnnotTerm)
    (envC : Env) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) (ψ : Name → Nat)
    (i : Nat) : AnnotTerm :=
  ConLeche.Semantics.blockRecAV (s ψ) rs.length (blockRecTyAV acval envC rs ψ) (eqs ψ) i

/-- The recursors' cons's valuation, at the block's own leaves. -/
@[expose] noncomputable def blockRecAcv (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) :
    Name → (Name → Nat) → AnnotTerm :=
  blockRecAcvOf acval (rs.map (·.1.name)) (blockRecLeafAV acval envC rs s eqs)

/-- **The recursor stage, at the run.**  Its premises are the check's
own success, the two facts `declBlock` hands the lane (the
recogniser's member names and the constructors' STORAGE), the LEAF's
five facts — the grading one only AT A BLOCK POSITION, which is where
`blockRecAV_facts` gives it and where the stage consumes it — and the
two SEMANTIC seams. -/
theorem blockRecStaged_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hndM : p.toBlockShape.memberNames.Nodup)
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ)
    (hnew : ∀ m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        Expr.recRulePlain r.1.type (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j) p.nP = true →
        RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := p.nP,
              fire := .plain, rhs := rhs, paramsBlind := true })) :
    BlockRecStaged (V := V) μ envC p.toBlockShape p.nP rs mpC := by
  have hfacts := ConLeche.checkBlockRecK_facts h
  have hcv := checkBlockRecK_cvFacts h
  have hnd := checkBlockRecK_nodup h hndM
  -- the valuation's two defining facts
  have hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) →
      blockRecAcv mpC.base2.acval envC rs s eqs n = mpC.base2.acval n := by
    intro n hne
    refine blockRecAcvOf_of_ne (fun m hm => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact hne r hr
  have hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ
          = ConLeche.Semantics.blockRecAV (s ψ) rs.length
              (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) i := by
    intro i r hr ψ
    have hi : (rs.map (·.1.name))[i]? = some r.1.name := by
      rw [List.getElem?_map, hr]; rfl
    rw [blockRecAcv, blockRecAcvOf_at hnd hi]
    rfl
  have hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 r.1.type
          = some (blockRecTyAV mpC.base2.acval envC rs ψ i) := by
    intro i r hr ψ
    obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
    exact hread
  -- the leaf's facts, transported to the valuation
  have hidx : ∀ r ∈ rs, ∃ i : Nat, rs[i]? = some r := fun r hr => List.getElem?_of_mem hr
  exact blockRecStaged_of mpC hnd
    (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.1) (fun r hr => (hcv r hr).2.2.1)
    (fun r hr => ⟨(hfacts r hr).1, (hfacts r hr).2.1, (hfacts r hr).2.2.1,
      (hfacts r hr).2.2.2.1⟩)
    hag
    (fun r hr ψ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafCl ψ i)
    (fun r hr ψ k => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafLift ψ i k)
    (fun r hr ψ₁ ψ₂ hq => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ₁, hacv i r hi ψ₂]
      exact hleafPar i r hi ψ₁ ψ₂ hq)
    (fun r hr ψ ρ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]
      exact hleafOk ψ i (List.getElem?_eq_some_iff.mp hi).1 ρ)
    (fun r hr ψ ρ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafVal ψ i ρ)
    (hrd_of_pre hμ mpC h rfl hty hacv hpre)
    (fun r hr rhs hrhs => (hfacts r hr).2.2.2.2 rhs hrhs)
    hctorsIn
    (hrecP_of mpC (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.2.1) hag hnew)
    (ConLeche.checkBlockRecK_reserved h)
    (fun r hr T i hslot => (hcv r hr).2.2.2 T i hslot)
    (fun r hr rhs hrhs T i hslot => checkBlockRecK_rhsNoProj h r hr rhs hrhs T i hslot)

end ConLeche.Model
