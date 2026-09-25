module

public import ConLeche.Verify.Inductives.PosCompleteLink
public import ConLeche.Model.Cover
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.BlockAssembly
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.BlockInv

public section

/-!
# `StoredEnv` from the environment's invariants (lane COMPLETE-6M)

The completeness theorem (`nestedBlockPositivity_of_official_accepts`,
`Verify/Inductives/PosCompleteLink.lean`) reads the environment the
nested-positivity walk runs in through `StoredEnv`.  This module derives
it at the context the install builds (`nestedShadow`/`targetShadow`: the
members' formers consed on fresh names, the walk's `find?`/`consts`
those of that environment) from the Model tier's invariants:

* `EnvWF` of the environment before the formers (`mp.base2.wf`) —
  `closed`, `fresh`, and "a member has no stored constructor";
* coverage `LfpCover mp []` — every stored inductive but `Quot` is a
  member of a recorded block, which owns its constructors (`LfpOwn`,
  with the COMPLETE-6M fields `nparams`, `sortEnd`, `ctorLvl`);
* the basis pins (`EnvModel.basis_pinned`) — `Quot`'s stored former is
  its pin, whose `all` is empty (so `Quot` is in no recorded block) and
  whose type ends in a sort.

The context's own facts (`FormersCtx`): its lookups and constants are the
environment's with the formers consed, every former is an inductive of a
member, closed, ending in a sort, and the members are fresh below.
`storedEnv_of_install` produces them from the install's former stage
(`checkBlockInds`).
-/

namespace ConLeche.Model
open ConLeche (Env Name ConstantInfo ConstantVal NestCtx Expr IndCaps quotName)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## Syntactic helpers -/

theorem le_piArity_of_stripPis :
    ∀ {k : Nat} {e : Expr} {r : List (Expr × ConLeche.BinderMeta) × Expr},
      e.stripPis k = some r → k ≤ e.piArity
  | 0, _, _, _ => Nat.zero_le _
  | k + 1, .forallE ty body m, r, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨r', h', -⟩ := h
    have := le_piArity_of_stripPis h'
    show k + 1 ≤ body.piArity + 1
    omega
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => by
    simp [Expr.stripPis] at h

theorem nameNodup_of_nodup : ∀ {ns : List Name}, ns.Nodup → ConLeche.Name.nodup ns = true
  | [], _ => rfl
  | n :: ns, h => by
    obtain ⟨hn, hns⟩ := List.nodup_cons.mp h
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨by simpa using hn, nameNodup_of_nodup hns⟩

/-- A resolving expression mentions no name absent from the environment. -/
theorem deepOcc_false_of_resolve {env : Env} {p : Name → Bool}
    (hp : ∀ n, p n = true → env.find? n = none) :
    ∀ (e : Expr), e.constsResolve env = true → e.deepOcc p = false
  | .bvar _, _ | .sort _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => by
    simp only [Expr.constsResolve] at h
    show ty.deepOcc p = false
    exact deepOcc_false_of_resolve hp ty h
  | .const n _, h => by
    simp only [Expr.constsResolve] at h
    show p n = false
    cases hpn : p n with
    | false => rfl
    | true => rw [hp n hpn] at h; exact nomatch h
  | .app f a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.deepOcc, deepOcc_false_of_resolve hp f h.1, deepOcc_false_of_resolve hp a h.2,
      Bool.or_self]
  | .lam t b _, h | .forallE t b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.deepOcc, deepOcc_false_of_resolve hp t h.1, deepOcc_false_of_resolve hp b h.2,
      Bool.or_self]
  | .letE t v b, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.deepOcc, deepOcc_false_of_resolve hp t h.1.1,
      deepOcc_false_of_resolve hp v h.1.2, deepOcc_false_of_resolve hp b h.2, Bool.or_self]
  | .proj _ _ x, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    show x.deepOcc p = false
    exact deepOcc_false_of_resolve hp x h.2

/-- `Quot`'s pin: an inductive with an empty `all`, ending in a sort. -/
theorem pinnedInfo_quot :
    ∃ cv, ConLeche.pinnedInfo quotName = .indInfo cv {} ∧ ∃ u, cv.type.resultSort = some u := by
  have h1 : ConLeche.pinnedInfo quotName = ConLeche.quotA := by unfold ConLeche.pinnedInfo; rfl
  have h2 : ConLeche.quotA = .indInfo ConLeche.quotA.toConstantVal {} := rfl
  exact ⟨_, h1.trans h2, _, rfl⟩

/-- A stored `Quot` is its pin. -/
theorem quot_stored {env : Env} (mp : EnvModelM V μ env) {ci : ConstantInfo}
    (hf : env.find? quotName = some ci) :
    ∃ cv, ci = .indInfo cv {} ∧ ∃ u, cv.type.resultSort = some u := by
  obtain ⟨cv, hq, hs⟩ := pinnedInfo_quot
  exact ⟨cv, ((mp.base2.basis_pinned quotName ci hf (by decide)).1).trans hq, hs⟩

/-! ## Recorded blocks, read at the environment -/

section Recorded

variable {env : Env} {mp : EnvModelM V μ env}

omit [SetTheory V] in
theorem LfpDatum.member_mem {D : LfpDatum V} (hlen : D.names.length = D.k) {mm : Nat}
    (hmm : mm < D.k) : D.member mm ∈ D.names := by
  simp only [LfpDatum.member, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (hlen ▸ hmm : mm < D.names.length), Option.getD_some]
  exact List.getElem_mem _

omit [SetTheory V] in
theorem LfpDatum.mem_member {D : LfpDatum V} (hlen : D.names.length = D.k) {n : Name}
    (hn : n ∈ D.names) : ∃ mm, mm < D.k ∧ D.member mm = n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
  refine ⟨i, hlen ▸ hi, ?_⟩
  simp only [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

/-- A covered stored inductive: a member of a recorded block, whose `all`
is the block's names. -/
theorem covered_of (hcov : LfpCover mp []) {J : Name} {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? J = some (.indInfo cv caps)) (hq : J ≠ quotName) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = J ∧ caps.all = D.names := by
  obtain ⟨D, hD, mm, hmm, rfl⟩ := hcov.cover J cv caps hf List.not_mem_nil hq
  exact ⟨D, hD, mm, hmm, rfl, hcov.all D hD mm hmm cv caps hf⟩

/-- A recorded member's constructor list, entry by entry: each entry is a
recorded constructor stored at the list's parameter count. -/
theorem entry_recorded (hcov : LfpCover mp []) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks)
    {mm : Nat} (hmm : mm < D.k) {n : Nat} {L : List (ConstantVal × Nat)}
    (hL : ConLeche.nestContainer (envCtx env) (D.member mm) = some (n, L))
    {x : ConstantVal × Nat} (hx : x ∈ L) :
    ∃ j, j < D.nctors mm ∧ env.find? (D.ctorName mm j) = some (.ctorInfo x.1 n x.2) := by
  obtain ⟨nP', L', hL', hlen, hfj⟩ := (hcov.own D hD).ctors mm hmm
  rw [hL] at hL'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact ⟨j, hlen ▸ hj, hfj j hj⟩

end Recorded

/-! ## The walk's context over the formers' environment -/

/-- **The walk's context the install builds** over the environment `env`
before the block: its lookups and constants are `env`'s with the
members' formers `new` consed; every former is an inductive of a member,
closed, whose type ends in a sort; the members are fresh in `env`. -/
structure FormersCtx (env : Env) (new : List ConstantInfo) (ctx : NestCtx) : Prop where
  find : ∀ n, ctx.find? n = Env.find? ⟨new ++ env.consts⟩ n
  consts : ctx.consts = new ++ env.consts
  newInd : ∀ c ∈ new, ∃ cv caps, c = .indInfo cv caps ∧ ctx.names.contains cv.name = true ∧
    cv.type.hasFvar = false ∧ ∃ u, cv.type.resultSort = some u
  fresh : ∀ n, ctx.names.contains n = true → env.find? n = none

section Ctx

variable {env : Env} {new : List ConstantInfo} {ctx : NestCtx}

theorem FormersCtx.find_off (h : FormersCtx env new ctx) {n : Name}
    (hn : ctx.names.contains n = false) : ctx.find? n = env.find? n := by
  rw [h.find, find?_append, find?_append_none (fun c hc hcn => by
    obtain ⟨cv, caps, rfl, hmem, -⟩ := h.newInd c hc
    rw [show (ConstantInfo.indInfo cv caps).name = cv.name from rfl] at hcn
    rw [hcn, hn] at hmem; exact nomatch hmem)]
  rfl

theorem FormersCtx.find_member (h : FormersCtx env new ctx) {n : Name}
    (hn : ctx.names.contains n = true) {ci : ConstantInfo} (hf : ctx.find? n = some ci) :
    ∃ cv caps, ci = .indInfo cv caps ∧ cv.type.hasFvar = false ∧
      ∃ u, cv.type.resultSort = some u := by
  rw [h.find, find?_append, h.fresh n hn] at hf
  cases hnew : new.find? (·.name == n) with
  | none => rw [hnew] at hf; exact nomatch hf
  | some c =>
    rw [hnew] at hf
    obtain rfl := Option.some.inj hf
    obtain ⟨cv, caps, rfl, -, hcl, hs⟩ := h.newInd _ (List.mem_of_find?_eq_some hnew)
    exact ⟨cv, caps, rfl, hcl, hs⟩

theorem FormersCtx.entries (h : FormersCtx env new ctx) (C : Name) :
    ctx.consts.filterMap (ctorEntry C) = env.consts.filterMap (ctorEntry C) := by
  rw [h.consts, List.filterMap_append]
  have : new.filterMap (ctorEntry C) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    obtain ⟨cv, caps, rfl, -⟩ := h.newInd c hc
    rfl
  rw [this, List.nil_append]

/-- Off the members, the walk reads a container as the environment does. -/
theorem FormersCtx.nestContainer_off (h : FormersCtx env new ctx) {C : Name}
    (hn : ctx.names.contains C = false) :
    ConLeche.nestContainer ctx C = ConLeche.nestContainer (envCtx env) C := by
  rw [nestContainer_eq, nestContainer_eq, h.find_off hn, h.entries]
  rfl

/-- A member has no stored constructor. -/
theorem FormersCtx.nestContainer_member (h : FormersCtx env new ctx) (hwf : ConLeche.EnvWF env)
    {J : Name} (hn : ctx.names.contains J = true) {cv : ConstantVal} {caps : IndCaps}
    (hf : ctx.find? J = some (.indInfo cv caps)) :
    ConLeche.nestContainer ctx J = some (caps.nparams, []) := by
  rw [nestContainer_eq, hf]
  show nestPick caps (ctx.consts.filterMap (ctorEntry J)) = _
  rw [h.entries, ctorEntries_fresh hwf (h.fresh J hn)]
  rfl

theorem nestContainer_ind {ctx : NestCtx} {C : Name} {r : Nat × List (ConstantVal × Nat)}
    (h : ConLeche.nestContainer ctx C = some r) :
    ∃ cv caps, ctx.find? C = some (.indInfo cv caps) := by
  rw [nestContainer_eq] at h
  split at h
  · rename_i cv caps hf; exact ⟨cv, caps, hf⟩
  · exact nomatch h

variable {mp : EnvModelM V μ env}

/-- A stored container off the members and `Quot` is covered, and the
walk reads its constructor list as the environment does. -/
theorem FormersCtx.covered (h : FormersCtx env new ctx) (hcov : LfpCover mp [])
    {J : Name} {r : Nat × List (ConstantVal × Nat)} (hq : J ≠ quotName)
    (hL : ConLeche.nestContainer ctx J = some r) :
    ctx.names.contains J = true ∨
    ∃ cv caps, env.find? J = some (.indInfo cv caps) ∧
      ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = J ∧ caps.all = D.names ∧
        ConLeche.nestContainer (envCtx env) J = some r := by
  cases hn : ctx.names.contains J with
  | true => exact .inl rfl
  | false =>
    obtain ⟨cv, caps, hf⟩ := nestContainer_ind hL
    rw [h.find_off hn] at hf
    obtain ⟨D, hD, mm, hmm, hm, hall⟩ := covered_of hcov hf hq
    exact .inr ⟨cv, caps, hf, D, hD, mm, hmm, hm, hall, by rw [← h.nestContainer_off hn]; exact hL⟩

/-- **A stored constructor's conclusion** (for lane COMPLETE-6R): past its
parameters and fields, a constructor the walk reads off a container other
than `Quot` is the container at the constructor's own level parameters,
applied (`LfpOwn.ctorConcl`). -/
theorem FormersCtx.ctorConcl (h : FormersCtx env new ctx) (hwf : ConLeche.EnvWF env)
    (hcov : LfpCover mp []) {J : Name} {n : Nat} {L : List (ConstantVal × Nat)}
    (hq : J ≠ quotName) (hL : ConLeche.nestContainer ctx J = some (n, L)) :
    ∀ x ∈ L, ∃ bs args, x.1.type.stripPis (n + x.2)
      = some (bs, Expr.mkAppN (.const J (x.1.levelParams.map .param)) args) := by
  intro x hx
  rcases h.covered hcov hq hL with hn | ⟨cv, caps, -, D, hD, mm, hmm, rfl, -, hL'⟩
  · obtain ⟨cv, caps, hf⟩ := nestContainer_ind hL
    rw [h.nestContainer_member hwf hn hf] at hL
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    exact nomatch hx
  · obtain ⟨j, hj, hfj⟩ := entry_recorded hcov hD hmm hL' hx
    obtain ⟨cv', nPc, nF, hf', bs, args, hs, -⟩ := (hcov.own D hD).ctorConcl mm hmm j hj
    rw [hfj] at hf'
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hf')
    exact ⟨bs, args, hs⟩

/-- **A stored constructor shares its container's level parameters** (for
lane COMPLETE-6R; `LfpOwn.ctorLvl`), off `Quot`. -/
theorem FormersCtx.ctorLvl (h : FormersCtx env new ctx) (hwf : ConLeche.EnvWF env)
    (hcov : LfpCover mp []) {J : Name} {n : Nat} {L : List (ConstantVal × Nat)}
    (hq : J ≠ quotName) (hL : ConLeche.nestContainer ctx J = some (n, L)) :
    ∀ x ∈ L, ∃ cv caps, ctx.find? J = some (.indInfo cv caps) ∧
      x.1.levelParams = cv.levelParams ∧ cv.levelParams.Nodup := by
  intro x hx
  rcases h.covered hcov hq hL with hn | ⟨cv, caps, hf, D, hD, mm, hmm, rfl, -, hL'⟩
  · obtain ⟨cv, caps, hf⟩ := nestContainer_ind hL
    rw [h.nestContainer_member hwf hn hf] at hL
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    exact nomatch hx
  · obtain ⟨j, hj, hfj⟩ := entry_recorded hcov hD hmm hL' hx
    obtain ⟨cv', nPc, nF, cvT, capsT, hf', hfT, hl⟩ := (hcov.own D hD).ctorLvl mm hmm j hj
    rw [hfj] at hf'
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hf')
    rw [hf] at hfT
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT)
    obtain ⟨cv'', caps'', hf'', hnd⟩ := (hcov.own D hD).lvlNodup mm hmm
    rw [hf] at hf''
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf'')
    have hnm : ctx.names.contains (D.member mm) = false := by
      cases hc : ctx.names.contains (D.member mm) with
      | false => rfl
      | true => rw [h.fresh _ hc] at hf; exact nomatch hf
    exact ⟨cv, caps, by rw [h.find_off hnm]; exact hf, hl, hnd⟩

/-- **A stored former off the members mentions no member** (for lane
COMPLETE-6's `StoredEnv.formerFresh`): it is stored below the formers,
where its type resolves (`EnvWF`) and the members are fresh. -/
theorem FormersCtx.formerFresh (h : FormersCtx env new ctx) (hwf : ConLeche.EnvWF env)
    {J : Name} {cv : ConstantVal} {caps : IndCaps} (hf : ctx.find? J = some (.indInfo cv caps))
    (hn : ctx.names.contains J = false) :
    cv.type.deepOcc (fun n => ctx.names.contains n) = false := by
  rw [h.find_off hn] at hf
  exact deepOcc_false_of_resolve (fun n hn => h.fresh n hn) _
    (hwf _ (ConLeche.Semantics.Env.find?_mem hf)).2.2.1

/-- A name stored below the formers is no member. -/
theorem FormersCtx.not_member (h : FormersCtx env new ctx) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) : ctx.names.contains n = false := by
  cases hc : ctx.names.contains n with
  | false => rfl
  | true => rw [h.fresh _ hc] at hf; exact nomatch hf

/-- **`StoredEnv` at the install's context.**  Over an environment with a
Model-tier carrier covered without exemptions (`LfpCover mp []`: every
stored inductive but `Quot` a member of a recorded block, which owns its
constructors), the walk's context over the members' formers consed on
fresh names (`FormersCtx`) satisfies every `StoredEnv` field. -/
theorem storedEnv_of_cover (h : FormersCtx env new ctx) (hcov : LfpCover mp []) :
    StoredEnv ctx := by
  have hwf : ConLeche.EnvWF env := mp.base2.wf
  -- a recorded block's names lie off the members, stored as inductives
  -- listing the block
  have hblk : ∀ D ∈ mp.lfpBlocks, ∀ J ∈ D.names, ctx.names.contains J = false ∧
      ∃ mm, mm < D.k ∧ D.member mm = J ∧ ∃ cv caps, env.find? J = some (.indInfo cv caps) ∧
        caps.all = D.names := by
    intro D hD J hJ
    obtain ⟨mm, hmm, rfl⟩ := LfpDatum.mem_member (hcov.len D hD) hJ
    obtain ⟨cv, caps, hf⟩ := LfpCover.member_find hD hmm
    exact ⟨h.not_member hf, mm, hmm, rfl, cv, caps, hf, hcov.all D hD mm hmm cv caps hf⟩
  refine ⟨?nparams, ?ctorArity, ?closed, ?nodup, ?blockClosed, ?fresh, ?block, ?quot, ?sortEnd,
    fun J cv caps hf hn => h.formerFresh hwf hf hn, ?ctorConcl⟩
  case ctorConcl =>
    intro J cv caps hf hq n L hL x hx
    obtain ⟨cv', caps', hf', hlv, -⟩ := h.ctorLvl hwf hcov hq hL x hx
    rw [hf] at hf'
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf')
    obtain ⟨bs, args, hs⟩ := h.ctorConcl hwf hcov hq hL x hx
    exact ⟨by rw [hlv], bs, _, hs, Expr.getAppFn_mkAppN _ _⟩
  case nparams =>
    intro J cv caps hf hq
    cases hn : ctx.names.contains J with
    | true => exact ⟨[], h.nestContainer_member hwf hn hf⟩
    | false =>
      rw [h.find_off hn] at hf
      obtain ⟨D, hD, mm, hmm, rfl, -⟩ := covered_of hcov hf hq
      obtain ⟨cv', caps', L, hf', -, hL⟩ := (hcov.own D hD).nparams mm hmm
      rw [hf] at hf'
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf')
      exact ⟨L, by rw [h.nestContainer_off hn]; exact hL⟩
  case ctorArity =>
    intro J n L hq hL x hx
    obtain ⟨bs, args, hs⟩ := h.ctorConcl hwf hcov hq hL x hx
    exact le_piArity_of_stripPis hs
  case closed =>
    refine ⟨fun ci hci => ?_, fun n ci hf => ?_⟩
    · rw [h.consts] at hci
      rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨cv, caps, rfl, -, hcl, -⟩ := h.newInd ci hci
        exact hcl
      · exact (hwf ci hci).1
    · rw [h.find] at hf
      have hci := ConLeche.Semantics.Env.find?_mem hf
      rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨cv, caps, rfl, -, hcl, -⟩ := h.newInd ci hci
        exact hcl
      · exact (hwf ci hci).1
  case nodup =>
    intro J n L hq hL x hx
    obtain ⟨cv, caps, -, hl, hnd⟩ := h.ctorLvl hwf hcov hq hL x hx
    rw [hl]; exact nameNodup_of_nodup hnd
  case blockClosed =>
    intro C cv caps hf hCn hCq J hJ n hn
    rw [h.find_off hCn] at hf
    obtain ⟨D, hD, mm, hmm, rfl, hall⟩ := covered_of hcov hf hCq
    have hsub : ∀ m ∈ D.member mm :: ConLeche.nestFrameMates ctx (D.member mm), m ∈ D.names := by
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact LfpDatum.member_mem (hcov.len D hD) hmm
      · simp only [ConLeche.nestFrameMates, ConLeche.nestBlockOf, h.find_off hCn, hf,
          List.mem_filter, List.mem_eraseDups] at hm
        exact hall ▸ hm.1
    obtain ⟨hJn, -, -, -, cvJ, capsJ, hfJ, hallJ⟩ := hblk D hD J (hsub J hJ)
    simp only [ConLeche.nestBlockOf, h.find_off hJn, hfJ, hallJ]
    exact List.contains_iff_mem.mpr (hsub n hn)
  case fresh =>
    intro J n L hL x hx
    obtain ⟨nPc, hci⟩ := ConLeche.nestContainer_mem hL x hx
    rw [h.consts] at hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨cv, caps, hc, -⟩ := h.newInd _ hci
      exact nomatch hc
    · exact deepOcc_false_of_resolve (fun n hn => h.fresh n hn) _ (hwf _ hci).2.2.1
  case block =>
    intro I cv caps J hf hIn hJ
    rw [h.find_off hIn] at hf
    by_cases hIq : I = quotName
    · subst hIq
      obtain ⟨cvq, hci, -⟩ := quot_stored mp hf
      obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj hci
      exact nomatch hJ
    obtain ⟨D, hD, mm, hmm, rfl, hall⟩ := covered_of hcov hf hIq
    rw [hall] at hJ
    obtain ⟨hJn, mm', hmm', rfl, cv', caps', hfJ, hallJ⟩ := hblk D hD _ hJ
    obtain ⟨cv₁, caps₁, L₁, hf₁, hp₁, -⟩ := (hcov.own D hD).nparams mm hmm
    obtain ⟨cv₂, caps₂, L₂, hf₂, hp₂, -⟩ := (hcov.own D hD).nparams mm' hmm'
    rw [hf] at hf₁; rw [hfJ] at hf₂
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf₁)
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf₂)
    refine ⟨hJn, cv', caps', by rw [h.find_off hJn]; exact hfJ, ?_, fun n hn => ?_⟩
    · rw [← hp₁ (fun _ => 0), ← hp₂ (fun _ => 0)]
    · rw [hall, ← hallJ]; exact hn
  case quot =>
    intro I cv caps hf hIn hIq hmem
    rw [h.find_off hIn] at hf
    obtain ⟨D, hD, mm, hmm, rfl, hall⟩ := covered_of hcov hf hIq
    rw [hall] at hmem
    obtain ⟨-, -, -, -, cvq, capsq, hfq, hallq⟩ := hblk D hD _ hmem
    obtain ⟨cvq', hci, -⟩ := quot_stored mp hfq
    obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj hci
    rw [← hallq] at hmem
    exact nomatch hmem
  case sortEnd =>
    intro J cv caps hf
    cases hn : ctx.names.contains J with
    | true =>
      obtain ⟨cv', caps', hci, -, hs⟩ := h.find_member hn hf
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hci
      exact hs
    | false =>
      rw [h.find_off hn] at hf
      by_cases hJq : J = quotName
      · subst hJq
        obtain ⟨cvq, hci, hs⟩ := quot_stored mp hf
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj hci
        exact hs
      obtain ⟨D, hD, mm, hmm, rfl, -⟩ := covered_of hcov hf hJq
      obtain ⟨cv', caps', u, hf', hu⟩ := (hcov.own D hD).sortEnd mm hmm
      rw [hf] at hf'
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf')
      exact ⟨u, hu⟩

/-- **`StoredEnv` at the uniform install's walk context** (`BlockShape.nestCtx`
over the formers' environment `envI`, as `nestedShadow` builds it), from
the former stage's run (`checkBlockInds`), over an environment whose
carrier is covered without exemptions.  Nothing else is assumed: the
formers' facts are the stage's (`blockFormerFacts_of`). -/
theorem storedEnv_of_install (hμ : μ.verifiedChecks = true) {F : Nat} {env envI : Env}
    {p₀ : ConLeche.BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {q : ConLeche.BlockShape}
    (mp : EnvModelM V μ env) (hcov : LfpCover mp [])
    (h : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hlps : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps) (fvsP : List Expr) :
    StoredEnv (q.nestCtx fvsP envI.find? envI.consts) := by
  obtain ⟨ppsOf, sOf, hF⟩ := blockFormerFacts_of hμ mp h hlps
  obtain ⟨-, -, -, -, -, -, -, -, hcons, -⟩ := ConLeche.checkBlockInds_shape h
  obtain ⟨new, hnew, hall⟩ := consBlockInds_consts (p₁ := q) (isRec := isRec) cvTas 0 env
  rw [← hcons] at hnew
  have hlenN : q.memberNames.length = cvTas.length := by
    rw [hF.lenCv]; simp [ConLeche.BlockShape.memberNames, ConLeche.BlockShape.k]
  have hcvName : ∀ (m : Nat) (cv : ConstantVal), cvTas[m]? = some cv →
      q.memberNames.contains cv.name = true := by
    intro m cv hm
    have hml : m < q.memberNames.length := by
      rw [hlenN]; exact (List.getElem?_eq_some_iff.mp hm).1
    rw [hF.nameOf m cv hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml,
      Option.getD_some]
    exact List.contains_iff_mem.mpr (List.getElem_mem hml)
  refine storedEnv_of_cover (mp := mp) (new := new) ⟨fun n => ?_, hnew, fun c hc => ?_, fun n hn => ?_⟩
    hcov
  · show List.find? _ envI.consts = List.find? _ (new ++ env.consts)
    rw [hnew]
  · obtain ⟨cv, hcv, j, rfl⟩ := hall c hc
    obtain ⟨m, hm⟩ := List.getElem?_of_mem hcv
    obtain ⟨bs, hs⟩ := hF.stripOf m cv hm
    exact ⟨cv, _, rfl, hcvName m cv hm, (hF.tyWFOf m cv hm).1, _, resultSort_of_stripPis_sort hs⟩
  · have hn' : n ∈ q.memberNames := List.contains_iff_mem.mp hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn'
    have hic : i < cvTas.length := hlenN ▸ hi
    have hm : cvTas[i]? = some cvTas[i] := List.getElem?_eq_getElem hic
    have := hF.freshOf i _ hm
    rwa [hF.nameOf i _ hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this

end Ctx

end ConLeche.Model
