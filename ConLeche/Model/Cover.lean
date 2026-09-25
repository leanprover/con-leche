module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Annot.BitConsCross
import ConLeche.Model.Install
import ConLeche.Model.Annot.CanonCrest

public section

/-!
# Coverage, and the fold step's shape that carries it (lanes L8, L8a)

NESTPLAN L8 (U6), charter item 2 ("the model needs only this
least-fixed-point clause from each inductive").  `LfpCover mp ex`: every
stored inductive but `Quot` and the names in `ex` (the block being
installed — its formers are stored before its clause is recorded) is a
member of a recorded block (`EnvModelM.lfpBlocks`), and every recorded
block's names are distinct, as many as its members, and its members'
stored `all` lists them.

**Not an `EnvModelM` field.**  It is FALSE while the modeller can
install an `.indInfo` (`Model/DeclInd.lean` records no clause; NESTPLAN
Q-B), so the fold carries it CONDITIONALLY (`Model/Fold.lean`,
`EnvModelOk`, under `FoldCoverPB`) until the flip (L9).

**The step shape (lane L8a).**  A fold step concludes
`CoverStep mp env₂` — `∃ mp' : EnvModelM V μ env₂, LfpCover mp [] →
LfpCover mp' []`: a carrier at the step's result, together with
coverage carried from the input carrier to it.  Not the weaker
`mp.lfpBlocks ⊆ mp'.lfpBlocks ∧ …`: coverage needs, beyond the recorded
list, which inductives the step STORES (a fresh one must be recorded or
exempt) and, at a record, that the block's names are distinct and are
its members' `all` — facts of the step, available only where the step
is proved.  The implication states exactly what the fold consumes and
composes (`CoverTo.trans`).  Inside a step, the chain of conses moves
the exemption list (`CoverTo mp ex env' ex'`): a former's cons adds its
name, the block's record (`EnvModelM.addLfp`) removes its names, every
other cons keeps it (`coverA_cons`, from the cons funnel's
`∃ mp', mp'.base2.acval = …` by `EnvModelM.keepLfp`: the funnel's
carrier with the input's recorded list, re-proved at the extension).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche (Env Name ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## Constructor ownership (lane COVERB)

A container frame reads a recorded member's constructors off the
environment (`nestContainer`: every stored constructor whose result head
is the member, in install order).  Ownership says that reading is the
block's own list: every stored constructor whose head is a recorded
member is one of that member's recorded constructors, in order, and a
member without constructors reads its recorded parameter count.  It is
stated at the environment's own context (`envCtx`), which the walk's
context reads (`nestContainer_ctx`). -/

/-- The entry `nestContainer` collects for a stored constant at the
container name `C` (its `filterMap` function, verbatim). -/
@[expose] def ctorEntry (C : Name) : ConstantInfo → Option (ConstantVal × Nat × Nat)
  | .ctorInfo cv nPc nF =>
    match cv.type.stripPis (nPc + nF) with
    | some (_, body) =>
      match body.getAppFn with
      | .const n _ => if n == C then some (cv, nPc, nF) else none
      | _ => none
    | none => none
  | _ => none

/-- The environment as a walk context: `nestContainer` reads only its
`find?` and `consts`. -/
@[expose] def envCtx (env : Env) : ConLeche.NestCtx where
  names := []
  lps := []
  nP := 0
  nIdxs := []
  params := []
  sort := .zero
  find? := env.find?
  consts := env.consts

/-- `nestContainer`'s result from its constructor entries. -/
@[expose] def nestPick (caps : ConLeche.IndCaps) :
    List (ConstantVal × Nat × Nat) → Option (Nat × List (ConstantVal × Nat))
  | [] => some (caps.nparams, [])
  | cs@((_, nPc, _) :: _) => some (nPc, (cs.map fun c => (c.1, c.2.2)).reverse)

theorem filterMap_ext' {α β : Type} {f g : α → Option β} (h : ∀ a, f a = g a)
    (l : List α) : l.filterMap f = l.filterMap g := by
  rw [funext h]

theorem nestContainer_eq (ctx : ConLeche.NestCtx) (C : Name) :
    ConLeche.nestContainer ctx C = match ctx.find? C with
      | some (.indInfo _ caps) => nestPick caps (ctx.consts.filterMap (ctorEntry C))
      | _ => none := by
  unfold ConLeche.nestContainer
  split
  · rename_i hfind
    rw [hfind]
    dsimp only
    rw [filterMap_ext' (g := ctorEntry C)]
    · unfold nestPick
      generalize List.filterMap (ctorEntry C) ctx.consts = cs
      cases cs <;> rfl
    · intro ci; cases ci <;> rfl
  · next hne =>
    split
    · next h => exact absurd h (hne _ _)
    · rfl

/-- The walk's context reads `nestContainer` as the environment does. -/
theorem nestContainer_ctx {env : Env} {ctx : ConLeche.NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) (hconsts : ctx.consts = env.consts) (C : Name) :
    ConLeche.nestContainer ctx C = ConLeche.nestContainer (envCtx env) C := by
  rw [nestContainer_eq, nestContainer_eq, hfind, hconsts]
  rfl

/-- A cons whose head is no constructor of `C`, at a stored `C`, keeps
`C`'s constructor list. -/
theorem nestContainer_cons {env : Env} {c₀ : ConstantInfo} {C : Name}
    (hfresh : env.find? c₀.name = none) (hC : (env.find? C).isSome = true)
    (hent : ctorEntry C c₀ = none) :
    ConLeche.nestContainer (envCtx ⟨c₀ :: env.consts⟩) C
      = ConLeche.nestContainer (envCtx env) C := by
  rw [nestContainer_eq, nestContainer_eq]
  show (match (⟨c₀ :: env.consts⟩ : Env).find? C with
      | some (.indInfo _ caps) => nestPick caps ((c₀ :: env.consts).filterMap (ctorEntry C))
      | _ => none) = (match env.find? C with
      | some (.indInfo _ caps) => nestPick caps (env.consts.filterMap (ctorEntry C))
      | _ => none)
  rw [ConLeche.Env.find?_cons_of_isSome hfresh hC, List.filterMap_cons, hent]

/-- **A recorded block's constructor ownership** (`ContBlockOk.ctors`/
`noCtors`, at the environment's own context). -/
structure LfpOwn (env : Env) (D : LfpDatum V) : Prop where
  ctors : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer (envCtx env) (D.member c)
      = some (nP', L) ∧
    L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
      env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2)
  noCtors : ∀ c, c < D.k → ∀ nP',
    ConLeche.nestContainer (envCtx env) (D.member c) = some (nP', []) →
    ∃ cv caps, env.find? (D.member c) = some (.indInfo cv caps) ∧ cv.levelParams.Nodup ∧
      (∀ ψ, (D.params ψ).length = nP') ∧
      ∀ mm, mm < D.k → ∃ cvm capsm, env.find? (D.member mm) = some (.indInfo cvm capsm) ∧
        cvm.levelParams = cv.levelParams
  /-- every member's level parameters are distinct (finding F6: the
  install's `checkConstantValF` checks it, as official's
  `check_duplicated_univ_params` does) -/
  lvlNodup : ∀ c, c < D.k → ∃ cv caps, env.find? (D.member c) = some (.indInfo cv caps) ∧
    cv.levelParams.Nodup
  /-- **every recorded constructor concludes in its member applied to its
  parameters and indices** (finding F8): past its parameters and fields
  the stored type is the member at the constructor's own level
  parameters applied to `nPc + |ids c|`
  arguments — the install's constructor check (`checkSumCtor_shape`), as
  official's (`check_constructors`, `is_valid_ind_app`: `nparams +
  nindices` arguments, `inductive.cpp`) -/
  ctorConcl : ∀ c, c < D.k → ∀ j, j < D.nctors c → ∃ cv nPc nF,
    env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF) ∧
    ∃ bs args, cv.type.stripPis (nPc + nF)
        = some (bs, Expr.mkAppN (.const (D.member c) (cv.levelParams.map .param)) args) ∧
      ∀ ψ, args.length = nPc + (D.ids c ψ).length
  /-- **every member's recorded parameter count is the block's and its
  constructors'** (lane COMPLETE-6M): `IndCaps.nparams` (official's
  `inductive_val.nparams`) is the datum's parameter telescope's length,
  and `nestContainer`'s count — the head constructor's, hence (by
  `ctors`) every recorded constructor's — is it.  The install records
  `BlockShape.nP` and stores every constructor at it (`blockCapsAt`,
  `consSumCtors`); a basis block's pin carries its own. -/
  nparams : ∀ c, c < D.k → ∃ cv caps L, env.find? (D.member c) = some (.indInfo cv caps) ∧
    (∀ ψ, (D.params ψ).length = caps.nparams) ∧
    ConLeche.nestContainer (envCtx env) (D.member c) = some (caps.nparams, L)
  /-- **every member's former is a syntactic telescope ending in a sort**
  (lane COMPLETE-6M): the install's `checkBlockTele` strips it at
  `nP + nIdx` to a `.sort` (`BlockFormerFacts.stripOf`); a basis former is
  literal -/
  sortEnd : ∀ c, c < D.k → ∃ cv caps u, env.find? (D.member c) = some (.indInfo cv caps) ∧
    cv.type.resultSort = some u
  /-- **every recorded constructor shares its member's level parameters**
  (lane COMPLETE-6M; with `lvlNodup`, they are distinct): the install
  stores every constructor and every former at the block's level
  parameters (the recogniser's `blockShape?`); a basis pin is literal -/
  ctorLvl : ∀ c, c < D.k → ∀ j, j < D.nctors c → ∃ cv nPc nF cvT capsT,
    env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF) ∧
    env.find? (D.member c) = some (.indInfo cvT capsT) ∧ cv.levelParams = cvT.levelParams

omit [SetTheory V] in
/-- Ownership across an extension that keeps every lookup and every
recorded member's constructor list. -/
theorem LfpOwn.mono {env env' : Env} {D : LfpDatum V} (h : LfpOwn env D)
    (hfwd : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hnc : ∀ c, c < D.k → ConLeche.nestContainer (envCtx env') (D.member c)
      = ConLeche.nestContainer (envCtx env) (D.member c)) : LfpOwn env' D where
  ctors := fun c hc => by
    obtain ⟨nP', L, hL, hlen, hj⟩ := h.ctors c hc
    exact ⟨nP', L, (hnc c hc).trans hL, hlen, fun j hjl => hfwd _ _ (hj j hjl)⟩
  noCtors := fun c hc nP' hL => by
    obtain ⟨cv, caps, hf, hnd, hlen, hall⟩ := h.noCtors c hc nP' ((hnc c hc).symm.trans hL)
    refine ⟨cv, caps, hfwd _ _ hf, hnd, hlen, fun mm hmm => ?_⟩
    obtain ⟨cvm, capsm, hfm, hl⟩ := hall mm hmm
    exact ⟨cvm, capsm, hfwd _ _ hfm, hl⟩
  lvlNodup := fun c hc => by
    obtain ⟨cv, caps, hf, hnd⟩ := h.lvlNodup c hc
    exact ⟨cv, caps, hfwd _ _ hf, hnd⟩
  ctorConcl := fun c hc j hj => by
    obtain ⟨cv, nPc, nF, hf, hsh⟩ := h.ctorConcl c hc j hj
    exact ⟨cv, nPc, nF, hfwd _ _ hf, hsh⟩
  nparams := fun c hc => by
    obtain ⟨cv, caps, L, hf, hp, hL⟩ := h.nparams c hc
    exact ⟨cv, caps, L, hfwd _ _ hf, hp, (hnc c hc).trans hL⟩
  sortEnd := fun c hc => by
    obtain ⟨cv, caps, u, hf, hu⟩ := h.sortEnd c hc
    exact ⟨cv, caps, u, hfwd _ _ hf, hu⟩
  ctorLvl := fun c hc j hj => by
    obtain ⟨cv, nPc, nF, cvT, capsT, hf, hfT, hl⟩ := h.ctorLvl c hc j hj
    exact ⟨cv, nPc, nF, cvT, capsT, hfwd _ _ hf, hfwd _ _ hfT, hl⟩

/-! ### Constructor entries, computed -/

theorem constsBound_stripPis {env : Env} :
    ∀ {k : Nat} {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {b : Expr},
      ConstsBound env e → e.stripPis k = some (bs, b) → ConstsBound env b
  | 0, e, bs, b, h, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact h
  | k + 1, .forallE ty body m, bs, b, h, hs => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', b'⟩, hs', he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact constsBound_stripPis ((constsBound_forallE).mp h).2 hs'
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs
  | _ + 1, .sort _, _, _, _, hs | _ + 1, .const _ _, _, _, _, hs
  | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs
  | _ + 1, .proj _ _ _, _, _, _, hs => by simp [Expr.stripPis] at hs

theorem constsBound_getAppFn {env : Env} :
    ∀ {e : Expr} {n : Name} {us : List Level},
      ConstsBound env e → e.getAppFn = .const n us → (env.find? n).isSome = true
  | .app f _, n, us, h, hg => constsBound_getAppFn ((constsBound_app).mp h).1 hg
  | .const n' us', n, us, h, hg => by
    simp only [Expr.getAppFn, Expr.const.injEq] at hg
    obtain ⟨rfl, -⟩ := hg
    exact (constsBound_const).mp h
  | .bvar _, _, _, _, hg | .fvar _ _, _, _, _, hg | .sort _, _, _, _, hg
  | .lam _ _ _, _, _, _, hg | .forallE _ _ _, _, _, _, hg | .letE _ _ _, _, _, _, hg
  | .lit _, _, _, _, hg | .proj _ _ _, _, _, _, hg => by simp [Expr.getAppFn] at hg

/-- A stored constant's constructor entry at `C` names a stored head. -/
theorem ctorEntry_isSome_found {env : Env} {ci : ConstantInfo} {C : Name}
    (hb : ConstsBound env ci.toConstantVal.type) (h : (ctorEntry C ci).isSome = true) :
    (env.find? C).isSome = true := by
  cases ci with
  | ctorInfo cv nPc nF =>
    dsimp only [ctorEntry] at h
    cases hs : cv.type.stripPis (nPc + nF) with
    | none => rw [hs] at h; exact nomatch h
    | some p =>
      obtain ⟨bs, body⟩ := p
      rw [hs] at h
      dsimp only at h
      cases hg : body.getAppFn with
      | const n us =>
        rw [hg] at h
        dsimp only at h
        by_cases hn : n = C
        · subst hn
          exact constsBound_getAppFn (constsBound_stripPis hb hs) hg
        · rw [if_neg (by simpa using hn)] at h; exact nomatch h
      | _ => rw [hg] at h; exact nomatch h
  | _ => exact nomatch h

/-- A constructor's entry at its own head. -/
theorem ctorEntry_self {c₀ : ConstantInfo} {cv : ConstantVal} {nPc nF : Nat}
    {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr} {T : Name} {us : List Level}
    (hc : c₀ = .ctorInfo cv nPc nF) (hs : cv.type.stripPis (nPc + nF) = some (bs, body))
    (hg : body.getAppFn = .const T us) : ctorEntry T c₀ = some (cv, nPc, nF) := by
  subst hc
  simp only [ctorEntry, hs, hg, beq_self_eq_true, if_true]

/-- A constructor has an entry only at its own head. -/
theorem ctorEntry_head {c₀ : ConstantInfo} {cv : ConstantVal} {nPc nF : Nat}
    {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr} {T : Name} {us : List Level}
    (hc : c₀ = .ctorInfo cv nPc nF) (hs : cv.type.stripPis (nPc + nF) = some (bs, body))
    (hg : body.getAppFn = .const T us) {C : Name} (h : (ctorEntry C c₀).isSome = true) :
    C = T := by
  subst hc
  simp only [ctorEntry, hs, hg] at h
  by_cases hne : T = C
  · exact hne.symm
  · rw [if_neg (by simpa using hne)] at h
    exact nomatch h

/-- The cons premise `hhead` at a constructor whose head is `T`. -/
theorem hhead_ctor {env : Env} {ex : List Name} {c₀ : ConstantInfo} {cv : ConstantVal}
    {nPc nF : Nat} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr} {T : Name}
    {us : List Level}
    (hc : c₀ = .ctorInfo cv nPc nF) (hs : cv.type.stripPis (nPc + nF) = some (bs, body))
    (hg : body.getAppFn = .const T us)
    (hT : T ∈ ex ∨ ∃ cv caps, env.find? T = some (.indInfo cv caps) ∧ caps.all = []) :
    ∀ cv nPc nF, c₀ = .ctorInfo cv nPc nF → ∀ C, (ctorEntry C c₀).isSome = true →
      C ∈ ex ∨ ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = [] := by
  intro _ _ _ _ C h
  rw [ctorEntry_head hc hs hg h]
  exact hT

/-- **No stored constructor has a fresh head.** -/
theorem ctorEntries_fresh {env : Env} (hwf : ConLeche.EnvWF env) {C : Name}
    (hC : env.find? C = none) : env.consts.filterMap (ctorEntry C) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro ci hci
  cases h : ctorEntry C ci with
  | none => rfl
  | some _ =>
    have := ctorEntry_isSome_found
      (ConLeche.Semantics.envWF_constsBound hwf ci hci).1 (by rw [h]; rfl)
    rw [hC] at this
    exact nomatch this

omit [SetTheory V] in
/-- **Ownership at a one-member block**, from its former, its stored
constructor entries and their lookups. -/
theorem lfpOwn_one {env : Env} {D : LfpDatum V} {T : Name} {cv : ConstantVal}
    {caps : ConLeche.IndCaps} {cs : List (ConstantVal × Nat × Nat)}
    (hk : D.k = 1) (hm : D.member 0 = T) (hf : env.find? T = some (.indInfo cv caps))
    (hcs : env.consts.filterMap (ctorEntry T) = cs)
    (hctors : ∃ nP' L, nestPick caps cs = some (nP', L) ∧ L.length = D.nctors 0 ∧
      ∀ j (hj : j < L.length), env.find? (D.ctorName 0 j) = some (.ctorInfo L[j].1 nP' L[j].2))
    (hno : ∀ nP', nestPick caps cs = some (nP', []) →
      cv.levelParams.Nodup ∧ ∀ ψ, (D.params ψ).length = nP')
    (hnd : cv.levelParams.Nodup)
    (hconcl : ∀ nP' L, nestPick caps cs = some (nP', L) → ∀ j (hj : j < L.length),
      ∃ bs args, L[j].1.type.stripPis (nP' + L[j].2)
          = some (bs, Expr.mkAppN (.const T (L[j].1.levelParams.map .param)) args) ∧
        ∀ ψ, args.length = nP' + (D.ids 0 ψ).length)
    (hnp : ∃ L, nestPick caps cs = some (caps.nparams, L))
    (hpar : ∀ ψ, (D.params ψ).length = caps.nparams)
    (hsort : ∃ u, cv.type.resultSort = some u)
    (hclvl : ∀ nP' L, nestPick caps cs = some (nP', L) → ∀ j (hj : j < L.length),
      L[j].1.levelParams = cv.levelParams) : LfpOwn env D := by
  have hnc : ConLeche.nestContainer (envCtx env) T = nestPick caps cs := by
    rw [nestContainer_eq]
    show (match env.find? T with
      | some (.indInfo _ caps) => nestPick caps (env.consts.filterMap (ctorEntry T))
      | _ => none) = _
    rw [hf, hcs]
  refine ⟨fun c hc => ?_, fun c hc nP' hL => ?_, fun c hc => ?_, fun c hc j hj => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc j hj => ?_⟩
  · obtain rfl : c = 0 := by omega
    rw [hm, hnc]; exact hctors
  · obtain rfl : c = 0 := by omega
    rw [hm, hnc] at hL
    obtain ⟨h1, h2⟩ := hno nP' hL
    refine ⟨cv, caps, by rw [hm]; exact hf, h1, h2, fun mm hmm => ?_⟩
    obtain rfl : mm = 0 := by omega
    exact ⟨cv, caps, by rw [hm]; exact hf, rfl⟩
  · obtain rfl : c = 0 := by omega
    exact ⟨cv, caps, by rw [hm]; exact hf, hnd⟩
  · obtain rfl : c = 0 := by omega
    obtain ⟨nP', L, hL, hlen, hfj⟩ := hctors
    have hjL : j < L.length := by rw [hlen]; exact hj
    refine ⟨L[j].1, nP', L[j].2, hfj j hjL, ?_⟩
    rw [hm]
    exact hconcl nP' L hL j hjL
  · obtain rfl : c = 0 := by omega
    obtain ⟨L, hL⟩ := hnp
    exact ⟨cv, caps, L, by rw [hm]; exact hf, hpar, by rw [hm, hnc]; exact hL⟩
  · obtain rfl : c = 0 := by omega
    obtain ⟨u, hu⟩ := hsort
    exact ⟨cv, caps, u, by rw [hm]; exact hf, hu⟩
  · obtain rfl : c = 0 := by omega
    obtain ⟨nP', L, hL, hlen, hfj⟩ := hctors
    have hjL : j < L.length := by rw [hlen]; exact hj
    exact ⟨L[j].1, nP', L[j].2, cv, caps, hfj j hjL, by rw [hm]; exact hf, hclvl nP' L hL j hjL⟩

omit [SetTheory V] in
/-- **Ownership at a one-member block without constructors**, recorded
right after its former's cons. -/
theorem lfpOwn_former0 {env : Env} (hwf : ConLeche.EnvWF env) {c₀ : ConstantInfo}
    {cv : ConstantVal} {caps : ConLeche.IndCaps} (hc : c₀ = .indInfo cv caps)
    (hfresh : env.find? c₀.name = none) {D : LfpDatum V} (hk : D.k = 1)
    (hm : D.member 0 = c₀.name) (hn : D.nctors 0 = 0) (hnd : cv.levelParams.Nodup)
    (hp : ∀ ψ, (D.params ψ).length = caps.nparams) (hsort : ∃ u, cv.type.resultSort = some u) :
    LfpOwn ⟨c₀ :: env.consts⟩ D := by
  subst hc
  refine lfpOwn_one (cs := []) hk hm (ConLeche.Env.find?_cons_self _ _) ?_
    ⟨caps.nparams, [], rfl, hn.symm, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    (fun nP' h => by
      obtain rfl : caps.nparams = nP' := by
        simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h; exact h.1
      exact ⟨hnd, hp⟩) hnd
    (fun nP' L h j hj => by
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact absurd hj (Nat.not_lt_zero j))
    ⟨[], rfl⟩ hp hsort
    (fun nP' L h j hj => by
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact absurd hj (Nat.not_lt_zero j))
  show (_ :: env.consts).filterMap _ = []
  rw [List.filterMap_cons]
  exact ctorEntries_fresh hwf hfresh

/-- **Coverage** (L8's `lfp_cover`), except at the names `ex`; with
constructor ownership (lane COVERB). -/
structure LfpCover {env : Env} (mp : EnvModelM V μ env) (ex : List Name) : Prop where
  cover : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → n ∉ ex →
    n ≠ ConLeche.quotName → ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n
  nodup : ∀ D ∈ mp.lfpBlocks, D.names.Nodup
  len : ∀ D ∈ mp.lfpBlocks, D.names.length = D.k
  all : ∀ D ∈ mp.lfpBlocks, ∀ mm, mm < D.k → ∀ cv caps,
    env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names
  /-- no recorded member is pending -/
  fresh : ∀ D ∈ mp.lfpBlocks, ∀ mm, mm < D.k → D.member mm ∉ ex
  /-- every recorded block owns its members' constructors -/
  own : ∀ D ∈ mp.lfpBlocks, LfpOwn env D
  /-- every recorded block's operator is as wide as its members (no
  instance components: official's nested→mutual encoding is never
  mirrored, charter item 4) — the positivity model's frame monotonicity
  covers the members only (lane NESTIND, session 20) -/
  wid : ∀ D ∈ mp.lfpBlocks, D.N = D.k

/-- The empty environment is covered. -/
theorem lfpCover_empty : LfpCover (EnvModelM.empty V μ) [] where
  cover := fun _ _ _ h => by
    rw [show Env.empty.find? _ = none from rfl] at h; exact nomatch h
  nodup := fun _ hD => nomatch hD
  len := fun _ hD => nomatch hD
  all := fun _ hD => nomatch hD
  fresh := fun _ hD => nomatch hD
  own := fun _ hD => nomatch hD
  wid := fun _ hD => nomatch hD

/-- A recorded member is stored as an inductive former. -/
theorem LfpCover.member_find {env : Env} {mp : EnvModelM V μ env} {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) :
    ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) :=
  (mp.lfp_ok D hD).2.1.1 mm hmm

/-- A recorded member's former lists a non-empty block. -/
theorem LfpCover.all_ne {env : Env} {mp : EnvModelM V μ env} {ex : List Name}
    (h : LfpCover mp ex) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    {cv : ConstantVal} {caps : ConLeche.IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) : caps.all ≠ [] := by
  rw [h.all D hD mm hmm cv caps hf]
  intro h0
  have := h.len D hD
  rw [h0] at this
  simp at this
  omega

/-- **Transport** across an extension of the environment: every lookup
kept, the recorded list kept, the new inductives exempt, the exemption
list growing only by names fresh below, and every stored name's
constructor list kept. -/
theorem LfpCover.ext {env env' : Env} {mp : EnvModelM V μ env}
    {mp' : EnvModelM V μ env'} {ex ex' : List Name} (h : LfpCover mp ex)
    (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hfwd : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hback : ∀ n cv caps, env'.find? n = some (.indInfo cv caps) → n ∉ ex' →
      n ≠ ConLeche.quotName → env.find? n = some (.indInfo cv caps) ∧ n ∉ ex)
    (hex' : ∀ n ∈ ex', n ∈ ex ∨ env.find? n = none)
    (hnc : ∀ C, (env.find? C).isSome = true → C ∉ ex →
      (∀ cv caps, env.find? C = some (.indInfo cv caps) → caps.all ≠ []) →
      ConLeche.nestContainer (envCtx env') C = ConLeche.nestContainer (envCtx env) C) :
    LfpCover mp' ex' where
  cover := fun n cv caps hf hn hq => by
    obtain ⟨hf0, hn0⟩ := hback n cv caps hf hn hq
    rw [hL]; exact h.cover n cv caps hf0 hn0 hq
  nodup := fun D hD => h.nodup D (hL ▸ hD)
  len := fun D hD => h.len D (hL ▸ hD)
  all := fun D hD mm hmm cv caps hf => by
    rw [hL] at hD
    obtain ⟨cv0, caps0, hf0⟩ := LfpCover.member_find hD hmm
    rw [hfwd _ _ hf0] at hf
    injection hf with hf
    injection hf with _ hcaps
    subst hcaps
    exact h.all D hD mm hmm _ _ hf0
  fresh := fun D hD mm hmm hin => by
    rw [hL] at hD
    rcases hex' _ hin with h' | h'
    · exact h.fresh D hD mm hmm h'
    · obtain ⟨cv0, caps0, hf0⟩ := LfpCover.member_find hD hmm
      rw [hf0] at h'; exact nomatch h'
  own := fun D hD => by
    rw [hL] at hD
    refine (h.own D hD).mono hfwd fun c hc => hnc _ ?_ (h.fresh D hD c hc)
      (fun cv caps hf => h.all_ne hD hc hf)
    obtain ⟨cv0, caps0, hf0⟩ := LfpCover.member_find hD hc
    rw [hf0]; rfl
  wid := fun D hD => h.wid D (hL ▸ hD)

/-- **A fresh cons** keeping the recorded list: the exemption list may
grow by the new name, the new constant, if an inductive, is `Quot` or
exempt, and, if a constructor, its head is pending or a former with an
empty `all` (`Quot.mk`'s `Quot`).  A former's cons is `LfpCover.pend`. -/
theorem LfpCover.cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩} {ex ex' : List Name} (h : LfpCover mp ex)
    (hfresh : env.find? c₀.name = none) (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hex : ∀ n ∈ ex, n ∈ ex')
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName ∨ c₀.name ∈ ex')
    (hex' : ∀ n ∈ ex', n ∈ ex ∨ n = c₀.name)
    (hhead : ∀ cv nPc nF, c₀ = .ctorInfo cv nPc nF → ∀ C, (ctorEntry C c₀).isSome = true →
      C ∈ ex ∨ ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = []) :
    LfpCover mp' ex' := by
  refine h.ext hL (fun _ _ hf => findPreserved_cons hfresh hf) ?_ ?_ ?_
  · intro n cv caps hf hn hq
    rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · rename_i heq
      have hnm : c₀.name = n := by simpa using heq
      rcases hni cv caps (Option.some.inj hf) with h' | h'
      · exact absurd (hnm ▸ h') hq
      · exact absurd (hnm ▸ h') hn
    · exact ⟨hf, fun h' => hn (hex n h')⟩
  · intro n hn
    rcases hex' n hn with h' | rfl
    · exact Or.inl h'
    · exact Or.inr hfresh
  · intro C hC hCex hall
    refine nestContainer_cons hfresh hC ?_
    cases hent : ctorEntry C c₀ with
    | none => rfl
    | some _ =>
      obtain ⟨cv, nPc, nF, hc0⟩ : ∃ cv nPc nF, c₀ = .ctorInfo cv nPc nF := by
        cases c₀ with
        | ctorInfo cv a b => exact ⟨cv, a, b, rfl⟩
        | _ => simp [ctorEntry] at hent
      rcases hhead cv nPc nF hc0 C (by rw [hent]; rfl) with h' | ⟨cv, caps, hf, hnil⟩
      · exact absurd h' hCex
      · exact absurd hnil (hall cv caps hf)
/-- **A former's cons** (or any cons of a fresh non-constructor): the new
name joins the exemption list. -/
theorem LfpCover.pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩} {ex : List Name} (h : LfpCover mp ex)
    (hfresh : env.find? c₀.name = none) (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hhead : ∀ cv nPc nF, c₀ = .ctorInfo cv nPc nF → ∀ C, (ctorEntry C c₀).isSome = true →
      C ∈ ex ∨ ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = []) :
    LfpCover mp' (c₀.name :: ex) :=
  h.cons hfresh hL (fun _ h' => List.mem_cons_of_mem _ h')
    (fun _ _ _ => Or.inr List.mem_cons_self)
    (fun _ hn => (List.mem_cons.mp hn).elim Or.inr Or.inl) hhead

/-- **The block's record** (`EnvModelM.addLfp`, `declBlock`'s step at
its constructors' environment): the block's members leave the
exemption list, given its names distinct, one per member, listed as
their formers' `all`, and its constructors owned. -/
theorem LfpCover.addLfp {env : Env} {mp : EnvModelM V μ env} {ex : List Name}
    (h : LfpCover mp ex) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names)
    (hown : LfpOwn env D) (hwid : D.N = D.k := by rfl) :
    LfpCover (mp.addLfp D hL hst hrd hrdC) (ex.filter (· ∉ D.names)) where
  cover := fun n cv caps hf hn hq => by
    by_cases hD : n ∈ D.names
    · obtain ⟨mm, hmm, rfl⟩ := List.getElem_of_mem hD
      refine ⟨D, EnvModelM.mem_addLfp mp D hL hst hrd hrdC, mm, hlen ▸ hmm, ?_⟩
      simp [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm]
    · have hn0 : n ∉ ex := fun h' => hn (List.mem_filter.mpr ⟨h', by simpa using hD⟩)
      obtain ⟨D', hD', rest⟩ := h.cover n cv caps hf hn0 hq
      exact ⟨D', List.mem_cons_of_mem _ hD', rest⟩
  nodup := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hnd
    · exact h.nodup D' h'
  len := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hlen
    · exact h.len D' h'
  all := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hall
    · exact h.all D' h'
  fresh := fun D' hD' mm hmm hin => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · have hmem : D'.member mm ∈ D'.names := by
        simp only [LfpDatum.member, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (hlen ▸ hmm : mm < D'.names.length), Option.getD_some]
        exact List.getElem_mem _
      exact (List.mem_filter.mp hin).2 |> fun h2 => by simp [hmem] at h2
    · exact h.fresh D' h' mm hmm (List.mem_filter.mp hin).1
  own := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hown
    · exact h.own D' h'
  wid := fun D' hD' => by
    rcases List.mem_cons.mp hD' with rfl | h'
    · exact hwid
    · exact h.wid D' h'

/-- `LfpCover.addLfp` at a named result list. -/
theorem LfpCover.addLfp_to {env : Env} {mp : EnvModelM V μ env} {ex ex'' : List Name}
    (h : LfpCover mp ex) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names)
    (hown : LfpOwn env D)
    (hex : ex.filter (· ∉ D.names) = ex'') (hwid : D.N = D.k := by rfl) :
    LfpCover (mp.addLfp D hL hst hrd hrdC) ex'' :=
  hex ▸ h.addLfp D hL hst hrd hrdC hnd hlen hall hown hwid

/-- A one-member block's record empties the exemption list its former's
cons opened. -/
theorem filter_not_mem_self (n : Name) : [n].filter (· ∉ [n]) = [] := by
  simp

/-! ## The step shape -/

/-- **Coverage carried along a (partial) step**, from exemption list
`ex` at `mp` to `ex'` at a carrier at `env'`. -/
@[expose] def CoverTo {env : Env} (mp : EnvModelM V μ env) (ex : List Name) (env' : Env)
    (ex' : List Name) : Prop :=
  ∃ mp' : EnvModelM V μ env', LfpCover mp ex → LfpCover mp' ex'

/-- **The fold step's conclusion** (lane L8a; the module docstring). -/
abbrev CoverStep {env : Env} (mp : EnvModelM V μ env) (env' : Env) : Prop :=
  CoverTo mp [] env' []

theorem CoverTo.nonempty {env env' : Env} {mp : EnvModelM V μ env} {ex ex' : List Name}
    (h : CoverTo mp ex env' ex') : Nonempty (EnvModelM V μ env') :=
  h.elim fun mp' _ => ⟨mp'⟩

theorem CoverTo.refl {env : Env} (mp : EnvModelM V μ env) (ex : List Name) :
    CoverTo mp ex env ex := ⟨mp, id⟩

theorem CoverTo.trans {env env₁ env₂ : Env} {mp : EnvModelM V μ env}
    {ex ex₁ ex₂ : List Name} (h₁ : CoverTo mp ex env₁ ex₁)
    (h₂ : ∀ mp₁ : EnvModelM V μ env₁, CoverTo mp₁ ex₁ env₂ ex₂) : CoverTo mp ex env₂ ex₂ := by
  obtain ⟨mp₁, h₁⟩ := h₁
  obtain ⟨mp₂, h₂⟩ := h₂ mp₁
  exact ⟨mp₂, h₂ ∘ h₁⟩

/-- A step whose result is the input environment. -/
theorem CoverTo.of_eq {env env' : Env} {mp : EnvModelM V μ env} {ex : List Name}
    (h : env' = env) : CoverTo mp ex env' ex := h ▸ CoverTo.refl mp ex

/-- **The fold's form**: coverage at the input under a premise `P`
gives a carrier at the result with coverage under `P`. -/
theorem CoverTo.lift {env env' : Env} {mp : EnvModelM V μ env} {P : Prop}
    (h : CoverStep mp env') (hcov : P → LfpCover mp []) :
    ∃ mp' : EnvModelM V μ env', P → LfpCover mp' [] :=
  h.elim fun mp' h' => ⟨mp', fun hP => h' (hcov hP)⟩

/-! ## The cons funnel, keeping the recorded list -/

/-- **A funnel carrier, rebuilt with the input's recorded list** (the
same `base2`): the recorded clauses re-proved as the funnel does. -/
theorem EnvModelM.keepLfpOf {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀) (mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩)
    (hac : mp'.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    ∃ mk : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mk.base2 = mp'.base2 ∧ mk.lfpBlocks = mp.lfpBlocks := by
  have hbound := ConLeche.Semantics.envWF_constsBound mp.base2.wf
  have hok := mp.lfp_ok_transport (acval' := acvalWith mp.base2.acval c₀.name A)
    (fun _ _ hf _ => findPreserved_cons hfresh hf)
    (fun n _ hf _ => acvalWith_ne fun h => by
      rw [h, hfresh] at hf; exact nomatch hf)
    (fun _ _ _ hf ψ _ hta =>
      have hm := ConLeche.Semantics.Env.find?_mem hf
      denoteMeta_cons_mono hfresh (hcross.type hm) ψ 0 (hbound _ hm).1 hta)
    (fun _ _ _ _ hf ψ _ hta =>
      have hm := ConLeche.Semantics.Env.find?_mem hf
      denoteMeta_cons_mono hfresh (hcross.type hm) ψ 0 (hbound _ hm).1 hta)
    (fun _ _ _ _ hf _ _ _ hA ψ _ hta =>
      have hm := ConLeche.Semantics.Env.find?_mem hf
      denoteMeta_cons_mono hfresh (canonCrest_consCrossAt (hcross.type hm) hA) ψ _
        (canonCrest_constsBound (hbound _ hm).1 hA) hta)
  exact ⟨{ mp' with
    lfpBlocks := mp.lfpBlocks
    lfp_ok := by rw [hac]; exact hok }, rfl, rfl⟩

/-- **The cons funnel's carrier, with the input's recorded list.**  The
funnel (`declStep_preserves_of_cons*`, and every basis variant) builds
`lfpBlocks := mp.lfpBlocks` but exposes only its leaf; this rebuilds a
carrier at the same leaf with the input's list, re-proving the recorded
clauses exactly as the funnel does (`lfp_ok_transport` at a fresh cons
whose head is no projection table, or a table whose slots no stored
piece mentions). -/
theorem EnvModelM.keepLfp {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      mp'.lfpBlocks = mp.lfpBlocks := by
  obtain ⟨mp', hac⟩ := h
  obtain ⟨mk, hb, hL⟩ := EnvModelM.keepLfpOf hfresh hcross mp' hac
  exact ⟨mk, by rw [hb]; exact hac, hL⟩

/-- **A fresh cons, through the funnel, carrying coverage** and keeping
the funnel's leaf (the chains that read it downstream: `Eq`'s). -/
theorem coverA_cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex ex' : List Name}
    (hfresh : env.find? c₀.name = none)
    (hex : ∀ n ∈ ex, n ∈ ex')
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName ∨ c₀.name ∈ ex')
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hex' : ∀ n ∈ ex', n ∈ ex ∨ n = c₀.name := by intro _ h; exact Or.inl h)
    (hhead : ∀ cv nPc nF, c₀ = .ctorInfo cv nPc nF → ∀ C, (ctorEntry C c₀).isSome = true →
      C ∈ ex ∨ ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = [] := by
      intro _ _ _ h; exact nomatch h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      (LfpCover mp ex → LfpCover mp' ex') := by
  obtain ⟨mp', hac, hL⟩ := EnvModelM.keepLfp hfresh (ConsCrossEnv.ofNtc hntc) h
  exact ⟨mp', hac, fun hc => hc.cons hfresh hL hex hni hex' hhead⟩

/-- **A fresh non-inductive cons** (or `Quot`'s), through the funnel:
coverage at the same exemption list. -/
theorem coverTo_cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (hni : ∀ cv caps, c₀ = .indInfo cv caps → c₀.name = ConLeche.quotName)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hhead : ∀ cv nPc nF, c₀ = .ctorInfo cv nPc nF → ∀ C, (ctorEntry C c₀).isSome = true →
      C ∈ ex ∨ ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = [] := by
      intro _ _ _ h; exact nomatch h) :
    CoverTo mp ex ⟨c₀ :: env.consts⟩ ex :=
  (coverA_cons hfresh (fun _ h => h) (fun cv caps h' => Or.inl (hni cv caps h')) h hntc
    (fun _ h => Or.inl h) hhead).imp
    fun _ h => h.2

/-- **A former's cons**, through the funnel: its name joins the
exemption list. -/
theorem coverA_pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hnct : ∀ cv nPc nF, c₀ ≠ .ctorInfo cv nPc nF := by intro _ _ _ h; exact nomatch h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A ∧
      (LfpCover mp ex → LfpCover mp' (c₀.name :: ex)) :=
  coverA_cons hfresh (fun _ h => List.mem_cons_of_mem _ h)
    (fun _ _ _ => Or.inr List.mem_cons_self) h hntc
    (fun _ hn => (List.mem_cons.mp hn).elim Or.inr Or.inl)
    (fun _ _ _ h => absurd h (hnct _ _ _))

/-- **A former's cons**, through the funnel, as a `CoverTo`. -/
theorem coverTo_pend {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {ex : List Name}
    (hfresh : env.find? c₀.name = none)
    (h : ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl := by intro _ h; exact nomatch h)
    (hnct : ∀ cv nPc nF, c₀ ≠ .ctorInfo cv nPc nF := by intro _ _ _ h; exact nomatch h) :
    CoverTo mp ex ⟨c₀ :: env.consts⟩ (c₀.name :: ex) :=
  (coverA_pend hfresh h hntc hnct).imp fun _ h => h.2

/-- **A block's record** on a carrier whose leaf is `acval`: the block's
names leave the exemption list (`hex` names the result). -/
theorem coverTo_addLfp {env env' : Env} {mp : EnvModelM V μ env} {ex ex' ex'' : List Name}
    {acval : Name → (Name → Nat) → AnnotTerm}
    (h : ∃ mp' : EnvModelM V μ env', mp'.base2.acval = acval ∧
      (LfpCover mp ex → LfpCover mp' ex'))
    (D : LfpDatum V) (hL : LfpClause acval D) (hst : LfpStored env' D)
    (hrd : LfpReads acval env' D) (hrdC : LfpCtorReads acval env' D)
    (hnd : D.names.Nodup) (hlen : D.names.length = D.k)
    (hall : ∀ mm, mm < D.k → ∀ cv caps,
      env'.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names)
    (hown : LfpOwn env' D)
    (hex : ex'.filter (· ∉ D.names) = ex'') (hwid : D.N = D.k := by rfl) :
    CoverTo mp ex env' ex'' := by
  obtain ⟨mp', hac, hc⟩ := h
  subst hac hex
  exact ⟨mp'.addLfp D hL hst hrd hrdC, fun h0 => (hc h0).addLfp D _ _ _ _ hnd hlen hall hown hwid⟩

/-- A one-member block's names are distinct. -/
theorem nodup_one (n : Name) : [n].Nodup := by simp

omit [SetTheory V] in
/-- `LfpCover.addLfp`'s `all` premise at a one-member block: its former's
stored `all`. -/
theorem lfpAll_one {env' : Env} {D : LfpDatum V} {n : Name} {c : ConstantInfo} (hk : D.k = 1)
    (hm : D.member 0 = n) (hf0 : env'.find? n = some c)
    (hc : ∀ cv caps, c = .indInfo cv caps → caps.all = D.names) :
    ∀ mm, mm < D.k → ∀ cv caps,
      env'.find? (D.member mm) = some (.indInfo cv caps) → caps.all = D.names := by
  intro mm hmm cv caps hf
  obtain rfl : mm = 0 := by omega
  rw [hm, hf0] at hf
  exact hc cv caps (Option.some.inj hf)

end ConLeche.Model
