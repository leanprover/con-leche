module

public import ConLeche.Model.Inductives.StructRecSpine
public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.NestedCopyRewrite
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The reading of a rewritten term (task #315, lane RW)

The nested elimination's `replaceAllNested`
(`ConLeche/Kernel/Inductives/NestedElim.lean`) rewrites a container
occurrence `J Ds is` to its mimic `Jaux p⃗ is`.  The tree reads that
walk syntactically — the `replace{All,If}Nested_*` family in
`Verify/Inductives/NestedCopyRewrite.lean` — and nowhere semantically:
no theorem there relates a rewritten term to `denoteMeta`.  The model
needs exactly that, because the pins' components in REWRITTEN form
(K.59, `nestedPinCompsOk`) occur in no constructor the auxiliary block
ever checks: the rewrite DROPS `Ds`, so the auxiliary block's own
type-checks never see them and the recomputation of K.59 is the only
place they exist.

Three things live here.

* **`RewriteRel`** — an `Expr`-level relation between the input and the
  output of the walk: congruence at every former, plus one `fire` case
  `J Ds ↦ Jaux p⃗` at a pin (the occurrence's INDICES are taken by the
  ordinary `app` congruence, since the walk copies them unchanged, so
  `fire` needs no list relation of its own).  It is produced from a run
  of `replaceAllNested` by `replaceAllNested_rel`, an induction in the
  landed `replaceAllNested_unchanged_or_aux`/`_frame` idiom, and it is
  closed under `Expr.instantiate1` of related terms
  (`RewriteRel.instantiate1`) — which is what the transport needs,
  because `denoteMeta` OPENS a binder with `.fvar d ty` while the walk
  descends closed and with a REWRITTEN domain, so the two sides open at
  different `.fvar` types.  `RewriteRel.fvar` relates an `.fvar` to
  itself at an arbitrary stored type, which is sound because
  `denoteMeta` reads an `.fvar` by its index alone.

  A RELATION on `Expr`: no new `AnnotTerm` former, no second
  interpreter, no new substitution API — the derived-term-formers
  ruling is respected.  The walk's own `liftLooseBVars` closure is not
  needed at all: this tree's `Expr.instantiate1` does not lift its
  replacement (`ConLeche/Kernel/ExprOps.lean`), so the `bvar` step
  consumes the related pair directly.

* **The transport** `denoteMeta_of_rewriteRel`: a related pair's
  readings exist together, and the right one is the left one with every
  FIRED position replaced by the reading of the planted mimic —
  `ReadRel (PlantRead …)`, the annotation-level mirror of the same
  congruence.  Stated at ONE environment: the change of environment
  (the members' formers' `ENV₁` to the auxiliary formers' `ENVA`) is a
  separate, landed crossing (`prefixCross_of`, `denoteMeta_env_mono`),
  and composing the two is the consumer's one line.  The plant's own
  reading is `plantRead` — and at the elimination's parameter spine it
  is `AnnotTerm.mkAppN (acval A ψ') (paramBvarsAt nP d)` on the nose
  (`plantRead_paramBvars`), which is `auxTargetRead`'s shape.

* **The producer** `candDsOf`/`candAsOf`: pin `q`'s candidate component
  family, the K.59 rewrites read at the auxiliary model and interpreted
  at the parameter frame, with `candDs_reads_of_run` for its reading.
  **Where recorded-ness enters**: `nestedPinCompsOk` (K.59) is the only
  record that the rewrites RUN and that the state does not grow — the
  second half is what makes the plants pins of the state the walk
  started at, hence names of the auxiliary block; and the copies'
  resolution at `ENVA` (`hfind` below) is `MutualFormersFacts.find`/
  `.lps` at the copy formers, which the run carries.  Neither is proved
  here: both are hypotheses, named at the statements that take them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level BinderMeta Literal ConstantInfo ConstantVal
  NestedParts ElimState NestedPin)

universe w

/-! ## The relation -/

/-- **THE REWRITE, AS A RELATION** (task #315 lane RW): congruence at
every `Expr` former, plus the one `fire` case the elimination performs
— a container's application to its parameter arguments `Ds` replaced by
the mimic `A` applied to the block's parameter openers.

`auxNames` is the list of names the plants may carry (the pins'
auxiliaries); `blvls` and `params` are the walk's own, fixed
throughout.

The occurrence's INDEX arguments do not appear: `replaceIfNested` copies
them unchanged, so `J Ds is ↦ A p⃗ is` is `fire` followed by `app`
congruence at each index (`RewriteRel.mkAppN`).

`fvar` relates an `.fvar` to itself at an ARBITRARY stored type.  That
is what makes the relation closed under the binder step of `denoteMeta`,
which opens the two sides with `.fvar d ty` and `.fvar d ty'`; it is
sound because `denoteMeta`'s `.fvar` clause reads the index alone. -/
inductive RewriteRel (auxNames : List Name) (blvls : List Level) (params : List Expr) :
    Expr → Expr → Prop
  | bvar (i : Nat) : RewriteRel auxNames blvls params (.bvar i) (.bvar i)
  | fvar (i : Nat) (ty ty' : Expr) :
      RewriteRel auxNames blvls params (.fvar i ty) (.fvar i ty')
  | sort (u : Level) : RewriteRel auxNames blvls params (.sort u) (.sort u)
  | const (n : Name) (us : List Level) :
      RewriteRel auxNames blvls params (.const n us) (.const n us)
  | lit (l : Literal) : RewriteRel auxNames blvls params (.lit l) (.lit l)
  | app {f f' a a' : Expr} :
      RewriteRel auxNames blvls params f f' → RewriteRel auxNames blvls params a a' →
      RewriteRel auxNames blvls params (.app f a) (.app f' a')
  | lam {ty ty' b b' : Expr} (m : BinderMeta) :
      RewriteRel auxNames blvls params ty ty' → RewriteRel auxNames blvls params b b' →
      RewriteRel auxNames blvls params (.lam ty b m) (.lam ty' b' m)
  | forallE {ty ty' b b' : Expr} (m : BinderMeta) :
      RewriteRel auxNames blvls params ty ty' → RewriteRel auxNames blvls params b b' →
      RewriteRel auxNames blvls params (.forallE ty b m) (.forallE ty' b' m)
  | letE {ty ty' v v' b b' : Expr} :
      RewriteRel auxNames blvls params ty ty' → RewriteRel auxNames blvls params v v' →
      RewriteRel auxNames blvls params b b' →
      RewriteRel auxNames blvls params (.letE ty v b) (.letE ty' v' b')
  | proj (s : Name) (i : Nat) {x x' : Expr} :
      RewriteRel auxNames blvls params x x' →
      RewriteRel auxNames blvls params (.proj s i x) (.proj s i x')
  | fire {A : Name} (I : Name) (us : List Level) (Ds : List Expr) :
      A ∈ auxNames →
      RewriteRel auxNames blvls params
        (Expr.mkAppN (.const I us) Ds) (Expr.mkAppN (.const A blvls) params)

namespace RewriteRel

variable {auxNames : List Name} {blvls : List Level} {params : List Expr}

/-- The relation is reflexive: no position fired. -/
theorem rfl' (auxNames : List Name) (blvls : List Level) (params : List Expr) :
    ∀ e : Expr, RewriteRel auxNames blvls params e e
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (rfl' _ _ _ f) (rfl' _ _ _ a)
  | .lam ty b m => .lam m (rfl' _ _ _ ty) (rfl' _ _ _ b)
  | .forallE ty b m => .forallE m (rfl' _ _ _ ty) (rfl' _ _ _ b)
  | .letE ty v b => .letE (rfl' _ _ _ ty) (rfl' _ _ _ v) (rfl' _ _ _ b)
  | .proj s i x => .proj s i (rfl' _ _ _ x)

/-- More admissible plants is a weaker relation. -/
theorem mono {as as' : List Name} (hsub : ∀ n ∈ as, n ∈ as') :
    ∀ {e e' : Expr}, RewriteRel as blvls params e e' → RewriteRel as' blvls params e e' := by
  intro e e' h
  induction h with
  | bvar i => exact .bvar i
  | fvar i ty ty' => exact .fvar i ty ty'
  | sort u => exact .sort u
  | const n us => exact .const n us
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam m _ _ ih1 ih2 => exact .lam m ih1 ih2
  | forallE m _ _ ih1 ih2 => exact .forallE m ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | proj s i _ ih => exact .proj s i ih
  | fire I us Ds hA => exact .fire I us Ds (hsub _ hA)

/-- An application spine's head travels; the arguments are unchanged. -/
theorem mkAppN : ∀ (as : List Expr) {f f' : Expr}, RewriteRel auxNames blvls params f f' →
    RewriteRel auxNames blvls params (Expr.mkAppN f as) (Expr.mkAppN f' as)
  | [], _, _, h => h
  | a :: as, _, _, h => mkAppN as (.app h (rfl' _ _ _ a))

/-- **THE RELATION IS CLOSED UNDER INSTANTIATION** (the binder step):
substituting related terms for the same variable keeps the pair
related.  The `fire` case needs the walk's parameters to be
`bvar`-closed — they are the block's parameter openers, a spine of
`.fvar`s — and nothing else; in particular no `liftLooseBVars` closure
is needed, because `Expr.instantiate1` does not lift its replacement. -/
theorem instantiate1 (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true)
    {v v' : Expr} (hv : RewriteRel auxNames blvls params v v') :
    ∀ {e e' : Expr}, RewriteRel auxNames blvls params e e' →
      ∀ j : Nat, RewriteRel auxNames blvls params (e.instantiate1 v j) (e'.instantiate1 v' j) := by
  intro e e' h
  induction h with
  | bvar i =>
    intro j
    show RewriteRel _ _ _
      (if i = j then v else if i > j then .bvar (i - 1) else .bvar i)
      (if i = j then v' else if i > j then .bvar (i - 1) else .bvar i)
    split
    · exact hv
    · split
      · exact .bvar _
      · exact .bvar _
  | fvar i ty ty' => intro j; exact .fvar i ty ty'
  | sort u => intro j; exact .sort u
  | const n us => intro j; exact .const n us
  | lit l => intro j; exact .lit l
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | lam m _ _ ih1 ih2 => intro j; exact .lam m (ih1 j) (ih2 (j + 1))
  | forallE m _ _ ih1 ih2 => intro j; exact .forallE m (ih1 j) (ih2 (j + 1))
  | letE _ _ _ ih1 ih2 ih3 => intro j; exact .letE (ih1 j) (ih2 j) (ih3 (j + 1))
  | proj s i _ ih => intro j; exact .proj s i (ih j)
  | fire I us Ds hA =>
    intro j
    rw [Expr.mkAppN_instantiate1, Expr.mkAppN_instantiate1]
    have hp : params.map (fun a => a.instantiate1 v' j) = params := by
      rw [List.map_congr_left (g := id) ?_, List.map_id]
      intro a ha
      exact Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le j) (hpb a ha))
    rw [hp]
    exact .fire I us _ hA

/-! ### THE REWRITE AT A `Π`, AND WHERE IT DID NOT FIRE (task #315 WIDE
(f3) step 5)

`CopyOrdTele`'s producer needs two readings of the relation that the
transport above did not.

* **a `Π` relates only to a `Π`, domain to domain.**  The `fire` case's
  two sides are APPLICATIONS of a constant, and a binder is neither, so
  the rewrite can no more create a `Π`-prefix than destroy one.  This is
  the half that makes the copy's tower the mint's;
* **where nothing fired, the two terms are `ErasedEq`.**  Every plant
  the walk makes is headed by one of the mimic names, so a subterm of
  the OUTPUT that mentions no mimic name is a subterm the walk did not
  touch — up to the `.fvar` types the congruence is allowed to move and
  the denotation never reads.  This is the half that makes the copy's
  telescope DOMAINS the mint's.

Together they say: at a field the block classified recursive or
reflexive, whose `Π`-prefix domains are member-free BY THE
CLASSIFICATION (`mutualPositivity`'s `forallE` arm makes a domain
mentioning a member `.negative`), the copy's recorded telescope is the
mint's own `Π`-prefix, domain for domain. -/

/-- **WHERE NOTHING FIRED, THE TWO TERMS ARE `ErasedEq`**: every plant
is an application of a mimic name, so an output that mentions none of
them was rebuilt and not rewritten.  The conclusion is `ErasedEq` and
not equality because the congruence may move a `.fvar`'s recorded type
(`RewriteRel.fvar`), which is exactly what `ErasedEq` forgets and what
`denoteMeta` never reads. -/
theorem erasedEq_of_noAux :
    ∀ {e e' : Expr}, RewriteRel auxNames blvls params e e' →
      (∀ A ∈ auxNames, e'.mentionsConst A = false) → Expr.ErasedEq e e' := by
  intro e e' h
  induction h with
  | bvar i => intro _; exact Expr.ErasedEq.rfl _
  | fvar i ty ty' => intro _; exact (_root_.rfl : i = i)
  | sort u => intro _; exact Expr.ErasedEq.rfl _
  | const n us => intro _; exact Expr.ErasedEq.rfl _
  | lit l => intro _; exact Expr.ErasedEq.rfl _
  | app _ _ ihf iha =>
    intro hm
    exact ⟨ihf fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).1,
      iha fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).2⟩
  | lam m _ _ ih1 ih2 =>
    intro hm
    exact ⟨_root_.rfl, ih1 fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).1,
      ih2 fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).2⟩
  | forallE m _ _ ih1 ih2 =>
    intro hm
    exact ⟨_root_.rfl, ih1 fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).1,
      ih2 fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    intro hm
    refine ⟨ih1 fun A hA => ?_, ih2 fun A hA => ?_, ih3 fun A hA => ?_⟩
    · exact (by simpa only [Expr.mentionsConst, Bool.or_eq_false_iff, and_assoc] using hm A hA :
        _ = false ∧ _ = false ∧ _ = false).1
    · exact (by simpa only [Expr.mentionsConst, Bool.or_eq_false_iff, and_assoc] using hm A hA :
        _ = false ∧ _ = false ∧ _ = false).2.1
    · exact (by simpa only [Expr.mentionsConst, Bool.or_eq_false_iff, and_assoc] using hm A hA :
        _ = false ∧ _ = false ∧ _ = false).2.2
  | proj s i _ ih =>
    intro hm
    exact ⟨_root_.rfl, _root_.rfl, ih fun A hA => (by
        simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using hm A hA :
          _ = false ∧ _ = false).2⟩
  | @fire A I us Ds hA =>
    intro hm
    have h1 : (Expr.mkAppN (.const A blvls) params).mentionsConst A = true :=
      mentionsConst_mkAppN_of_fn params (.const A blvls) (by simp [Expr.mentionsConst])
    rw [hm A hA] at h1
    exact nomatch h1

/-- **THE REWRITE DOES NOT MOVE A BINDER**: the `fire` clause's two
sides are APPLICATIONS of a constant, and a binder is neither, so at a
`Π` the only clause that applies is the congruence.  Stated on the
OUTPUT because the consumer holds the COPY (the walk's output) and
wants the MINT. -/
theorem forallE_inv' :
    ∀ {e e' : Expr}, RewriteRel auxNames blvls params e e' →
      ∀ {ty' bo' : Expr} {bm : BinderMeta}, e' = .forallE ty' bo' bm →
        ∃ ty bo, e = .forallE ty bo bm ∧
          RewriteRel auxNames blvls params ty ty' ∧
          RewriteRel auxNames blvls params bo bo' := by
  intro e e' h
  cases h with
  | forallE m hty hbo =>
    intro ty' bo' bm he
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      simpa only [Expr.forallE.injEq] using he
    exact ⟨_, _, rfl, hty, hbo⟩
  | fire I us Ds hA =>
    intro ty' bo' bm he
    have := congrArg Expr.getAppFn he
    rw [Expr.getAppFn_mkAppN] at this
    exact nomatch (this : Expr.const _ blvls = _)
  | _ => intro ty' bo' bm he; exact nomatch he

/-- **THE `Π`-PREFIX, OPENED ON BOTH SIDES** (task #315 WIDE (f3) step
5): the walk's OUTPUT and its INPUT open at the same count and the same
depth, their openers' recorded types are `ErasedEq`, and the two leaves
stay related — provided each of the OUTPUT's opener types carries no
mimic name.

That proviso is the classification's own: `mutualPositivity`'s
`forallE` arm answers `.negative` at a binder whose domain mentions a
member of the block, and the mimic names ARE members of the auxiliary
block, so a field the block classified recursive or reflexive has
member-free prefix domains and the rewrite cannot have touched them.

The openers themselves are `.fvar d ty` against `.fvar d ty'`, so they
differ exactly in the type the denotation never reads — which is why
the conclusion is `ErasedEq` and not equality, and why the two opened
bodies are related by `RewriteRel.instantiate1` rather than equal. -/
theorem openPisAtFvars_of_noAux
    (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true) :
    ∀ (n : Nat) {e e' : Expr} {d : Nat} {fvs' : List Expr} {o' : Expr},
      RewriteRel auxNames blvls params e e' →
      ConLeche.openPisAtFvars n e' d = some (fvs', o') →
      (∀ (k : Nat) (x : Expr), fvs'[k]? = some x →
        ∀ X ∈ auxNames, (Expr.fvarTypeD x).mentionsConst X = false) →
      ∃ fvs o, ConLeche.openPisAtFvars n e d = some (fvs, o) ∧
        fvs.length = n ∧ fvs'.length = n ∧
        (∀ (k : Nat) (x x' : Expr), fvs[k]? = some x → fvs'[k]? = some x' →
          Expr.ErasedEq (Expr.fvarTypeD x) (Expr.fvarTypeD x')) ∧
        RewriteRel auxNames blvls params o o' := by
  intro n
  induction n with
  | zero =>
    intro e e' d fvs' o' hrel hop _
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨[], e, _root_.rfl, _root_.rfl, _root_.rfl, by intro k x x' hx; simp at hx, hrel⟩
  | succ n ih =>
    intro e e' d fvs' o' hrel hop hno
    match e', hop with
    | .forallE ty' rest' mb, hop =>
      obtain ⟨ty, rest, rfl, hty, hrest⟩ := RewriteRel.forallE_inv' hrel _root_.rfl
      simp only [ConLeche.openPisAtFvars] at hop
      cases hq : ConLeche.openPisAtFvars n (rest'.instantiate1 (.fvar d ty')) (d + 1) with
      | none => rw [hq] at hop; exact nomatch hop
      | some q =>
        rw [hq] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        -- the head domain: the OUTPUT's carries no mimic name, so nothing fired in it
        have hty0 : Expr.ErasedEq ty ty' :=
          RewriteRel.erasedEq_of_noAux hty (by
            intro X hX
            exact hno 0 (.fvar d ty') _root_.rfl X hX)
        -- the tail, one opener down
        obtain ⟨fvs, o, hopE, hlen, hlen', hdoms, hleaf⟩ :=
          ih (d := d + 1) (RewriteRel.instantiate1 hpb (.fvar d ty ty') hrest 0)
            hq (by
              intro k x hx X hX
              exact hno (k + 1) x hx X hX)
        refine ⟨.fvar d ty :: fvs, o, ?_, by simp [hlen], by simp [hlen'], ?_, hleaf⟩
        · show (match ConLeche.openPisAtFvars n (rest.instantiate1 (.fvar d ty)) (d + 1) with
              | some (fvs, e) => some (Expr.fvar d ty :: fvs, e)
              | none => none) = _
          rw [hopE]
        · intro k x x' hx hx'
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
            subst hx; subst hx'
            exact hty0
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx hx'
            exact hdoms k x x' hx hx'

end RewriteRel

/-! ## The producer: a run of the walk gives the relation -/

section Producer

open ConLeche (replaceIfNested replaceAllNested nestedOccOk ElimState CheckError CheckM
  containerInfo? IndCaps ContainerInfo)

variable {env : Env} {blvls : List Level} {params : List Expr}
  {pbs₀ : List (Expr × BinderMeta)}

private theorem rrErr_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

private theorem rrNone_ne_some {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

local syntax "rr_throw" : tactic
local macro_rules
  | `(tactic| rr_throw) =>
    `(tactic| first
        | (exfalso; exact rrErr_ne_ok (by assumption))
        | (exfalso; exact rrNone_ne_some (by assumption)))

/-- An application spine splits at any prefix of its arguments. -/
theorem mkAppN_append : ∀ (as bs : List Expr) (f : Expr),
    Expr.mkAppN f (as ++ bs) = Expr.mkAppN (Expr.mkAppN f as) bs
  | [], _, _ => rfl
  | a :: as, bs, f => mkAppN_append as bs (.app f a)

/-- **THE OCCURRENCE TEST'S TWO VERDICTS**, re-proved here because the
landed `nestedOccOk_verdicts` is private to `NestedCopyRewrite`: a
`true` says some parameter argument mentions a name of the growing
list, and the `.ok` says none of them carries a loose bound variable. -/
private theorem occOk_verdicts {I : Name} {names : List Name} {nP : Nat}
    {args : List Expr} (h : ConLeche.nestedOccOk I names nP args = .ok true) :
    ((args.take nP).any fun a => names.any fun T => a.mentionsConst T) = true ∧
    (∀ a ∈ args.take nP, a.looseBVarsBounded 0 = true) := by
  unfold ConLeche.nestedOccOk at h
  dsimp only at h
  split at h
  · rr_throw
  · rename_i hcond
    simp only [Except.ok.injEq] at h
    refine ⟨h, ?_⟩
    rw [h, Bool.true_and] at hcond
    have hl : ((args.take nP).any fun a => !a.looseBVarsBounded 0) = false := by
      simpa using hcond
    intro a ha
    have := List.any_eq_false.mp hl a ha
    simpa using this

/-- **ONE FIRING, AS THE RELATION**: whenever `replaceIfNested`
replaces a term, the pair is related — the fired position is the
container's application to its parameter arguments and the plant is the
auxiliary of a pin of the resulting state. -/
theorem replaceIfNested_rel {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    RewriteRel (st'.pins.map (·.aux)) blvls params e e' := by
  obtain ⟨I, lvls, cv, caps, ci, hfn, hfind, hci, hnP, hocc⟩ := replaceIfNested_fire_inv h
  obtain ⟨hment, hloose⟩ := occOk_verdicts hocc
  have he : e = Expr.mkAppN (.const I lvls) e.getAppArgs := by
    rw [← hfn]; exact (Expr.mkAppN_getApp e).symm
  obtain ⟨q, st₁, hr, hqm, -⟩ :=
    replaceIfNested_occurrence he hfind hci hnP hment hloose h
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have key : RewriteRel (st'.pins.map (·.aux)) blvls params
      (Expr.mkAppN (Expr.mkAppN (.const I lvls) (e.getAppArgs.take ci.nP))
        (e.getAppArgs.drop ci.nP))
      (Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params) (e.getAppArgs.drop ci.nP)) :=
    RewriteRel.mkAppN _ (RewriteRel.fire I lvls _ (List.mem_map_of_mem hqm))
  rwa [← mkAppN_append, List.take_append_drop, ← he] at key

/-- **THE WALK PRODUCES THE RELATION** (task #315 lane RW): every run of
the top-down replace relates its input to its output, with the plants
among the resulting state's pins. -/
theorem replaceAllNested_rel :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      RewriteRel (st'.pins.map (·.aux)) blvls params e e' := by
  -- the two states a binary node threads, as a plant-name inclusion
  have hgrow : ∀ {sa sb : ElimState} {x y : Expr},
      replaceAllNested env blvls params pbs₀ sa x = .ok (y, sb) →
      ∀ n ∈ sa.pins.map (·.aux), n ∈ sb.pins.map (·.aux) := by
    intro sa sb x y hrun n hn
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hn
    exact List.mem_map_of_mem ((replaceAllNested_pins_prefix _ hrun).1.subset hz)
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
      · split at h
        · rr_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact replaceIfNested_rel heq
        · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    · split at h
      · rr_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact replaceIfNested_rel heq
      · split at h
        · rr_throw
        · rename_i f' st1 heq1
          split at h
          · rr_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .app ((ihf heq1).mono (hgrow heq2)) (iha heq2)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    · split at h
      · rr_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact replaceIfNested_rel heq
      · split at h
        · rr_throw
        · rename_i ty' st1 heq1
          split at h
          · rr_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .lam m ((ihty heq1).mono (hgrow heq2)) (ihb heq2)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    · split at h
      · rr_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact replaceIfNested_rel heq
      · split at h
        · rr_throw
        · rename_i ty' st1 heq1
          split at h
          · rr_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .forallE m ((ihty heq1).mono (hgrow heq2)) (ihb heq2)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    · split at h
      · rr_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact replaceIfNested_rel heq
      · split at h
        · rr_throw
        · rename_i ty' st1 heq1
          split at h
          · rr_throw
          · rename_i v' st2 heq2
            split at h
            · rr_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .letE
                (((ihty heq1).mono (hgrow heq2)).mono (hgrow heq3))
                ((ihv heq2).mono (hgrow heq3)) (ihb heq3)
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact RewriteRel.rfl' _ _ _ _
    · split at h
      · rr_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact replaceIfNested_rel heq
      · split at h
        · rr_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .proj s i (ihx heq1)

end Producer

/-! ## The annotation-level mirror -/

/-- **THE READING OF A PLANT**: an annotation term that is the reading,
at some depth, of a mimic applied to the walk's parameters.  The
predicate the transport's `fire` case lands in: at a fired position the
rewritten term's reading IS a planted mimic's. -/
def PlantRead (acval : Name → (Name → Nat) → AnnotTerm) (envA : Env) (φ : Name → Nat)
    (auxNames : List Name) (blvls : List Level) (params : List Expr) (u : AnnotTerm) : Prop :=
  ∃ (d : Nat) (A : Name), A ∈ auxNames ∧
    denoteMeta acval envA φ d (Expr.mkAppN (.const A blvls) params) = some u

/-- **THE REWRITE AT THE READINGS**: the annotation-level mirror of
`RewriteRel` — the same congruence, with the `fire` case replacing a
subreading by a plant's.  `ReadRel P ea ea'` is "`ea'` is `ea` with each
fired pin's reading replaced by the mimic's", stated positionally
rather than as a substitution operator, which `AnnotTerm` does not
have and which the derived-term-formers ruling would not allow us to
add. -/
inductive ReadRel (P : AnnotTerm → Prop) : AnnotTerm → AnnotTerm → Prop
  | refl (t : AnnotTerm) : ReadRel P t t
  | fire {t u : AnnotTerm} : P u → ReadRel P t u
  | app {f f' a a' : AnnotTerm} :
      ReadRel P f f' → ReadRel P a a' → ReadRel P (.app f a) (.app f' a')
  | lam (u : Nat) {ty ty' b b' : AnnotTerm} :
      ReadRel P ty ty' → ReadRel P b b' → ReadRel P (.lam u ty b) (.lam u ty' b')
  | pi (u v : Nat) {ty ty' b b' : AnnotTerm} :
      ReadRel P ty ty' → ReadRel P b b' → ReadRel P (.pi u v ty b) (.pi u v ty' b')
  | fst {e e' : AnnotTerm} : ReadRel P e e' → ReadRel P (.fst e) (.fst e')
  | snd {e e' : AnnotTerm} : ReadRel P e e' → ReadRel P (.snd e) (.snd e')

/-- The iterated field reading is a congruence for `ReadRel`. -/
theorem ReadRel.projAV {P : AnnotTerm → Prop} :
    ∀ (i : Nat) {e e' : AnnotTerm}, ReadRel P e e' →
      ReadRel P (ConLeche.Semantics.projAV i e) (ConLeche.Semantics.projAV i e')
  | 0, _, _, h => .fst h
  | i + 1, _, _, h => ReadRel.projAV i (.snd h)

/-! ## The transport -/

variable {env : Env} {φ : Name → Nat} {acval : Name → (Name → Nat) → AnnotTerm}

private theorem sizeB_pos : ∀ e : Expr, 0 < e.sizeB := by
  intro e; cases e <;> simp [Expr.sizeB]

private theorem denoteMeta_of_rewriteRel_aux {auxNames : List Name} {blvls : List Level}
    {params : List Expr}
    (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true)
    (hplant : ∀ (d : Nat) (A : Name), A ∈ auxNames →
      ∃ u, denoteMeta acval env φ d (Expr.mkAppN (.const A blvls) params) = some u) :
    ∀ (n : Nat) (e e' : Expr), e.sizeB ≤ n → RewriteRel auxNames blvls params e e' →
      ∀ (d : Nat) (ea : AnnotTerm), denoteMeta acval env φ d e = some ea →
        ∃ ea', denoteMeta acval env φ d e' = some ea' ∧
          ReadRel (PlantRead acval env φ auxNames blvls params) ea ea' := by
  intro n
  induction n with
  | zero =>
    intro e e' hle _ _ _ _
    exact absurd hle (by have := sizeB_pos e; omega)
  | succ n ih =>
    intro e e' hle h d ea hd
    cases h with
    | bvar i => rw [denoteMeta.eq_def] at hd; exact nomatch hd
    | fvar i ty ty' =>
      rw [denoteMeta_fvar] at hd
      exact ⟨_, denoteMeta_fvar acval d i ty', by rw [← Option.some.inj hd]; exact .refl _⟩
    | sort u => exact ⟨ea, hd, .refl _⟩
    | const m us => exact ⟨ea, hd, .refl _⟩
    | lit l => exact ⟨ea, hd, .refl _⟩
    | letE _ _ _ => rw [denoteMeta.eq_def] at hd; exact nomatch hd
    | @app f f' a a' hf ha =>
      simp only [Expr.sizeB] at hle
      obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hd
      obtain ⟨fa', hfa', hrf⟩ := ih f f' (by omega) hf d fa hfa
      obtain ⟨aa', haa', hra⟩ := ih a a' (by omega) ha d aa haa
      refine ⟨.app fa' aa', ?_, .app hrf hra⟩
      rw [denoteMeta_app, hfa', haa']; rfl
    | @lam ty ty' b b' m hty hb =>
      simp only [Expr.sizeB] at hle
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv hd
      obtain ⟨ta', hta', hrt⟩ := ih ty ty' (by omega) hty d ta hta
      obtain ⟨ba', hba', hrb⟩ := ih (b.instantiate1 (.fvar d ty)) (b'.instantiate1 (.fvar d ty'))
        (by rw [Expr.sizeB_instantiate1 _ rfl]; omega)
        (RewriteRel.instantiate1 hpb (RewriteRel.fvar d ty ty') hb 0) (d + 1) ba hba
      refine ⟨.lam (pwBit φ m.pw) ta' ba', ?_, .lam _ hrt hrb⟩
      rw [denoteMeta_lam, hta', hba']; rfl
    | @forallE ty ty' b b' m hty hb =>
      simp only [Expr.sizeB] at hle
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hd
      obtain ⟨ta', hta', hrt⟩ := ih ty ty' (by omega) hty d ta hta
      obtain ⟨ba', hba', hrb⟩ := ih (b.instantiate1 (.fvar d ty)) (b'.instantiate1 (.fvar d ty'))
        (by rw [Expr.sizeB_instantiate1 _ rfl]; omega)
        (RewriteRel.instantiate1 hpb (RewriteRel.fvar d ty ty') hb 0) (d + 1) ba hba
      refine ⟨.pi 0 (pwBit φ m.pw) ta' ba', ?_, .pi _ _ hrt hrb⟩
      rw [denoteMeta_forallE, hta', hba']; rfl
    | @proj s i x x' hx =>
      simp only [Expr.sizeB] at hle
      obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv hd
      obtain ⟨ia', hia', hri⟩ := ih x x' (by omega) hx d ia hia
      rcases hcase with ⟨entry, hfp, rfl⟩ | ⟨hfp, hdec⟩
      · refine ⟨ConLeche.Semantics.projAV (i + entry.off) ia', ?_, ReadRel.projAV _ hri⟩
        rw [denoteMeta_proj, hia']
        show (match env.findProj? s i with
          | some e => some (ConLeche.Semantics.projAV (i + e.off) ia')
          | none => AnnotTerm.projPair? i ia') = _
        rw [hfp]
      · rcases i with _ | _ | i
        · simp only [AnnotTerm.projPair?, Option.some.injEq] at hdec
          refine ⟨.fst ia', ?_, by rw [← hdec]; exact .fst hri⟩
          rw [denoteMeta_proj_pair _ _ _ _ _ hfp, hia']; rfl
        · simp only [AnnotTerm.projPair?, Option.some.injEq] at hdec
          refine ⟨.snd ia', ?_, by rw [← hdec]; exact .snd hri⟩
          rw [denoteMeta_proj_pair _ _ _ _ _ hfp, hia']; rfl
        · exact nomatch hdec
    | fire I us Ds hA =>
      obtain ⟨u, hu⟩ := hplant d _ hA
      exact ⟨u, hu, .fire ⟨d, _, hA, hu⟩⟩

/-- **THE TRANSPORT** (task #315 lane RW, the missing object): a
rewritten term denotes whenever the term it rewrites does, and its
reading is the original's with every FIRED position replaced by the
reading of the planted mimic.

Stated at one environment and one model: the environment change from
the members' formers' `ENV₁` to the auxiliary formers' `ENVA` is the
landed crossing (`prefixCross_of`), and the consumer composes the two.

The hypotheses are exactly two, and both are about the walk's own data:
the parameters are `bvar`-closed (they are `openPisAtFvars`' `.fvar`
spine), and every admissible plant reads — `plantRead` derives the
second from the copies' resolution at the environment. -/
theorem denoteMeta_of_rewriteRel {auxNames : List Name} {blvls : List Level}
    {params : List Expr}
    (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true)
    (hplant : ∀ (d : Nat) (A : Name), A ∈ auxNames →
      ∃ u, denoteMeta acval env φ d (Expr.mkAppN (.const A blvls) params) = some u)
    {e e' : Expr} (h : RewriteRel auxNames blvls params e e')
    {d : Nat} {ea : AnnotTerm} (hd : denoteMeta acval env φ d e = some ea) :
    ∃ ea', denoteMeta acval env φ d e' = some ea' ∧
      ReadRel (PlantRead acval env φ auxNames blvls params) ea ea' :=
  denoteMeta_of_rewriteRel_aux hpb hplant e.sizeB e e' Nat.le.refl h d ea hd

/-! ## The plant's own reading -/

/-- **A PLANTED MIMIC DENOTES**: the plant is a constant the
environment stores, applied to the walk's parameters, and the
parameters are `.fvar`s, which read at every depth. -/
theorem plant_denotes {blvls : List Level} {params : List Expr} {A : Name}
    {ci : ConstantInfo} (hf : env.find? A = some ci)
    (hlen : blvls.length = ci.toConstantVal.levelParams.length)
    (hparams : ∀ a ∈ params, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty) (d : Nat) :
    ∃ u, denoteMeta acval env φ d (Expr.mkAppN (.const A blvls) params) = some u := by
  obtain ⟨vs, hvs⟩ := denoteMetaSpine_of_all (acval := acval) (env := env) (φ := φ) (d := d)
    params (fun a ha => by
      obtain ⟨i, ty, rfl⟩ := hparams a ha
      exact ⟨_, denoteMeta_fvar acval d i ty⟩)
  exact ⟨_, denoteMeta_mkAppN_of params (denoteMeta_const hf hlen) hvs⟩

/-- **AND IT READS AS THE AUXILIARY TARGET**: at the elimination's own
parameter spine — `openPisAtFvars`' same-index `.fvar`s — the plant's
reading is the mimic's leaf applied to the parameter variables, the
shape `auxTargetRead` is built from (`NestedPinLeafAll.lean`).  So a
fired position's reading is a carrier of the auxiliary block, on the
nose, with no further computation. -/
theorem plant_reads {blvls : List Level} {params : List Expr} {A : Name} {nP : Nat}
    {ci : ConstantInfo} (hf : env.find? A = some ci)
    (hlen : blvls.length = ci.toConstantVal.levelParams.length)
    (hidx : ∀ (j : Nat) (x : Expr), params[j]? = some x → ∃ ty, x = Expr.fvar j ty)
    (hplen : params.length = nP) (d : Nat) :
    denoteMeta acval env φ d (Expr.mkAppN (.const A blvls) params)
      = some (AnnotTerm.mkAppN (acval A (Level.substFn φ ci.toConstantVal.levelParams blvls))
          (paramBvarsAt nP d)) := by
  have hsp : DenoteMetaSpine acval env φ d params (paramBvarsAt nP d) := by
    have h := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) d params 0
      (fun k x hx => by
        obtain ⟨ty, hty⟩ := hidx k x hx
        exact ⟨ty, by rw [hty, Nat.zero_add]⟩)
    rw [hplen] at h
    have heq : ((List.range nP).map fun k => AnnotTerm.bvar (d - 1 - (0 + k)))
        = paramBvarsAt nP d := by
      unfold paramBvarsAt
      exact List.map_congr_left (fun k _ => by rw [Nat.zero_add])
    rwa [heq] at h
  exact denoteMeta_mkAppN_of params (denoteMeta_const hf hlen) hsp

/-! ## The candidate component family -/

/-- **PIN `q`'S CANDIDATE COMPONENTS, AS READINGS**: K.59's rewritten
components, read at the AUXILIARY formers' model — the family the
entry theorem's step (iii) is stated at.  Total, in `pinOf`'s style
(`NestedPins.lean`): the `getD` is discharged by `candDs_reads`. -/
def candDsOf (acval : Name → (Name → Nat) → AnnotTerm) (envA : Env) (nP : Nat)
    (comps : List (List Expr)) (ψ : Name → Nat) (q : Nat) : List AnnotTerm :=
  (comps.getD q []).map fun c => (denoteMeta acval envA ψ nP c).getD default

/-- **PIN `q`'S CANDIDATE COMPONENTS, AS VALUES**: `candDsOf`
interpreted at a frame fitting the block's parameters — the `as : Nat →
List V` that `pinLfpAt`, `pins_le_of_declOrder` and `pinLfpAt_le`
(`NestedPinLeafAll.lean`, `NestedFit.lean`) take as given and that
nothing produced. -/
noncomputable def candAsOf (V : Type w) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (envA : Env) (nP : Nat)
    (comps : List (List Expr)) (ψ : Name → Nat) (ρp : Nat → V) (q : Nat) : List V :=
  (candDsOf acval envA nP comps ψ q).map (interp V ρp)

/-- Every entry of a spine reading gives the spine's `getD` reading. -/
private theorem denoteMetaSpine_map_getD {d : Nat} :
    ∀ (as : List Expr), (∀ a ∈ as, ∃ v, denoteMeta acval env φ d a = some v) →
      DenoteMetaSpine acval env φ d as
        (as.map fun a => (denoteMeta acval env φ d a).getD default)
  | [], _ => .nil
  | a :: as, h => by
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    exact .cons (by simp only [hv, Option.getD_some])
      (denoteMetaSpine_map_getD as (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- An `Option`-`mapM` keeps its list's length (`NestedElimInv`'s
`mapM_option_length`, re-proved here: that module is not re-exported
through this one's imports). -/
private theorem mapM_option_len {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_option_len hbs]

/-- A prefix of its own length is the whole list — K.59's no-growth
clause, read as "the re-run's pin table IS the elimination's". -/
private theorem pins_eq_of_no_growth {l l' : List NestedPin}
    (hpre : l <+: l') (hlen : l'.length = l.length) : l' = l := by
  obtain ⟨t, ht⟩ := hpre
  have hnil : t = [] := by
    have hl := congrArg List.length ht
    simp only [List.length_append] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [← ht, hnil, List.append_nil]

/-- **K.59 AT ONE PIN**, with the two facts the reading needs: the
recorded component list has the pin's spine's length, and at every
position the elimination's own walk runs at the FINAL state and leaves
the pin table untouched. -/
theorem nestedPinComps_at {p : NestedParts} {st : ElimState}
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)} {comps : List (List Expr)}
    (hrw : ConLeche.nestedPinCompRewrites env p st params pbs₀ = some comps)
    {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    ∃ cs, comps[q]? = some cs ∧ cs.length = qn.pin.getAppArgs.length ∧
      ∀ (i : Nat) (c : Expr), qn.pin.getAppArgs[i]? = some c →
        ∃ (c' : Expr) (st' : ElimState),
          ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st c
            = .ok (c', st') ∧ cs[i]? = some c' ∧ st'.pins = st.pins := by
  unfold ConLeche.nestedPinCompRewrites at hrw
  obtain ⟨cs, hcs, hstep⟩ := ConLeche.mapM_option_inv hrw q qn hq
  refine ⟨cs, hcs, mapM_option_len hstep, ?_⟩
  intro i c hc
  obtain ⟨c', hc', hstep'⟩ := ConLeche.mapM_option_inv hstep i c hc
  refine ⟨c', ?_⟩
  cases hr : ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st c with
  | error e => simp only [hr] at hstep'; exact nomatch hstep'
  | ok r =>
    obtain ⟨c'', st'⟩ := r
    simp only [hr] at hstep'
    split at hstep'
    · rename_i hlen
      simp only [Option.some.injEq] at hstep'
      subst hstep'
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      exact ⟨st', rfl, hc',
        pins_eq_of_no_growth (ConLeche.replaceAllNested_pins_prefix _ hr).1 hlen.2⟩
    · exact nomatch hstep'

/-- **THE CANDIDATE COMPONENTS READ** (task #315 lane RW, obligation
(i)): at every pin, K.59's rewritten components denote at the
auxiliary formers' environment, so `candDsOf` is a reading spine and
`candAsOf` is the family `pinLfpAt` wants.

**Where recorded-ness enters.**  `hrw` is K.59 (`nestedPinCompsOk`),
and BOTH of its halves are used: the rewrite RUNS at every component
(so `replaceAllNested_rel` has a run to read), and the state does not
GROW (so the plants are pins of the table the elimination finished
with, which is what `hfind` is stated at).  `hfind` is the copies'
resolution at `ENVA` — `MutualFormersFacts.find` and `.lps` at the copy
formers, which `NestedPinsRun` carries.  `hparams` is
`openPisAtFvars`' shape at `nestedRewriteData`'s spine.  `hDs` is the
components' UNREWRITTEN reading, `NestedPinSynFacts.pinDs` composed
with the prefix crossing. -/
theorem candDs_reads {envA : Env} {p : NestedParts} {st : ElimState} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)} {comps : List (List Expr)}
    (hrw : ConLeche.nestedPinCompRewrites env p st params pbs₀ = some comps)
    (hparams : ∀ a ∈ params, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty)
    (hfind : ∀ qn ∈ st.pins, ∃ ci : ConstantInfo, envA.find? qn.aux = some ci ∧
      (p.lps.map Level.param).length = ci.toConstantVal.levelParams.length)
    {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn)
    (hDs : ∀ c ∈ qn.pin.getAppArgs, ∃ ca, denoteMeta acval envA φ nP c = some ca) :
    DenoteMetaSpine acval envA φ nP (comps.getD q [])
      (candDsOf acval envA nP comps φ q) := by
  obtain ⟨cs, hcs, hlen, hstep⟩ := nestedPinComps_at hrw hq
  have hgetD : comps.getD q [] = cs := by
    rw [List.getD_eq_getElem?_getD, hcs]; rfl
  have hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, ty, rfl⟩ := hparams a ha
    rfl
  -- every plant of the elimination's own table reads at the auxiliary environment
  have hplant : ∀ (d : Nat) (A : Name), A ∈ st.pins.map (·.aux) →
      ∃ u, denoteMeta acval envA φ d
        (Expr.mkAppN (.const A (p.lps.map Level.param)) params) = some u := by
    intro d A hA
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hA
    obtain ⟨ci, hci, hcl⟩ := hfind z hz
    exact plant_denotes hci hcl hparams d
  unfold candDsOf
  rw [hgetD]
  refine denoteMetaSpine_map_getD cs ?_
  intro c' hc'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc'
  have hics : i < cs.length := by
    rcases Nat.lt_or_ge i cs.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hi; exact nomatch hi
  have hilt : i < qn.pin.getAppArgs.length := by omega
  obtain ⟨c, hc⟩ : ∃ c, qn.pin.getAppArgs[i]? = some c :=
    ⟨_, List.getElem?_eq_getElem hilt⟩
  obtain ⟨c'', st', hrun, hcsi, hpins⟩ := hstep i c hc
  have hceq : c'' = c' := Option.some.inj (hcsi.symm.trans hi)
  rw [hceq] at hrun
  have hrel : RewriteRel (st.pins.map (·.aux)) (p.lps.map Level.param) params c c' := by
    have := replaceAllNested_rel c hrun
    rwa [hpins] at this
  obtain ⟨ca, hca⟩ := hDs c (List.mem_of_getElem? hc)
  obtain ⟨ca', hca', -⟩ := denoteMeta_of_rewriteRel hpb hplant hrel hca
  exact ⟨ca', hca'⟩

end ConLeche.Model
