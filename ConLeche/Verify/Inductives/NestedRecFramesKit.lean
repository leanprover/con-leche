module

public import ConLeche.Verify.Inductives.NestedRecWalk
import ConLeche.Verify.Inductives.StructRec

public section

/-!
# The frames' syntactic kit (task #315, M7-2, PLAN-M7 §1e)

Two facts the restored recursor types' FRAMES need of the syntax, and
nothing else does:

* `mutualRecTy_paramPrefix` (A) — **a generated recursor type's
  parameter prefix is the FIRST former's**: `mutualRecTy` builds its
  outermost `nP` binders by `Expr.replacePisPw` over `f₀.tty`, which
  keeps every domain and resets only the binder data, so the two
  telescopes' domains coincide below `nP`;
* `AuxAppsOk.forallE_inv`/`AuxAppsOk_stripPis_dom` (the walk's shape,
  inverted along a `∀`-telescope) — the shape at depth `0` of a body
  gives the shape at depth `i` of its `i`-th binder domain, which is
  what the reading law (`denoteMeta_restoreWalk`) asks of each binder
  of a recursor type below its parameter prefix.
-/

namespace ConLeche

/-! ## A — the recursor type's parameter prefix -/

/-- A `replacePisPw` walk that succeeds has walked a `∀`-telescope. -/
theorem replacePisPw_stripPis_of {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr}, Expr.replacePisPw pw k e b = some r →
      ∃ (bs : List (Expr × BinderMeta)) (body : Expr), e.stripPis k = some (bs, body)
  | 0, e, _, _, _ => ⟨[], e, rfl⟩
  | k + 1, e, b, r, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', -⟩ := h
      obtain ⟨bs, body, hs⟩ := replacePisPw_stripPis_of k hr'
      exact ⟨(ty, m) :: bs, body, by simp only [Expr.stripPis, hs, Option.map_some]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h
    | .app _ _, h | .lam _ _ _, h | .letE _ _ _, h | .lit _, h
    | .proj _ _ _, h => simp [Expr.replacePisPw] at h

/-- **THE GENERATED RECURSOR TYPE'S PARAMETER PREFIX IS THE FIRST
FORMER'S** (PLAN-M7 §1e A): official spells every member's recursor
over `m_params`, the first former's parameter binders, and
`mutualRecTy` does the same — its outermost `nP` binders are
`Expr.replacePisPw pw nP f₀.tty _`, which keeps the domains and resets
only the binder data.  So the recursor type and the first former's
type strip `nP` binders with the SAME domains. -/
theorem mutualRecTy_paramPrefix {lps : List Name} {elim : Name} {large : Bool} {nP : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {m : Nat} {ty : Expr}
    {f₀ : MutualFormer}
    (hty : mutualRecTy lps elim large nP formers ctors m = some ty)
    (hf₀ : formers[0]? = some f₀) :
    ∃ (pbsA pbsR : List (Expr × BinderMeta)) (bodyF rest : Expr),
      f₀.tty.stripPis nP = some (pbsA, bodyF) ∧ ty.stripPis nP = some (pbsR, rest) ∧
      pbsR.map (·.1) = pbsA.map (·.1) := by
  unfold mutualRecTy at hty
  rw [hf₀] at hty
  cases hfm : formers[m]? with
  | none => rw [hfm] at hty; exact nomatch hty
  | some f =>
    rw [hfm] at hty
    simp only [Option.bind_eq_some_iff] at hty
    obtain ⟨q, -, major, -, minors, -, motives, -, hrep⟩ := hty
    obtain ⟨pbsA, bodyF, hsA⟩ := replacePisPw_stripPis_of nP hrep
    refine ⟨pbsA, _, bodyF, motives, hsA, replacePisPw_stripPis nP hrep hsA, ?_⟩
    rw [List.map_map]
    rfl

/-! ## A — the rule's λ prefix -/

/-- A `pisToLamsPw` walk that succeeds has walked a `∀`-telescope, and
its result strips the SAME domains as `λ`s (`replacePisPw_stripPis`'s
twin: the conversion keeps every domain and puts the datum `pw` on
every binder). -/
theorem pisToLamsPw_stripLams {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr}, Expr.pisToLamsPw pw k e b = some r →
      ∃ (bs : List (Expr × BinderMeta)) (body : Expr),
        e.stripPis k = some (bs, body) ∧
        r.stripLams k = some (bs.map fun x => (x.1, (⟨pw⟩ : BinderMeta)), b)
  | 0, e, b, r, h => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at h
    subst h
    exact ⟨[], e, rfl, rfl⟩
  | k + 1, e, b, r, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨bs, body, hs, hl⟩ := pisToLamsPw_stripLams k hr'
      exact ⟨(ty, m) :: bs, body, by simp only [Expr.stripPis, hs, Option.map_some],
        by simp only [Expr.stripLams, hl, Option.map_some, List.map_cons]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h
    | .app _ _, h | .lam _ _ _, h | .letE _ _ _, h | .lit _, h
    | .proj _ _ _, h => simp [Expr.pisToLamsPw] at h

/-- **THE GENERATED RULE'S λ PREFIX IS THE FIRST FORMER'S PARAMETER
TELESCOPE** (`mutualRecTy_paramPrefix`'s twin at the rules):
`mutualRecRhs` closes with `Expr.pisToLamsPw pw nP f₀.tty motives`, so
its outermost `nP` λ-binders carry the first former's domains and the
elimination's datum — the same domains the recursor type's parameter
prefix carries. -/
theorem mutualRecRhs_paramPrefix {lps : List Name} {elim : Name} {large : Bool} {nP : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recOf : Nat → Name}
    {rlvls : List Level} {J : Nat} {rhs : Expr} {f₀ : MutualFormer}
    (hrhs : mutualRecRhs lps elim large nP formers ctors recOf rlvls J = some rhs)
    (hf₀ : formers[0]? = some f₀) :
    ∃ (pbs : List (Expr × BinderMeta)) (bodyF motives : Expr),
      f₀.tty.stripPis nP = some (pbs, bodyF) ∧
      rhs.stripLams nP
        = some (pbs.map fun x =>
            (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)), motives) := by
  unfold mutualRecRhs at hrhs
  rw [hf₀] at hrhs
  cases hc : ctors[J]? with
  | none => rw [hc] at hrhs; exact nomatch hrhs
  | some c =>
    rw [hc] at hrhs
    simp only [Option.bind_eq_some_iff] at hrhs
    obtain ⟨q, -, inner, -, minors, -, motives, -, hrep⟩ := hrhs
    obtain ⟨pbs, bodyF, hs, hl⟩ := pisToLamsPw_stripLams nP hrep
    exact ⟨pbs, bodyF, motives, hs, hl⟩

/-! ## The walk's shape, inverted along a `∀`-telescope -/

/-- A spine is its head or an application. -/
theorem mkAppN_cases : ∀ (f : Expr) (args : List Expr),
    Expr.mkAppN f args = f ∨ ∃ g a, Expr.mkAppN f args = .app g a
  | _, [] => Or.inl rfl
  | f, a :: as => by
    show Expr.mkAppN (.app f a) as = _ ∨ ∃ g a', Expr.mkAppN (.app f a) as = .app g a'
    rcases mkAppN_cases (.app f a) as with h | ⟨g, a', h⟩
    · exact Or.inr ⟨f, a, h⟩
    · exact Or.inr ⟨g, a', h⟩

/-- **The `∀` node's shape, inverted**: a `∀` is no key-headed
application (a key's head is a constant), so the shape at it is the
`forallE` rule's. -/
theorem AuxAppsOk.forallE_inv {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat}
    {d : Nat} {ty b : Expr} {bm : BinderMeta}
    (h : AuxAppsOk R lps arityOf d (.forallE ty b bm)) :
    AuxAppsOk R lps arityOf d ty ∧ AuxAppsOk R lps arityOf (d + 1) b := by
  generalize hE : (Expr.forallE ty b bm : Expr) = E at h
  cases h with
  | @key _ n args _ _ _ _ _ _ =>
    exfalso
    rcases mkAppN_cases (.const n (lps.map .param)) args with h | ⟨g, a, h⟩ <;>
      rw [h] at hE <;> exact nomatch hE
  | app _ _ _ => exact nomatch hE
  | lam _ _ => exact nomatch hE
  | forallE h1 h2 =>
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj hE
    exact ⟨h1, h2⟩
  | letE _ _ _ => exact nomatch hE
  | proj _ => exact nomatch hE
  | const _ => exact nomatch hE
  | bvar => exact nomatch hE
  | sort => exact nomatch hE
  | lit => exact nomatch hE
  | fvar => exact nomatch hE

/-- **The shape at a binder of a `∀`-telescope**: the body's shape at
depth `0` gives binder `i`'s domain's shape at depth `i` — the walk's
precondition at each of a recursor type's binders below the parameter
prefix. -/
theorem AuxAppsOk_stripPis_dom {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {bs : List (Expr × BinderMeta)} {body : Expr},
      AuxAppsOk R lps arityOf d e → e.stripPis n = some (bs, body) →
      ∀ (i : Nat) (x : Expr × BinderMeta), bs[i]? = some x →
        AuxAppsOk R lps arityOf (d + i) x.1
  | 0, e, d, bs, body, _, hs, i, x, hx => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    rw [← hs.1] at hx
    exact nomatch hx
  | n + 1, e, d, bs, body, h, hs, i, x, hx => by
    match e, h, hs with
    | .forallE ty rest bm, h, hs =>
      obtain ⟨h1, h2⟩ := AuxAppsOk.forallE_inv h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', body'⟩, hs', heq⟩ := hs
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, Nat.add_zero]
        exact h1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have := AuxAppsOk_stripPis_dom n h2 hs' i x hx
        rwa [show d + 1 + i = d + (i + 1) from by omega] at this

end ConLeche
