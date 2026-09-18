module

public import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedElimInv

public section

/-!
# The rewrite, read field by field (task #315 L-B)

`replaceAllNested` (`ConLeche/Kernel/Inductives/NestedElim.lean`) is the
top-down replace the nested elimination runs over every constructor
residual.  The model tier reads a rewritten copy constructor FIELD BY
FIELD, and this module is the reading:

* **Monotonicity.**  The pins and the type names only ever grow —
  `mkCopies` appends, `replaceIfNested` either threads or mints,
  `replaceAllNested` and `elimCtors` only thread, and `elimLoop` `set`s
  a type keeping its name, so the NAMES list is untouched by the `set`
  (`*_pins_prefix`).  `newNames_mono` is the consequence the occurrence
  test needs: a name the growing list had, it still has.
* **The prune.**  A subterm mentioning none of the growing list's names
  is returned unchanged with the state untouched
  (`replaceAllNested_of_no_mention`) — the walk's first line, as a
  theorem.
* **The telescope.**  A `∀`-telescope is rewritten to a `∀`-telescope of
  the same length with the binder data untouched, and each domain and
  the body are themselves runs of the rewrite at intermediate states
  (`replaceAllNested_mkPisB`).  Both of the walk's routes through a
  binder — the prune firing at the top, and the domain-then-body
  descent — yield that form.
* **The occurrence.**  At the top of an application of a recorded
  container whose parameter arguments are closed and mention a new
  name, the walk returns the MIMIC of a pin of the resulting state,
  applied to the block's parameters and the occurrence's indices
  (`replaceAllNested_occurrence`), whether the pin was already minted
  (a `find?` hit) or is minted here (`mkCopies_got`).
* **Unchanged or a mimic.**  Every result is either the input term or
  mentions a pin's auxiliary (`replaceAllNested_unchanged_or_aux`).
-/

namespace ConLeche

variable {env : Env} {blvls : List Level} {params : List Expr}
  {pbs₀ : List (Expr × BinderMeta)}

/-- An `.error` never succeeds. -/
private theorem rwErr_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

/-- A declining step never returns a replacement. -/
private theorem rwNone_ne_some {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact rwErr_ne_ok (by assumption))
        | (exfalso; exact rwNone_ne_some (by assumption)))

/-! ## (R6) The new-name list only grows -/

/-- **The occurrence test's names only grow**: a prefix of the type
list's names carries every name it had. -/
theorem newNames_mono {st st' : ElimState}
    (h : st.types.map (·.name) <+: st'.types.map (·.name)) :
    ∀ T, T ∈ st.newNames → T ∈ st'.newNames :=
  fun _ hT => h.subset hT

/-! ## (R1) The pins and the names only grow -/

/-- **One mint group** only APPENDS: the pins the state carried stay a
prefix of the pins it has afterwards, and so do the type names. -/
theorem mkCopies_pins_prefix {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', got) →
      st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name)
  | [], st, st', got, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | J :: rest, st, st', got, h => by
    rw [mkCopies] at h
    split at h
    obtain ⟨copy, -, h⟩ := exceptBind_ok h
    obtain ⟨q, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := q
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hp, hn⟩ := mkCopies_pins_prefix hrec
    refine ⟨List.IsPrefix.trans (List.prefix_append _ _) hp, ?_⟩
    refine List.IsPrefix.trans ?_ hn
    simp

/-- **One occurrence**: `replaceIfNested` either passes the state
through or mints exactly one group, and a mint only appends. -/
theorem replaceIfNested_pins_prefix {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name) := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · split at h
                · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact ⟨List.prefix_refl _, List.prefix_refl _⟩
                · obtain ⟨q, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := q
                  split at h
                  · close_throw
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact mkCopies_pins_prefix hcop
      · close_throw
    · close_throw
  · close_throw

/-- What the walk preserves: the pins and the type names only grow. -/
private def Grows (st st' : ElimState) : Prop :=
  st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name)

private theorem Grows.rfl' (st : ElimState) : Grows st st :=
  ⟨List.prefix_refl _, List.prefix_refl _⟩

private theorem Grows.trans' {a b c : ElimState} (h₁ : Grows a b) (h₂ : Grows b c) :
    Grows a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- The walk returned the state it was given. -/
private theorem rwSame {st st' : ElimState} {e e' : Expr}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    Grows st st' := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact Grows.rfl' _

/-- **The top-down replace only threads the state**: the pins it was
given stay a prefix of the pins it returns, and so do the type names. -/
theorem replaceAllNested_pins_prefix :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name) := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact rwSame h
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact replaceIfNested_pins_prefix heq
        · exact rwSame h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact rwSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_pins_prefix heq
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact Grows.trans' (ihf heq1) (iha heq2)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact rwSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_pins_prefix heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact Grows.trans' (ihty heq1) (ihb heq2)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact rwSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_pins_prefix heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact Grows.trans' (ihty heq1) (ihb heq2)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact rwSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_pins_prefix heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i v' st2 heq2
            split at h
            · close_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact Grows.trans' (ihty heq1) (Grows.trans' (ihv heq2) (ihb heq3))
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact rwSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_pins_prefix heq
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1

/-- **One type's constructors**: `elimCtors` only threads the state. -/
theorem elimCtors_pins_prefix {nP : Nat} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name)
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Grows.rfl' _
  | (c, cty, nF) :: rest, st, st', cs', h => by
    rw [elimCtors] at h
    split at h
    · split at h
      · obtain ⟨q₁, h₁, h⟩ := exceptBind_ok h
        obtain ⟨cbody', st₁⟩ := q₁
        obtain ⟨q₂, h₂, h⟩ := exceptBind_ok h
        obtain ⟨rest', st₂⟩ := q₂
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact Grows.trans' (replaceAllNested_pins_prefix _ h₁) (elimCtors_pins_prefix h₂)
      · close_throw
    · close_throw

/-- Writing back the value a position already holds changes nothing. -/
private theorem list_set_self {α : Type} : ∀ {l : List α} {i : Nat} {a : α},
    l[i]? = some a → l.set i a = l
  | [], i, a, h => by simp at h
  | x :: xs, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    simp [h]
  | x :: xs, i + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [List.set, list_set_self h]

/-- The worklist step, as a growth fact. -/
private theorem elimLoop_grows {nP : Nat} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' → Grows st st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_throw
  | succ fuel ih =>
    intro qhead st st' h
    rw [elimLoop] at h
    cases htq : st.types[qhead]? with
    | none =>
      simp only [htq, Except.ok.injEq] at h
      obtain rfl := h
      exact Grows.rfl' _
    | some tq =>
      simp only [htq] at h
      split at h
      · close_throw
      · rename_i cs' st₁ heq
        -- K.40 threads the worklist position through `ElimState.curType`;
        -- the update changes neither list, so `Grows` is the same Prop
        have hg₁ : Grows st st₁ :=
          elimCtors_pins_prefix (st := { st with curType := qhead }) heq
        have h₁ : st₁.types[qhead]? = some tq := elimCtors_types_prefix heq qhead tq htq
        have hname : (st₁.types.map (·.name))[qhead]? = some tq.name := by
          rw [List.getElem?_map, h₁]; rfl
        have hset : ((st₁.types.set qhead { tq with ctors := cs' }).map (·.name))
            = st₁.types.map (·.name) := by
          rw [List.map_set]
          exact list_set_self hname
        have hg₂ : Grows st₁
            { st₁ with types := st₁.types.set qhead { tq with ctors := cs' } } := by
          refine ⟨List.prefix_refl _, ?_⟩
          show st₁.types.map (·.name) <+:
            ((st₁.types.set qhead { tq with ctors := cs' }).map (·.name))
          rw [hset]
          exact List.prefix_refl _
        exact Grows.trans' hg₁ (Grows.trans' hg₂ (ih (qhead + 1) h))

/-- **THE WORKLIST ONLY GROWS THE PINS AND THE NAMES** (task #315): the
worklist appends copies and rewrites constructor TYPES in place, so the
pins and the type names it was given stay prefixes. -/
theorem elimLoop_pins_prefix {nP : Nat} {fuel qhead : Nat} {st st' : ElimState}
    (h : elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st') :
    st.pins <+: st'.pins ∧ st.types.map (·.name) <+: st'.types.map (·.name) :=
  elimLoop_grows _ _ h

/-! ## (R2) The prune -/

/-- **THE PRUNE** (task #315): a subterm mentioning none of the growing
list's names is returned unchanged, with the state untouched. -/
theorem replaceAllNested_of_no_mention {st : ElimState} {e : Expr}
    (h : (st.newNames.any fun T => e.mentionsConst T) = false) :
    replaceAllNested env blvls params pbs₀ st e = .ok (e, st) := by
  rw [replaceAllNested.eq_def]
  simp only [h, Bool.not_false, if_true]

/-! ## `mentionsConst` through the shapes the rewrite builds -/

/-- The head of an application spine is mentioned by the spine. -/
theorem mentionsConst_mkAppN_of_fn {T : Name} :
    ∀ (args : List Expr) (f : Expr), f.mentionsConst T = true →
      (Expr.mkAppN f args).mentionsConst T = true
  | [], _, h => h
  | a :: as, f, h => by
    refine mentionsConst_mkAppN_of_fn as (.app f a) ?_
    simp [Expr.mentionsConst, h]

/-- An argument of an application spine is mentioned by the spine. -/
theorem mentionsConst_mkAppN_of_arg {T : Name} :
    ∀ {args : List Expr} {a : Expr}, a ∈ args → a.mentionsConst T = true →
      ∀ (f : Expr), (Expr.mkAppN f args).mentionsConst T = true
  | [], a, ha, _, _ => by simp at ha
  | x :: as, a, ha, hm, f => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact mentionsConst_mkAppN_of_fn as (.app f a) (by simp [Expr.mentionsConst, hm])
    · exact mentionsConst_mkAppN_of_arg ha' hm (.app f x)

/-- A disjunction is pruned only if both sides are. -/
private theorem any_or_false {ns : List Name} {f g : Name → Bool}
    (h : (ns.any fun T => f T || g T) = false) :
    ns.any f = false ∧ ns.any g = false := by
  refine ⟨?_, ?_⟩
  · cases hf : ns.any f with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp hf
      have hb := List.any_eq_false.mp h x hx
      simp [hfx] at hb
  · cases hg : ns.any g with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, hx, hgx⟩ := List.any_eq_true.mp hg
      have hb := List.any_eq_false.mp h x hx
      simp [hgx] at hb

/-- **The `∀`-telescope's parts are pruned with it**: if none of the
names occurs in `mkPisB bs res`, none occurs in a binder domain or in
the body. -/
theorem anyMentions_mkPisB_false {ns : List Name} :
    ∀ (bs : List (Expr × BinderMeta)) (res : Expr),
      (ns.any fun T => (mkPisB bs res).mentionsConst T) = false →
      (∀ l, l < bs.length →
          (ns.any fun T => (bs.getD l default).1.mentionsConst T) = false) ∧
        (ns.any fun T => res.mentionsConst T) = false
  | [], res, h => by
    rw [mkPisB_nil] at h
    exact ⟨fun l hl => by simp at hl, h⟩
  | b :: bs, res, h => by
    rw [mkPisB_cons] at h
    obtain ⟨h₁, h₂⟩ := any_or_false (f := fun T => b.1.mentionsConst T)
      (g := fun T => (mkPisB bs res).mentionsConst T) h
    obtain ⟨hd, hr⟩ := anyMentions_mkPisB_false bs res h₂
    refine ⟨?_, hr⟩
    intro l hl
    cases l with
    | zero => exact h₁
    | succ l => exact hd l (by simpa using hl)

/-! ## (R3) The telescope -/

/-- **THE REWRITE COMMUTES WITH THE `∀`-TELESCOPE** (task #315): a
`∀`-telescope is rewritten to a `∀`-telescope of the same length, with
the binder data untouched, and every binder domain and the body are
themselves runs of the rewrite at states between the one the telescope
started at and the one it ended at. -/
theorem replaceAllNested_mkPisB :
    ∀ (bs : List (Expr × BinderMeta)) {res : Expr} {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st (mkPisB bs res) = .ok (e', st') →
      ∃ (bs' : List (Expr × BinderMeta)) (res' : Expr),
        e' = mkPisB bs' res' ∧ bs'.length = bs.length ∧
        (∀ l, l < bs.length →
          (bs'.getD l default).2 = (bs.getD l default).2 ∧
          ∃ st₁ st₂ : ElimState,
            replaceAllNested env blvls params pbs₀ st₁ (bs.getD l default).1
              = .ok ((bs'.getD l default).1, st₂) ∧
            st.pins <+: st₁.pins ∧ st₂.pins <+: st'.pins ∧
            st.types.map (·.name) <+: st₁.types.map (·.name)) ∧
        ∃ st₁ st₂ : ElimState,
          replaceAllNested env blvls params pbs₀ st₁ res = .ok (res', st₂) ∧
          st.pins <+: st₁.pins ∧ st₂.pins <+: st'.pins ∧
          st.types.map (·.name) <+: st₁.types.map (·.name)
  | [], res, st, st', e', h => by
    rw [mkPisB_nil] at h
    refine ⟨[], e', (mkPisB_nil e').symm, rfl, fun l hl => absurd hl (by simp), ?_⟩
    exact ⟨st, st', h, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
  | b :: bs, res, st, st', e', h => by
    rw [mkPisB_cons] at h
    rw [replaceAllNested] at h
    split at h
    · -- **the prune fired**: nothing in the telescope mentions a name
      rename_i hc
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      rw [← mkPisB_cons] at hc h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hd, hr⟩ := anyMentions_mkPisB_false (b :: bs) res hc
      refine ⟨b :: bs, res, rfl, rfl, fun l hl => ⟨rfl, ?_⟩, ?_⟩
      · exact ⟨st, st, replaceAllNested_of_no_mention (hd l hl),
          List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
      · exact ⟨st, st, replaceAllNested_of_no_mention hr,
          List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
    · split at h
      · close_throw
      · -- `replaceIfNested` matches applications only
        exfalso
        rename_i r heq
        rw [show replaceIfNested env blvls params pbs₀ st
              (Expr.forallE b.1 (mkPisB bs res) b.2) = pure none from rfl] at heq
        exact rwNone_ne_some heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨bs'', res'', hshape, hlen, hbinds, stR₁, stR₂, hres, hrp₁, hrp₂,
              hrn₁⟩ := replaceAllNested_mkPisB bs heq2
            have hg₁ := replaceAllNested_pins_prefix _ heq1
            have hg₂ := replaceAllNested_pins_prefix _ heq2
            refine ⟨(ty', b.2) :: bs'', res'', ?_, by simp [hlen], ?_, ?_⟩
            · rw [mkPisB_cons, ← hshape]
            · intro l hl
              cases l with
              | zero =>
                refine ⟨rfl, st, st1, heq1, List.prefix_refl _, hg₂.1,
                  List.prefix_refl _⟩
              | succ l =>
                have hl' : l < bs.length := by simpa using hl
                obtain ⟨hbm, stB₁, stB₂, hrun, hp₁, hp₂, hn₁⟩ := hbinds l hl'
                exact ⟨hbm, stB₁, stB₂, hrun, hg₁.1.trans hp₁, hp₂, hg₁.2.trans hn₁⟩
            · exact ⟨stR₁, stR₂, hres, hg₁.1.trans hrp₁, hrp₂, hg₁.2.trans hrn₁⟩

/-! ## (R4) The minted name is a pin's -/

/-- **THE MINT RETURNS ONE OF ITS OWN PINS** (task #315): the name
`mkCopies` hands back is the auxiliary of a pin it left in the state —
the pin of the member the occurrence named, spelled at the pin's
components. -/
theorem mkCopies_got {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {a : Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', some a) →
      ∃ q ∈ st'.pins, q.aux = a ∧ q.container = I ∧
        q.pin = Expr.mkAppN (.const I lvls) Ds
  | [], st, st', a, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact absurd h.2 (by simp)
  | J :: rest, st, st', a, h => by
    rw [mkCopies] at h
    split at h
    rename_i auxName nextIdx _
    obtain ⟨copy, -, h⟩ := exceptBind_ok h
    obtain ⟨p, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := p
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hgot⟩ := h
    split at hgot
    · rename_i hJI
      simp only [Option.some.injEq] at hgot
      subst hgot
      simp only [beq_iff_eq] at hJI
      refine ⟨⟨auxName, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size, st.curType⟩, ?_,
        rfl, hJI, by rw [hJI]⟩
      refine (mkCopies_pins_prefix hrec).1.subset ?_
      simp
    · subst hgot
      exact mkCopies_got hrec

/-- An application spine with at least one argument is an `.app`. -/
theorem mkAppN_app : ∀ (args : List Expr), args ≠ [] → ∀ (f : Expr),
    ∃ u v, Expr.mkAppN f args = .app u v
  | [], h, _ => absurd rfl h
  | [a], _, f => ⟨f, a, rfl⟩
  | a :: x :: as, _, f => mkAppN_app (x :: as) (by simp) (.app f a)

/-- `mkAppN` over a spine extended on the right. -/
private theorem mkAppN_concat : ∀ (as : List Expr) (f a : Expr),
    Expr.mkAppN f (as ++ [a]) = .app (Expr.mkAppN f as) a
  | [], _, _ => rfl
  | b :: as, f, a => by
    show Expr.mkAppN (.app f b) (as ++ [a]) = _
    rw [mkAppN_concat as (.app f b) a]
    rfl

/-- **A CONSTANT HEAD SURVIVES THE WALK** (task #315 L-B): the walk's
only head-changing step is a FIRE, and its descent into `.app f a`
reaches the head through PREFIXES of the same spine — so a spine at
whose every prefix `replaceIfNested` declines comes back with the head
it went in with.

The hypothesis is uniform in the state because the descent walks the
function part at the state it was given (`f` at `st`, the argument at
the state `f` returned), so every prefix of the spine is offered to
`replaceIfNested` at the ORIGINAL `st`.

Its consumer reads the fire off the CLASSIFICATION rather than off the
mention: a copy field the auxiliary block calls `.recursive` has a
member-headed stored domain, and a container is no member of that
block, so the rewrite must have fired. -/
theorem replaceAllNested_head_const {env : Env} {blvls : List Level}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {I : Name} {us : List Level} :
    ∀ (as : List Expr) {st st' : ElimState} {e' : Expr},
      (∀ k : Nat, replaceIfNested env blvls params pbs₀ st
        (Expr.mkAppN (.const I us) (as.take k)) = .ok none) →
      replaceAllNested env blvls params pbs₀ st (Expr.mkAppN (.const I us) as)
        = .ok (e', st') →
      e'.getAppFn = Expr.const I us := by
  -- a reverse recursor, spelled here because the spine grows on the right
  have revRec : ∀ {motive : List Expr → Prop}, motive [] →
      (∀ (bs : List Expr) (b : Expr), motive bs → motive (bs ++ [b])) → ∀ bs, motive bs := by
    intro motive hnil hsnoc bs
    have key : ∀ cs : List Expr, motive cs.reverse := by
      intro cs
      induction cs with
      | nil => exact hnil
      | cons c cs ih =>
        rw [show (c :: cs).reverse = cs.reverse ++ [c] from by simp]
        exact hsnoc _ _ ih
    have h := key bs.reverse
    rwa [List.reverse_reverse] at h
  refine revRec ?_ ?_
  case _ =>
    intro st st' e' _ hrun
    rw [replaceAllNested.eq_def] at hrun
    replace hrun : (if (!st.newNames.any fun T => Expr.mentionsConst T (Expr.const I us)) = true
        then Except.ok (Expr.const I us, st)
        else Except.ok (Expr.const I us, st)) = Except.ok (e', st') := hrun
    rw [ite_self] at hrun
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    rw [← hrun.1]
    rfl
  case _ =>
    intro as a ih st st' e' hnone hrun
    have hih : ∀ k : Nat, replaceIfNested env blvls params pbs₀ st
        (Expr.mkAppN (.const I us) (as.take k)) = .ok none := by
      intro k
      have hk : as.take k = (as ++ [a]).take (min k as.length) := by
        rcases Nat.le_total k as.length with hle | hle
        · rw [show min k as.length = k from Nat.min_eq_left hle,
            List.take_append_of_le_length hle]
        · rw [show min k as.length = as.length from Nat.min_eq_right hle,
            List.take_left, List.take_of_length_le hle]
      rw [hk]
      exact hnone (min k as.length)
    rw [mkAppN_concat] at hrun
    rw [replaceAllNested.eq_def] at hrun
    split at hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      rw [← hrun.1]
      show (Expr.mkAppN (Expr.const I us) as).getAppFn = _
      rw [Expr.getAppFn_mkAppN]
      rfl
    · have hroot : replaceIfNested env blvls params pbs₀ st
          (.app (Expr.mkAppN (Expr.const I us) as) a) = .ok none := by
        have h := hnone (as ++ [a]).length
        rw [List.take_length, mkAppN_concat] at h
        exact h
      rw [hroot] at hrun
      simp only at hrun
      cases hf : replaceAllNested env blvls params pbs₀ st (Expr.mkAppN (Expr.const I us) as) with
      | error err => rw [hf] at hrun; exact nomatch hrun
      | ok r =>
        obtain ⟨u', st₁⟩ := r
        rw [hf] at hrun
        simp only at hrun
        cases ha : replaceAllNested env blvls params pbs₀ st₁ a with
        | error err => rw [ha] at hrun; simp only at hrun; exact nomatch hrun
        | ok r' =>
          obtain ⟨a', st₂⟩ := r'
          rw [ha] at hrun
          simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          rw [← hrun.1]
          show u'.getAppFn = _
          exact ih hih hf

/-- **A FIRED OCCURRENCE'S PARAMETERS ARE CLOSED** (task #315 L-B):
`nestedOccOk` REJECTS a nested occurrence whose parameter arguments
carry a local variable (official's "nested inductive datatypes
parameters cannot contain local variables"), so at an occurrence that
mentions a name of the growing list an ACCEPTED run has none.  The
`hloose` of `replaceIfNested_occurrence` and
`replaceAllNested_occurrence` is therefore a CONSEQUENCE of the run
rather than a second input — which is what a consumer needs at a
MINTED domain, where the parameter arguments are the container's
field's own and nothing records them closed. -/
theorem replaceIfNested_loose {st : ElimState} {e : Expr}
    {I : Name} {us : List Level} {args : List Expr} {cv : ConstantVal}
    {caps : IndCaps} {ci : ContainerInfo} {r : Option (Expr × ElimState)}
    (he : e = Expr.mkAppN (.const I us) args)
    (hfind : env.find? I = some (.indInfo cv caps))
    (hci : containerInfo? env I = some ci)
    (hnP : ci.nP ≤ args.length)
    (hment : ((args.take ci.nP).any fun a =>
      st.newNames.any fun T => a.mentionsConst T) = true)
    (h : replaceIfNested env blvls params pbs₀ st e = .ok r) :
    ∀ a ∈ args.take ci.nP, a.looseBVarsBounded 0 = true := by
  have hargsne : args ≠ [] := by
    intro hnil
    rw [hnil] at hment
    simp at hment
  have hfn : e.getAppFn = .const I us := by
    rw [he, Expr.getAppFn_mkAppN]; rfl
  have hargs : e.getAppArgs = args := by
    rw [he, Expr.getAppArgs_mkAppN]; rfl
  have hIq : (I == quotName) = false := by
    cases hq : I == quotName with
    | false => rfl
    | true =>
      exfalso
      have hnone : containerInfo? env I = none := by
        unfold containerInfo?
        simp [hq]
      rw [hnone] at hci
      simp at hci
  have hloose' : ((args.take ci.nP).any fun a => !a.looseBVarsBounded 0) = false := by
    cases hb : (args.take ci.nP).any fun a => !a.looseBVarsBounded 0 with
    | false => rfl
    | true =>
      exfalso
      unfold replaceIfNested at h
      split at h
      · rw [hfn, hargs] at h
        dsimp only at h
        rw [hfind, hIq] at h
        dsimp only at h
        simp only [Bool.false_eq_true, if_false] at h
        rw [hci] at h
        dsimp only at h
        rw [if_neg (by omega : ¬ args.length < ci.nP)] at h
        unfold nestedOccOk at h
        simp only [hment, hb, Bool.and_self, if_true, bind, Except.bind] at h
        exact nomatch h
      · obtain ⟨u, v, huv⟩ := mkAppN_app args hargsne (.const I us)
        rename_i hne
        exact hne u v (he.trans huv)
  intro a ha
  cases hab : a.looseBVarsBounded 0 with
  | true => rfl
  | false =>
    exfalso
    have hcon : ((args.take ci.nP).any fun a => !a.looseBVarsBounded 0) = true :=
      List.any_eq_true.mpr ⟨a, ha, by simp [hab]⟩
    rw [hloose'] at hcon
    exact nomatch hcon

/-- **ONE REWRITTEN OCCURRENCE** (task #315): at an application of a
recorded container whose parameter arguments are closed and mention a
name of the growing list, `replaceIfNested` fires — the result is the
mimic of a pin of the resulting state, applied to the block's
parameters and the occurrence's indices. -/
theorem replaceIfNested_occurrence {st : ElimState} {e : Expr}
    {I : Name} {us : List Level} {args : List Expr} {cv : ConstantVal}
    {caps : IndCaps} {ci : ContainerInfo} {r : Option (Expr × ElimState)}
    (he : e = Expr.mkAppN (.const I us) args)
    (hfind : env.find? I = some (.indInfo cv caps))
    (hci : containerInfo? env I = some ci)
    (hnP : ci.nP ≤ args.length)
    (hment : ((args.take ci.nP).any fun a =>
      st.newNames.any fun T => a.mentionsConst T) = true)
    (hloose : ∀ a ∈ args.take ci.nP, a.looseBVarsBounded 0 = true)
    (h : replaceIfNested env blvls params pbs₀ st e = .ok r) :
    ∃ (q : NestedPin) (st₁ : ElimState),
      r = some (Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params)
          (args.drop ci.nP), st₁) ∧
        q ∈ st₁.pins ∧ q.pin = Expr.mkAppN (.const I us) (args.take ci.nP) := by
  have hargsne : args ≠ [] := by
    intro hnil
    rw [hnil] at hment
    simp at hment
  have hfn : e.getAppFn = .const I us := by
    rw [he, Expr.getAppFn_mkAppN]; rfl
  have hargs : e.getAppArgs = args := by
    rw [he, Expr.getAppArgs_mkAppN]; rfl
  have hIq : (I == quotName) = false := by
    cases hq : I == quotName with
    | false => rfl
    | true =>
      exfalso
      have hnone : containerInfo? env I = none := by
        unfold containerInfo?
        simp [hq]
      rw [hnone] at hci
      simp at hci
  have hloose' : ((args.take ci.nP).any fun a => !a.looseBVarsBounded 0) = false := by
    cases hb : (args.take ci.nP).any fun a => !a.looseBVarsBounded 0 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, hx, hxb⟩ := List.any_eq_true.mp hb
      simp [hloose x hx] at hxb
  have hocc : nestedOccOk I st.newNames ci.nP args = .ok true := by
    unfold nestedOccOk
    simp [hment, hloose']
  unfold replaceIfNested at h
  split at h
  · rw [hfn, hargs] at h
    dsimp only at h
    rw [hfind, hIq] at h
    dsimp only at h
    simp only [Bool.false_eq_true, if_false] at h
    rw [hci] at h
    dsimp only at h
    rw [if_neg (by omega : ¬ args.length < ci.nP), hocc] at h
    simp only [bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false] at h
    split at h
    · rename_i q hq
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨q, st, rfl, List.mem_of_find?_eq_some hq, ?_⟩
      have := List.find?_some hq
      simpa using this
    · rename_i hmiss
      split at h
      · close_throw
      · rename_i v hcop
        obtain ⟨stM, gotM⟩ := v
        split at h
        · close_throw
        · rename_i auxI hgot
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hgot' : gotM = some auxI := hgot
          subst hgot'
          obtain ⟨q, hqmem, hqa, -, hqp⟩ := mkCopies_got hcop
          exact ⟨q, stM, by rw [hqa], hqmem, hqp⟩
  · exfalso
    obtain ⟨u, v, huv⟩ := mkAppN_app args hargsne (.const I us)
    rename_i hne
    exact hne u v (he.trans huv)

/-- **THE OCCURRENCE, READ OFF THE WALK** (task #315): at the top of an
application of a recorded container whose parameter arguments are
closed and mention a name of the growing list, the top-down replace
returns the mimic of a pin of the resulting state — the pin being the
container at those parameter arguments, the mimic applied to the
block's parameters and the occurrence's indices. -/
theorem replaceAllNested_occurrence {st st' : ElimState} {e e' : Expr}
    {I : Name} {us : List Level} {args : List Expr} {cv : ConstantVal}
    {caps : IndCaps} {ci : ContainerInfo}
    (he : e = Expr.mkAppN (.const I us) args)
    (hfind : env.find? I = some (.indInfo cv caps))
    (hci : containerInfo? env I = some ci)
    (hnP : ci.nP ≤ args.length)
    (hment : ((args.take ci.nP).any fun a =>
      st.newNames.any fun T => a.mentionsConst T) = true)
    (hloose : ∀ a ∈ args.take ci.nP, a.looseBVarsBounded 0 = true)
    (hrun : replaceAllNested env blvls params pbs₀ st e = .ok (e', st')) :
    ∃ q : NestedPin, q ∈ st'.pins ∧
      q.pin = Expr.mkAppN (.const I us) (args.take ci.nP) ∧
      e' = Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params) (args.drop ci.nP) := by
  -- the prune does not fire: a parameter argument mentions a new name
  have hany : (st.newNames.any fun T => e.mentionsConst T) = true := by
    obtain ⟨a, ha, hma⟩ := List.any_eq_true.mp hment
    obtain ⟨T, hT, hmT⟩ := List.any_eq_true.mp hma
    refine List.any_eq_true.mpr ⟨T, hT, ?_⟩
    rw [he]
    exact mentionsConst_mkAppN_of_arg (List.mem_of_mem_take ha) hmT _
  rw [replaceAllNested.eq_def] at hrun
  simp only [hany, Bool.not_true, Bool.false_eq_true, if_false] at hrun
  cases hri : replaceIfNested env blvls params pbs₀ st e with
  | error err =>
    rw [hri] at hrun
    exact absurd hrun (by simp)
  | ok o =>
    obtain ⟨q, st₁, rfl, hqm, hqp⟩ :=
      replaceIfNested_occurrence he hfind hci hnP hment hloose hri
    rw [hri] at hrun
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨q, hqm, hqp, rfl⟩

/-! ## (R5) Unchanged, or a mimic is mentioned -/

/-- **A FIRING IS A MIMIC** (task #315): whenever `replaceIfNested`
replaces a subterm, the replacement mentions the auxiliary of a pin the
step left in the state. -/
theorem replaceIfNested_some {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    ∃ q ∈ st'.pins, e'.mentionsConst q.aux = true := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · split at h
                · rename_i qq hqq
                  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  refine ⟨qq, List.mem_of_find?_eq_some hqq, ?_⟩
                  exact mentionsConst_mkAppN_of_fn _ _
                    (mentionsConst_mkAppN_of_fn _ _ (by simp [Expr.mentionsConst]))
                · obtain ⟨p, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := p
                  split at h
                  · close_throw
                  · rename_i auxI hgot
                    have hgot' : gotM = some auxI := hgot
                    subst hgot'
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨q, hqm, hqa, -, -⟩ := mkCopies_got hcop
                    refine ⟨q, hqm, ?_⟩
                    rw [hqa]
                    exact mentionsConst_mkAppN_of_fn _ _
                      (mentionsConst_mkAppN_of_fn _ _ (by simp [Expr.mentionsConst]))
      · close_throw
    · close_throw
  · close_throw

/-- The walk returned the term it was given. -/
private theorem rwSameE {st st' : ElimState} {e e' : Expr}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) : e' = e := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1.symm

/-- **THE REWRITE IS THE IDENTITY OR PLANTS A MIMIC** (task #315):
every result of the top-down replace is either the input term
unchanged, or mentions the auxiliary of a pin of the resulting state. -/
theorem replaceAllNested_unchanged_or_aux :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      e' = e ∨ ∃ q ∈ st'.pins, e'.mentionsConst q.aux = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact Or.inl (rwSameE h)
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (replaceIfNested_some heq)
        · exact Or.inl (rwSameE h)
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact Or.inl (rwSameE h)
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (replaceIfNested_some heq)
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases ihf heq1 with hf | ⟨q, hq, hm⟩
            · rcases iha heq2 with ha | ⟨q, hq, hm⟩
              · exact Or.inl (by rw [hf, ha])
              · exact Or.inr ⟨q, hq, by simp [Expr.mentionsConst, hm]⟩
            · exact Or.inr ⟨q, (replaceAllNested_pins_prefix _ heq2).1.subset hq,
                by simp [Expr.mentionsConst, hm]⟩
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact Or.inl (rwSameE h)
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (replaceIfNested_some heq)
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases ihty heq1 with hty | ⟨q, hq, hm⟩
            · rcases ihb heq2 with hb | ⟨q, hq, hm⟩
              · exact Or.inl (by rw [hty, hb])
              · exact Or.inr ⟨q, hq, by simp [Expr.mentionsConst, hm]⟩
            · exact Or.inr ⟨q, (replaceAllNested_pins_prefix _ heq2).1.subset hq,
                by simp [Expr.mentionsConst, hm]⟩
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact Or.inl (rwSameE h)
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (replaceIfNested_some heq)
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases ihty heq1 with hty | ⟨q, hq, hm⟩
            · rcases ihb heq2 with hb | ⟨q, hq, hm⟩
              · exact Or.inl (by rw [hty, hb])
              · exact Or.inr ⟨q, hq, by simp [Expr.mentionsConst, hm]⟩
            · exact Or.inr ⟨q, (replaceAllNested_pins_prefix _ heq2).1.subset hq,
                by simp [Expr.mentionsConst, hm]⟩
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact Or.inl (rwSameE h)
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (replaceIfNested_some heq)
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i v' st2 heq2
            split at h
            · close_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rcases ihty heq1 with hty | ⟨q, hq, hm⟩
              · rcases ihv heq2 with hv | ⟨q, hq, hm⟩
                · rcases ihb heq3 with hb | ⟨q, hq, hm⟩
                  · exact Or.inl (by rw [hty, hv, hb])
                  · exact Or.inr ⟨q, hq, by simp [Expr.mentionsConst, hm]⟩
                · exact Or.inr ⟨q, (replaceAllNested_pins_prefix _ heq3).1.subset hq,
                    by simp [Expr.mentionsConst, hm]⟩
              · refine Or.inr ⟨q, ?_, by simp [Expr.mentionsConst, hm]⟩
                exact (replaceAllNested_pins_prefix _ heq3).1.subset
                  ((replaceAllNested_pins_prefix _ heq2).1.subset hq)
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact Or.inl (rwSameE h)
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (replaceIfNested_some heq)
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases ihx heq1 with hx | ⟨q, hq, hm⟩
          · exact Or.inl (by rw [hx])
          · exact Or.inr ⟨q, hq, by simp [Expr.mentionsConst, hm]⟩

/-! ## (R6) The frame -/

/-- **THE MIMIC'S SHAPE**: whenever `replaceIfNested` fires it returns
the auxiliary of a pin applied to the walk's OWN parameters and to a
suffix of the occurrence's arguments — nothing else. -/
theorem replaceIfNested_shape {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    ∃ (A : Name) (n : Nat),
      e' = Expr.mkAppN (Expr.mkAppN (.const A blvls) params) (e.getAppArgs.drop n) := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · split at h
                · rename_i qq _
                  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨qq.aux, _, rfl⟩
                · obtain ⟨pr, -, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := pr
                  split at h
                  · close_throw
                  · rename_i auxI hgot
                    have hgot' : gotM = some auxI := hgot
                    subst hgot'
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨auxI, _, rfl⟩
      · close_throw
    · close_throw
  · close_throw

/-- **THE REWRITE PRESERVES THE FRAME** (task #315 L-B, DESIGN §U.38 (e)
step 3): the walk plants only the mimic — a constant applied to the
block's parameter openers and to arguments of the term it replaces — so
its output adds no loose `bvar` and no `fvar` leaf beyond the ones the
input and the parameters already carry.

Stated at an arbitrary `bvar` bound because the walk descends under
binders; the parameters are `bvar`-closed, hence bounded at every
depth (`looseBVarsBounded_mono`). -/
theorem replaceAllNested_frame {fvs : List Expr}
    (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true)
    (hpl : ∀ a ∈ params, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    ∀ (e : Expr) {k : Nat} {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      e.looseBVarsBounded k = true → (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
      e'.looseBVarsBounded k = true ∧ ∀ l ∈ e'.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
  -- the mimic, at the frame: its head is closed, its parameters are the
  -- openers and its remaining arguments are the input's own
  have hmimic : ∀ {A : Name} {n k : Nat} {e : Expr}, e.looseBVarsBounded k = true →
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
      (Expr.mkAppN (Expr.mkAppN (.const A blvls) params) (e.getAppArgs.drop n)).looseBVarsBounded k
          = true ∧
        ∀ l ∈ (Expr.mkAppN (Expr.mkAppN (.const A blvls) params)
            (e.getAppArgs.drop n)).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro A n k e hb hlv
    refine ⟨looseBVarsBounded_mkAppN (looseBVarsBounded_mkAppN rfl
        (fun a ha => Expr.looseBVarsBounded_mono (Nat.zero_le k) (hpb a ha)))
      (fun x hx => looseBVarsBounded_getAppArgs hb x (List.mem_of_mem_drop hx)), ?_⟩
    intro l hl
    rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
    · rcases fvarLeaves_mkAppN hl' with hl'' | ⟨a, ha, hla⟩
      · exact absurd hl'' (by simp [Expr.fvarLeaves])
      · exact hpl a ha l hla
    · exact hlv l (fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hlx)
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    · split at h
      · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact ⟨hb, hlv⟩
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
          exact hmimic hb hlv
        · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _); exact ⟨hb, hlv⟩
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.fvarLeaves, List.mem_append] at hlv
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _)
      exact ⟨by simp [Expr.looseBVarsBounded, hb.1, hb.2],
        fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl)⟩
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
        exact hmimic (by simp [Expr.looseBVarsBounded, hb.1, hb.2])
          (fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl))
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hbf, hlf⟩ := ihf heq1 hb.1 (fun l hl => hlv l (Or.inl hl))
            obtain ⟨hba, hla⟩ := iha heq2 hb.2 (fun l hl => hlv l (Or.inr hl))
            refine ⟨by simp [Expr.looseBVarsBounded, hbf, hba], fun l hl => ?_⟩
            simp only [Expr.fvarLeaves, List.mem_append] at hl
            rcases hl with hl | hl
            · exact hlf l hl
            · exact hla l hl
  | lam ty b m ihty ihb =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.fvarLeaves, List.mem_append] at hlv
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _)
      exact ⟨by simp [Expr.looseBVarsBounded, hb.1, hb.2],
        fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl)⟩
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
        exact hmimic (by simp [Expr.looseBVarsBounded, hb.1, hb.2])
          (fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl))
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hbt, hlt⟩ := ihty heq1 hb.1 (fun l hl => hlv l (Or.inl hl))
            obtain ⟨hbb, hlb⟩ := ihb heq2 hb.2 (fun l hl => hlv l (Or.inr hl))
            refine ⟨by simp [Expr.looseBVarsBounded, hbt, hbb], fun l hl => ?_⟩
            simp only [Expr.fvarLeaves, List.mem_append] at hl
            rcases hl with hl | hl
            · exact hlt l hl
            · exact hlb l hl
  | forallE ty b m ihty ihb =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.fvarLeaves, List.mem_append] at hlv
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _)
      exact ⟨by simp [Expr.looseBVarsBounded, hb.1, hb.2],
        fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl)⟩
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
        exact hmimic (by simp [Expr.looseBVarsBounded, hb.1, hb.2])
          (fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl))
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hbt, hlt⟩ := ihty heq1 hb.1 (fun l hl => hlv l (Or.inl hl))
            obtain ⟨hbb, hlb⟩ := ihb heq2 hb.2 (fun l hl => hlv l (Or.inr hl))
            refine ⟨by simp [Expr.looseBVarsBounded, hbt, hbb], fun l hl => ?_⟩
            simp only [Expr.fvarLeaves, List.mem_append] at hl
            rcases hl with hl | hl
            · exact hlt l hl
            · exact hlb l hl
  | letE ty v b ihty ihv ihb =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.fvarLeaves, List.mem_append] at hlv
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _)
      exact ⟨by simp [Expr.looseBVarsBounded, hb.1.1, hb.1.2, hb.2],
        fun l hl => hlv l (by simpa [Expr.fvarLeaves, List.mem_append, or_assoc] using hl)⟩
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
        exact hmimic (by simp [Expr.looseBVarsBounded, hb.1.1, hb.1.2, hb.2])
          (fun l hl => hlv l (by simpa [Expr.fvarLeaves, List.mem_append, or_assoc] using hl))
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i v' st2 heq2
            split at h
            · close_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hbt, hlt⟩ := ihty heq1 hb.1.1 (fun l hl => hlv l (Or.inl (Or.inl hl)))
              obtain ⟨hbv, hlvv⟩ := ihv heq2 hb.1.2 (fun l hl => hlv l (Or.inl (Or.inr hl)))
              obtain ⟨hbb, hlb⟩ := ihb heq3 hb.2 (fun l hl => hlv l (Or.inr hl))
              refine ⟨by simp [Expr.looseBVarsBounded, hbt, hbv, hbb], fun l hl => ?_⟩
              simp only [Expr.fvarLeaves, List.mem_append] at hl
              rcases hl with (hl | hl) | hl
              · exact hlt l hl
              · exact hlvv l hl
              · exact hlb l hl
  | proj s idx x ihx =>
    intro k st st' e' h hb hlv
    rw [replaceAllNested] at h
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.fvarLeaves] at hlv
    split at h
    · obtain ⟨rfl, -⟩ := (by simpa using h : _ ∧ _)
      exact ⟨by simp [Expr.looseBVarsBounded, hb], fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl)⟩
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, n, rfl⟩ := replaceIfNested_shape heq
        exact hmimic (by simp [Expr.looseBVarsBounded, hb])
          (fun l hl => hlv l (by simpa [Expr.fvarLeaves] using hl))
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbx, hlx⟩ := ihx heq1 hb hlv
          exact ⟨by simp [Expr.looseBVarsBounded, hbx],
            fun l hl => hlx l (by simpa [Expr.fvarLeaves] using hl)⟩

/-! ## (R7) THE HEAD, BACKWARDS (task #315 L-B)

`replaceAllNested_head_const` says a spine at whose every prefix the
step DECLINES comes back with the head it went in with.  Its consumer
wants the contrapositive at an arbitrary head: the elimination's rewrite
sends a field's normalised domain `w` to the domain the auxiliary block
STORED, and at a field the block's classification calls recursive at a
COPY that stored domain is headed by the MIMIC.  `w` itself names no
copy — the copies are not in the environment `w`'s reading resolves in
(`denoteMeta_some_found`, `NestedCopyFound.lean`) — so some PREFIX of
`w`'s spine fired, and a firing is a recorded container's application
(`replaceIfNested_fire_inv`).
-/

/-- A term that is not an application is its own spine head. -/
theorem getAppFn_of_not_app : ∀ {e : Expr}, (∀ f a, e ≠ Expr.app f a) → e.getAppFn = e
  | .app f a, h => absurd rfl (h f a)
  | .bvar _, _ | .sort _, _ | .lit _, _ | .fvar _ _, _ | .const _ _, _
  | .lam _ _ _, _ | .forallE _ _ _, _ | .letE _ _ _, _ | .proj _ _ _, _ => rfl

/-- **THE HEAD AT A NON-APPLICATION**: the walk at a term that is not an
application either FIRES at it, or hands back a term with the same top
former — so a CONSTANT-headed output pins the input to that constant. -/
private theorem rw_nonApp_head {A : Name} {us : List Level}
    {st st' : ElimState} {e' : Expr} :
    ∀ {hd : Expr}, (∀ f a, hd ≠ Expr.app f a) →
      replaceAllNested env blvls params pbs₀ st hd = .ok (e', st') →
      e'.getAppFn = Expr.const A us →
      hd = Expr.const A us ∨
        ∃ r, replaceIfNested env blvls params pbs₀ st hd = .ok (some r) := by
  intro hd hna h h2
  have hsame : (Except.ok (hd, st) : CheckM (Expr × ElimState)) = .ok (e', st') →
      hd = Expr.const A us ∨
        ∃ r, replaceIfNested env blvls params pbs₀ st hd = .ok (some r) := by
    intro hu
    simp only [Except.ok.injEq, Prod.mk.injEq] at hu
    rw [← hu.1, getAppFn_of_not_app hna] at h2
    exact Or.inl h2
  cases hd with
  | app f a => exact absurd rfl (hna f a)
  | bvar i =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · exact hsame h
  | sort u =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · exact hsame h
  | lit l =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · exact hsame h
  | fvar i ty =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · exact hsame h
  | const m ws =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · exact hsame h
  | lam ty b bm =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · split at h
        · close_throw
        · split at h
          · close_throw
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1] at h2
            simp only [Expr.getAppFn] at h2
            exact nomatch h2
  | forallE ty b bm =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · split at h
        · close_throw
        · split at h
          · close_throw
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1] at h2
            simp only [Expr.getAppFn] at h2
            exact nomatch h2
  | letE ty v b =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · split at h
        · close_throw
        · split at h
          · close_throw
          · split at h
            · close_throw
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1] at h2
              simp only [Expr.getAppFn] at h2
              exact nomatch h2
  | proj s i x =>
    simp only [replaceAllNested] at h
    split at h
    · exact hsame h
    · split at h
      · close_throw
      · exact Or.inr ⟨_, by assumption⟩
      · split at h
        · close_throw
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1] at h2
          simp only [Expr.getAppFn] at h2
          exact nomatch h2

/-- **THE HEAD SURVIVES, OR A PREFIX FIRED** (task #315 L-B): the
contrapositive of `replaceAllNested_head_const` at an arbitrary head.
At a spine whose head is not itself an application, a walk whose output
is headed by a CONSTANT either went in with that same head, or
`replaceIfNested` FIRED at one of the spine's prefixes — the descent
into `.app f a` offers every prefix to the step at the ORIGINAL state,
which is what makes the disjunction uniform in the state. -/
theorem replaceAllNested_head_or_fire {A : Name} {us : List Level} {hd : Expr}
    (hna : ∀ f a, hd ≠ Expr.app f a) :
    ∀ (as : List Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st (Expr.mkAppN hd as) = .ok (e', st') →
      e'.getAppFn = Expr.const A us →
      hd = Expr.const A us ∨
        ∃ (k : Nat) (r : Expr × ElimState),
          replaceIfNested env blvls params pbs₀ st (Expr.mkAppN hd (as.take k))
            = .ok (some r) := by
  -- a reverse recursor, spelled here because the spine grows on the right
  have revRec : ∀ {motive : List Expr → Prop}, motive [] →
      (∀ (bs : List Expr) (b : Expr), motive bs → motive (bs ++ [b])) → ∀ bs, motive bs := by
    intro motive hnil hsnoc bs
    have key : ∀ cs : List Expr, motive cs.reverse := by
      intro cs
      induction cs with
      | nil => exact hnil
      | cons c cs ih =>
        rw [show (c :: cs).reverse = cs.reverse ++ [c] from by simp]
        exact hsnoc _ _ ih
    have h := key bs.reverse
    rwa [List.reverse_reverse] at h
  refine revRec ?_ ?_
  case _ =>
    intro st st' e' hrun h2
    rcases rw_nonApp_head hna hrun h2 with h | ⟨r, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨0, r, hr⟩
  case _ =>
    intro as a ih st st' e' hrun h2
    rw [mkAppN_concat] at hrun
    rw [replaceAllNested.eq_def] at hrun
    split at hrun
    · -- the prune: the spine comes back unchanged
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      rw [← hrun.1] at h2
      rw [show (Expr.mkAppN hd as).app a = Expr.mkAppN hd (as ++ [a]) from
          (mkAppN_concat as hd a).symm,
        Expr.getAppFn_mkAppN, getAppFn_of_not_app hna] at h2
      exact Or.inl h2
    · split at hrun
      · close_throw
      · -- the whole spine fired
        rename_i r hr
        refine Or.inr ⟨(as ++ [a]).length, r, ?_⟩
        rw [List.take_length, mkAppN_concat]
        exact hr
      · simp only at hrun
        cases hf : replaceAllNested env blvls params pbs₀ st (Expr.mkAppN hd as) with
        | error err => rw [hf] at hrun; exact nomatch hrun
        | ok rf =>
          obtain ⟨u', st₁⟩ := rf
          rw [hf] at hrun
          simp only at hrun
          cases ha : replaceAllNested env blvls params pbs₀ st₁ a with
          | error err => rw [ha] at hrun; simp only at hrun; exact nomatch hrun
          | ok ra =>
            obtain ⟨a', st₂⟩ := ra
            rw [ha] at hrun
            simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
            rw [← hrun.1] at h2
            simp only [Expr.getAppFn] at h2
            rcases ih hf h2 with h | ⟨k, r, hr⟩
            · exact Or.inl h
            · refine Or.inr ⟨min k as.length, r, ?_⟩
              rw [show (as ++ [a]).take (min k as.length) = as.take k from by
                rcases Nat.le_total k as.length with hle | hle
                · rw [show min k as.length = k from Nat.min_eq_left hle,
                    List.take_append_of_le_length hle]
                · rw [show min k as.length = as.length from Nat.min_eq_right hle,
                    List.take_left, List.take_of_length_le hle]]
              exact hr

/-- **A FIRING IS A RECORDED CONTAINER'S APPLICATION** (task #315 L-B):
the step's own guards, read backwards.  Whenever `replaceIfNested`
replaces a term, that term is an application whose head is a stored
inductive type former with a recorded container block, carrying at
least the block's parameters, and passing the occurrence test. -/
theorem replaceIfNested_fire_inv {st : ElimState} {e : Expr} {r : Expr × ElimState}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some r)) :
    ∃ (I : Name) (lvls : List Level) (cv : ConstantVal) (caps : IndCaps)
      (ci : ContainerInfo),
      e.getAppFn = Expr.const I lvls ∧ env.find? I = some (.indInfo cv caps) ∧
        containerInfo? env I = some ci ∧ ci.nP ≤ e.getAppArgs.length ∧
        nestedOccOk I st.newNames ci.nP e.getAppArgs = .ok true := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · rename_i I lvls hfn
      split at h
      · rename_i cv caps hfind
        split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · rename_i ci hci
            dsimp only at h
            split at h
            · close_throw
            · rename_i hlen
              obtain ⟨nested, hnest, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · rename_i hnt
                have hnested : nested = true := by
                  cases nested with
                  | true => rfl
                  | false => exact absurd rfl hnt
                exact ⟨I, lvls, cv, caps, ci, hfn, hfind, hci, by omega,
                  by rw [hnest, hnested]⟩
      · close_throw
    · close_throw
  · close_throw

/-- A spine head is never itself an application. -/
theorem getAppFn_not_app : ∀ (e f a : Expr), e.getAppFn ≠ Expr.app f a
  | .app g b, f, a => getAppFn_not_app g f a
  | .bvar _, _, _ | .sort _, _, _ | .lit _, _, _ | .fvar _ _, _, _ | .const _ _, _, _
  | .lam _ _ _, _, _ | .forallE _ _ _, _, _ | .letE _ _ _, _, _
  | .proj _ _ _, _, _ => by simp only [Expr.getAppFn]; exact nofun

/-- A term that is not an application has no spine arguments. -/
theorem getAppArgs_of_not_app : ∀ {e : Expr}, (∀ f a, e ≠ Expr.app f a) → e.getAppArgs = []
  | .app f a, h => absurd rfl (h f a)
  | .bvar _, _ | .sort _, _ | .lit _, _ | .fvar _ _, _ | .const _ _, _
  | .lam _ _ _, _ | .forallE _ _ _, _ | .letE _ _ _, _ | .proj _ _ _, _ => rfl

/-- **THE OCCURRENCE TEST'S VERDICT IS A FUNCTION OF THE PARAMETER
ARGUMENTS ALONE** (task #315 L-B): so it is the same at the whole spine
as at any prefix long enough to carry them. -/
private theorem nestedOccOk_take_congr {I : Name} {names : List Name} {nP : Nat}
    {as bs : List Expr} (h : as.take nP = bs.take nP) :
    nestedOccOk I names nP as = nestedOccOk I names nP bs := by
  unfold nestedOccOk
  simp only [h]

/-- **THE OCCURRENCE TEST'S TWO VERDICTS** (task #315 L-B): a `true`
says some parameter argument mentions a name of the growing list, and
the `.ok` says none of them carries a loose bound variable. -/
private theorem nestedOccOk_verdicts {I : Name} {names : List Name} {nP : Nat}
    {args : List Expr} (h : nestedOccOk I names nP args = .ok true) :
    ((args.take nP).any fun a => names.any fun T => a.mentionsConst T) = true ∧
    (∀ a ∈ args.take nP, a.looseBVarsBounded 0 = true) := by
  unfold nestedOccOk at h
  dsimp only at h
  split at h
  · close_throw
  · rename_i hcond
    simp only [Except.ok.injEq] at h
    refine ⟨h, ?_⟩
    rw [h, Bool.true_and] at hcond
    have hl : ((args.take nP).any fun a => !a.looseBVarsBounded 0) = false := by
      simpa using hcond
    intro a ha
    have := List.any_eq_false.mp hl a ha
    simpa using this

/-- **THE BACKWARDS INVERSION** (task #315 L-B, DESIGN "the backwards
inversion"): a walk whose OUTPUT is headed by a constant its INPUT is
not headed by has fired at the TOP, and the firing gives the input's
head as a RECORDED CONTAINER, the pin at its parameter arguments, and
the output as the MIMIC applied to the walk's parameters and the
occurrence's indices.

This is `replaceAllNested_occurrence` read the other way round, and it
is what an `ordF`-RIGHT field at a PIN target wants: the auxiliary
block's classification says the STORED domain is headed by the mimic at
`p.k + q`, the mimic is a copy and a copy is in no environment the
field's normalised domain `w` reads in, so `w` is the CONTAINER's
application — with no analysis of `w`'s syntax anywhere.

**The fire is at the TOP even though the inversion finds it at a
prefix.**  `nestedOccOk`'s verdict depends only on `args.take ci.nP`,
which every prefix long enough to be tested shares with the whole spine
(`nestedOccOk_take_congr`), and the shorter prefixes decline on the
length test.  The walk is top-down, so the whole spine was offered
first: a prefix that fires means the top fired.  That is what yields the
OUTPUT's shape and not merely its head — and the shape is what ties the
copy's recorded index expressions to `w`'s own index arguments.

The side condition is stated at the HEAD, which is all the proof uses
and all a consumer can cheaply supply: it is NOT a preservation property
of the positivity walk, but a consequence of `w` READING at the
members-only environment — `denoteMeta_head_ne_fresh`
(`Model/Inductives/NestedCopyFound.lean`) off the `denoteMeta` conjunct
`copyFieldReadCoreQ` already returns. -/
theorem replaceAllNested_container_head {A : Name} {us : List Level}
    {st st' : ElimState} {e e' : Expr}
    (hrun : replaceAllNested env blvls params pbs₀ st e = .ok (e', st'))
    (hhead : e'.getAppFn = Expr.const A us)
    (hfree : e.getAppFn ≠ Expr.const A us) :
    ∃ (I : Name) (lvls : List Level) (cv : ConstantVal) (caps : IndCaps)
      (ci : ContainerInfo) (q : NestedPin),
      e.getAppFn = Expr.const I lvls ∧
        env.find? I = some (.indInfo cv caps) ∧
        containerInfo? env I = some ci ∧
        ci.nP ≤ e.getAppArgs.length ∧
        q ∈ st'.pins ∧
        q.pin = Expr.mkAppN (.const I lvls) (e.getAppArgs.take ci.nP) ∧
        e' = Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params)
              (e.getAppArgs.drop ci.nP) := by
  have hna : ∀ f a, e.getAppFn ≠ Expr.app f a := getAppFn_not_app e
  have hsp : Expr.mkAppN e.getAppFn e.getAppArgs = e := Expr.mkAppN_getApp e
  have hrun' : replaceAllNested env blvls params pbs₀ st
      (Expr.mkAppN e.getAppFn e.getAppArgs) = .ok (e', st') := by rw [hsp]; exact hrun
  rcases replaceAllNested_head_or_fire hna e.getAppArgs hrun' hhead with hcst | ⟨k, r, hr⟩
  · exact absurd hcst hfree
  obtain ⟨I, lvls, cv, caps, ci, hfnP, hfind, hci, hlenP, hocc⟩ := replaceIfNested_fire_inv hr
  have hargs : (Expr.mkAppN e.getAppFn (e.getAppArgs.take k)).getAppArgs
      = e.getAppArgs.take k := by
    rw [Expr.getAppArgs_mkAppN, getAppArgs_of_not_app hna, List.nil_append]
  have hfn : e.getAppFn = Expr.const I lvls := by
    rwa [Expr.getAppFn_mkAppN, getAppFn_of_not_app hna] at hfnP
  rw [hargs] at hlenP hocc
  simp only [List.length_take] at hlenP
  have hnPk : ci.nP ≤ k := by omega
  have hnPlen : ci.nP ≤ e.getAppArgs.length := by omega
  -- the top fired too: the verdict is the prefix's
  have hoccFull : nestedOccOk I st.newNames ci.nP e.getAppArgs = .ok true :=
    (nestedOccOk_take_congr (I := I) (names := st.newNames)
      (by rw [List.take_take, Nat.min_eq_left hnPk])).trans hocc
  obtain ⟨hment, hloose⟩ := nestedOccOk_verdicts hoccFull
  have he : e = Expr.mkAppN (.const I lvls) e.getAppArgs := by
    rw [← hfn]; exact hsp.symm
  obtain ⟨q, hqm, hqp, hqe⟩ :=
    replaceAllNested_occurrence he hfind hci hnPlen hment hloose hrun
  exact ⟨I, lvls, cv, caps, ci, q, hfn, hfind, hci, hnPlen, hqm, hqp, hqe⟩

/-- **THE FIRED PIN IS ONE THE WALK WENT IN WITH** (task #315 L-B):
`replaceAllNested_container_head` at a walk that MINTS NOTHING — which
is exactly what K.51's two length conjuncts certify about the
elimination's own rewrite at the FINAL state.  The walk's pins are a
prefix of its output's and the output's have the length it started with,
so the prefix is an equality and the pin can be named by its INDEX. -/
theorem replaceAllNested_container_head_stable {A : Name} {us : List Level}
    {st st' : ElimState} {e e' : Expr}
    (hrun : replaceAllNested env blvls params pbs₀ st e = .ok (e', st'))
    (hhead : e'.getAppFn = Expr.const A us)
    (hfree : e.getAppFn ≠ Expr.const A us)
    (hstable : st'.pins.length ≤ st.pins.length) :
    ∃ (I : Name) (lvls : List Level) (cv : ConstantVal) (caps : IndCaps)
      (ci : ContainerInfo) (q : NestedPin),
      e.getAppFn = Expr.const I lvls ∧
        env.find? I = some (.indInfo cv caps) ∧
        containerInfo? env I = some ci ∧
        ci.nP ≤ e.getAppArgs.length ∧
        q ∈ st.pins ∧
        q.pin = Expr.mkAppN (.const I lvls) (e.getAppArgs.take ci.nP) ∧
        e' = Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params)
              (e.getAppArgs.drop ci.nP) := by
  obtain ⟨I, lvls, cv, caps, ci, q, hfn, hfind, hci, hnP, hqm, hqp, hqe⟩ :=
    replaceAllNested_container_head hrun hhead hfree
  have hpre := (replaceAllNested_pins_prefix e hrun).1
  have heq : st.pins = st'.pins := hpre.eq_of_length_le hstable
  exact ⟨I, lvls, cv, caps, ci, q, hfn, hfind, hci, hnP, heq ▸ hqm, hqp, hqe⟩

end ConLeche
