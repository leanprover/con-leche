module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
public import ConLeche.Verify.Inductives.NestedRestoreTbl
public import ConLeche.Verify.Inductives.NestedInv
public import ConLeche.Verify.EraseAnnots
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.StructRec

public section

/-!
# The restore's syntactic kit (task #315)

Small, self-contained facts the nested restore's reading law needs and
that no existing module states: how `mentionsFvar` and `mentionsConst`
are settled by the scope and resolution invariants, how the `∀`-telescope
operators (`stripPis`, `mkPisB`, `piBinders`, `openPisAtFvars`) commute
with the restore walk, what the restore table's `pins` lookup and
`auxNames` say about the elimination state, and the head/argument shape
of a pin re-opened at the block's parameters.

Every name carries the `rk` prefix (the lane's namespace discipline).
-/

namespace ConLeche

open Expr

/-! ## Variables -/

/-- A well-scoped term mentions no variable at or above its scope. -/
theorem rk_mentionsFvar_false_of_WScoped {d q : Nat} :
    ∀ {e : Expr}, Expr.WScoped d e → d ≤ q → e.mentionsFvar q = false := by
  intro e
  induction e generalizing d with
  | bvar i => intro _ _; exact mentionsFvar_bvar
  | sort u => intro _ _; exact mentionsFvar_sort
  | const n us => intro _ _; exact mentionsFvar_const
  | lit l => intro _ _; exact mentionsFvar_lit
  | fvar idx ty ih =>
    intro h hq
    simp only [Expr.WScoped] at h
    obtain ⟨h1, h2⟩ := h
    rw [Expr.mentionsFvar_fvar, ih h2 (by omega), Bool.or_false,
      beq_eq_false_iff_ne]
    omega
  | app f a ihf iha =>
    intro h hq
    simp only [Expr.WScoped] at h
    rw [Expr.mentionsFvar_app, ihf h.1 hq, iha h.2 hq]
    rfl
  | lam ty b m ihty ihb =>
    intro h hq
    simp only [Expr.WScoped] at h
    rw [Expr.mentionsFvar_lam, ihty h.1 hq, ihb h.2 hq]
    rfl
  | forallE ty b m ihty ihb =>
    intro h hq
    simp only [Expr.WScoped] at h
    rw [Expr.mentionsFvar_forallE, ihty h.1 hq, ihb h.2 hq]
    rfl
  | letE ty v b ihty ihv ihb =>
    intro h hq
    simp only [Expr.WScoped] at h
    rw [Expr.mentionsFvar_letE, ihty h.1 hq, ihv h.2.1 hq, ihb h.2.2 hq]
    rfl
  | proj s i x ih =>
    intro h hq
    simp only [Expr.WScoped] at h
    rw [Expr.mentionsFvar_proj, ih h hq]

/-- A term with no free variable at all mentions none. -/
theorem rk_mentionsFvar_false_of_not_hasFvar {q : Nat} :
    ∀ {e : Expr}, e.hasFvar = false → e.mentionsFvar q = false := by
  intro e
  induction e with
  | bvar i => intro _; exact mentionsFvar_bvar
  | sort u => intro _; exact mentionsFvar_sort
  | const n us => intro _; exact mentionsFvar_const
  | lit l => intro _; exact mentionsFvar_lit
  | fvar idx ty _ => intro h; exact absurd h (by simp [Expr.hasFvar])
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    rw [Expr.mentionsFvar_app, ihf h.1, iha h.2]
    rfl
  | lam ty b m ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    rw [Expr.mentionsFvar_lam, ihty h.1, ihb h.2]
    rfl
  | forallE ty b m ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    rw [Expr.mentionsFvar_forallE, ihty h.1, ihb h.2]
    rfl
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    rw [Expr.mentionsFvar_letE, ihty h.1.1, ihv h.1.2, ihb h.2]
    rfl
  | proj s i x ih =>
    intro h
    simp only [Expr.hasFvar] at h
    rw [Expr.mentionsFvar_proj, ih h]

/-- A term whose parameter abstraction has no free variable left had
all of its variables inside the abstracted range. -/
theorem rk_fvarsBelow_of_abstractRange_noFvar {k : Nat} :
    ∀ {e : Expr}, (e.abstractRange 0 k 0).hasFvar = false → e.fvarsBelow k := by
  have key : ∀ (e : Expr) (c : Nat),
      (e.abstractRange 0 k c).hasFvar = false → e.fvarsBelow k := by
    intro e
    induction e with
    | bvar i => intro _ _; trivial
    | sort u => intro _ _; trivial
    | const n us => intro _ _; trivial
    | lit l => intro _ _; trivial
    | fvar idx ty _ =>
      intro c h
      simp only [Expr.abstractRange] at h
      split at h
      · rename_i hlt
        show idx < k
        omega
      · exact absurd h (by simp [Expr.hasFvar])
    | app f a ihf iha =>
      intro c h
      simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
      exact ⟨ihf c h.1, iha c h.2⟩
    | lam ty b m ihty ihb =>
      intro c h
      simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
      exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
    | forallE ty b m ihty ihb =>
      intro c h
      simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
      exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
    | letE ty v b ihty ihv ihb =>
      intro c h
      simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
      exact ⟨ihty c h.1.1, ihv c h.1.2, ihb (c + 1) h.2⟩
    | proj s i x ih =>
      intro c h
      simp only [Expr.abstractRange, Expr.hasFvar] at h
      exact ih c h
  intro e h
  exact key e 0 h

/-- Erasure turns a variable bound into well-scopedness: the erased
annotations are closed. -/
theorem rk_WScoped_eraseAnnots_of_fvarsBelow {d : Nat} :
    ∀ {e : Expr}, e.fvarsBelow d → Expr.WScoped d e.eraseAnnots := by
  intro e
  induction e with
  | bvar i => intro _; simp [Expr.eraseAnnots, Expr.WScoped]
  | sort u => intro _; simp [Expr.eraseAnnots, Expr.WScoped]
  | const n us => intro _; simp [Expr.eraseAnnots, Expr.WScoped]
  | lit l => intro _; simp [Expr.eraseAnnots, Expr.WScoped]
  | fvar idx ty _ =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨h, by simp⟩
  | app f a ihf iha =>
    intro h
    exact (by simp only [Expr.eraseAnnots, Expr.WScoped]; exact ⟨ihf h.1, iha h.2⟩)
  | lam ty b m ihty ihb =>
    intro h
    exact (by simp only [Expr.eraseAnnots, Expr.WScoped]; exact ⟨ihty h.1, ihb h.2⟩)
  | forallE ty b m ihty ihb =>
    intro h
    exact (by simp only [Expr.eraseAnnots, Expr.WScoped]; exact ⟨ihty h.1, ihb h.2⟩)
  | letE ty v b ihty ihv ihb =>
    intro h
    exact (by
      simp only [Expr.eraseAnnots, Expr.WScoped]
      exact ⟨ihty h.1, ihv h.2.1, ihb h.2.2⟩)
  | proj s i x ih =>
    intro h
    exact (by simp only [Expr.eraseAnnots, Expr.WScoped]; exact ih h)

/-! ## Constants -/

/-- A term whose constants all resolve mentions no name the environment
does not hold. -/
theorem rk_mentionsConst_false_of_constsResolve {env : Env} {n : Name} :
    ∀ {e : Expr}, e.constsResolve env = true → env.find? n = none →
      e.mentionsConst n = false := by
  intro e
  induction e with
  | bvar i => intro _ _; rfl
  | sort u => intro _ _; rfl
  | lit l => intro _ _; rfl
  | const m us =>
    intro h hn
    simp only [Expr.constsResolve] at h
    simp only [Expr.mentionsConst, beq_eq_false_iff_ne, ne_eq]
    intro hc
    rw [hc, hn] at h
    simp at h
  | fvar idx ty ih =>
    intro h hn
    exact ih h hn
  | app f a ihf iha =>
    intro h hn
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, ihf h.1 hn, iha h.2 hn]
    rfl
  | lam ty b m ihty ihb =>
    intro h hn
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, ihty h.1 hn, ihb h.2 hn]
    rfl
  | forallE ty b m ihty ihb =>
    intro h hn
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, ihty h.1 hn, ihb h.2 hn]
    rfl
  | letE ty v b ihty ihv ihb =>
    intro h hn
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, ihty h.1.1 hn, ihv h.1.2 hn, ihb h.2 hn]
    rfl
  | proj s i x ih =>
    intro h hn
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, ih h.2 hn, Bool.or_false,
      beq_eq_false_iff_ne, ne_eq]
    intro hc
    have h1 := h.1
    rw [hc, hn] at h1
    simp at h1

/-- Opening a `∀`-telescope keeps every constant resolvable: the
variables' annotations and the residual all resolve. -/
theorem rk_openPisAtFvars_constsResolve {env : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → e.constsResolve env = true →
      (∀ x ∈ fvs, x.fvarTypeD.constsResolve env = true) ∧
        o.constsResolve env = true := by
  intro n
  induction n with
  | zero =>
    intro e d fvs o h he
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by intro x hx; exact absurd hx (by simp), he⟩
  | succ n ih =>
    intro e d fvs o h he
    cases e with
    | forallE dom body bm =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars n (body.instantiate1 (.fvar d dom)) (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some pr =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.constsResolve, Bool.and_eq_true] at he
        obtain ⟨hdom, hbody⟩ := he
        obtain ⟨hfvs, ho⟩ := ih hop (Expr.constsResolve_instantiate1 hdom 0 hbody)
        refine ⟨?_, ho⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hfvs x hx
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

/-! ## Telescopes -/

/-- `mkPisB` is stripped by `stripPis` at its own length. -/
theorem rk_mkPisB_stripPis : ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
    (mkPisB bs body).stripPis bs.length = some (bs, body)
  | [], _ => rfl
  | b :: bs, body => by
    show (Expr.forallE b.1 (mkPisB bs body) b.2).stripPis (bs.length + 1) = _
    rw [Expr.stripPis, rk_mkPisB_stripPis bs body]
    rfl

/-- **The restore walk commutes with `stripPis`**: the walk of a
`∀`-telescope is a `∀`-telescope of the same length, with the same
binder data, whose body is the walk of the body at the deeper level. -/
theorem rk_restoreWalk_stripPis {R : RestoreTbl} :
    ∀ (n : Nat) {d : Nat} {e e' : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      restoreWalk R d e = .ok e' → e.stripPis n = some (bs, body) →
      ∃ (bs' : List (Expr × BinderMeta)) (body' : Expr),
        e'.stripPis n = some (bs', body') ∧ restoreWalk R (d + n) body = .ok body' ∧
          bs'.length = bs.length ∧ bs'.map (·.2) = bs.map (·.2) := by
  intro n
  induction n with
  | zero =>
    intro d e e' bs body hw hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨[], e', rfl, hw, rfl, rfl⟩
  | succ n ih =>
    intro d e e' bs body hw hs
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at hs
      cases hb : b.stripPis n with
      | none => rw [hb] at hs; exact nomatch hs
      | some pr =>
        obtain ⟨bs₀, body₀⟩ := pr
        rw [hb] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ty', b', hty, hbw, rfl⟩ := restoreWalk_forallE_inv hw
        obtain ⟨bs', body', hs', hw', hlen, hmeta⟩ := ih hbw hb
        refine ⟨(ty', bm) :: bs', body', ?_, ?_, ?_, ?_⟩
        · rw [Expr.stripPis, hs']; rfl
        · rw [show d + (n + 1) = d + 1 + n by omega]; exact hw'
        · simp only [List.length_cons, hlen]
        · simp only [List.map_cons, hmeta]
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch hs

/-- **Splitting a strip**: a telescope stripped at `k + m` strips at
`k` and then at `m`, at the two halves of the binder list. -/
theorem rk_stripPis_split :
    ∀ (k m : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis (k + m) = some (bs, body) →
      ∃ mid : Expr, e.stripPis k = some (bs.take k, mid) ∧
        mid.stripPis m = some (bs.drop k, body) := by
  intro k
  induction k with
  | zero =>
    intro m e bs body h
    exact ⟨e, rfl, by simpa using h⟩
  | succ k ih =>
    intro m e bs body h
    rw [show k + 1 + m = k + m + 1 by omega] at h
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at h
      cases hb : b.stripPis (k + m) with
      | none => rw [hb] at h; exact nomatch h
      | some pr =>
        obtain ⟨bs₀, body₀⟩ := pr
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mid, h1, h2⟩ := ih m hb
        refine ⟨mid, ?_, ?_⟩
        · rw [Expr.stripPis, h1]
          simp
        · simpa using h2
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

/-- **The restored constructor type strips to the SAME residual**: the
walk rewrites only inside the parameter and field domains — a residual
mentioning no auxiliary name is its own restoration. -/
theorem rk_restoreNested_stripPis {R : RestoreTbl} {nP nF : Nat} (hnP : R.nP = nP)
    {tyA tyR : Expr} {cbs : List (Expr × BinderMeta)} {resid : Expr}
    (hstrip : tyA.stripPis (nP + nF) = some (cbs, resid))
    (hres : restoreNested R tyA = .ok tyR)
    (hfree : ∀ n ∈ R.auxNames, resid.mentionsConst n = false) :
    ∃ cbs' : List (Expr × BinderMeta), tyR.stripPis (nP + nF) = some (cbs', resid) ∧
      cbs'.map (·.2) = cbs.map (·.2) := by
  obtain ⟨mid, h1, h2⟩ := rk_stripPis_split nP nF hstrip
  have hcl : cbs.length = nP + nF := stripPis_length _ hstrip
  have htk : (cbs.take nP).length = nP := by
    rw [List.length_take, hcl]; omega
  have hs : tyA.stripPis R.nP = some (cbs.take nP, mid) := by rw [hnP]; exact h1
  have hpi : 0 < R.nP → ∃ ty b bm, tyA = Expr.forallE ty b bm := by
    intro hlt
    rw [hnP] at hlt
    obtain ⟨j, rfl⟩ : ∃ j, nP = j + 1 := ⟨nP - 1, by omega⟩
    cases tyA with
    | forallE ty b bm => exact ⟨ty, b, bm, rfl⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h1
  obtain ⟨body', hw, rfl⟩ := restoreNested_pis hs hpi hres
  obtain ⟨bs', body'', hsb, hw', -, hmeta⟩ := rk_restoreWalk_stripPis nF hw h2
  have hresid : restoreWalk R (0 + nF) resid = .ok resid :=
    restoreWalk_of_no_aux (0 + nF) resid hfree
  obtain rfl : body'' = resid := Except.ok.inj (hw'.symm.trans hresid)
  rw [mkPisB_eq_foldr]
  refine ⟨cbs.take nP ++ bs', stripPis_append nP ?_ hsb, ?_⟩
  · have hmk := rk_mkPisB_stripPis (cbs.take nP) body'
    rw [htk] at hmk
    exact hmk
  · rw [List.map_append, hmeta, ← List.map_append, List.take_append_drop]

/-! ## The restore table -/

/-- Inversion for a pin-map `lookup` over a raw pin list. -/
theorem rk_pinsLookupInv {nP : Nat} {n : Name} {pin : Expr} :
    ∀ {l : List NestedPin},
      (l.map fun q => (q.aux, Expr.abstractRange q.pin 0 nP 0)).lookup n = some pin →
      ∃ q ∈ l, q.aux = n ∧ pin = Expr.abstractRange q.pin 0 nP 0
  | [], h => by exact absurd h (by simp)
  | q :: rest, h => by
    rw [List.map_cons, List.lookup_cons] at h
    split at h
    · rename_i he
      exact ⟨q, List.mem_cons_self .., (beq_iff_eq.mp he).symm,
        (Option.some.inj h).symm⟩
    · obtain ⟨q', hq', hn, hp⟩ := rk_pinsLookupInv h
      exact ⟨q', List.mem_cons_of_mem _ hq', hn, hp⟩

/-- **Inversion of the pin map**: every `lookup` hit is a recorded pin,
abstracted at the block's parameters. -/
theorem rk_restoreTbl_pins_lookup_inv {p : NestedParts} {st : ElimState} {n : Name}
    {pin : Expr} (h : (restoreTbl p st).pins.lookup n = some pin) :
    ∃ q ∈ st.pins, q.aux = n ∧ pin = Expr.abstractRange q.pin 0 p.nP 0 := by
  simp only [restoreTbl] at h
  exact rk_pinsLookupInv h

/-- **The closure guard, read at a pin**: the abstracted pin carries no
free variable and no loose bound variable above the parameters. -/
theorem rk_pinsClosed_of {nP : Nat} {pins : List NestedPin}
    (h : pinsClosed nP pins = true) :
    ∀ q ∈ pins, (Expr.abstractRange q.pin 0 nP 0).hasFvar = false ∧
      (Expr.abstractRange q.pin 0 nP 0).looseBVarsBounded nP = true := by
  intro q hq
  simp only [pinsClosed, List.all_eq_true] at h
  have hq' := h q hq
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hq'
  exact hq'

/-! ## Spines and substitution

The spine roundtrip `e = Expr.mkAppN e.getAppFn e.getAppArgs` is NOT
restated here: it already exists as `Expr.mkAppN_getApp`
(`ConLeche/Verify/InferLemmas.lean`), in the orientation
`Expr.mkAppN e.getAppFn e.getAppArgs = e`.
-/

/-- `instSeq` distributes over an application spine. -/
theorem rk_instSeq_mkAppN : ∀ (vs : List Expr) (t : Nat) (f : Expr) (as : List Expr),
    Expr.instSeq vs t (Expr.mkAppN f as)
      = Expr.mkAppN (Expr.instSeq vs t f) (as.map (Expr.instSeq vs t)) := by
  intro vs
  induction vs with
  | nil =>
    intro t f as
    have hid : as.map (Expr.instSeq [] t) = as := by
      induction as with
      | nil => rfl
      | cons a as ih => rw [List.map_cons, ih]; rfl
    rw [hid]
    rfl
  | cons v vs ih =>
    intro t f as
    show Expr.instSeq vs (t - 1) ((Expr.mkAppN f as).instantiate1 v t) = _
    rw [mkAppN_instantiate1, ih, List.map_map]
    rfl

/-- A closed term is its own `instSeq`. -/
theorem rk_instSeq_eq_self_of_bounded : ∀ (vs : List Expr) (t : Nat) {e : Expr},
    e.looseBVarsBounded 0 = true → Expr.instSeq vs t e = e := by
  intro vs
  induction vs with
  | nil => intro _ _ _; rfl
  | cons v vs ih =>
    intro t e hb
    show Expr.instSeq vs (t - 1) (e.instantiate1 v t) = e
    rw [instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le t) hb)]
    exact ih (t - 1) hb

/-! ## `∀`-telescopes, built -/

/-- A variable absent from every domain and from the body is absent
from the telescope. -/
theorem rk_mentionsFvar_mkPisB_false {q : Nat} :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
      (∀ b ∈ bs, b.1.mentionsFvar q = false) → body.mentionsFvar q = false →
      (mkPisB bs body).mentionsFvar q = false
  | [], _, _, hbody => hbody
  | b :: bs, body, hbs, hbody => by
    show (Expr.forallE b.1 (mkPisB bs body) b.2).mentionsFvar q = false
    rw [Expr.mentionsFvar_forallE, hbs b List.mem_cons_self,
      rk_mentionsFvar_mkPisB_false bs body
        (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hbody]
    rfl

/-- The converse: a variable absent from the telescope is absent from
every domain and from the body. -/
theorem rk_mentionsFvar_mkPisB_false_inv {q : Nat} :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
      (mkPisB bs body).mentionsFvar q = false →
      (∀ b ∈ bs, b.1.mentionsFvar q = false) ∧ body.mentionsFvar q = false
  | [], _, h => ⟨by intro b hb; exact absurd hb (by simp), h⟩
  | b :: bs, body, h => by
    rw [show mkPisB (b :: bs) body = Expr.forallE b.1 (mkPisB bs body) b.2 from rfl,
      Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at h
    obtain ⟨hrest, hbody⟩ := rk_mentionsFvar_mkPisB_false_inv bs body h.2
    refine ⟨?_, hbody⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact hrest x hx

/-- `piBinders` finds exactly the binders `mkPisB` put there, when the
body is not itself a `∀` (its head is a constant). -/
theorem rk_piBinders_mkPisB_length : ∀ (bs : List (Expr × BinderMeta)) (body : Expr)
    {n : Name} {us : List Level}, body.getAppFn = .const n us →
    ((mkPisB bs body).piBinders).1.length = bs.length
  | [], body, _, _, h => by
    show (body.piBinders).1.length = 0
    cases body with
    | forallE ty b bm => exact nomatch h
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => rfl
  | b :: bs, body, _, _, h => by
    show ((Expr.forallE b.1 (mkPisB bs body) b.2).piBinders).1.length = bs.length + 1
    simp only [Expr.piBinders, List.length_cons]
    rw [rk_piBinders_mkPisB_length bs body h]

/-! ## The restored pin -/

/-- **The restored pin keeps its head**: re-opening the abstracted pin
at the parameter variables changes only annotations. -/
theorem rk_restoredPin_getAppFn {nP : Nat} {J : Name} {lvls : List Level}
    {DsE : List Expr} {fvsP : List Expr} (hlenP : fvsP.length = nP)
    (hidx : ∀ k, k < nP → ∃ ty, fvsP[k]? = some (.fvar k ty))
    (hb : (Expr.mkAppN (.const J lvls) DsE).looseBVarsBounded 0 = true) :
    (Expr.instSeq fvsP (nP - 1)
        (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0)).getAppFn
      = .const J lvls := by
  have he := eraseAnnots_openAbstract (nP := nP)
    (Expr.mkAppN (.const J lvls) DsE) hb fvsP hlenP hidx
  have h2 : (Expr.mkAppN (.const J lvls) DsE).eraseAnnots
      = Expr.mkAppN (.const J lvls) (DsE.map Expr.eraseAnnots) := by
    rw [eraseAnnots_mkAppN]; rfl
  have h3 := getAppFn_eraseAnnots (Expr.instSeq fvsP (nP - 1)
    (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0))
  rw [he, h2, Expr.getAppFn_mkAppN] at h3
  exact eraseAnnots_eq_const h3.symm

/-- **The restored pin keeps its argument count.** -/
theorem rk_restoredPin_getAppArgs_length {nP : Nat} {J : Name} {lvls : List Level}
    {DsE : List Expr} {fvsP : List Expr} (hlenP : fvsP.length = nP)
    (hidx : ∀ k, k < nP → ∃ ty, fvsP[k]? = some (.fvar k ty))
    (hb : (Expr.mkAppN (.const J lvls) DsE).looseBVarsBounded 0 = true) :
    (Expr.instSeq fvsP (nP - 1)
        (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0)).getAppArgs.length
      = DsE.length := by
  have he := eraseAnnots_openAbstract (nP := nP)
    (Expr.mkAppN (.const J lvls) DsE) hb fvsP hlenP hidx
  have h2 : (Expr.mkAppN (.const J lvls) DsE).eraseAnnots
      = Expr.mkAppN (.const J lvls) (DsE.map Expr.eraseAnnots) := by
    rw [eraseAnnots_mkAppN]; rfl
  have h3 := getAppArgs_eraseAnnots (Expr.instSeq fvsP (nP - 1)
    (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0))
  rw [he, h2, Expr.getAppArgs_mkAppN,
    show (Expr.const J lvls).getAppArgs = [] from rfl, List.nil_append] at h3
  have h4 := congrArg List.length h3
  simpa using h4.symm

/-- **The restored pin mentions no field variable**: the pin is
variable-free and the openers are chosen fresh. -/
theorem rk_restoredPin_mentionsFvar_false {nP q : Nat} {pin : Expr} {fvsP : List Expr}
    (hfv : pin.hasFvar = false) (hP : ∀ v ∈ fvsP, v.mentionsFvar q = false) :
    (Expr.instSeq fvsP (nP - 1) pin).mentionsFvar q = false :=
  mentionsFvar_instSeq_of_false fvsP (nP - 1)
    (rk_mentionsFvar_false_of_not_hasFvar hfv) hP

/-! ## Bound variables under an opener -/

/-- **Inversion of the loose-bvar bound under one opening**: a body
bounded after its binder is opened at a variable was bounded one
binder deeper. -/
theorem rk_looseBVarsBounded_instantiate1_inv {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).looseBVarsBounded k = true →
      e.looseBVarsBounded (k + 1) = true := by
  intro e
  induction e with
  | sort u => intro _ _; rfl
  | const n us => intro _ _; rfl
  | lit l => intro _ _; rfl
  | fvar idx ty' _ => intro _ _; rfl
  | bvar i =>
    intro k h
    simp only [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    split at h
    · omega
    · split at h
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
        omega
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
        omega
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i x ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.looseBVarsBounded] at h
    simp only [Expr.looseBVarsBounded]
    exact ih k h

/-- Two equal entries of a `Nodup` list sit at the same index. -/
theorem rk_nodupIdxEq {L : List Name} (hL : L.Nodup) {u w : Nat} {v : Name}
    (hu : L[u]? = some v) (hw : L[w]? = some v) : u = w := by
  obtain ⟨hu', hu''⟩ := List.getElem?_eq_some_iff.mp hu
  obtain ⟨hw', hw''⟩ := List.getElem?_eq_some_iff.mp hw
  have e1 : List.idxOf v L = u := by rw [← hu'']; exact hL.idxOf_getElem u hu'
  have e2 : List.idxOf v L = w := by rw [← hw'']; exact hL.idxOf_getElem w hw'
  omega

/-- **THE RESTORE TABLE'S `auxNames` ARE THE MINT'S OWN NAMES**: every
name the walk may fire on is fresh in the pre-block environment and is
not one of the block's own `k` members.  The copies' freshness guard
answers the first half; the auxiliary block's `blockNames.Nodup`, read
through the pins/types alignment, answers the second. -/
theorem rk_restoreTbl_auxNames_fresh {env : Env} {p : NestedParts} {st : ElimState}
    {b : MutualBlock} (hnd : b.blockNames.Nodup) (hal : PinsAligned p.k st)
    (hb : auxBlock p st = some b) (hfresh : copiesFresh env p.k st = true) :
    ∀ n ∈ (restoreTbl p st).auxNames, env.find? n = none ∧ n ∉ b.memberNames.take p.k := by
  rw [MutualBlock.blockNames] at hnd
  have hlen := hal.1
  have hmn : b.memberNames = st.types.map (·.name) := auxBlock_memberNames_eq hb
  have hmemNd : b.memberNames.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hdmc : ∀ a ∈ b.memberNames, ∀ c ∈ b.ctors.map (·.cv.name), a ≠ c :=
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  have hdr : ∀ a ∈ b.memberNames ++ b.ctors.map (·.cv.name),
      ∀ c ∈ (List.range b.k).map b.recName, a ≠ c := (List.nodup_append.mp hnd).2.2
  have hk : b.k = st.types.length := auxBlock_k hb
  obtain ⟨-, hform⟩ := auxBlock_former hb
  have hctors := (auxBlock_fields hb).2.2.2
  have hcopy : ∀ x ∈ nestedCopyNames p.k st, env.find? x = none := by
    intro x hx
    simp only [copiesFresh, List.all_eq_true] at hfresh
    simpa using hfresh x hx
  have htake : ∀ (x : Name), x ∈ b.memberNames.take p.k →
      ∃ i, i < p.k ∧ b.memberNames[i]? = some x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hi
    split at hi
    · exact ⟨i, by assumption, hi⟩
    · exact absurd hi (by simp)
  have hpinT : ∀ (j : Nat) (q : NestedPin), st.pins[j]? = some q →
      ∃ t, st.types[p.k + j]? = some t ∧ t.name = q.aux ∧ t ∈ st.types.drop p.k := by
    intro j q hj
    obtain ⟨t, ht, htn⟩ := hal.2 j q hj
    refine ⟨t, ht, htn, List.mem_of_getElem? (i := j) ?_⟩
    rw [List.getElem?_drop]
    exact ht
  have hcn : ∀ (t : AuxType), t ∈ st.types.drop p.k →
      t.name ∈ nestedCopyNames p.k st ∧ t.name.str "rec" ∈ nestedCopyNames p.k st ∧
        ∀ c ∈ t.ctors, c.1 ∈ nestedCopyNames p.k st := by
    intro t ht
    simp only [nestedCopyNames, List.mem_flatMap]
    refine ⟨⟨t, ht, List.mem_cons_self ..⟩,
      ⟨t, ht, List.mem_cons_of_mem _ List.mem_cons_self⟩, ?_⟩
    intro c hc
    exact ⟨t, ht, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨c, hc, rfl⟩))⟩
  have hmni : ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      b.memberNames[i]? = some t.name := by
    intro i t hi
    rw [hmn]
    simp only [List.getElem?_map, hi, Option.map_some]
  have hctorName : ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      ∀ c ∈ t.ctors, c.1 ∈ b.ctors.map (·.cv.name) := by
    intro i t hi c hc
    rw [hctors]
    refine List.mem_map.mpr ⟨⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, i⟩, ?_, rfl⟩
    refine List.mem_flatten.mpr ⟨t.ctors.map fun c =>
      (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, i⟩ : MutualCtor), ?_, List.mem_map.mpr ⟨c, hc, rfl⟩⟩
    exact List.mem_map.mpr ⟨(t, i), List.mk_mem_zipIdx_iff_getElem?.mpr hi, rfl⟩
  have hrecName : ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      b.recName i = t.name.str "rec" := by
    intro i t hi
    obtain ⟨nIdx, hfo, -⟩ := hform i t hi
    simp only [MutualBlock.recName, List.getD_eq_getElem?_getD, hfo, Option.getD_some]
  intro n hn
  simp only [restoreTbl] at hn
  rcases List.mem_append.mp hn with hn | hn
  · rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
      obtain ⟨t, ht, htn, htd⟩ := hpinT j q hj
      refine ⟨by rw [← htn]; exact hcopy _ (hcn t htd).1, ?_⟩
      intro hmem
      obtain ⟨i, hilt, hi⟩ := htake _ hmem
      have h2 : b.memberNames[p.k + j]? = some q.aux := by
        rw [hmni (p.k + j) t ht, htn]
      exact absurd (rk_nodupIdxEq hmemNd hi h2) (by omega)
    · simp only [List.mem_flatMap] at hn
      obtain ⟨t, htd, hnc⟩ := hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnc
      refine ⟨hcopy _ ((hcn t htd).2.2 c hc), ?_⟩
      intro hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp htd
      rw [List.getElem?_drop] at hj
      exact hdmc c.1 (List.mem_of_mem_take hmem) c.1
        (hctorName (p.k + j) t hj c hc) rfl
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
    obtain ⟨t, ht, htn, htd⟩ := hpinT j q hj
    refine ⟨by rw [← htn]; exact hcopy _ (hcn t htd).2.1, ?_⟩
    intro hmem
    have hjl : j < st.pins.length := (List.getElem?_eq_some_iff.mp hj).1
    have hrec : q.aux.str "rec" ∈ (List.range b.k).map b.recName := by
      refine List.mem_map.mpr ⟨p.k + j, List.mem_range.mpr (by rw [hk]; omega), ?_⟩
      rw [hrecName (p.k + j) t ht, htn]
    exact hdr _ (List.mem_append_left _ (List.mem_of_mem_take hmem)) _ hrec rfl

end ConLeche
