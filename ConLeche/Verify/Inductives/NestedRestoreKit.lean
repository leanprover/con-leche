module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
public import ConLeche.Verify.Inductives.NestedRestoreTbl
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
of a pin re-opened at the block's parameters; and, in the last section,
how the walk moves a bound variable, which is what makes the scratch
block's recorded PROJECTION GUARDS the restored constructor's guards.

The names carry the lane's namespace discipline: `rk` for the kit's
first sections, `rg` for the guards' (task #315 M7-2).
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

/-! ## The guards' invariance under the restore (task #315 M7-2)

The nested route RE-USES the scratch block's recorded `ProjTable`, whose
`guards` field was computed at the AUXILIARY constructor's type
(`structProjGuards`, through `structUsedLater`); the model's table clause
asks for the guards of the RESTORED constructor's type.  The two agree,
and nothing in the tree said so.

The invariance is a statement about ONE bound variable: `structUsedLater
cty nP j` strips `nP + j + 1` binders and asks whether `bvar 0` — field
`j`'s own variable — occurs loose in what is left.  So what has to be
shown is that `restoreWalk` neither ADDS nor LOSES an occurrence of a
variable bound BELOW its current depth `d`.

* it can never ADD one, and that needs no hypothesis at all: every term
  the node step produces is built from `pin.liftLooseBVars d 0`, whose
  loose indices are all `≥ d`, and from arguments of the node it
  replaced (`rg_restoreNode_hasLooseBVar`);
* it can only LOSE one by dropping `args.take R.nP` at a fired pin, and
  the scratch block's own field classification forbids exactly that — an
  ORDINARY field's domain mentions no auxiliary name at all, so the walk
  is the identity on it, and a RECURSIVE or REFLEXIVE field's domain (and
  the constructor's residual) carries the block's PARAMETER spine in that
  prefix, whose indices are `≥ d` too.

`RestoreKeepsLoose` names the CONCLUSION rather than a condition, so the
two halves compose: the shapes above each establish it, and it is closed
under the node formers, hence under a `∀`-telescope
(`rg_keepsLoose_stripPis`).  That is what carries it from the fields to
the constructor type and so to `structProjGuards`. -/

/-! ## Loose variables under a lift and along a spine -/

/-- **A lift hides the variables it skips**: `liftLooseBVars d c` moves
every loose index at or above `c` up by `d`, so no index in `[c, c + d)`
survives — at `c = 0` the lifted term mentions nothing below `d`. -/
theorem rg_hasLooseBVar_liftLooseBVars : ∀ (e : Expr) {d c q : Nat}, c ≤ q → q < c + d →
    (e.liftLooseBVars d c).hasLooseBVar q = false := by
  intro e
  induction e with
  | bvar i =>
    intro d c q h1 h2
    simp only [Expr.liftLooseBVars]
    split
    · rename_i hge
      simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
      omega
    · rename_i hlt
      simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
      omega
  | app f a ihf iha =>
    intro d c q h1 h2
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, ihf h1 h2, iha h1 h2, Bool.or_self]
  | lam ty b bm ihty ihb =>
    intro d c q h1 h2
    have hb := ihb (d := d) (c := c + 1) (q := q + 1) (by omega) (by omega)
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, ihty h1 h2, hb, Bool.or_self]
  | forallE ty b bm ihty ihb =>
    intro d c q h1 h2
    have hb := ihb (d := d) (c := c + 1) (q := q + 1) (by omega) (by omega)
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, ihty h1 h2, hb, Bool.or_self]
  | letE ty v b ihty ihv ihb =>
    intro d c q h1 h2
    have hb := ihb (d := d) (c := c + 1) (q := q + 1) (by omega) (by omega)
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, ihty h1 h2, ihv h1 h2, hb, Bool.or_self]
  | proj s i pe ih =>
    intro d c q h1 h2
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, ih h1 h2]
  | fvar i ty => intro d c q _ _; rfl
  | sort u => intro d c q _ _; rfl
  | const n us => intro d c q _ _; rfl
  | lit l => intro d c q _ _; rfl

/-- **A spine's loose variables** are its head's and its arguments'. -/
theorem rg_hasLooseBVar_mkAppN : ∀ (args : List Expr) (f : Expr) (q : Nat),
    (Expr.mkAppN f args).hasLooseBVar q
      = (f.hasLooseBVar q || args.any (fun a => a.hasLooseBVar q))
  | [], f, q => by simp [Expr.mkAppN]
  | a :: as, f, q => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      rg_hasLooseBVar_mkAppN as]
    simp only [Expr.hasLooseBVar, List.any_cons]
    exact Bool.or_assoc _ _ _

/-- A term free of `bvar q` has arguments free of it. -/
theorem rg_hasLooseBVar_getAppArgs_false {e : Expr} {q : Nat} (h : e.hasLooseBVar q = false) :
    ∀ a ∈ e.getAppArgs, a.hasLooseBVar q = false := by
  intro a ha
  rw [← Expr.mkAppN_getApp e, rg_hasLooseBVar_mkAppN] at h
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at h
  simpa using h.2 a ha

/-! ## The node step never adds an occurrence -/

/-- **The head half never adds a variable bound below `d`**: what it
produces is the lifted pin — free of every index below `d`
(`rg_hasLooseBVar_liftLooseBVars`) — applied to arguments of the node it
replaced. -/
theorem rg_restoreHead_hasLooseBVar {R : RestoreTbl} {d q : Nat} {e x : Expr}
    (h : restoreHead R d e = .ok (some x)) (hq : q < d) (he : e.hasLooseBVar q = false) :
    x.hasLooseBVar q = false := by
  have hargs : ∀ a ∈ e.getAppArgs, a.hasLooseBVar q = false :=
    rg_hasLooseBVar_getAppArgs_false he
  simp only [restoreHead] at h
  have hlift : ∀ pin : Expr, (pin.liftLooseBVars d 0).hasLooseBVar q = false := fun pin =>
    rg_hasLooseBVar_liftLooseBVars pin (Nat.zero_le _) (by omega)
  split at h
  · split at h
    · split at h
      · exact nomatch h
      · obtain rfl := Option.some.inj (Except.ok.inj h)
        rw [rg_hasLooseBVar_mkAppN, hlift _]
        simp only [Bool.false_or, List.any_eq_false]
        intro a ha
        simpa using hargs a (List.mem_of_mem_drop ha)
    · split at h
      · split at h
        · exact nomatch h
        · split at h
          · obtain rfl := Option.some.inj (Except.ok.inj h)
            rw [rg_hasLooseBVar_mkAppN, rg_hasLooseBVar_mkAppN]
            simp only [Expr.hasLooseBVar, Bool.false_or, Bool.or_eq_false_iff,
              List.any_eq_false]
            refine ⟨fun a ha => ?_, fun a ha => ?_⟩
            · simpa using rg_hasLooseBVar_getAppArgs_false (hlift _) a ha
            · simpa using hargs a (List.mem_of_mem_drop ha)
          · exact nomatch h
      · exact nomatch h
  · exact nomatch h

/-- **The node step never adds a variable bound below `d`.** -/
theorem rg_restoreNode_hasLooseBVar {R : RestoreTbl} {d q : Nat} {e x : Expr}
    (h : restoreNode R d e = .ok (some x)) (hq : q < d) (he : e.hasLooseBVar q = false) :
    x.hasLooseBVar q = false := by
  cases e with
  | const n us =>
    rw [restoreNode_const] at h
    split at h
    · obtain rfl := Option.some.inj (Except.ok.inj h)
      rfl
    · exact rg_restoreHead_hasLooseBVar h hq he
  | _ =>
    rw [restoreNode_eq_head (by intro n us hq'; exact Expr.noConfusion hq')] at h
    exact rg_restoreHead_hasLooseBVar h hq he

/-! ## `RestoreKeepsLoose` -/

/-- **The restore is transparent to the variables bound below `d`**:
whatever the walk makes of `e` at depth `d` has exactly the loose
occurrences of `e` at every index below `d`.

It names the CONCLUSION, not a condition, and that is the point: the two
halves of the argument — the shapes at which the walk provably keeps
every such occurrence — each establish it, and it is closed under the
node formers, hence under a `∀`-telescope.  So the fields' local facts
compose into the constructor type's. -/
@[expose] def RestoreKeepsLoose (R : RestoreTbl) (d : Nat) (e : Expr) : Prop :=
  ∀ e', restoreWalk R d e = .ok e' → ∀ q, q < d → e'.hasLooseBVar q = e.hasLooseBVar q

/-- **An auxiliary-free term is its own restoration**, so it keeps
every variable — this is the ORDINARY field's case: its domain
`constsResolve`s at the pre-block environment, where no auxiliary name
exists. -/
theorem rg_keepsLoose_of_no_aux {R : RestoreTbl} {d : Nat} {e : Expr}
    (h : ∀ n ∈ R.auxNames, e.mentionsConst n = false) : RestoreKeepsLoose R d e := by
  intro e' hw q _
  obtain rfl := Except.ok.inj ((restoreWalk_of_no_aux d e h).symm.trans hw)
  rfl

/-- **The Π node**: the domain is walked at the same depth and the body
one deeper, and an index below `d` is an index below `d + 1` under the
binder. -/
theorem rg_keepsLoose_forallE {R : RestoreTbl} {d : Nat} {ty b : Expr} {bm : BinderMeta}
    (hty : RestoreKeepsLoose R d ty) (hb : RestoreKeepsLoose R (d + 1) b) :
    RestoreKeepsLoose R d (.forallE ty b bm) := by
  intro e' hw q hq
  obtain ⟨ty', b', hty', hb', rfl⟩ := restoreWalk_forallE_inv hw
  simp only [Expr.hasLooseBVar, hty _ hty' q hq, hb _ hb' (q + 1) (by omega)]

/-- **The parameter spine mentions nothing below its own frame**: the
variables `structPsAt o nP` are the `nP` binders at `o`, so an index
below `o` is none of them. -/
theorem rg_hasLooseBVar_structPsAt {o nP q : Nat} (h : q < o) :
    ∀ a ∈ structPsAt o nP, a.hasLooseBVar q = false := by
  intro a ha
  simp only [structPsAt, List.mem_map, List.mem_range] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
  omega

/-- **A pin's fire keeps every variable below `d`**: the walk replaces
the node by `pin.liftLooseBVars d 0` — free of every index below `d` —
applied to `args.drop R.nP`, which it copies verbatim.  So the only
occurrences that could be lost are those in `args.take R.nP`, and
`htake` is exactly the classification's guarantee that there are none:
at a recursive or reflexive field of the scratch block that prefix is
the block's PARAMETER spine (`structCtorResidOk`, `mutualPositivity`). -/
theorem rg_keepsLoose_pin {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level}
    {args : List Expr} {pin : Expr}
    (hp : R.pins.lookup n = some pin) (hrec : R.recMap.lookup n = none)
    (haux : n ∈ R.auxNames) (hlen : R.nP ≤ args.length)
    (htake : ∀ a ∈ args.take R.nP, ∀ q, q < d → a.hasLooseBVar q = false) :
    RestoreKeepsLoose R d (Expr.mkAppN (.const n us) args) := by
  intro e' hw q hq
  obtain rfl := Except.ok.inj ((restoreWalk_pin hp hrec haux hlen).symm.trans hw)
  have htk : (args.take R.nP).any (fun a => a.hasLooseBVar q) = false := by
    simp only [List.any_eq_false]
    intro a ha
    simpa using htake a ha q hq
  have hall : (args.any fun a => a.hasLooseBVar q)
      = (args.drop R.nP).any (fun a => a.hasLooseBVar q) := by
    have h0 : ((args.take R.nP ++ args.drop R.nP).any fun a => a.hasLooseBVar q)
        = (args.drop R.nP).any (fun a => a.hasLooseBVar q) := by
      simp only [List.any_append, htk, Bool.false_or]
    rwa [List.take_append_drop] at h0
  rw [rg_hasLooseBVar_mkAppN, rg_hasLooseBVar_mkAppN,
    rg_hasLooseBVar_liftLooseBVars pin (Nat.zero_le _) (by omega)]
  simp only [Expr.hasLooseBVar, Bool.false_or, hall]

/-- **A pin's fire at the block's parameter frame**, the form the
scratch block's own checks leave behind: a recursive or reflexive
field's residual and a constructor's residual are the member applied to
`structPsAt o R.nP` first (`mutualPositivity`, `structCtorResidOk`),
where `o` is the frame the walk has reached — so the dropped prefix is
parameters, never a field variable. -/
theorem rg_keepsLoose_spine {R : RestoreTbl} {d o : Nat} {n : Name} {us : List Level}
    {e pin : Expr} (hfn : e.getAppFn = .const n us)
    (hp : R.pins.lookup n = some pin) (hrec : R.recMap.lookup n = none)
    (haux : n ∈ R.auxNames) (hlen : R.nP ≤ e.getAppArgs.length) (hd : d ≤ o)
    (htake : e.getAppArgs.take R.nP = structPsAt o R.nP) :
    RestoreKeepsLoose R d e := by
  have he : Expr.mkAppN (.const n us) e.getAppArgs = e := by
    rw [← hfn]; exact Expr.mkAppN_getApp e
  rw [← he]
  refine rg_keepsLoose_pin hp hrec haux hlen (fun a ha q hq => ?_)
  rw [htake] at ha
  exact rg_hasLooseBVar_structPsAt (by omega) a ha

/-- **The telescope**: a `∀`-prefix whose domains each keep their
variables, over a body that keeps its own, keeps every variable of the
whole — `rg_keepsLoose_forallE` iterated along `stripPis`. -/
theorem rg_keepsLoose_stripPis {R : RestoreTbl} :
    ∀ (m : Nat) {d : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis m = some (bs, body) →
      (∀ i, i < m → RestoreKeepsLoose R (d + i) (bs.getD i default).1) →
      RestoreKeepsLoose R (d + m) body → RestoreKeepsLoose R d e := by
  intro m
  induction m with
  | zero =>
    intro d e bs body hs _ hbody
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simpa using hbody
  | succ m ih =>
    intro d e bs body hs hdoms hbody
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at hs
      cases hb : b.stripPis m with
      | none => rw [hb] at hs; exact nomatch hs
      | some pr =>
        obtain ⟨bs₀, body₀⟩ := pr
        rw [hb] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine rg_keepsLoose_forallE ?_ (ih (d := d + 1) hb ?_ ?_)
        · simpa using hdoms 0 (by omega)
        · intro i hi
          have h1 := hdoms (i + 1) (by omega)
          simp only [List.getD_cons_succ] at h1
          rw [show d + 1 + i = d + (i + 1) by omega]
          exact h1
        · rw [show d + 1 + m = d + (m + 1) by omega]
          exact hbody
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch hs

/-! ## The guards -/

/-- **`structUsedLater` is invariant under the restore**: field `j`'s
variable occurs in the remainder of the RESTORED constructor telescope
exactly when it occurs in the remainder of the auxiliary one.

The restore rebuilds the parameter prefix and walks the rest
(`restoreNested_pis`, `rk_restoreWalk_stripPis`), so the remainder after
binder `nP + j` is walked at depth `j + 1` — and `bvar 0` there is a
variable bound below that depth, which `RestoreKeepsLoose` keeps.  The
premises are the fields' and the residual's own shapes; at the scratch
block they come from the classification (`mutualCtorKinds`) and the
residual's check (`structCtorResidOk`). -/
theorem rg_structUsedLater_restoreNested {R : RestoreTbl} {nP nF j : Nat} (hnP : R.nP = nP)
    (hj : j < nF) {ctyA ctyR : Expr} {cbs : List (Expr × BinderMeta)} {resid : Expr}
    (hstrip : ctyA.stripPis (nP + nF) = some (cbs, resid))
    (hres : restoreNested R ctyA = .ok ctyR)
    (hdoms : ∀ i, i < nF → RestoreKeepsLoose R i (cbs.getD (nP + i) default).1)
    (hresid : RestoreKeepsLoose R nF resid) :
    structUsedLater ctyR nP j = structUsedLater ctyA nP j := by
  rw [show nP + nF = nP + j + 1 + (nF - j - 1) by omega] at hstrip
  obtain ⟨mid, hs1, hs2⟩ := rk_stripPis_split (nP + j + 1) (nF - j - 1) hstrip
  have hmid : RestoreKeepsLoose R (j + 1) mid := by
    refine rg_keepsLoose_stripPis (nF - j - 1) hs2 (fun i hi => ?_) ?_
    · have h1 := hdoms (j + 1 + i) (by omega)
      have h2 : (cbs.drop (nP + j + 1)).getD i default = cbs.getD (nP + (j + 1 + i)) default := by
        rw [show nP + (j + 1 + i) = nP + j + 1 + i by omega]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [h2]
      exact h1
    · rw [show j + 1 + (nF - j - 1) = nF by omega]
      exact hresid
  obtain ⟨body₀, hsP, hsF⟩ := rk_stripPis_split nP (j + 1) hs1
  have hsP' : ctyA.stripPis R.nP = some ((cbs.take (nP + j + 1)).take nP, body₀) := by
    rw [hnP]; exact hsP
  have hpi : 0 < R.nP → ∃ ty b bm, ctyA = Expr.forallE ty b bm := by
    intro hlt
    rw [hnP] at hlt
    obtain ⟨u, rfl⟩ : ∃ u, nP = u + 1 := ⟨nP - 1, by omega⟩
    cases ctyA with
    | forallE ty b bm => exact ⟨ty, b, bm, rfl⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch hsP
  obtain ⟨body', hw, rfl⟩ := restoreNested_pis hsP' hpi hres
  obtain ⟨bs', mid', hsb, hw', -, -⟩ := rk_restoreWalk_stripPis (j + 1) hw hsF
  have hmk := rk_mkPisB_stripPis ((cbs.take (nP + j + 1)).take nP) body'
  rw [stripPis_length nP hsP] at hmk
  have hR : (mkPisB ((cbs.take (nP + j + 1)).take nP) body').stripPis (nP + j + 1)
      = some ((cbs.take (nP + j + 1)).take nP ++ bs', mid') := stripPis_append nP hmk hsb
  rw [mkPisB_eq_foldr]
  simp only [structUsedLater, hR, hs1, Expr.hasLooseBVarB_eq]
  exact hmid mid' (by simpa using hw') 0 (by omega)

/-- A fold whose step agrees on every element of the list. -/
theorem rg_foldl_congr {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ c, f c a = g c a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: as, b, h => by
    simp only [List.foldl_cons, h a List.mem_cons_self b]
    exact rg_foldl_congr f g as _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **THE PROJECTION GUARDS ARE INVARIANT UNDER THE RESTORE** (task
#315).  The nested route re-uses the scratch block's recorded
`ProjTable`, whose `guards` were computed at the AUXILIARY constructor's
type; the model's table clause asks for the guards of the RESTORED
constructor's type.  They are the same list: the guards are a fold over
`structUsedLater` at the fields strictly below `nF`, and every one of
those answers is invariant (`rg_structUsedLater_restoreNested`). -/
theorem rg_structProjGuards_restoreNested {R : RestoreTbl} {nP nF : Nat} (hnP : R.nP = nP)
    {ctyA ctyR : Expr} {cbs : List (Expr × BinderMeta)} {resid : Expr}
    (hstrip : ctyA.stripPis (nP + nF) = some (cbs, resid))
    (hres : restoreNested R ctyA = .ok ctyR)
    (hdoms : ∀ i, i < nF → RestoreKeepsLoose R i (cbs.getD (nP + i) default).1)
    (hresid : RestoreKeepsLoose R nF resid) (sorts : List Level) :
    structProjGuards ctyR nP nF sorts = structProjGuards ctyA nP nF sorts := by
  simp only [structProjGuards]
  refine List.map_congr_left (fun i hi => ?_)
  rw [List.mem_range] at hi
  refine rg_foldl_congr _ _ (List.range i) _ (fun j hj c => ?_)
  rw [List.mem_range] at hj
  rw [rg_structUsedLater_restoreNested hnP (by omega) hstrip hres hdoms hresid]

end ConLeche
