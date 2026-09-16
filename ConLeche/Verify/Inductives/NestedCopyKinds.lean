module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedCopyTele

public section

/-!
# The aux block's field classification, syntactically (task #315 L-B)

The nested elimination hands the mutual install an AUXILIARY block
whose constructor fields have a known shape: a copy's field is the
container's own field with every nested occurrence replaced by an
application of a minted copy at the block's parameters (a RECURSIVE
field, `k = 0`), possibly under a `∀`-prefix of member-free domains (a
REFLEXIVE field).  This module reads the install's classifier
(`mutualPositivity`, `mutualCtorKinds`,
`ConLeche/Kernel/Inductives/MutualInstall.lean`) at exactly those
shapes, so the model tier never re-walks the classifier:

* `mutualPositivity_ordinary`/`_pi`/`_rec` — the three ways the walk
  ends at a copy's field;
* `mutualCtorKinds_getD` — the kinds list read back positionally, with
  `_ordinary`/`_rec`/`_refl` at the shapes the elimination produces;
* `members3_find?_name` — the aux block's member table looked up by
  NAME (the elimination knows the copy's name, not its index);
* the `abstractRange` kit (`abstractTele`, `abstractRange_mkPisB`,
  `closeTelescope_mkPisB_strip`) that turns `mkCopy`'s stored former
  back into a telescope the classifier can strip.
-/

namespace ConLeche

open Expr

/-! ## List kit -/

/-- **`find?` at a unique key**: when the keys `f` assigns to `l`'s
entries are pairwise distinct, the first entry keyed like `x` IS `x`. -/
theorem List.find?_eq_of_nodup_map {α β : Type} [BEq β] [LawfulBEq β] (f : α → β)
    {l : List α} (hnd : (l.map f).Nodup) {x : α} (hx : x ∈ l) :
    l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a l ih =>
    rw [_root_.List.map_cons, _root_.List.nodup_cons] at hnd
    rw [_root_.List.find?_cons]
    split
    · next hbe =>
      have hb : f a = f x := by simpa using hbe
      rcases _root_.List.mem_cons.mp hx with rfl | hx'
      · rfl
      · exact absurd (hb ▸ (_root_.List.mem_map.mpr ⟨x, hx', rfl⟩ : f x ∈ l.map f)) hnd.1
    · next hbe =>
      have hb : ¬ f a = f x := by simpa using hbe
      rcases _root_.List.mem_cons.mp hx with rfl | hx'
      · exact absurd rfl hb
      · exact ih hnd.2 hx'

/-- The kernel's pin lookup (`replaceIfNested`, `fun q => q.pin == pin`)
at a pin list whose pins are distinct: it finds the pin's own entry. -/
theorem find?_pin_of_nodup {st : ElimState} (hnd : (st.pins.map (·.pin)).Nodup)
    {q : NestedPin} (hq : q ∈ st.pins) {e : Expr} (he : q.pin = e) :
    st.pins.find? (fun y => y.pin == e) = some q := by
  subst he
  exact List.find?_eq_of_nodup_map (·.pin) hnd hq

/-- `any` distributes over a pointwise `||`. -/
private theorem anyOr {α : Type} (p q : α → Bool) :
    ∀ l : List α, l.any (fun a => p a || q a) = (l.any p || l.any q)
  | [] => rfl
  | a :: l => by
    simp only [_root_.List.any_cons, anyOr p q l]
    cases p a <;> cases q a <;> cases l.any p <;> cases l.any q <;> rfl

/-- A prefix of an append is read back by its length. -/
private theorem takeLen {α : Type} {l₁ l₂ : List α} {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := _root_.List.take_left' h

/-- A suffix of an append is read back by the prefix's length. -/
private theorem dropLen {α : Type} {l₁ l₂ : List α} {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := _root_.List.drop_left' h

/-! ## `mentionsMember` and `mentionsConst` at the shapes -/

/-- The parameter spine's length. -/
theorem structPsAt_length (o nP : Nat) : (structPsAt o nP).length = nP := by
  simp [structPsAt]

/-- `mentionsMember` splits at a `∀`. -/
theorem mentionsMember_forallE (names : List Name) (d b : Expr) (bm : BinderMeta) :
    mentionsMember names (.forallE d b bm)
      = (mentionsMember names d || mentionsMember names b) := by
  show names.any (fun T => (Expr.mentionsConst T d || Expr.mentionsConst T b)) = _
  rw [anyOr]
  rfl

/-- A member-free `∀` has member-free parts. -/
theorem mentionsMember_forallE_false {names : List Name} {d b : Expr} {bm : BinderMeta}
    (h : mentionsMember names (.forallE d b bm) = false) :
    mentionsMember names d = false ∧ mentionsMember names b = false := by
  rw [mentionsMember_forallE] at h
  simpa using h

/-- A `∀`-telescope mentions what its body mentions. -/
theorem mentionsConst_mkPisB {T : Name} : ∀ (bs : List (Expr × BinderMeta)) (X : Expr),
    X.mentionsConst T = true → (mkPisB bs X).mentionsConst T = true
  | [], X, h => by rwa [mkPisB_nil]
  | b :: bs, X, h => by
    rw [mkPisB_cons]
    show (Expr.mentionsConst T b.1 || Expr.mentionsConst T (mkPisB bs X)) = true
    rw [mentionsConst_mkPisB bs X h]
    exact Bool.or_true _

/-- A member application mentions a member. -/
theorem mentionsMember_mkAppN_const {names : List Name} {T : Name} (hT : T ∈ names)
    (us : List Level) (args : List Expr) :
    mentionsMember names (Expr.mkAppN (.const T us) args) = true :=
  _root_.List.any_eq_true.mpr
    ⟨T, hT, Expr.mentionsConst_mkAppN_head args (.const T us) (by simp [Expr.mentionsConst])⟩

/-- A `∀`-telescope over a member application mentions a member. -/
theorem mentionsMember_mkPisB_const {names : List Name} {T : Name} (hT : T ∈ names)
    (bs : List (Expr × BinderMeta)) (us : List Level) (args : List Expr) :
    mentionsMember names (mkPisB bs (Expr.mkAppN (.const T us) args)) = true :=
  _root_.List.any_eq_true.mpr
    ⟨T, hT, mentionsConst_mkPisB bs _
      (Expr.mentionsConst_mkAppN_head args (.const T us) (by simp [Expr.mentionsConst]))⟩

/-- An application spine is never a `∀`. -/
theorem mkAppN_ne_forallE : ∀ (args : List Expr) (f : Expr),
    (∀ d b m, f ≠ .forallE d b m) → ∀ d b m, Expr.mkAppN f args ≠ .forallE d b m
  | [], _, hf => hf
  | a :: as, f, _ =>
    mkAppN_ne_forallE as (.app f a) (fun _ _ _ h => Expr.noConfusion h)

/-- A constant spine is never a `∀`. -/
theorem mkAppN_const_ne_forallE (T : Name) (us : List Level) (args : List Expr) :
    ∀ d b m, Expr.mkAppN (.const T us) args ≠ .forallE d b m :=
  mkAppN_ne_forallE args (.const T us) (fun _ _ _ h => Expr.noConfusion h)

/-! ## The aux block's member table, by name -/

/-- The member table's names ARE the block's member names. -/
private theorem members3_map_fst_go :
    ∀ (l : List (ConstantVal × Nat)) (o : Nat),
      (((l.zipIdx o).map fun q => (q.1.1.name, q.2, q.1.2)).map (·.1)) = l.map (·.1.name)
  | [], _ => rfl
  | a :: l, o => by
    rw [_root_.List.zipIdx_cons, _root_.List.map_cons, _root_.List.map_cons,
      _root_.List.map_cons, members3_map_fst_go l (o + 1)]

/-- The member table's names ARE the block's member names. -/
theorem members3_map_fst (b : MutualBlock) : b.members3.map (·.1) = b.memberNames := by
  rw [MutualBlock.members3, MutualBlock.memberNames]
  exact members3_map_fst_go b.formers 0

/-- **The block's member table, looked up by NAME** (the elimination
knows a copy's name, not its position): at distinct member names, the
entry of the former at position `t` is `(name, t, nIdx)`. -/
theorem members3_find?_name {b : MutualBlock} {t : Nat} {cv : ConstantVal} {nIdx : Nat}
    (hnd : b.memberNames.Nodup) (ht : b.formers[t]? = some (cv, nIdx)) :
    b.members3.find? (·.1 == cv.name) = some (cv.name, t, nIdx) := by
  have hmem : (cv.name, t, nIdx) ∈ b.members3 := by
    rw [MutualBlock.members3]
    exact _root_.List.mem_map.mpr
      ⟨((cv, nIdx), t), _root_.List.mk_mem_zipIdx_iff_getElem?.mpr ht, rfl⟩
  exact List.find?_eq_of_nodup_map (·.1) (by rw [members3_map_fst]; exact hnd) hmem

/-! ## `abstractRange` at the copy's telescope -/

/-- A constant carries no free variables. -/
theorem abstractRange_const (n : Name) (us : List Level) (d k c : Nat) :
    (Expr.const n us).abstractRange d k c = .const n us := rfl

/-- Bulk abstraction commutes with an application spine. -/
theorem abstractRange_mkAppN (d k : Nat) : ∀ (args : List Expr) (f : Expr) (c : Nat),
    (Expr.mkAppN f args).abstractRange d k c
      = Expr.mkAppN (f.abstractRange d k c) (args.map (·.abstractRange d k c))
  | [], _, _ => rfl
  | a :: as, f, c => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      abstractRange_mkAppN d k as (.app f a) c]
    rfl

/-- **The parameter spine, abstracted**: the first `nP` fvar levels
abstracted out of the parameter variables are the parameter bvars at
cursor `c`. -/
theorem abstractRange_params {params : List Expr} {nP c : Nat}
    (hlen : params.length = nP)
    (hfv : ∀ j x, params[j]? = some x → ∃ ty, x = Expr.fvar j ty) :
    params.map (·.abstractRange 0 nP c) = structPsAt c nP := by
  refine _root_.List.ext_getElem? fun j => ?_
  rcases Nat.lt_or_ge j nP with hj | hj
  · have hj' : j < params.length := by omega
    have hx : params[j]? = some params[j] := _root_.List.getElem?_eq_getElem hj'
    obtain ⟨ty, hty⟩ := hfv j _ hx
    rw [_root_.List.getElem?_map, hx, structPsAt, _root_.List.getElem?_map,
      _root_.List.getElem?_range hj]
    show some ((params[j]).abstractRange 0 nP c) = _
    rw [hty]
    show some (if 0 ≤ j ∧ j < 0 + nP then Expr.bvar (c + (0 + nP - 1 - j)) else .fvar j ty) = _
    rw [if_pos (by omega)]
    congr 2
    omega
  · rw [_root_.List.getElem?_eq_none (by simp [hlen]; omega),
      _root_.List.getElem?_eq_none (by simp [structPsAt]; omega)]

/-- The binder domains of a telescope, bulk-abstracted, each under the
binders that precede it. -/
@[expose] def abstractTele (d k : Nat) : Nat → List (Expr × BinderMeta) →
    List (Expr × BinderMeta)
  | _, [] => []
  | c, b :: bs => (b.1.abstractRange d k c, b.2) :: abstractTele d k (c + 1) bs

/-- Abstraction keeps a telescope's length. -/
theorem abstractTele_length (d k : Nat) : ∀ (c : Nat) (bs : List (Expr × BinderMeta)),
    (abstractTele d k c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by
    rw [abstractTele, _root_.List.length_cons, _root_.List.length_cons,
      abstractTele_length d k (c + 1) bs]

/-- Entry `l` of an abstracted telescope: the entry's domain abstracted
at cursor `c + l`. -/
theorem abstractTele_getD (d k : Nat) : ∀ (bs : List (Expr × BinderMeta)) (c l : Nat),
    l < bs.length →
    (abstractTele d k c bs).getD l default
      = (((bs.getD l default).1).abstractRange d k (c + l), (bs.getD l default).2)
  | [], _, _, h => absurd h (by simp)
  | b :: bs, c, 0, _ => by
    rw [abstractTele]
    rfl
  | b :: bs, c, l + 1, h => by
    rw [abstractTele, _root_.List.getD_cons_succ, _root_.List.getD_cons_succ,
      abstractTele_getD d k bs (c + 1) l (by simpa using h),
      show c + 1 + l = c + (l + 1) from by omega]

/-- **Bulk abstraction through a `∀`-telescope**: the domains are
abstracted one cursor deeper each, the body under them all. -/
theorem abstractRange_mkPisB (d k : Nat) : ∀ (bs : List (Expr × BinderMeta)) (res : Expr)
    (c : Nat), (mkPisB bs res).abstractRange d k c
      = mkPisB (abstractTele d k c bs) (res.abstractRange d k (c + bs.length))
  | [], res, c => by
    rw [mkPisB_nil, abstractTele, mkPisB_nil, _root_.List.length_nil, Nat.add_zero]
  | b :: bs, res, c => by
    rw [mkPisB_cons, abstractTele]
    show Expr.forallE (b.1.abstractRange d k c) ((mkPisB bs res).abstractRange d k (c + 1)) b.2 = _
    rw [abstractRange_mkPisB d k bs res (c + 1), mkPisB_cons, _root_.List.length_cons,
      show c + 1 + bs.length = c + (bs.length + 1) from by omega]

/-! ## The stored copy, stripped again -/

/-- A `∀`-telescope strips back to its own binders. -/
private theorem stripPis_mkPisB_self' : ∀ (bs : List (Expr × BinderMeta)) (res : Expr),
    (mkPisB bs res).stripPis bs.length = some (bs, res)
  | [], res => by rw [mkPisB_nil, _root_.List.length_nil, Expr.stripPis]
  | b :: bs, res => by
    rw [mkPisB_cons, _root_.List.length_cons]
    show (Expr.stripPis bs.length (mkPisB bs res)).map
      (fun p => ((b.1, b.2) :: p.1, p.2)) = some (b :: bs, res)
    rw [stripPis_mkPisB_self' bs res]
    rfl

/-- Telescopes append. -/
private theorem mkPisB_append' : ∀ (bs₁ bs₂ : List (Expr × BinderMeta)) (res : Expr),
    mkPisB (bs₁ ++ bs₂) res = mkPisB bs₁ (mkPisB bs₂ res)
  | [], _, _ => by rw [_root_.List.nil_append, mkPisB_nil]
  | b :: bs₁, bs₂, res => by
    rw [_root_.List.cons_append, mkPisB_cons, mkPisB_cons, mkPisB_append' bs₁ bs₂ res]

/-- **`mkCopy`'s stored former, stripped again**: closing the first
former's (fvar-free) parameter binders around a `∀`-telescope and
stripping all of them back yields the parameter binders, the
telescope's binders abstracted under them, and the body abstracted
under everything. -/
theorem closeTelescope_mkPisB_strip {pbs bs : List (Expr × BinderMeta)} {res : Expr}
    (h : ∀ b ∈ pbs, b.1.hasFvar = false) :
    (closeTelescope pbs 0 (mkPisB bs res)).stripPis (pbs.length + bs.length)
      = some (pbs ++ abstractTele 0 pbs.length 0 bs,
          res.abstractRange 0 pbs.length bs.length) := by
  rw [closeTelescope_eq_mkPisB pbs 0 (mkPisB bs res) h, abstractRange_mkPisB,
    Nat.zero_add, ← mkPisB_append']
  have hlen : pbs.length + bs.length
      = (pbs ++ abstractTele 0 pbs.length 0 bs).length := by
    rw [_root_.List.length_append, abstractTele_length]
  rw [hlen, stripPis_mkPisB_self']

end ConLeche
