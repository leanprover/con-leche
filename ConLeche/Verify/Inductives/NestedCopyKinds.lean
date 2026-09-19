module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedCopyRewrite
import ConLeche.Verify.Inductives.FixParts

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

/-! ## K.32 read back — the copies' recursive targets (task #315 L-B)

`nestedCopyTargetsOk` (`ConLeche/Kernel/Inductives/NestedInstall.lean`)
is a run conjunct with no `_inv`: it is stated as one `Bool` and
consumed positionally.  What `CopyCtorInst`'s `ordF` RIGHT arm and
`pinF` need of it is one clause — a copy field the auxiliary block
classified recursive or reflexive INTO the copy's own group comes from
a container field whose CLOSED domain, its `Π`-prefix peeled, is
headed by the targeted group member.  The two lemmas below read the
kinds table (`nestedPinKinds`) and then that clause off the Bool. -/

/-- The per-pin kinds table, positionally: entry `q` describes the
stored copy `p.k + q`, one classification per constructor. -/
theorem nestedPinKinds_get {p : NestedParts} {b : MutualBlock} {stored : List AuxStored}
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (h : nestedPinKinds p b stored = some kinds)
    {q : Nat} {ks : List (List (RecFieldKind × Nat))} (hq : kinds[q]? = some ks) :
    ∃ a : AuxStored, stored[p.k + q]? = some a ∧
      ∀ (j : Nat) (cv : ConstantVal) (nPc nF : Nat), a.ctors[j]? = some (cv, nPc, nF) →
        ks[j]? = mutualCtorKinds b.members3 b.lps b.nP (cv, nF) := by
  unfold nestedPinKinds at h
  have hqlen : q < (stored.drop p.k).length := by
    have hlt := (_root_.List.getElem?_eq_some_iff.mp hq).1
    rw [List.mapM_option_length h] at hlt
    exact hlt
  have hd : (stored.drop p.k)[q]? = some ((stored.drop p.k)[q]'hqlen) :=
    _root_.List.getElem?_eq_getElem hqlen
  obtain ⟨ks', hks', hf⟩ := mapM_option_inv h q _ hd
  rw [hq] at hks'
  obtain rfl : ks = ks' := Option.some.inj hks'
  refine ⟨_, by rw [← hd, _root_.List.getElem?_drop], fun j cv nPc nF hc => ?_⟩
  obtain ⟨k', hk', hfj⟩ := mapM_option_inv hf j _ hc
  rw [hk']
  exact hfj.symm

/-- K.26's Bool, inverted: the kinds table exists, has one entry per
pin, and classifies every field ordinary, recursive or reflexive into
the auxiliary block. -/
theorem nestedPinKindsOk_inv {p : NestedParts} {b : MutualBlock} {st : ElimState}
    {stored : List AuxStored} (h : nestedPinKindsOk p b st stored = true) :
    ∃ kinds : List (List (List (RecFieldKind × Nat))),
      nestedPinKinds p b stored = some kinds ∧ kinds.length = st.pins.length := by
  unfold nestedPinKindsOk nestedPinKindsAt at h
  cases hk : nestedPinKinds p b stored with
  | none => rw [hk] at h; exact nomatch h
  | some kinds =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨kinds, rfl, h.1⟩

/-- **K.32's clause, read back**: at pin `q` of the group
`[qn.grpBase, qn.grpBase + qn.grpSize)`, constructor `j` and field `l`,
a kind that is recursive or reflexive with a target INSIDE the group
forces the container member's stored constructor `j` to MENTION, at
field `l`, the container-group member the target names. -/
theorem nestedCopyTargetsOk_head {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedCopyTargetsOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {a : AuxStored} (ha : stored[p.k + q]? = some a)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cv : ConstantVal} {nPc nF : Nat} (hc : a.ctors[j]? = some (cv, nPc, nF))
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    (hr : r = .recursive ∨ r = .reflexive)
    (hlo : p.k + qn.grpBase ≤ t) (hhi : t < p.k + qn.grpBase + qn.grpSize) :
    ∃ (jbs : List (Expr × BinderMeta)) (rJ : Expr) (domJ : Expr × BinderMeta)
      (Jt : ContainerMember) (d : Nat) (tbs : List (Expr × BinderMeta)) (jres : Expr)
      (us : List Level),
      cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ) ∧
      jbs[ci.nP + l]? = some domJ ∧
      ci.members[t - p.k - qn.grpBase]? = some Jt ∧
      domJ.1.stripPis d = some (tbs, jres) ∧
      jres.getAppFn = .const Jt.name us := by
  unfold nestedCopyTargetsOk nestedCopyTargetsAt at h
  rw [hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hqv := h q hq
  rw [hqn, hks, ha] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJ] at hqv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hqv
  have hjv := hqv j hj
  rw [hkf, hc, hcJ] at hjv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := hjv l hlLt
  rw [hl] at hlv
  simp only at hlv
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, hlo⟩, hhi⟩
    rcases hr with rfl | rfl
    · simp
    · simp)] at hlv
  -- the two telescopes
  cases hsC : cv.type.stripPis (p.nP + nF) with
  | none => rw [hsC] at hlv; simp only at hlv; exact nomatch hlv
  | some qC =>
  obtain ⟨cbs, rC⟩ := qC
  cases hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) with
  | none => rw [hsC, hsJ] at hlv; simp only at hlv; exact nomatch hlv
  | some qJ =>
  obtain ⟨jbs, rJ⟩ := qJ
  rw [hsC, hsJ] at hlv
  simp only at hlv
  cases hdC : cbs[p.nP + l]? with
  | none => rw [hdC] at hlv; simp only at hlv; exact nomatch hlv
  | some domC =>
  cases hdJ : jbs[ci.nP + l]? with
  | none => rw [hdC, hdJ] at hlv; simp only at hlv; exact nomatch hlv
  | some domJ =>
  rw [hdC, hdJ] at hlv
  simp only at hlv
  cases hpk : domJ.1.stripPis (Expr.piBinders domC.1).1.length with
  | none => rw [hpk] at hlv; simp only at hlv; exact nomatch hlv
  | some qP =>
  obtain ⟨tbs, jres⟩ := qP
  cases hJt : ci.members[t - p.k - qn.grpBase]? with
  | none => rw [hpk, hJt] at hlv; simp only at hlv; exact nomatch hlv
  | some Jt =>
  rw [hpk, hJt] at hlv
  simp only [Bool.and_eq_true] at hlv
  obtain ⟨hhead, -⟩ := hlv
  -- the peeled body is headed by the target member
  obtain ⟨us, hfn⟩ : ∃ us, jres.getAppFn = .const Jt.name us := by
    cases hf : jres.getAppFn with
    | const nm us =>
      rw [hf] at hhead
      simp only [beq_iff_eq] at hhead
      exact ⟨us, by rw [hhead]⟩
    | _ => rw [hf] at hhead; simp only at hhead; exact nomatch hhead
  refine ⟨jbs, rJ, domJ, Jt, (Expr.piBinders domC.1).1.length, tbs, jres, us, ?_, ?_, ?_, ?_, ?_⟩
  · first | exact hsJ | rfl
  · first | exact hdJ | rfl
  · first | exact hJt | rfl
  · exact hpk
  · exact hfn

/-- **K.32's clause as a mention** — the `ordF` right arm's form: the
container member's stored constructor `j` MENTIONS, at field `l`, the
container-group member the target names. -/
theorem nestedCopyTargetsOk_mentions {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedCopyTargetsOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {a : AuxStored} (ha : stored[p.k + q]? = some a)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cv : ConstantVal} {nPc nF : Nat} (hc : a.ctors[j]? = some (cv, nPc, nF))
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    (hr : r = .recursive ∨ r = .reflexive)
    (hlo : p.k + qn.grpBase ≤ t) (hhi : t < p.k + qn.grpBase + qn.grpSize) :
    ∃ (jbs : List (Expr × BinderMeta)) (rJ : Expr) (domJ : Expr × BinderMeta)
      (Jt : ContainerMember),
      cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ) ∧
      jbs[ci.nP + l]? = some domJ ∧
      ci.members[t - p.k - qn.grpBase]? = some Jt ∧
      domJ.1.mentionsConst Jt.name = true := by
  obtain ⟨jbs, rJ, domJ, Jt, d, tbs, jres, us, hsJ, hdJ, hJt, hpk, hfn⟩ :=
    nestedCopyTargetsOk_head h hk hq hqn hks ha hci hJ hj hkf hc hcJ hl hr hlo hhi
  refine ⟨jbs, rJ, domJ, Jt, hsJ, hdJ, hJt, ?_⟩
  have hjm : jres.mentionsConst Jt.name = true := by
    have := mentionsConst_mkAppN_of_fn (T := Jt.name) jres.getAppArgs jres.getAppFn
      (by rw [hfn]; simp [Expr.mentionsConst])
    rw [Expr.mkAppN_getApp jres] at this
    exact this
  rw [stripPis_mkPisB _ hpk]
  exact mentionsConst_mkPisB tbs jres hjm

/-- **K.60's clause, read back**: at pin `q`, constructor `j` and field
`l` of the CONTAINER's own stored constructor, a domain headed by
another stored container `K` — not a member of the container's own
group — whose first `ciK.nP` arguments mention one of that group's
members forces the auxiliary block's classification of the COPY's field
`l` to be `.recursive` into a PIN (`p.k ≤ t`).

K.32's twin, running the other way, and in the same positional style as
`nestedPinKinds_get` and `nestedCopyTargetsOk_head`, so the same
readers apply.  It needs no `stored[p.k + q]`: the guard is entirely on
the container's side and the conclusion entirely on the kinds table's. -/
theorem nestedCopyPinFieldsOk_head {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedCopyPinFieldsOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    {K : Name} {us : List Level} (hhead : domJ.1.getAppFn = .const K us)
    (hnm : ((ci.members.map (·.name)).contains K) = false)
    {ciK : ContainerInfo} (hciK : containerInfo? env K = some ciK)
    {e : Expr} (he : e ∈ domJ.1.getAppArgs.take ciK.nP)
    (hmen : mentionsMember (ci.members.map (·.name)) e = true) :
    r = .recursive ∧ p.k ≤ t := by
  unfold nestedCopyPinFieldsOk nestedCopyPinFieldsAt nestedCopyFieldsAt at h
  rw [hk] at h
  simp only at h
  have hqv := allPair_fst_mem h q (_root_.List.mem_range.mpr hq)
  rw [hqn, hks] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJ] at hqv
  simp only at hqv
  have hjv := allPair_fst_mem hqv j (_root_.List.mem_range.mpr hj)
  rw [hkf, hcJ] at hjv
  simp only at hjv
  rw [hsJ] at hjv
  simp only at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := allPair_fst_mem hjv l (_root_.List.mem_range.mpr hlLt)
  rw [hl, hdJ] at hlv
  simp only [copyPinFieldOk] at hlv
  rw [hhead] at hlv
  simp only at hlv
  rw [if_neg (by rw [hnm]; simp), hciK] at hlv
  simp only at hlv
  rw [if_pos (by
    simp only [_root_.List.any_eq_true]
    exact ⟨e, he, hmen⟩)] at hlv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlv
  exact hlv


/-- **K.63's clause, read back**: at pin `q`, constructor `j` and field
`l` of the CONTAINER's own stored constructor, a domain that is a
non-empty `Π` telescope whose BODY is headed by another stored
container `K` — not a member of the container's own group — whose first
`ciK.nP` arguments mention one of that group's members forces the
auxiliary block's classification of the COPY's field `l` to be
`.reflexive` into a PIN (`p.k ≤ t`).

`nestedCopyPinFieldsOk_head`'s twin one `Π`-tower down, in the same
positional style and off the SAME walk — `nestedCopyFieldsAt` computes
both arms in one pass and these two theorems read its two components.
The PINF lane consumes this one as the producer of `copyPinFReadRefl`'s
`hkA`. -/
theorem nestedCopyReflFieldsOk_head {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedCopyReflFieldsOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    {d : Expr} {bdy : Expr} {bm : BinderMeta} (hpi : domJ.1 = .forallE d bdy bm)
    {K : Name} {us : List Level} (hhead : (stripDomPis domJ.1).getAppFn = .const K us)
    (hnm : ((ci.members.map (·.name)).contains K) = false)
    {ciK : ContainerInfo} (hciK : containerInfo? env K = some ciK)
    {e : Expr} (he : e ∈ (stripDomPis domJ.1).getAppArgs.take ciK.nP)
    (hmen : mentionsMember (ci.members.map (·.name)) e = true) :
    r = .reflexive ∧ p.k ≤ t := by
  unfold nestedCopyReflFieldsOk nestedCopyReflFieldsAt nestedCopyFieldsAt at h
  rw [hk] at h
  simp only at h
  have hqv := allPair_snd_mem h q (_root_.List.mem_range.mpr hq)
  rw [hqn, hks] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJ] at hqv
  simp only at hqv
  have hjv := allPair_snd_mem hqv j (_root_.List.mem_range.mpr hj)
  rw [hkf, hcJ] at hjv
  simp only at hjv
  rw [hsJ] at hjv
  simp only at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := allPair_snd_mem hjv l (_root_.List.mem_range.mpr hlLt)
  rw [hl, hdJ] at hlv
  simp only [copyReflFieldOk] at hlv
  rw [hpi] at hlv
  simp only at hlv
  rw [← hpi, hhead] at hlv
  simp only at hlv
  rw [if_neg (by rw [hnm]; simp), hciK] at hlv
  simp only at hlv
  rw [if_pos (by
    simp only [_root_.List.any_eq_true]
    exact ⟨e, he, hmen⟩)] at hlv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlv
  exact hlv

/-! ## THE CONTAINER INSTANCE MAP, INVERTED (task #315 K.61 and K.62)

K.61's Bool is stated over `List.range st.pins.length` and reads the
map's table off `nestedInstMaps`; the model consumes it at ONE pin and
ONE own pin of that pin's container.  These theorems are that shape,
and every datum in them is one of `nestedInstMapOk`'s own lookups, so
they cost no new check.

`nestedInstMapOk_at` is both halves of K.61's first clause at a pair:
the map is DEFINED at `q` (totality) and its value at `qK` is a pin
`σ` of the block whose recorded pin TERM is the container's own pin
`own[qK]` — `nestedPinRootPairOk_inv`'s correspondence, positionally
rather than as a membership.  That one equality of pin terms carries
the container's name, the level list, the components and the index
telescope together, exactly as K.41's does.

`nestedInstMapOk_collapsed` is the reading at a COLLAPSED pair: two own
pins that σ sends to ONE block pin have the same pin term, so their
components and index telescopes agree.  The map may collapse — it is
not checked injective — and this is what the wide identification reads
there.

`nestedInstMapOk_target` is K.61's second clause, in
`nestedCopyPinFieldsOk_head`'s binders (K.60's guard verbatim, read off
the telescope instantiated at the parameter openers): the copy's field
lands on the instance map's value at the own-pin position its
container's field sits at.

`nestedOrdOutsideOk_at` is K.62 at one edge. -/

/-- **K.61's map, at one pin and one own pin.** -/
theorem nestedInstMapOk_at {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedInstMapOk env p b st stored = true)
    {q : Nat} (hq : q < st.pins.length)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {lvls : List Level} {Ds : List Expr}
    (hld : nestedPinLvlsDs env qn = some (lvls, Ds))
    {own : List Expr} (hown : containerOwnPinsAt env qn.container lvls Ds = some own)
    {qK : Nat} {e : Expr} (he : own[qK]? = some e) :
    ∃ (m : List Nat) (σ : Nat) (rn : NestedPin),
      nestedInstMapAt env st q = some m ∧ m[qK]? = some σ ∧
        σ < st.pins.length ∧ st.pins[σ]? = some rn ∧ rn.pin = e := by
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedInstMapOk nestedInstMapOkAt at h
    rw [hms] at h; simp at h
  | some maps =>
    obtain ⟨m, -, hm⟩ := mapM_option_inv hms q q (by simp [hq])
    have hm0 := hm
    simp only [nestedInstMapAt, bind, Option.bind, hqn, hld, hown] at hm
    obtain ⟨σ, hσ, hfi⟩ := mapM_option_inv hm qK e he
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    exact ⟨m, σ, st.pins[σ], hm0, hσ, hlt, List.getElem?_eq_getElem hlt, by simpa using hp⟩

/-- **K.61's map at a COLLAPSED pair**: two own pins with one image have
one pin term. -/
theorem nestedInstMapOk_collapsed {env : Env} {st : ElimState}
    {m : List Nat} {q : Nat} (hm : nestedInstMapAt env st q = some m)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {lvls : List Level} {Ds : List Expr}
    (hld : nestedPinLvlsDs env qn = some (lvls, Ds))
    {own : List Expr} (hown : containerOwnPinsAt env qn.container lvls Ds = some own)
    {qK₁ qK₂ σ : Nat} {e₁ e₂ : Expr}
    (he₁ : own[qK₁]? = some e₁) (he₂ : own[qK₂]? = some e₂)
    (h₁ : m[qK₁]? = some σ) (h₂ : m[qK₂]? = some σ) : e₁ = e₂ := by
  simp only [nestedInstMapAt, bind, Option.bind, hqn, hld, hown] at hm
  obtain ⟨σ₁, hσ₁, hf₁⟩ := mapM_option_inv hm qK₁ e₁ he₁
  obtain ⟨σ₂, hσ₂, hf₂⟩ := mapM_option_inv hm qK₂ e₂ he₂
  have hs₁ : σ = σ₁ := by rw [h₁] at hσ₁; simpa using hσ₁
  have hs₂ : σ = σ₂ := by rw [h₂] at hσ₂; simpa using hσ₂
  obtain ⟨hlt₁, hp₁, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf₁
  obtain ⟨hlt₂, hp₂, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf₂
  have hq₁ : st.pins[σ₁].pin = e₁ := by simpa using hp₁
  have hq₂ : st.pins[σ₂].pin = e₂ := by simpa using hp₂
  have hσ12 : σ₁ = σ₂ := by omega
  subst hσ12
  exact hq₁.symm.trans hq₂

/-- **K.61's clause at an own-pin field, AT EITHER DEPTH** (task #315
K.65): the inversion stated after the `Π`-strip, so that it answers at
a REFLEXIVE nested field as well as at a finitary one.  `stripDomPis`
is the identity on a domain that is not a `Π` and `domPiDepth` is `0`
there, so `nestedInstMapOk_target` below is this theorem at a
const-headed domain. -/
theorem nestedInstMapOk_target_refl {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedInstMapOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {own0 : List Expr} (hown0 : containerOwnPinsSelf env qn.container = some own0)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    {K : Name} {us : List Level} (hhead : (stripDomPis domJ.1).getAppFn = .const K us)
    (hnm : ((ci.members.map (·.name)).contains K) = false)
    {ciK : ContainerInfo} (hciK : containerInfo? env K = some ciK)
    {a : Expr} (ha : a ∈ (stripDomPis domJ.1).getAppArgs.take ciK.nP)
    (hmen : mentionsMember (ci.members.map (·.name)) a = true) :
    ∃ (qK : Nat) (e0 : Expr) (m : List Nat),
      own0.findIdx? (fun x => x == Expr.instantiateList
          (Expr.mkAppN (stripDomPis domJ.1).getAppFn
            ((stripDomPis domJ.1).getAppArgs.take ciK.nP))
          (containerParamOpeners ci.nP).reverse (l + domPiDepth domJ.1)) = some qK ∧
        own0[qK]? = some e0 ∧
        e0 = Expr.instantiateList
          (Expr.mkAppN (stripDomPis domJ.1).getAppFn
            ((stripDomPis domJ.1).getAppArgs.take ciK.nP))
          (containerParamOpeners ci.nP).reverse (l + domPiDepth domJ.1) ∧
        nestedInstMapAt env st q = some m ∧
        m.getD qK st.pins.length = t - p.k := by
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedInstMapOk nestedInstMapOkAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms q q (by simp [hq])
  unfold nestedInstMapOk nestedInstMapOkAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hqv := h q hq
  rw [hqn, hks] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJ, hown0] at hqv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hqv
  have hjv := hqv j hj
  rw [hkf, hcJ] at hjv
  simp only at hjv
  rw [hsJ] at hjv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := hjv l hlLt
  rw [hl, hdJ] at hlv
  simp only at hlv
  rw [hhead] at hlv
  simp only at hlv
  rw [if_neg (by rw [hnm]; simp), hciK] at hlv
  simp only at hlv
  rw [if_pos (by
    simp only [_root_.List.any_eq_true]
    exact ⟨a, ha, hmen⟩)] at hlv
  rw [← hhead] at hlv
  cases hfi : own0.findIdx? (fun x => x == Expr.instantiateList
      (Expr.mkAppN (stripDomPis domJ.1).getAppFn
        ((stripDomPis domJ.1).getAppArgs.take ciK.nP))
      (containerParamOpeners ci.nP).reverse (l + domPiDepth domJ.1)) with
  | none => rw [hfi] at hlv; simp at hlv
  | some qK =>
    rw [hfi] at hlv
    simp only [beq_iff_eq] at hlv
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    refine ⟨qK, own0[qK], m, rfl, List.getElem?_eq_getElem hlt, by simpa using hp, hm, ?_⟩
    rw [show maps.getD q [] = m from by rw [List.getD_eq_getElem?_getD, hmq]; rfl] at hlv
    simpa using hlv

/-- **K.61's clause at an own-pin FINITARY field**, in
`nestedCopyPinFieldsOk_head`'s binders: `nestedInstMapOk_target_refl`
at a domain whose head is a constant, where `stripDomPis` is the
identity and `domPiDepth` is `0` (a `Π`'s `getAppFn` is the `Π`
itself, never a `.const`). -/
theorem nestedInstMapOk_target {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedInstMapOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {own0 : List Expr} (hown0 : containerOwnPinsSelf env qn.container = some own0)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    {K : Name} {us : List Level} (hhead : domJ.1.getAppFn = .const K us)
    (hnm : ((ci.members.map (·.name)).contains K) = false)
    {ciK : ContainerInfo} (hciK : containerInfo? env K = some ciK)
    {a : Expr} (ha : a ∈ domJ.1.getAppArgs.take ciK.nP)
    (hmen : mentionsMember (ci.members.map (·.name)) a = true) :
    ∃ (qK : Nat) (e0 : Expr) (m : List Nat),
      own0.findIdx? (fun x => x == Expr.instantiateList
          (Expr.mkAppN domJ.1.getAppFn (domJ.1.getAppArgs.take ciK.nP))
          (containerParamOpeners ci.nP).reverse l) = some qK ∧
        own0[qK]? = some e0 ∧
        e0 = Expr.instantiateList
          (Expr.mkAppN domJ.1.getAppFn (domJ.1.getAppArgs.take ciK.nP))
          (containerParamOpeners ci.nP).reverse l ∧
        nestedInstMapAt env st q = some m ∧
        m.getD qK st.pins.length = t - p.k := by
  have hnf : stripDomPis domJ.1 = domJ.1 ∧ domPiDepth domJ.1 = 0 := by
    cases hd : domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hhead
      have hc : Expr.forallE ty bo bm = Expr.const K us := hhead
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  have hres := nestedInstMapOk_target_refl h hk hq hqn hks hci hJ hown0 hj hkf hcJ hsJ hl hdJ
    (by rw [hnf.1]; exact hhead) hnm hciK (by rw [hnf.1]; exact ha) hmen
  rw [hnf.1, hnf.2, Nat.add_zero] at hres
  exact hres

/-- **K.62 at one edge, WITH K.66's SECOND HALF**: an `ordF`-right
reference leaves the instance — both the container's own pins' classes
(the instance map's image) and its members' (the mint group). -/
theorem nestedOrdOutsideOk_at {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdOutsideOk env p b st stored = true)
    {edges : List (Nat × Nat × Bool)}
    (hedges : nestedPinEdges env p b st stored = some edges)
    {q t : Nat} (hq : q < st.pins.length)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {mentions : Bool} (hmem : (q, t, mentions) ∈ edges)
    (hno : mentions = false) :
    ∃ m : List Nat, nestedInstMapAt env st q = some m ∧ m.contains t = false ∧
      (t < qn.grpBase ∨ qn.grpBase + qn.grpSize ≤ t) := by
  subst hno
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdOutsideOk nestedOrdOutsideAt at h
    rw [hms] at h; simp at h
  | some maps =>
  unfold nestedOrdOutsideOk nestedOrdOutsideAt at h
  rw [hms, hedges] at h
  simp only [_root_.List.all_eq_true] at h
  have hb := h _ hmem
  rw [Bool.false_or, hqn] at hb
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hb
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms q q (by simp [hq])
  refine ⟨m, hm, ?_, hb2⟩
  rw [show maps.getD q [] = m from by rw [List.getD_eq_getElem?_getD, hmq]; rfl] at hb1
  simpa using hb1


/-! ## THE REWRITTEN ORDINARY FIELD'S TARGET, INVERTED (task #315 K.67)

K.62 inverted says where such a target is NOT.  This says where it IS:
at the field of the container `K` that the block's copy at pin `q`
rewrote, the recorded target is the block class of the class the OWNER
`J` — the container whose own pin number `qK` this copy is — gave the
same field, recomputed from `K`'s STORED constructor at `J`'s own
components (`ordTargetDom`).  Two implications rather than a
disjunction, because the consumer always knows which case it is in:
the owner's reading is headed either by one of `J`'s MEMBERS or by one
of `J`'s own pins, and the two are told apart by the same `findIdx?`
the Bool runs.

Every datum is one of `nestedOrdTargetOk`'s own lookups, so this costs
no new check. -/

/-- **K.67 at one owner, one own pin, one constructor and one field.** -/
theorem nestedOrdTargetOk_at_refl {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdTargetOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    {q : Nat} (hq : mapR.getD qK st.pins.length = q)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {Jm : ContainerMember} (hJm : ci.members[q - qn.grpBase]? = some Jm)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : Jm.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    (hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true)
    (hkt : p.k ≤ t)
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {M : Name} {us : List Level}
    (hhead : (ordTargetDom ci.nP ownSelf qK l domJ.1).getAppFn = .const M us) :
    (∀ mm, (ciJ.members.map (·.name)).findIdx? (· == M) = some mm →
        t = p.k + gn.grpBase + mm) ∧
    (∀ (ciM : ContainerInfo) (qJ : Nat),
      (ciJ.members.map (·.name)).findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      ownSelf.findIdx? (fun e => e == Expr.mkAppN (ordTargetDom ci.nP ownSelf qK l domJ.1).getAppFn
          ((ordTargetDom ci.nP ownSelf qK l domJ.1).getAppArgs.take ciM.nP)) = some qJ →
      t = p.k + mapR.getD qJ st.pins.length) := by
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdTargetOk nestedOrdTargetAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms g g (by simp [hg])
  have hmeq : m = mapR := by rw [hm] at hmapR; simpa using hmapR
  unfold nestedOrdTargetOk nestedOrdTargetAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hgv := h g hg
  rw [hgn] at hgv
  simp only at hgv
  rw [hciJ] at hgv
  simp only at hgv
  rw [hown] at hgv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hgv
  have hqv := hgv qK hqK
  rw [show maps.getD g [] = mapR from by
    rw [List.getD_eq_getElem?_getD, hmq]; exact hmeq] at hqv
  rw [hq, hqn, hks] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJm] at hqv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hqv
  have hjv := hqv j hj
  rw [hkf, hcJ] at hjv
  simp only at hjv
  rw [hsJ] at hjv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := hjv l hlLt
  rw [hl, hdJ] at hlv
  simp only at hlv
  rw [if_neg (by simp [hrec, hkt]), if_neg (by simp [hord])] at hlv
  rw [hhead] at hlv
  simp only at hlv
  refine ⟨fun mm hmm => ?_, fun ciM qJ hnm hciM hfi => ?_⟩
  · rw [hmm] at hlv
    simpa using hlv
  · rw [hnm, hciM] at hlv
    simp only at hlv
    rw [← hhead] at hlv
    rw [hfi] at hlv
    simpa using hlv

/-- **K.67 at a FINITARY field**, where the cut is the identity: the
domain's head is a `.const`, so it is not a `Π` and `stripDomPis` and
`domPiDepth` say nothing.  K.61's `nestedInstMapOk_target` pattern. -/
theorem nestedOrdTargetOk_at {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdTargetOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    {q : Nat} (hq : mapR.getD qK st.pins.length = q)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {Jm : ContainerMember} (hJm : ci.members[q - qn.grpBase]? = some Jm)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : Jm.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    (hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true)
    (hkt : p.k ≤ t)
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {K : Name} {usK : List Level} (hfin : domJ.1.getAppFn = .const K usK)
    {M : Name} {us : List Level}
    (hhead : (Expr.instantiateList domJ.1
        (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppFn
      = .const M us) :
    (∀ mm, (ciJ.members.map (·.name)).findIdx? (· == M) = some mm →
        t = p.k + gn.grpBase + mm) ∧
    (∀ (ciM : ContainerInfo) (qJ : Nat),
      (ciJ.members.map (·.name)).findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      ownSelf.findIdx? (fun e => e == Expr.mkAppN
          (Expr.instantiateList domJ.1
            (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppFn
          ((Expr.instantiateList domJ.1
            (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppArgs.take
              ciM.nP)) = some qJ →
      t = p.k + mapR.getD qJ st.pins.length) := by
  have hnf : stripDomPis domJ.1 = domJ.1 ∧ domPiDepth domJ.1 = 0 := by
    cases hd : domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hfin
      have hc : Expr.forallE ty bo bm = Expr.const K usK := hfin
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  have hdm : ordTargetDom ci.nP ownSelf qK l domJ.1
      = Expr.instantiateList domJ.1
          (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hnf.1, hnf.2, Nat.add_zero]
  rw [← hdm] at hhead ⊢
  exact nestedOrdTargetOk_at_refl h hk hg hgn hciJ hown hmapR hqK hq hqn hks hci hJm hj hkf hcJ
    hsJ hl hdJ hrec hkt hord hhead


/-! ## THE BLOCK'S OWN CLASS AT A REWRITTEN ORDINARY FIELD (task #315 K.68)

K.67 inverted answers about a copy that is another container's own pin.
This answers about the block's OWN pins, in the block's own vocabulary:
the recorded target is the class the block's own recomputation names —
a MEMBER by its name among `p.memberNames`, or a PIN by its term among
`nestedPinTermsSelf`, the same table the recomputation instantiates in.

Two implications rather than a disjunction, for K.67's reason: the
consumer always knows which case it is in. -/

/-- **K.68 at one pin, one constructor and one field.** -/
theorem nestedOrdSelfTargetOk_at_refl {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdSelfTargetOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {Jm : ContainerMember} (hJm : ci.members[q - qn.grpBase]? = some Jm)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : Jm.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    (hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true)
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {M : Name} {us : List Level}
    (hhead : (ordTargetDom ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn = .const M us) :
    (∀ mm, p.memberNames.findIdx? (· == M) = some mm → t = mm) ∧
    (∀ (ciM : ContainerInfo) (z : Nat),
      p.memberNames.findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (ordTargetDom ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn
          ((ordTargetDom ci.nP (nestedPinTermsSelf p st) q l
            domJ.1).getAppArgs.take ciM.nP)) = some z →
      t = p.k + z) := by
  unfold nestedOrdSelfTargetOk nestedOrdSelfTargetAt at h
  rw [hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hqv := h q hq
  rw [hqn, hks] at hqv
  simp only at hqv
  rw [hci] at hqv
  simp only at hqv
  rw [hJm] at hqv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hqv
  have hjv := hqv j hj
  rw [hkf, hcJ] at hjv
  simp only at hjv
  rw [hsJ] at hjv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hjv
  have hlLt : l < kf.length := (_root_.List.getElem?_eq_some_iff.mp hl).1
  have hlv := hjv l hlLt
  rw [hl, hdJ] at hlv
  simp only at hlv
  rw [if_neg (by simp [hrec]), if_neg (by simp [hord])] at hlv
  rw [hhead] at hlv
  simp only at hlv
  refine ⟨fun mm hmm => ?_, fun ciM z hnm hciM hfi => ?_⟩
  · rw [hmm] at hlv
    simpa using hlv
  · rw [hnm, hciM] at hlv
    simp only at hlv
    rw [← hhead] at hlv
    rw [hfi] at hlv
    simpa using hlv

/-- **K.68 at a FINITARY field**, where the cut is the identity. -/
theorem nestedOrdSelfTargetOk_at {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdSelfTargetOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length) {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {Jm : ContainerMember} (hJm : ci.members[q - qn.grpBase]? = some Jm)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : Jm.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {rJ : Expr}
    (hsJ : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, rJ))
    {l : Nat} {r : RecFieldKind} {t : Nat} (hl : kf[l]? = some (r, t))
    {domJ : Expr × BinderMeta} (hdJ : jbs[ci.nP + l]? = some domJ)
    (hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true)
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {K : Name} {usK : List Level} (hfin : domJ.1.getAppFn = .const K usK)
    {M : Name} {us : List Level}
    (hhead : (Expr.instantiateList domJ.1
        ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
        l).getAppFn = .const M us) :
    (∀ mm, p.memberNames.findIdx? (· == M) = some mm → t = mm) ∧
    (∀ (ciM : ContainerInfo) (z : Nat),
      p.memberNames.findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (Expr.instantiateList domJ.1
            ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
            l).getAppFn
          ((Expr.instantiateList domJ.1
            ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
            l).getAppArgs.take ciM.nP)) = some z →
      t = p.k + z) := by
  have hnf : stripDomPis domJ.1 = domJ.1 ∧ domPiDepth domJ.1 = 0 := by
    cases hd : domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hfin
      have hc : Expr.forallE ty bo bm = Expr.const K usK := hfin
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  have hdm : ordTargetDom ci.nP (nestedPinTermsSelf p st) q l domJ.1
      = Expr.instantiateList domJ.1
          ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hnf.1, hnf.2, Nat.add_zero]
  rw [← hdm] at hhead ⊢
  exact nestedOrdSelfTargetOk_at_refl h hk hq hqn hks hci hJm hj hkf hcJ hsJ hl hdJ hrec hord hhead

end ConLeche
