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


/-! ## THE OWNER'S FIRING, PRODUCED FROM THE TWO LOOKUPS (task #315 K.70)

`ordRootFired` is K.67's head test read as a Bool, so each of the two
arms K.67's walk takes — the head among the owner's MEMBERS, or among
the containers of its own PINS — produces it.  K.70 puts the walk's
assertions BELOW that Bool, so an inversion at either arm has to
re-enter the branch, and these two are what it enters with. -/

/-- The head is one of the owner's members. -/
theorem ordRootFired_of_mem {env : Env} {memsJ : List Name} {ownSelf : List Expr}
    {W : Expr} {M : Name} {us : List Level} {mm : Nat}
    (hhead : W.getAppFn = .const M us)
    (hmm : memsJ.findIdx? (· == M) = some mm) :
    ordRootFired env memsJ ownSelf W = true := by
  unfold ordRootFired
  rw [hhead]
  simp only [Bool.or_eq_true]
  refine Or.inl ?_
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmm
  have hMe : memsJ[mm] = M := by simpa using hp
  exact List.contains_iff_exists_mem_beq.mpr ⟨memsJ[mm], List.getElem_mem hlt, by simp [hMe]⟩

/-- The head is the container of one of the owner's own pins. -/
theorem ordRootFired_of_pin {env : Env} {memsJ : List Name} {ownSelf : List Expr}
    {W : Expr} {M : Name} {us : List Level} {ciM : ContainerInfo} {qJ : Nat}
    (hhead : W.getAppFn = .const M us)
    (hciM : containerInfo? env M = some ciM)
    (hfi : ownSelf.findIdx? (fun e => e == Expr.mkAppN W.getAppFn
      (W.getAppArgs.take ciM.nP)) = some qJ) :
    ordRootFired env memsJ ownSelf W = true := by
  unfold ordRootFired
  rw [show W.getAppFn = Expr.const M us from hhead] at *
  simp only [Bool.or_eq_true]
  refine Or.inr ?_
  simp only [hciM, hfi, Option.isSome_some]

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
    {Wn : Expr}
    (hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = Wn)
    {M : Name} {us : List Level}
    (hhead : Wn.getAppFn = .const M us) :
    (∀ mm, (ciJ.members.map (·.name)).findIdx? (· == M) = some mm →
        t = p.k + gn.grpBase + mm) ∧
    (∀ (ciM : ContainerInfo) (qJ : Nat),
      (ciJ.members.map (·.name)).findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      ownSelf.findIdx? (fun e => e == Expr.mkAppN Wn.getAppFn
          (Wn.getAppArgs.take ciM.nP)) = some qJ →
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
  simp only [Bool.and_eq_true] at hqv
  obtain ⟨-, hqv⟩ := hqv
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
  rw [if_neg (by simp [hrec, hkt])] at hlv
  rw [hnorm] at hlv
  refine ⟨fun mm hmm => ?_, fun ciM qJ hnm hciM hfi => ?_⟩
  · rw [if_pos (ordRootFired_of_mem (ownSelf := ownSelf) (env := env) hhead hmm), hhead] at hlv
    simp only at hlv
    rw [hmm] at hlv
    simpa using hlv
  · rw [if_pos (ordRootFired_of_pin (memsJ := ciJ.members.map (·.name)) hhead hciM hfi),
      hhead] at hlv
    simp only at hlv
    rw [hnm, hciM] at hlv
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
    {K : Name} {usK : List Level}
    (hfin : (ordTargetDomL Jm.lps ownSelf qK domJ.1).getAppFn = .const K usK)
    {M : Name} {us : List Level}
    (hhead : (Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
        (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppFn
      = .const M us) :
    (∀ mm, (ciJ.members.map (·.name)).findIdx? (· == M) = some mm →
        t = p.k + gn.grpBase + mm) ∧
    (∀ (ciM : ContainerInfo) (qJ : Nat),
      (ciJ.members.map (·.name)).findIdx? (· == M) = none →
      containerInfo? env M = some ciM →
      ownSelf.findIdx? (fun e => e == Expr.mkAppN
          (Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
            (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppFn
          ((Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
            (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l).getAppArgs.take
              ciM.nP)) = some qJ →
      t = p.k + mapR.getD qJ st.pins.length) := by
  have hnf : stripDomPis (ordTargetDomL Jm.lps ownSelf qK domJ.1)
      = ordTargetDomL Jm.lps ownSelf qK domJ.1 ∧
      domPiDepth (ordTargetDomL Jm.lps ownSelf qK domJ.1) = 0 := by
    cases hd : ordTargetDomL Jm.lps ownSelf qK domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hfin
      have hc : Expr.forallE ty bo bm = Expr.const K usK := hfin
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  have hdm : ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1
      = Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
          (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hnf.1, hnf.2, Nat.add_zero]
  rw [← hdm] at hhead ⊢
  exact nestedOrdTargetOk_at_refl h hk hg hgn hciJ hown hmapR hqK hq hqn hks hci hJm hj hkf hcJ
    hsJ hl hdJ hrec hkt (ordHeadRed_const hhead) hhead


/-- **K.70's ARM (A), THE MEMBER HALF — THE MINTED GROUP'S IMAGE IS
CONTIGUOUS** (task #315 K.70): the block pin the owner's own pin `qK`
is mapped to sits at offset `q - qn.grpBase` in the block's group, and
the owner's own pin for the container's member `mm` — the one at the
same offset in the owner's own table — is mapped to the block's
`qn.grpBase + mm`.

It is a statement about the MAP alone: no field, no recomputation and
no head.  That is all a container-RECURSIVE field at a MEMBER target
needs, because both copies' targets are already exact there
(`CopyCtorShape.recF` gives the block's as `p.k + qn.grpBase + mm` and
the owner's as `dR.k + baseK + mm`) and only the map's contiguity ties
the two. -/
theorem nestedOrdTargetOk_grp_at {env : Env} {p : NestedParts} {b : MutualBlock}
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
    {mm : Nat} (hmm : mm < qn.grpSize) :
    mapR.getD (qK - (q - qn.grpBase) + mm) st.pins.length = qn.grpBase + mm := by
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
  simp only [Bool.and_eq_true] at hqv
  obtain ⟨hgrp, -⟩ := hqv
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at hgrp
  have hcell := hgrp mm hmm
  simpa using hcell

/-- **K.70's ARM (C) — THE OWNER DID NOT FIRE, AND THE BLOCK'S TARGET
LEAVES THE OWNER'S INSTANCE** (task #315 K.70).

K.62 and K.66 say a rewritten ordinary field's target leaves the
COPY's own instance — its own container's pins and its own mint group.
This says the same one nesting level up, and only where the owner's
own recomputation did NOT fire: the target is in neither the image of
the OWNER's instance map nor the OWNER's own mint group.  Where the
owner DID fire the positive row (`nestedOrdTargetOk_at_refl`) speaks
instead, so the two are a dichotomy and neither is a weakening of the
other. -/
theorem nestedOrdTargetOk_out_at {env : Env} {p : NestedParts} {b : MutualBlock}
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
    {Wn : Expr}
    (hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = Wn)
    (hnofire : ordRootFired env (ciJ.members.map (·.name)) ownSelf Wn = false) :
    mapR.contains (t - p.k) = false ∧
      (t < p.k + gn.grpBase ∨ p.k + gn.grpBase + gn.grpSize ≤ t) := by
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
  simp only [Bool.and_eq_true] at hqv
  obtain ⟨-, hqv⟩ := hqv
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
  rw [if_neg (by simp [hrec, hkt])] at hlv
  rw [hnorm] at hlv
  rw [if_neg (by simp [hnofire]), if_neg (by simp [hord])] at hlv
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hlv
  exact hlv

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
    {M : Name} {us : List Level}
    (hhead : (ordHeadRed
      (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1)).getAppFn
      = .const M us) :
    (∀ mm, p.memberNames.findIdx? (· == M) = some mm → t = mm) ∧
    (p.memberNames.findIdx? (· == M) = none →
      ∃ (ciM : ContainerInfo) (z : Nat),
      containerInfo? env M = some ciM ∧
      (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (ordHeadRed
            (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1)).getAppFn
          ((ordHeadRed (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l
            domJ.1)).getAppArgs.take ciM.nP)) = some z ∧
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
  rw [if_neg (by simp [hrec])] at hlv
  rw [hhead] at hlv
  simp only at hlv
  refine ⟨fun mm hmm => ?_, fun hnm => ?_⟩
  · rw [hmm] at hlv
    simpa using hlv
  · -- the strengthened arms (task #315 WIDE (3)): the head's container
    -- lookup and the own-pin `findIdx?` BOTH succeed, because their
    -- `none` arms are `false`
    rw [hnm] at hlv
    simp only at hlv
    obtain ⟨ciM, hciM⟩ : ∃ ciM, containerInfo? env M = some ciM := by
      cases hc : containerInfo? env M with
      | none => rw [hc] at hlv; exact nomatch hlv
      | some c => exact ⟨c, rfl⟩
    rw [hciM] at hlv
    simp only at hlv
    rw [← hhead] at hlv
    obtain ⟨z, hfi⟩ : ∃ z, (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
        (ordHeadRed
          (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1)).getAppFn
        ((ordHeadRed (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l
          domJ.1)).getAppArgs.take ciM.nP)) = some z := by
      cases hc : (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (ordHeadRed
            (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1)).getAppFn
          ((ordHeadRed (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l
            domJ.1)).getAppArgs.take ciM.nP)) with
      | none => rw [hc] at hlv; exact nomatch hlv
      | some z => exact ⟨z, rfl⟩
    rw [hfi] at hlv
    exact ⟨ciM, z, hciM, hfi, by simpa using hlv⟩

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
    {K : Name} {usK : List Level}
    (hfin : (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1).getAppFn = .const K usK)
    {M : Name} {us : List Level}
    (hhead : (ordHeadRed
        (Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
          ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
          l)).getAppFn = .const M us) :
    (∀ mm, p.memberNames.findIdx? (· == M) = some mm → t = mm) ∧
    (p.memberNames.findIdx? (· == M) = none →
      ∃ (ciM : ContainerInfo) (z : Nat),
      containerInfo? env M = some ciM ∧
      (nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (ordHeadRed
            (Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
              ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
              l)).getAppFn
          ((ordHeadRed
            (Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
              ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse)
              l)).getAppArgs.take ciM.nP)) = some z ∧
      t = p.k + z) := by
  have hnf : stripDomPis (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
      = ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1 ∧
      domPiDepth (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1) = 0 := by
    cases hd : ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hfin
      have hc : Expr.forallE ty bo bm = Expr.const K usK := hfin
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  have hdm : ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1
      = Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
          ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hnf.1, hnf.2, Nat.add_zero]
  rw [← hdm] at hhead ⊢
  exact nestedOrdSelfTargetOk_at_refl h hk hq hqn hks hci hJm hj hkf hcJ hsJ hl hdJ hrec hhead

/-! ## THE REWRITTEN ORDINARY FIELD'S DOMAIN, INVERTED (task #315 K.69)

K.67 and K.68 inverted say which CLASS the two copies of a container
constructor give a field the container calls ordinary.  This says that
their two field DOMAINS are ONE SUBSTITUTION apart: the block's copy's
is the owner's, at the owner's level parameters instantiated at the
block pin's levels and the owner's parameter openers instantiated at
the block pin's components (`ordRootInst`).

The guard is the OWNER's firing — K.67's head test, applied to the
mint's POSITIVITY NORMAL FORM (`ordRootNorm`, which runs the walk only
where the mint's head is not already a constant).  Where the head IS
already a constant the normal form is the term itself and nothing is
run: such a term is its own positivity normalisation
(`normPosDomM_indApp`), the head survives the substitution, and the
equation carries from the mints to the normalisations.  Where it is
not — the REDUCTION SLIVER — both sides are normalised the same way
before the comparison, so the row holds whenever the owner fired at
all.  Where the owner did NOT fire nothing is claimed: that is the
mixed corner, whose block-side target leaves the instance and which
the model closes with an entry.

Every datum is one of `nestedOrdNormOk`'s own lookups, so this costs no
new check. -/

/-- **A CONSTANT SPINE HEAD SURVIVES A BULK INSTANTIATION**: neither
`instantiateList`'s `.app` clause nor its `.const` clause moves the
head of an application spine.  What lets the FINITARY inversion below
read `ordRootNorm` off `ordTargetDomL`'s head, which is where the
recomputation's own guards are stated. -/
theorem getAppFn_instantiateList_const : ∀ {e : Expr} {c : Name} {us : List Level}
    {vs : List Expr} {d : Nat}, e.getAppFn = .const c us →
    (e.instantiateList vs d).getAppFn = .const c us := by
  intro e
  induction e with
  | app f a ih _ =>
    intro c us vs d h
    simp only [Expr.instantiateList, Expr.getAppFn] at h ⊢
    exact ih h
  | const n us' => intro c us vs d h; simpa only [Expr.instantiateList] using h
  | _ => intro c us vs d h; simp only [Expr.getAppFn] at h; exact absurd h (by simp)

/-- **K.69 at one owner, one own pin, one constructor and one field.** -/
theorem nestedOrdNormOk_at_refl {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {Wn : Expr}
    (hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = Wn)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf Wn = true)
    {Wb : Expr}
    (hinst : ordRootInst m₀.lps ciJ.nP
        (l + domPiDepth (ordTargetDomL Jm.lps ownSelf qK domJ.1))
        ((nestedPinTermsSelf p st).getD g default) Wn = some Wb)
    {Wn₁ : Expr}
    (hnormB : ordHeadRed (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1)
      = Wn₁) :
    Wn₁ = Wb := by
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdNormOk nestedOrdNormAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms g g (by simp [hg])
  have hmeq : m = mapR := by rw [hm] at hmapR; simpa using hmapR
  unfold nestedOrdNormOk nestedOrdNormAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hgv := h g hg
  rw [hgn] at hgv
  simp only at hgv
  rw [hciJ] at hgv
  simp only at hgv
  rw [hown] at hgv
  simp only at hgv
  rw [hm₀] at hgv
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
  rw [if_neg (by simp [hord])] at hlv
  rw [hnorm] at hlv
  rw [if_neg (by simp [hfire]), if_neg (by simp [hrec])] at hlv
  -- the block-head row (WIDE (f3) step 2) sits between the kind test
  -- and the instantiation; it is ASSERTED here under its own guard
  -- (the RAW mint fired), and read separately by
  -- `nestedOrdNormOk_blkHead`
  -- the three conjuncts under the guard: the block-head row (WIDE
  -- (f3) step 2), THIS row's instantiation, and K.72's tower
  simp only [Bool.and_eq_true] at hlv
  replace hlv := hlv.1.2
  rw [hinst] at hlv
  simp only at hlv
  rw [hnormB] at hlv
  simpa using hlv

/-- **THE OWNER'S FIRING FORCES THE BLOCK'S CLASSIFICATION** (task #315
WIDE (f3), K.69 STRENGTHENED) — the row's sibling inversion, and the
producer of the model's `hfireOrd` (`rs₂ → rs₁`).

At a field the shared container calls ORDINARY, where the OWNER's
recomputation fired — its positivity normal form is headed by a
constant that is one of the owner's group members or the container of
one of the owner's own pins — the BLOCK's copy of that field is
`.recursive` or `.reflexive`.

**Why the row may assert it.**  A constant head survives the block's
instantiation, and a constant-headed inductive application is its own
`whnf` (`whnf_indApp_eq`, `normPosDomM_indApp`), so the block's own
positivity walk meets the same inductive head and rewrites the field.
Every `blkRss`-guarded row (K.67's `ordTgt`, K.68's `ordGe`, K.69's
`ordRead`) ASSUMES this conclusion, so none of them can produce it;
the row's own arm is where it lives.

The lookups are `nestedOrdNormOk_at_refl`'s, character for character —
the two differ only in which side of the strengthened arm they read. -/
theorem nestedOrdNormOk_fire {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {Wn : Expr}
    (hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = Wn)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf Wn = true) :
    (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdNormOk nestedOrdNormAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms g g (by simp [hg])
  have hmeq : m = mapR := by rw [hm] at hmapR; simpa using hmapR
  unfold nestedOrdNormOk nestedOrdNormAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hgv := h g hg
  rw [hgn] at hgv
  simp only at hgv
  rw [hciJ] at hgv
  simp only at hgv
  rw [hown] at hgv
  simp only at hgv
  rw [hm₀] at hgv
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
  rw [if_neg (by simp [hord])] at hlv
  rw [hnorm] at hlv
  rw [if_neg (by simp [hfire])] at hlv
  cases hr : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) with
  | true => rfl
  | false => rw [hr] at hlv; simp at hlv

/-- **A FIRING ROOT IS CONSTANT-HEADED**, and that is `ordRootFired`'s
own first `match`: every other head answers `false`.  What lets the
strengthened row's consumers drop the head guard — the firing they
already hold carries it. -/
theorem getAppFn_const_of_ordRootFired {env : Env} {memsJ : List Name} {ownSelf : List Expr}
    {W : Expr} (h : ordRootFired env memsJ ownSelf W = true) :
    ∃ (M : Name) (us : List Level), W.getAppFn = .const M us := by
  unfold ordRootFired at h
  cases hd : W.getAppFn with
  | const M us => exact ⟨M, us, rfl⟩
  | _ => rw [hd] at h; simp at h

/-- **`ordRootInst` MOVES NO CONSTANT HEAD** (task #315 WIDE (f3) step
3(b)): the block's recomputation is the owner's at the block pin's
levels and components (K.69's own equation), and every step of that
substitution — the level instantiation, the parameter abstraction and
the components' fold — leaves a constant head where it found it.

That is what ties the two recomputations' head NAMES, which the wide
identification's consumers spend where they compare the OWNER's target
pin and the BLOCK's at ONE container.  At a constant-headed stored
domain the tie was free; at a bare-parameter one it is this. -/
theorem ordRootInst_getAppFn_const {lpsJ : List Name} {nPJ cut : Nat} {pinG W Wb : Expr}
    {M : Name} {us : List Level}
    (h : ordRootInst lpsJ nPJ cut pinG W = some Wb)
    (hW : W.getAppFn = Expr.const M us) :
    ∃ us' : List Level, Wb.getAppFn = Expr.const M us' := by
  unfold ordRootInst at h
  cases hp : pinG.getAppFn with
  | const I lvlsJ =>
    rw [hp] at h
    obtain rfl : Wb = Expr.instantiateList
        (Expr.abstractRange (W.instantiateLevelParams lpsJ lvlsJ) 0 nPJ cut)
        ((pinG.getAppArgs.take nPJ).reverse) cut := (Option.some.inj h).symm
    refine ⟨us.map (Level.subst lpsJ lvlsJ), ?_⟩
    refine getAppFn_instantiateList_const ?_
    -- the abstraction, on the spine the head already has
    rw [show W.instantiateLevelParams lpsJ lvlsJ
        = Expr.mkAppN (W.instantiateLevelParams lpsJ lvlsJ).getAppFn
            (W.instantiateLevelParams lpsJ lvlsJ).getAppArgs from (Expr.mkAppN_getApp _).symm,
      Expr.getAppFn_instantiateLevelParams, hW]
    rw [abstractRange_mkAppN,
      show Expr.instantiateLevelParams lpsJ lvlsJ (Expr.const M us)
        = Expr.const M (us.map (Level.subst lpsJ lvlsJ)) from rfl,
      abstractRange_const, Expr.getAppFn_mkAppN]
    rfl
  | _ => rw [hp] at h; exact nomatch h

/-- **THE STRENGTHENED ROW AT THE RECOMPUTATION ITSELF** — the shape
the run reads it in.  The guard is the owner's firing at
the ENVIRONMENT-FREE head normal form (`ordHeadRed`, task #315 WIDE
(f3) step 1), which is the term the row itself tests, so the guard
needs no separate head hypothesis and no normalisation input. -/
theorem nestedOrdNormOk_fire_at {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = true) :
    (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
  obtain ⟨M, us, hhd⟩ := getAppFn_const_of_ordRootFired hfire
  exact nestedOrdNormOk_fire h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf
    hcJ hsJ hl hdJ hord (ordHeadRed_const hhd) hfire

/-- **THE BLOCK'S OWN RECOMPUTATION IS CONSTANT-HEADED** (task #315
WIDE (f3) step 2), K.69's third sibling inversion.

At a field the shared container calls ORDINARY whose OWNER's RAW
recomputation fired — the mint itself, before any reduction — the
BLOCK's recomputation, the same stored domain instantiated at the
BLOCK pin's own components, is headed by a constant.

**THE GUARD IS THE RAW MINT'S FIRING AND NOT ITS NORMAL FORM'S**, and
that is measured, not chosen.  The block's recomputation IS the owner's
under the mint's substitution and a substitution does not move a
CONSTANT head — but the owner's NORMAL FORM being constant-headed says
nothing about the mint it came from, and at a redex mint
(`tests/e2e/nested_redex_owner.ndjson`) the block's raw recomputation
is a redex too.  Under the normalised guard this row FIRES on that
official ACCEPT.  The raw guard is exactly the one the model's
`hscope` already carries.

**Why it had to be recorded.**  The model asked this of the STORED
domain instead, in eight places, and that is FALSE: a product
container's field domain is a bare parameter (`Pair α β | mk (a : α)
(b : β)`), whose `getAppFn` is a `bvar`, while the recomputation at the
owner's components is constant-headed.  Asserting the stored-domain
form in the kernel turns three OFFICIAL ACCEPTS into errors
(`nested_pin_nocollide`, `nested_p04`, `nested_bvar_field`).  This is
the form the model actually spends, it is the RECOMPUTATION's head, and
it cannot fire: the owner's normal form is constant-headed (the guard),
a substitution does not move a constant head, and the block's
recomputation is the owner's under the mint's substitution.

The lookups are `nestedOrdNormOk_at_refl`'s, character for character. -/
theorem nestedOrdNormOk_blkHead {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    (hfireRaw : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = true) :
    ∃ (M : Name) (us : List Level),
      (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn
        = .const M us := by
  obtain ⟨M₀, us₀, hhd₀⟩ := getAppFn_const_of_ordRootFired hfireRaw
  have hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1)
      = ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1 := ordHeadRed_const hhd₀
  have hfire := hfireRaw
  have hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true :=
    nestedOrdNormOk_fire h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf hcJ hsJ
      hl hdJ hord hnorm hfire
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdNormOk nestedOrdNormAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms g g (by simp [hg])
  have hmeq : m = mapR := by rw [hm] at hmapR; simpa using hmapR
  unfold nestedOrdNormOk nestedOrdNormAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hgv := h g hg
  rw [hgn] at hgv
  simp only at hgv
  rw [hciJ] at hgv
  simp only at hgv
  rw [hown] at hgv
  simp only at hgv
  rw [hm₀] at hgv
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
  rw [if_neg (by simp [hord])] at hlv
  rw [hnorm] at hlv
  rw [if_neg (by simp [hfire]), if_neg (by simp [hrec])] at hlv
  simp only [Bool.and_eq_true] at hlv
  obtain ⟨⟨hlv, -⟩, -⟩ := hlv
  cases hd : (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn with
  | const M us => exact ⟨M, us, rfl⟩
  | _ => rw [hd] at hlv; simp [hfireRaw] at hlv

/-- **K.72 — THE COPY'S OWN `Π`-TOWER, AT ONE FIELD** (task #315 WIDE
(f3) step 4 (3)): at a field the shared container calls ORDINARY and
the block's rewrite made recursive, the BLOCK's copy of that field
carries a `Π`-prefix as deep as the container's stored domain's PLUS
the one the mint's substitution plants into the stripped body.

**Why the SUM, and why one comparison and not two arms.**  The naive
row — "the copy's depth is the container's stored domain's" — is
REFUTED by `tests/e2e/nested_comp_tower.ndjson` (`K α | mk (a : α)`
minted at `K (Nat → J β)`), an official ACCEPT at which the container's
domain is a bare parameter (depth `0`) and the copy's field is
`Nat → <copy>` (depth `1`).  The missing summand is exactly the tower
the COMPONENT brings, and `ordTargetDom` — which strips the container's
tower and then substitutes the components — measures it:
`domPiDepth` of the recomputation is the planted depth and nothing
else.  So the two "arms" the design row named are the two summands of
ONE equation.

**It cannot fire**, category (B): the copy's field domain is
`replaceAllNested` of the minted domain, the mint is the container's
stored domain at the pin's levels folded onto the pin's components, and
neither the rewrite nor a level instantiation turns a `Π` into a
non-`Π` or the other way round.  The addressing is K.32's own, so the
row costs one `stored` read and one `stripPis` on a walk the arm
already runs.

The lookups are `nestedOrdNormOk_at_refl`'s, character for character;
what is new is the `stored` chain, which is `nestedCopyTargetsAt`'s. -/
theorem nestedOrdNormOk_tower {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    (hfireRaw : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = true)
    -- the BLOCK's copy, at K.32's own addressing
    {aS : AuxStored} (haS : stored[p.k + q]? = some aS)
    {cvCa : ConstantVal} {nPc nF : Nat} (hac : aS.ctors[j]? = some (cvCa, nPc, nF))
    {cbs : List (Expr × BinderMeta)} {rC : Expr}
    (hsC : cvCa.type.stripPis (p.nP + nF) = some (cbs, rC))
    {domC : Expr × BinderMeta} (hdC : cbs[p.nP + l]? = some domC) :
    (Expr.piBinders domC.1).1.length
      = domPiDepth domJ.1
        + domPiDepth (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1) := by
  obtain ⟨M₀, us₀, hhd₀⟩ := getAppFn_const_of_ordRootFired hfireRaw
  have hnorm : ordHeadRed (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1)
      = ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1 := ordHeadRed_const hhd₀
  have hfire := hfireRaw
  have hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true :=
    nestedOrdNormOk_fire h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf hcJ hsJ
      hl hdJ hord hnorm hfire
  cases hms : nestedInstMaps env st with
  | none =>
    unfold nestedOrdNormOk nestedOrdNormAt at h
    rw [hms] at h; simp at h
  | some maps =>
  obtain ⟨m, hmq, hm⟩ := mapM_option_inv hms g g (by simp [hg])
  have hmeq : m = mapR := by rw [hm] at hmapR; simpa using hmapR
  unfold nestedOrdNormOk nestedOrdNormAt at h
  rw [hms, hk] at h
  simp only [_root_.List.all_eq_true, _root_.List.mem_range] at h
  have hgv := h g hg
  rw [hgn] at hgv
  simp only at hgv
  rw [hciJ] at hgv
  simp only at hgv
  rw [hown] at hgv
  simp only at hgv
  rw [hm₀] at hgv
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
  rw [if_neg (by simp [hord])] at hlv
  rw [hnorm] at hlv
  rw [if_neg (by simp [hfire]), if_neg (by simp [hrec])] at hlv
  simp only [Bool.and_eq_true] at hlv
  replace hlv := hlv.2
  rw [haS] at hlv
  simp only at hlv
  rw [hac] at hlv
  simp only at hlv
  rw [hsC] at hlv
  simp only at hlv
  rw [hdC] at hlv
  simpa using hlv

/-- **K.69 at a FINITARY field**, where the two cuts are the identity:
the recomputed domains' heads are `.const`s, so neither is a `Π` and
`stripDomPis` and `domPiDepth` say nothing.  K.67's
`nestedOrdTargetOk_at` pattern, at both sides — the owner's cut is what
`ordRootInst` abstracts above, and the block's is what the conclusion's
left-hand side carries. -/
theorem nestedOrdNormOk_at {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {K : Name} {usK : List Level}
    (hfin : (ordTargetDomL Jm.lps ownSelf qK domJ.1).getAppFn = .const K usK)
    {KB : Name} {usB : List Level}
    (hfinB : (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1).getAppFn
      = .const KB usB)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
        (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l) = true)
    {Wb : Expr}
    (hinst : ordRootInst m₀.lps ciJ.nP l
        ((nestedPinTermsSelf p st).getD g default)
        (Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
          (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l) = some Wb) :
    Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
        ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse) l = Wb := by
  have hcut : ∀ (own : List Expr) (z : Nat) (K' : Name) (us' : List Level),
      (ordTargetDomL Jm.lps own z domJ.1).getAppFn = .const K' us' →
      stripDomPis (ordTargetDomL Jm.lps own z domJ.1)
          = ordTargetDomL Jm.lps own z domJ.1 ∧
        domPiDepth (ordTargetDomL Jm.lps own z domJ.1) = 0 := by
    intro own z K' us' hf
    cases hd : ordTargetDomL Jm.lps own z domJ.1 with
    | forallE ty bo bm =>
      rw [hd] at hf
      have hc : Expr.forallE ty bo bm = Expr.const K' us' := hf
      exact nomatch hc
    | _ => exact ⟨rfl, rfl⟩
  obtain ⟨hs₁, hd₁⟩ := hcut ownSelf qK K usK hfin
  obtain ⟨hs₂, hd₂⟩ := hcut (nestedPinTermsSelf p st) q KB usB hfinB
  have hdmR : ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1
      = Expr.instantiateList (ordTargetDomL Jm.lps ownSelf qK domJ.1)
          (((ownSelf.getD qK default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hs₁, hd₁, Nat.add_zero]
  have hdmB : ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1
      = Expr.instantiateList (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)
          ((((nestedPinTermsSelf p st).getD q default).getAppArgs.take ci.nP).reverse) l := by
    unfold ordTargetDom
    rw [hs₂, hd₂, Nat.add_zero]
  have hheadR : (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1).getAppFn = .const K usK := by
    rw [hdmR]; exact getAppFn_instantiateList_const hfin
  have hheadB : (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn
      = .const KB usB := by
    rw [hdmB]; exact getAppFn_instantiateList_const hfinB
  rw [← hdmB]
  refine nestedOrdNormOk_at_refl h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf
    hcJ hsJ hl hdJ hrec hord (ordHeadRed_const hheadR) ?_ ?_ (ordHeadRed_const hheadB)
  · rw [hdmR]; exact hfire
  · rw [hdmR, hd₁, Nat.add_zero]; exact hinst

/-- **K.69 AS A TERM EQUATION, GUARDED ON THE RECOMPUTATIONS** (task
#315 WIDE (f3), lane LE) — `nestedOrdNormOk_at_pi` with its two head
guards asked of the terms they are SPENT on.

`_at_pi` takes the head of the STORED domain (level-instantiated and
stripped) on each side and uses it for nothing but
`getAppFn_instantiateList_const`, i.e. to produce the head of the
RECOMPUTATION — which is the only thing `ordHeadRed_const` wants.  The
two are not the same term: `ordTargetDom` instantiates the stripped
domain at the owner's components, so a stored domain headed by a BARE
PARAMETER has a constant-headed recomputation and no constant head of
its own (`tests/e2e/nested_bvar_field.ndjson`, and `Pair α β` in
`nested_pin_nocollide`/`nested_p04`).  Asked here of the
recomputations, the theorem covers those fields too, and the OWNER's
half of the guard becomes free: a firing root IS constant-headed
(`getAppFn_const_of_ordRootFired`).

`nestedOrdNormOk_at_pi` is this theorem at a constant-headed stored
domain, and keeps its own name because that is the shape the run's
`ordNormAt` reads today. -/
theorem nestedOrdNormOk_at_head {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {K : Name} {usK : List Level}
    (hheadR : (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1).getAppFn = .const K usK)
    {KB : Name} {usB : List Level}
    (hheadB : (ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1).getAppFn
      = .const KB usB)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = true)
    {Wb : Expr}
    (hinst : ordRootInst m₀.lps ciJ.nP
        (l + domPiDepth (ordTargetDomL Jm.lps ownSelf qK domJ.1))
        ((nestedPinTermsSelf p st).getD g default)
        (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = some Wb) :
    ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1 = Wb :=
  nestedOrdNormOk_at_refl h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf
    hcJ hsJ hl hdJ hrec hord (ordHeadRed_const hheadR) hfire hinst
    (ordHeadRed_const hheadB)

/-- **K.69 AS A TERM EQUATION AT A REFLEXIVE FIELD** (task #315 WIDE (3),
lane LE) — `nestedOrdNormOk_at`'s twin under a `Π`-tower, and the shape
the model side reads the row in.

`nestedOrdNormOk_at` asks the head test of the recomputation ITSELF,
which is the finitary guard: a domain that is a `Π` has a `.forallE`
head and the hypothesis is unsatisfiable there.  A REFLEXIVE field's
domain is a tower over the spine, and both cuts move with it
(`stripDomPis`, `domPiDepth`) — so the guard belongs on the STRIPPED
term, which is exactly where `ordTargetDom` performs its own
instantiation.  Stated that way the theorem covers BOTH kinds: at a
finitary field `stripDomPis` is the identity and `domPiDepth` is `0`.

**Nothing is normalised and nothing is run.**  A `.const`-headed
stripped term stays `.const`-headed under the bulk instantiation
(`getAppFn_instantiateList_const`), so `ordRootNorm` returns its input
on BOTH sides (`ordHeadRed_const`) and the row's comparison is between
the two RECOMPUTATIONS: the block's IS the owner's, at the owner's
level parameters instantiated at the block pin's levels and the owner's
parameter openers instantiated at the block pin's components.  That is
`ordRootInst`'s spelling, which is the left-hand side of the model
side's own reading law (`denoteMeta_ordRootInst_read`,
`Model/Inductives/NestedFieldRead.lean`), so the two meet with nothing
in between.

**It is `nestedOrdNormOk_at_head` at a constant-headed stored domain**
(task #315 WIDE (f3)): the two guards here are spent on producing the
two RECOMPUTATIONS' heads and on nothing else, and asked of those
directly the theorem also covers a stored domain headed by a bare
parameter, which this one does not.

**NOTHING READS IT SINCE WIDE (f3) STEP 3**: `NestedPinsRun.ordNormAt`,
its one consumer, now takes neither head — the owner's comes free off
the firing and the block's is the step-2 row — so it reads `_at_head`
directly.  This specialisation is kept as the documented bridge between
the two shapes and as the statement a constant-headed stored domain
still licenses; it is in `tests/unconsumed.sh`'s advisory list by
design. -/
theorem nestedOrdNormOk_at_pi {env : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored}
    (h : nestedOrdNormOk env p b st stored = true)
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hk : nestedPinKinds p b stored = some kinds)
    {g : Nat} (hg : g < st.pins.length) {gn : NestedPin} (hgn : st.pins[g]? = some gn)
    {ciJ : ContainerInfo} (hciJ : containerInfo? env gn.container = some ciJ)
    {ownSelf : List Expr} (hown : containerOwnPinsSelf env gn.container = some ownSelf)
    {m₀ : ContainerMember} (hm₀ : ciJ.members.head? = some m₀)
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
    (hord : mentionsMember (ci.members.map (·.name)) domJ.1 = false)
    {K : Name} {usK : List Level}
    (hfin : (stripDomPis (ordTargetDomL Jm.lps ownSelf qK domJ.1)).getAppFn = .const K usK)
    {KB : Name} {usB : List Level}
    (hfinB : (stripDomPis (ordTargetDomL Jm.lps (nestedPinTermsSelf p st) q domJ.1)).getAppFn
      = .const KB usB)
    (hfire : ordRootFired env (ciJ.members.map (·.name)) ownSelf
      (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = true)
    {Wb : Expr}
    (hinst : ordRootInst m₀.lps ciJ.nP
        (l + domPiDepth (ordTargetDomL Jm.lps ownSelf qK domJ.1))
        ((nestedPinTermsSelf p st).getD g default)
        (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1) = some Wb) :
    ordTargetDom Jm.lps ci.nP (nestedPinTermsSelf p st) q l domJ.1 = Wb :=
  nestedOrdNormOk_at_head h hk hg hgn hciJ hown hm₀ hmapR hqK hq hqn hks hci hJm hj hkf
    hcJ hsJ hl hdJ hrec hord (getAppFn_instantiateList_const hfin)
    (getAppFn_instantiateList_const hfinB) hfire hinst

/-! ## K.69's recomputation, in the run's spelling (task #315 WIDE (3) (4c))

`ordTargetDom` is the kernel's spelling of "the container's stored
field domain at the pin's components": the stored domain at the copy's
LEVEL instantiation, stripped of its own `Π`-tower, and instantiated in
BULK (`Expr.instantiateList` at the reversed component list, from the
cut the field's earlier binders add).  What the RUN carries at the same
field is the MINTED domain — `mkCopy`'s `instPis` of the same stored
constructor type at the same components, read off the minted
telescope — and the model reads that one, so the two spellings have to
be identified before either reading can be compared.

They are one lemma apart and no more: `instantiateList` at the reversed
list IS the descending `instantiate1` fold (`instSpine_eq_instantiateList_at`,
`instSpine_eq_instSeq`), which is the idiom `NestedPinsRun.copyResid`'s
minted telescope is stated in (`Expr.instSeq Ds (nP - 1 + l) …`).  The
components themselves are read off the OWN-PIN TABLE entry: its head
carries the levels `ordTargetLvls` picks up, and its first `nP`
arguments are the components.  Nothing is normalised and nothing is
run — this is the third of the three gaps the tie is named in, at its
SYNTACTIC half. -/

/-- **`ordTargetDom` IS THE MINTED DOMAIN'S SPELLING** (task #315 WIDE
(3), lane LE): at an own-pin table entry that is a constant applied to
exactly `nP` components, the recomputation is the stored domain at the
entry's levels, stripped, and instantiated at the components by the
descending fold the run's minted telescope uses.

Stated with `stripDomPis`/`domPiDepth` still in it, so that it covers a
REFLEXIVE field's `Π`-tower as well as a finitary field's spine; the
finitary corollary below is the tower-free reading. -/
theorem ordTargetDom_eq_instSeq {lps : List Name} {nP l : Nat} {ownSelf : List Expr}
    {qK : Nat} {I : Name} {lvls : List Level} {Ds : List Expr} {dom : Expr}
    (hown : ownSelf.getD qK default = Expr.mkAppN (.const I lvls) Ds)
    (hlen : Ds.length = nP) :
    ordTargetDom lps nP ownSelf qK l dom
      = Expr.instSeq Ds (nP - 1 + (l + domPiDepth (ordTargetDomL lps ownSelf qK dom)))
          (stripDomPis (dom.instantiateLevelParams lps lvls)) := by
  have hlvls : ordTargetLvls ownSelf qK = lvls := by
    unfold ordTargetLvls
    rw [hown, Expr.getAppFn_mkAppN]
    rfl
  have hargs : ((ownSelf.getD qK default).getAppArgs.take nP) = Ds := by
    rw [hown, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
    rw [List.take_of_length_le (Nat.le_of_eq hlen)]
  unfold ordTargetDom
  rw [hargs]
  have hL : ordTargetDomL lps ownSelf qK dom = dom.instantiateLevelParams lps lvls := by
    unfold ordTargetDomL; rw [hlvls]
  rw [hL]
  cases hnP : nP with
  | zero =>
    obtain rfl : Ds = [] := List.length_eq_zero_iff.mp (by rw [hlen, hnP])
    rw [List.reverse_nil, Expr.instantiateList_nil]
    rfl
  | succ n =>
    rw [← Expr.instSpine_eq_instantiateList_at, Expr.instSpine_eq_instSeq, hlen, hnP,
      show l + domPiDepth (dom.instantiateLevelParams lps lvls) + (n + 1) - 1
        = n + 1 - 1 + (l + domPiDepth (dom.instantiateLevelParams lps lvls)) from by omega]

/-! ### The block's own-pin table entry, at the run's pin record

`ordTargetDom`'s components come from the table entry it is addressed
at, and at the BLOCK's side that table is `nestedPinTermsSelf` — the
recorded pin terms with the block's parameters abstracted and re-opened
at `containerParamOpeners`.  Since those openers are the parameter
FVARS themselves (at the placeholder annotation `sort 0`), the entry is
the recorded pin with its components' fvar ANNOTATIONS normalised and
nothing else moved: the head, the levels and the arity are the run's
own.  That is what makes `ordTargetDom_eq_instSeq_flat` applicable at
the block's side with the run's `st.pins` record as its only input. -/

/-- Bulk instantiation commutes with an application spine. -/
theorem instantiateList_mkAppN (vs : List Expr) (d : Nat) :
    ∀ (args : List Expr) (f : Expr),
      Expr.instantiateList (Expr.mkAppN f args) vs d
        = Expr.mkAppN (Expr.instantiateList f vs d)
            (args.map fun a => Expr.instantiateList a vs d)
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      instantiateList_mkAppN vs d as (.app f a), List.map_cons]
    simp only [Expr.instantiateList]
    rfl

/-- **THE BLOCK'S OWN-PIN TABLE ENTRY IS THE RECORDED PIN** (task #315
WIDE (3), lane LE): same head, same levels, same arity — the
components carried through the abstraction and the openers, which move
nothing but a component's free-variable annotations. -/
theorem nestedPinTermsSelf_shape {p : NestedParts} {st : ElimState} {q : Nat}
    {pn : NestedPin} {I : Name} {lvls : List Level} {Ds : List Expr}
    (hq : st.pins[q]? = some pn) (hpin : pn.pin = Expr.mkAppN (.const I lvls) Ds) :
    (nestedPinTermsSelf p st).getD q default
      = Expr.mkAppN (.const I lvls)
          (Ds.map fun a => Expr.instantiateList (Expr.abstractRange a 0 p.nP 0)
            (containerParamOpeners p.nP).reverse 0) := by
  unfold nestedPinTermsSelf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hq]
  simp only [Option.map_some, Option.getD_some]
  rw [hpin, abstractRange_mkAppN, abstractRange_const, instantiateList_mkAppN,
    show Expr.instantiateList (.const I lvls) (containerParamOpeners p.nP).reverse 0
      = .const I lvls from by simp only [Expr.instantiateList], List.map_map]
  rfl

/-! ### The tower is TABLE-INDEPENDENT (task #315 WIDE (f3) step 4,
object (1))

`ordTargetDomL` is the stored domain at whichever own-pin table it is
addressed at, and the only thing the table contributes is the LEVELS.
Level instantiation maps a `forallE` to a `forallE` and nothing else to
one, so the `Π`-tower's DEPTH — and, up to the same instantiation, its
body — is the STORED domain's and is the same number at every table.
That is what lets the OWNER's cut and the BLOCK's be one number
without flatness, which is the reflexive twin's first object. -/

/-- **Level instantiation commutes with the `Π`-strip**, the term-level
twin of `domPiDepth_instantiateLevelParams` (task #315 WIDE (f3) step
5): `instantiateLevelParams` maps a `forallE` to a `forallE` and
nothing else to one, so stripping before and after are the same term.

What spends it is the HEAD of `ordTargetDom` at a container-RECURSIVE
nested field, where the stored domain's own head is a constant
(`ContainerModeled.nestPinSpineAbs`) and the recomputation has to carry
that constant through the level substitution and the cut. -/
theorem stripDomPis_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, stripDomPis (e.instantiateLevelParams ks us)
      = (stripDomPis e).instantiateLevelParams ks us := by
  intro e
  induction e with
  | forallE ty body m _ ih => simp only [Expr.instantiateLevelParams, stripDomPis, ih]
  | _ => rfl

/-- Level instantiation does not move the `Π`-tower's depth. -/
theorem domPiDepth_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, domPiDepth (e.instantiateLevelParams ks us) = domPiDepth e := by
  intro e
  induction e with
  | forallE ty body m _ ih => simp only [Expr.instantiateLevelParams, domPiDepth, ih]
  | _ => rfl

/-- **THE TOWER'S DEPTH IS THE STORED DOMAIN'S, AT EVERY TABLE**: the
number `ordTargetDom` cuts at is `l + domPiDepth dom`, and no own-pin
table moves it. -/
theorem domPiDepth_ordTargetDomL (lps : List Name) (t : List Expr) (q : Nat) (dom : Expr) :
    domPiDepth (ordTargetDomL lps t q dom) = domPiDepth dom :=
  domPiDepth_instantiateLevelParams _ _ dom

/-- **THE RECOMPUTATION'S HEAD IS THE STRIPPED STORED DOMAIN'S** (task
#315 WIDE (f3) step 5): `ordTargetDom` is the stored domain at the
copy's levels, `Π`-stripped and then cut at the field's own depth, and
none of the three moves a constant head — the levels are substituted
INTO it, the strip is structural, and `instantiateList` never touches a
spine head (`getAppFn_instantiateList_const`).

**Where the constant comes from is the arm, not this lemma.**  At a
field the container calls ORDINARY it is `nestedOrdNormAt`'s own firing
(`getAppFn_const_of_ordRootFired`); at one it calls RECURSIVE-nested it
is free, because `ContainerModeled.nestPinSpineAbs` exhibits the cut
spine AS the recorded pin, whose head is `.const`. -/
theorem getAppFn_ordTargetDom_of_stripDomPis {lps : List Name} {nP qK l : Nat}
    {ownSelf : List Expr} {dom : Expr} {M : Name} {us : List Level}
    (h : (stripDomPis dom).getAppFn = .const M us) :
    (ordTargetDom lps nP ownSelf qK l dom).getAppFn
      = .const M (us.map (Level.subst lps (ordTargetLvls ownSelf qK))) := by
  refine getAppFn_instantiateList_const ?_
  show (stripDomPis (Expr.instantiateLevelParams lps (ordTargetLvls ownSelf qK) dom)).getAppFn = _
  rw [stripDomPis_instantiateLevelParams, Expr.getAppFn_instantiateLevelParams, h]
  rfl

/-- An erasure-equal partner of a constant IS that constant, read on
the LEFT (`ErasedEq`'s own match; the `Norm` file's twin reads it on
the right). -/
theorem erasedEq_const_left {K : Name} {us : List Level} {e : Expr}
    (h : Expr.ErasedEq (.const K us) e) : e = .const K us := by
  match e, h with
  | .const n vs, h => obtain ⟨rfl, rfl⟩ := h; rfl

/-- **AN ERASURE-EQUAL PARTNER HAS THE SAME CONSTANT HEAD** (task #315
WIDE (f3) step 3(b)): what a proof spends a constant head on survives
the annotation round trip the two openings differ by, so a head read
off ONE of the two spellings serves the other. -/
theorem erasedEq_getAppFn_const {e e' : Expr} {K : Name} {us : List Level}
    (h : Expr.ErasedEq e e') (hK : e.getAppFn = Expr.const K us) :
    e'.getAppFn = Expr.const K us := by
  have h1 := (ErasedEq.getApp h).1
  rw [hK] at h1
  exact erasedEq_const_left h1

/-- A tower of depth zero is its own body. -/
theorem stripDomPis_of_depth_zero {E : Expr} (h : domPiDepth E = 0) : stripDomPis E = E := by
  cases E with
  | forallE ty bo bm => exact nomatch (h : domPiDepth bo + 1 = 0)
  | _ => rfl

/-- **`ordTargetDom` IS THE MINTED DOMAIN'S SPELLING, AT THE FLAT
GUARD** (task #315 WIDE (f3) step 3(b)): at a stored domain with no
`Π`-tower the cut is the field's own `l` and the term is the stored
domain at the entry's levels — `NestedPinsRun.copyResid`'s minted
telescope entry, character for character.

**The guard is FLATNESS and not the domain's constant HEAD**, which is
what the finitary form used to ask: a product container's field domain
is a BARE PARAMETER (`Pair α β | mk (a : α) (b : β)`), whose `getAppFn`
is a `bvar`, so the head form is unstatable at `nested_bvar_field`,
`nested_pin_nocollide` and `nested_p04` — three official ACCEPTS —
while flatness holds at all three. -/
theorem ordTargetDom_eq_instSeq_flat {lps : List Name} {nP l : Nat} {ownSelf : List Expr}
    {qK : Nat} {I : Name} {lvls : List Level} {Ds : List Expr} {dom : Expr}
    (hown : ownSelf.getD qK default = Expr.mkAppN (.const I lvls) Ds)
    (hlen : Ds.length = nP)
    (hflat : domPiDepth dom = 0) :
    ordTargetDom lps nP ownSelf qK l dom
      = Expr.instSeq Ds (nP - 1 + l) (dom.instantiateLevelParams lps lvls) := by
  have hL : ordTargetDomL lps ownSelf qK dom = dom.instantiateLevelParams lps lvls := by
    unfold ordTargetDomL
    rw [show ordTargetLvls ownSelf qK = lvls from by
      unfold ordTargetLvls; rw [hown, Expr.getAppFn_mkAppN]; rfl]
  have hd : domPiDepth (dom.instantiateLevelParams lps lvls) = 0 := by
    rw [domPiDepth_instantiateLevelParams]; exact hflat
  rw [ordTargetDom_eq_instSeq hown hlen, hL, stripDomPis_of_depth_zero hd, hd, Nat.add_zero]

/-- **K.69'S BLOCK SIDE, IN THE RUN'S IDIOM** (task #315 WIDE (3), lane
LE; at the FLAT guard since WIDE (f3) step 3(b)):
`ordTargetDom_eq_instSeq_flat` addressed at the block's own table, with
the run's pin record as its only input — the recomputation is the
container's stored field domain at the pin's LEVELS, folded onto the
pin's COMPONENTS at the field's own cut, which is the spelling
`NestedPinsRun.copyResid`'s minted telescope carries.

The components arrive through `nestedPinTermsSelf`'s abstraction and
re-opening; that round trip normalises a component's free-variable
annotations and moves nothing else, which is why the equation can be
stated against the run's recorded `Ds` at all. -/
theorem ordTargetDom_pinTermsSelf_flat {p : NestedParts} {st : ElimState} {q : Nat}
    {pn : NestedPin} {I : Name} {lvls : List Level} {Ds : List Expr}
    {lps : List Name} {nP l : Nat} {dom : Expr}
    (hq : st.pins[q]? = some pn) (hpin : pn.pin = Expr.mkAppN (.const I lvls) Ds)
    (hlen : Ds.length = nP)
    (hflat : domPiDepth dom = 0) :
    ordTargetDom lps nP (nestedPinTermsSelf p st) q l dom
      = Expr.instSeq
          (Ds.map fun a => Expr.instantiateList (Expr.abstractRange a 0 p.nP 0)
            (containerParamOpeners p.nP).reverse 0)
          (nP - 1 + l) (dom.instantiateLevelParams lps lvls) :=
  ordTargetDom_eq_instSeq_flat (nestedPinTermsSelf_shape hq hpin)
    (by rw [List.length_map]; exact hlen) hflat

/-! ### The tower's cut, syntactically (task #315 WIDE (3), step 1)

`ordTargetDom` strips the stored domain's own `Π`-tower BEFORE it
instantiates, at the cut `l + domPiDepth` the tower pushes the
parameters out to; the RUN instantiates the whole tower at the field's
own `l` and opens it afterwards.  The two spellings are one
commutation apart, and the commutation is the only thing the reflexive
arm needs that the finitary one did not: substitution passes through a
`Π`-binder with its index bumped (`Expr.instSeq_forallE`), so the two
differ by exactly the tower the substitution PLANTS into the stripped
body, and `stripDomPis_instSeq_tower` MEASURES that tower rather than
excluding it with a head guard. -/

/-- `stripDomPis` and `domPiDepth` at a domain that is not a `Π`. -/
theorem stripDomPis_notPi {E : Expr} (hnf : ∀ ty bo bm, E ≠ Expr.forallE ty bo bm) :
    stripDomPis E = E ∧ domPiDepth E = 0 := by
  cases E with
  | forallE ty bo bm => exact absurd rfl (hnf ty bo bm)
  | _ => exact ⟨rfl, rfl⟩

/-- **THE `Π`-TOWER AND THE CUT, WITH NO GUARD AT ALL** (task #315
WIDE (f3) step 4): the mint instantiates a field's WHOLE stored domain
at the field's own cut; `ordTargetDom` strips the domain's tower first
and instantiates the BODY at the cut the tower pushes out to.  The two
end at the same stripped term, and the mint's tower is the stored
domain's plus whatever the substitution PLANTS into the stripped
body — which is K.72's equation, read on the mint.

**It needs no head hypothesis**, and that is its whole point: a guard
asking the stripped body to be constant-headed would exclude the
planted `Π` instead of measuring it, and `tests/e2e/nested_comp_tower.ndjson`
is a shape at which there IS one.  One induction over the `Π`-prefix,
`Expr.instSeq_forallE` at each step.  `stripDomPis_instSeq2_notPi`
(`Verify/Inductives/NestedCopyNorm.lean`) is the reading of it under a
guard that is not a head. -/
theorem stripDomPis_instSeq_tower :
    ∀ (E : Expr) (vs : List Expr) (t : Nat), vs.length ≤ t + 1 →
      domPiDepth (Expr.instSeq vs t E)
          = domPiDepth E
            + domPiDepth (Expr.instSeq vs (t + domPiDepth E) (stripDomPis E)) ∧
        stripDomPis (Expr.instSeq vs t E)
          = stripDomPis (Expr.instSeq vs (t + domPiDepth E) (stripDomPis E)) := by
  intro E
  induction E with
  | forallE ty bo bm _ ihbo =>
    intro vs t hlen
    obtain ⟨hd, hs⟩ := ihbo vs (t + 1) (by omega)
    rw [Expr.instSeq_forallE vs t ty bo bm hlen]
    have hcut : t + 1 + domPiDepth bo = t + (domPiDepth bo + 1) := by omega
    refine ⟨?_, ?_⟩
    · show domPiDepth (Expr.instSeq vs (t + 1) bo) + 1
        = domPiDepth bo + 1
          + domPiDepth (Expr.instSeq vs (t + (domPiDepth bo + 1)) (stripDomPis bo))
      rw [hd, ← hcut]
      omega
    · show stripDomPis (Expr.instSeq vs (t + 1) bo)
        = stripDomPis (Expr.instSeq vs (t + (domPiDepth bo + 1)) (stripDomPis bo))
      rw [hs, hcut]
  | _ =>
    intro vs t _
    exact ⟨(Nat.zero_add _).symm, rfl⟩

/-- `stripPis` at a domain's OWN tower depth always succeeds, and its
body is `stripDomPis`. -/
theorem stripPis_domPiDepth : ∀ (e : Expr),
    ∃ bs : List (Expr × BinderMeta),
      e.stripPis (domPiDepth e) = some (bs, stripDomPis e) ∧ bs.length = domPiDepth e := by
  intro e
  induction e with
  | forallE ty bo bm _ ihbo =>
    obtain ⟨bs, hs, hlen⟩ := ihbo
    refine ⟨(ty, bm) :: bs, ?_, ?_⟩
    · show (Expr.stripPis (domPiDepth bo) bo).map (fun q => ((ty, bm) :: q.1, q.2))
        = some ((ty, bm) :: bs, stripDomPis bo)
      rw [hs]; rfl
    · show bs.length + 1 = domPiDepth bo + 1
      rw [hlen]
  | _ => exact ⟨[], rfl, rfl⟩

/-- **A DOMAIN OPENS AT ITS OWN TOWER DEPTH**: the openers are fresh
variables and the leaf is `stripDomPis` at them. -/
theorem openPis_domPiDepth (e : Expr) (d : Nat) :
    ∃ fvs : List Expr,
      openPisAtFvars (domPiDepth e) e d
          = some (fvs, Expr.instSeq fvs (domPiDepth e - 1) (stripDomPis e)) ∧
        fvs.length = domPiDepth e ∧ AllFvarsL fvs := by
  obtain ⟨bs, hstrip, hlen⟩ := stripPis_domPiDepth e
  obtain ⟨fvs, hfl, hallF, hlaw⟩ := openPisAtFvars_mkPisB (domPiDepth e) bs hlen d
  refine ⟨fvs, ?_, hfl, hallF⟩
  have h := hlaw (stripDomPis e)
  rw [← stripPis_mkPisB _ hstrip] at h
  exact h

/-! ## `NoProjAt` through the owner's recomputation

`ordTargetDom` — the owner's own recomputation of a rewritten ordinary
field's target (K.67's spelling) — is built from the stored domain by
three list-shaped operations, and the block model's crossing guard
(`ProjFree`, `Model/Inductives/BlockRepCross.lean`) has to travel all
three.  None of them creates a node: `stripDomPis` drops binders,
`instantiateList` and `instSeq` replace `bvar`s by terms the caller
guards.  (`Expr.NoProjAt.instantiate1` and `.instantiateLevelParams`
are `Verify/ProjSlots.lean`'s; these are the three the recomputation
adds.) -/

/-- Bulk instantiation adds no `.proj T i` node when no replacement
carries one: `Expr.instantiateList_cons` peels the list and
`Expr.NoProjAt.instantiate1` does each step. -/
theorem rg_noProjAt_instantiateList {T : Name} {i : Nat} :
    ∀ (vs : List Expr), (∀ v ∈ vs, Expr.NoProjAt T i v) →
      ∀ (e : Expr) (d : Nat), Expr.NoProjAt T i e →
        Expr.NoProjAt T i (e.instantiateList vs d) := by
  intro vs
  induction vs with
  | nil => intro _ e d h; rw [Expr.instantiateList_nil]; exact h
  | cons v vs ih =>
    intro hvs e d h
    rw [Expr.instantiateList_cons]
    exact Expr.NoProjAt.instantiate1 (hvs v (List.mem_cons_self ..)) _ d
      (ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) e (d + 1) h)

/-- A descending instantiation sequence adds no `.proj T i` node when no
argument carries one. -/
theorem rg_noProjAt_instSeq {T : Name} {i : Nat} :
    ∀ (as : List Expr), (∀ a ∈ as, Expr.NoProjAt T i a) →
      ∀ (t : Nat) (e : Expr), Expr.NoProjAt T i e →
        Expr.NoProjAt T i (Expr.instSeq as t e) := by
  intro as
  induction as with
  | nil => intro _ t e h; rw [Expr.instSeq]; exact h
  | cons a as ih =>
    intro has t e h
    rw [Expr.instSeq]
    exact ih (fun x hx => has x (List.mem_cons_of_mem _ hx)) (t - 1) _
      (Expr.NoProjAt.instantiate1 (has a (List.mem_cons_self ..)) e t h)

/-- Stripping a domain's own binders keeps the absence: the result is a
subterm. -/
theorem rg_noProjAt_stripDomPis {T : Name} {i : Nat} :
    ∀ (e : Expr), Expr.NoProjAt T i e → Expr.NoProjAt T i (stripDomPis e) := by
  intro e
  induction e with
  | forallE ty b m _ ihb =>
    intro h
    rw [stripDomPis]
    exact ihb (Expr.noProjAt_forallE.mp h).2
  | _ => intro h; exact h

/-- Abstraction over a range of fvars adds no `.proj T i` node: an
abstracted `fvar` becomes a `bvar` and every other node is rebuilt. -/
theorem rg_noProjAt_abstractRange {T : Name} {i : Nat} :
    ∀ (e : Expr) (d k c : Nat), Expr.NoProjAt T i e →
      Expr.NoProjAt T i (Expr.abstractRange e d k c) := by
  intro e
  induction e with
  | bvar _ => intro d k c _; simp [Expr.abstractRange]
  | sort _ => intro d k c _; simp [Expr.abstractRange]
  | lit _ => intro d k c _; simp [Expr.abstractRange]
  | const _ _ => intro d k c _; simp [Expr.abstractRange]
  | fvar idx ty _ =>
    intro d k c h
    rw [Expr.abstractRange]
    split
    · simp
    · exact h
  | app f a ihf iha =>
    intro d k c h
    rw [Expr.abstractRange, Expr.noProjAt_app]
    exact ⟨ihf d k c (Expr.noProjAt_app.mp h).1, iha d k c (Expr.noProjAt_app.mp h).2⟩
  | lam ty b m ihty ihb =>
    intro d k c h
    rw [Expr.abstractRange, Expr.noProjAt_lam]
    exact ⟨ihty d k c (Expr.noProjAt_lam.mp h).1, ihb d k (c + 1) (Expr.noProjAt_lam.mp h).2⟩
  | forallE ty b m ihty ihb =>
    intro d k c h
    rw [Expr.abstractRange, Expr.noProjAt_forallE]
    exact ⟨ihty d k c (Expr.noProjAt_forallE.mp h).1,
      ihb d k (c + 1) (Expr.noProjAt_forallE.mp h).2⟩
  | letE ty v b ihty ihv ihb =>
    intro d k c h
    rw [Expr.abstractRange, Expr.noProjAt_letE]
    exact ⟨ihty d k c (Expr.noProjAt_letE.mp h).1, ihv d k c (Expr.noProjAt_letE.mp h).2.1,
      ihb d k (c + 1) (Expr.noProjAt_letE.mp h).2.2⟩
  | proj s n e ihe =>
    intro d k c h
    rw [Expr.abstractRange, Expr.noProjAt_proj]
    exact ⟨(Expr.noProjAt_proj.mp h).1, ihe d k c (Expr.noProjAt_proj.mp h).2⟩

/-- An application spine adds no `.proj T i` node when neither its head
nor its arguments carry one. -/
theorem rg_noProjAt_mkAppN {T : Name} {i : Nat} :
    ∀ (as : List Expr) (f : Expr), Expr.NoProjAt T i f →
      (∀ a ∈ as, Expr.NoProjAt T i a) → Expr.NoProjAt T i (Expr.mkAppN f as) := by
  intro as
  induction as with
  | nil => intro f hf _; exact hf
  | cons a as ih =>
    intro f hf has
    rw [Expr.mkAppN]
    exact ih _ (Expr.noProjAt_app.mpr ⟨hf, has a (List.mem_cons_self ..)⟩)
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

end ConLeche
