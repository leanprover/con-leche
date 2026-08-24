import Setlec.Kernel.IExpr

/-!
# Snapshot promotion (task #64, annotate-snapshot measurement variant)

Copy a discarded snapshot's *stored output* into the retained store:
the sub-DAG of a tier-two index is re-interned bottom-up, index-memoized
(`O(|sub-DAG|)`, never tree-shaped).  Tier-one expression indices are
kept as-is (tier one is frozen while the snapshot lives, so they are
valid in the retained store); level and name indices below the
snapshot-creation sizes are likewise kept, and only the snapshot's own
extensions are re-interned.

RC discipline: the promotion reads only the `Harvest` — the snapshot's
tier-two node table and its level/name tables.  If the snapshot never
interned a level (resp. name), its level (name) table is physically the
retained store's own and promotion never touches indices at or above
the base, so the retained tables are never pushed while aliased; if it
did intern, the snapshot's table is its own copy (the fork's first
write detached it) and the retained tables are unshared.  Either way
every retained-store push mutates a uniquely-referenced table.
-/

namespace Setlec

/-- The pieces of a discarded snapshot store that promotion reads. -/
structure Harvest where
  tnodes : Array ENode
  lnodes : Array LNode
  nnodes : Array NNode

/-- Extract the promotion inputs from a (snapshot) store. -/
def EStore.harvest (st : EStore) : Harvest :=
  ⟨st.tnodes, st.lnodes, st.nnodes⟩

/-- Promote one snapshot level index (`lbase` = the retained store's
level-table size at snapshot creation; indices below it are shared). -/
def promoteLGo (h : Harvest) (lbase : Nat) (st : EStore)
    (memo : Std.HashMap LIdx LIdx) (u : LIdx) :
    LIdx × EStore × Std.HashMap LIdx LIdx :=
  if u < lbase then (u, st, memo) else
  match memo[u]? with
  | some r => (r, st, memo)
  | none =>
    match h.lnodes[u]? with
    | none => (u, st, memo)
    | some n =>
      let (n', st, memo) : LNode × EStore × Std.HashMap LIdx LIdx :=
        match n with
        | .zero => (.zero, st, memo)
        | .succ v =>
          if _h : v < u then
            let (v', st, memo) := promoteLGo h lbase st memo v
            (.succ v', st, memo)
          else (n, st, memo)
        | .max v w =>
          if _h : v < u ∧ w < u then
            let (v', st, memo) := promoteLGo h lbase st memo v
            let (w', st, memo) := promoteLGo h lbase st memo w
            (.max v' w', st, memo)
          else (n, st, memo)
        | .imax v w =>
          if _h : v < u ∧ w < u then
            let (v', st, memo) := promoteLGo h lbase st memo v
            let (w', st, memo) := promoteLGo h lbase st memo w
            (.imax v' w', st, memo)
          else (n, st, memo)
        | .param nm => (.param nm, st, memo)
      let (r, st) := st.internL n'
      (r, st, memo.insert u r)
termination_by u
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Promote one snapshot name index (`nbase` as `lbase`). -/
def promoteNGo (h : Harvest) (nbase : Nat) (st : EStore)
    (memo : Std.HashMap NIdx NIdx) (i : NIdx) :
    NIdx × EStore × Std.HashMap NIdx NIdx :=
  if i < nbase then (i, st, memo) else
  match memo[i]? with
  | some r => (r, st, memo)
  | none =>
    match h.nnodes[i]? with
    | none => (i, st, memo)
    | some n =>
      let (n', st, memo) : NNode × EStore × Std.HashMap NIdx NIdx :=
        match n with
        | .anonymous => (.anonymous, st, memo)
        | .str pre s =>
          if _h : pre < i then
            let (pre', st, memo) := promoteNGo h nbase st memo pre
            (.str pre' s, st, memo)
          else (n, st, memo)
        | .num pre k =>
          if _h : pre < i then
            let (pre', st, memo) := promoteNGo h nbase st memo pre
            (.num pre' k, st, memo)
          else (n, st, memo)
      let (r, st) := st.internN n'
      (r, st, memo.insert i r)
termination_by i
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Promotion state threaded through the expression walk. -/
structure PromoteSt where
  st : EStore
  memoE : Std.HashMap Nat EIdx := {}
  memoL : Std.HashMap LIdx LIdx := {}
  memoN : Std.HashMap NIdx NIdx := {}

@[inline] def PromoteSt.level (p : PromoteSt) (h : Harvest) (lbase : Nat)
    (u : LIdx) : LIdx × PromoteSt :=
  match p with
  | ⟨st, mE, mL, mN⟩ =>
    let (u', st, mL) := promoteLGo h lbase st mL u
    (u', ⟨st, mE, mL, mN⟩)

@[inline] def PromoteSt.levels (p : PromoteSt) (h : Harvest) (lbase : Nat)
    (us : List LIdx) : List LIdx × PromoteSt :=
  us.foldr (fun u (acc, p) =>
    let (u', p) := p.level h lbase u
    (u' :: acc, p)) ([], p)

@[inline] def PromoteSt.name (p : PromoteSt) (h : Harvest) (nbase : Nat)
    (i : NIdx) : NIdx × PromoteSt :=
  match p with
  | ⟨st, mE, mL, mN⟩ =>
    let (i', st, mN) := promoteNGo h nbase st mN i
    (i', ⟨st, mE, mL, mN⟩)

@[inline] def PromoteSt.bm (p : PromoteSt) (h : Harvest) (lbase : Nat)
    (m : IBinderMeta) : IBinderMeta × PromoteSt :=
  match m.cod with
  | none => (m, p)
  | some u =>
    let (u', p) := p.level h lbase u
    (⟨m.bi, some u'⟩, p)

/-- Promote one snapshot tier-two node, by offset `j` (children in
tier one are kept — tier one was frozen under the snapshot, so they
denote the same nodes in the retained store). -/
def promoteEGo (h : Harvest) (lbase nbase : Nat) (p : PromoteSt)
    (j : Nat) : EIdx × PromoteSt :=
  match p.memoE[j]? with
  | some r => (r, p)
  | none =>
    match h.tnodes[j]? with
    | none => (tierTag + j, p)
    | some n =>
      let sub (p : PromoteSt) (c : EIdx) : EIdx × PromoteSt :=
        if c < tierTag then (c, p)
        else if _h : c - tierTag < j then promoteEGo h lbase nbase p (c - tierTag)
        else (c, p)
      let (n', p) : ENode × PromoteSt :=
        match n with
        | .bvar i => (.bvar i, p)
        | .fvar idx nm t =>
          let (t', p) := sub p t
          let (nm', p) := p.name h nbase nm
          (.fvar idx nm' t', p)
        | .sort u =>
          let (u', p) := p.level h lbase u
          (.sort u', p)
        | .const nm us =>
          let (us', p) := p.levels h lbase us
          let (nm', p) := p.name h nbase nm
          (.const nm' us', p)
        | .app f a =>
          let (f', p) := sub p f
          let (a', p) := sub p a
          (.app f' a', p)
        | .lam nm t b m =>
          let (t', p) := sub p t
          let (b', p) := sub p b
          let (m', p) := p.bm h lbase m
          let (nm', p) := p.name h nbase nm
          (.lam nm' t' b' m', p)
        | .forallE nm t b m =>
          let (t', p) := sub p t
          let (b', p) := sub p b
          let (m', p) := p.bm h lbase m
          let (nm', p) := p.name h nbase nm
          (.forallE nm' t' b' m', p)
        | .letE nm t v b =>
          let (t', p) := sub p t
          let (v', p) := sub p v
          let (b', p) := sub p b
          let (nm', p) := p.name h nbase nm
          (.letE nm' t' v' b', p)
        | .lit l => (.lit l, p)
        | .proj s i e =>
          let (e', p) := sub p e
          let (s', p) := p.name h nbase s
          (.proj s' i e', p)
      match p with
      | ⟨st, mE, mL, mN⟩ =>
        let (r, st) := st.intern n'
        (r, ⟨st, mE.insert j r, mL, mN⟩)
termination_by j
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

/-- Promote a snapshot index into the retained store: tier-one indices
are kept, a tier-two index has its sub-DAG re-interned. -/
def EStore.promoteE (st : EStore) (h : Harvest) (lbase nbase : Nat)
    (e : EIdx) : EIdx × EStore :=
  if e < tierTag then (e, st)
  else
    let (r, p) := promoteEGo h lbase nbase ⟨st, {}, {}, {}⟩ (e - tierTag)
    (r, p.st)

end Setlec
