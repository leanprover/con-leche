module

public import ConLeche.Semantics.Tower.SigChainI
public import ConLeche.Semantics.Tower.TowerWire

@[expose] public section

/-!
# The chosen tuple's closedness (task #315, U-8)

`SigChainI.lean`'s Σ'-chain kit, on the syntactic side: the block's
recursor leaf `blockRecAVI s k T eqs mm` — the `mm`-th projection of
the chosen element of the chain of the `k` lifted component types
followed by the equations' conjunction — is bounded at whatever bound
the components are, provided the equations are bounded `k` deeper
(they sit under the `k` tuple binders).

The walk is the `TowerWire.lean` one: `projChainAV` and `selChainAV`
are transparent (`fst`/`snd`, a `const` head and `prf`), `andChainAV`
and `sigChainAV` each add ONE binder per entry, and the chain's `i`-th
type `(T i).liftN i 0` is bounded at `K + i` by `bvarsBelow_liftN` —
which is exactly `FieldsBelow K (blockTsAV k T)`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The conjunction -/

omit [SetTheory V] in
/-- A conjunct chain of bounded propositions is bounded: `andAV`'s
binder is over the head, and the tail is lifted past it. -/
theorem andChainAV_below :
    ∀ {es : List AnnotTerm} {K : Nat}, (∀ e ∈ es, Term.bvarsBelow K e.erase) →
      Term.bvarsBelow K (andChainAV es).erase
  | [], _, _ => trivial
  | e :: es, K, h => by
    show Term.bvarsBelow K (andAV e (andChainAV es)).erase
    unfold andAV
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN trivial ?_
    intro a ha
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h e (.head _)
    · refine ⟨h e (.head _), ?_⟩
      rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 _ K 0
        (andChainAV_below (es := es) fun e' he' => h e' (.tail _ he'))

/-! ## The chain -/

omit [SetTheory V] in
/-- The `i`-th projection adds no variable. -/
theorem projChainAV_below :
    ∀ {i : Nat} {e : AnnotTerm} {K : Nat}, Term.bvarsBelow K e.erase →
      Term.bvarsBelow K (projChainAV i e).erase
  | 0, _, _, h => h
  | i + 1, e, _K, h => projChainAV_below (i := i) (e := .snd e) h

omit [SetTheory V] in
/-- **The Σ'-chain is bounded**: each component at its own depth (the
earlier components' binders), the proposition at the full depth. -/
theorem sigChainAV_below {s : Nat} :
    ∀ {Ts : List AnnotTerm} {Q : AnnotTerm} {K : Nat}, FieldsBelow K Ts →
      Term.bvarsBelow (K + Ts.length) Q.erase →
      Term.bvarsBelow K (sigChainAV s Ts Q).erase
  | [], _, _, _, hQ => by simpa [sigChainAV] using hQ
  | T :: Ts, Q, K, h, hQ => by
    show Term.bvarsBelow K (sigAV s T (sigChainAV s Ts Q)).erase
    unfold sigAV
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN trivial ?_
    intro a ha
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h.1
    · refine ⟨h.1, sigChainAV_below (Ts := Ts) h.2 ?_⟩
      rwa [show K + 1 + Ts.length = K + (T :: Ts).length from by simp; omega]

omit [SetTheory V] in
/-- The chosen element is bounded where the chain is. -/
theorem selChainAV_below {s K : Nat} {Ts : List AnnotTerm} {Q : AnnotTerm}
    (h : Term.bvarsBelow K (sigChainAV s Ts Q).erase) :
    Term.bvarsBelow K (selChainAV s Ts Q).erase := by
  unfold selChainAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN trivial ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h
  · trivial

/-! ## The block's lifted component types -/

omit [SetTheory V] in
theorem fieldsBelow_blockTs_go {k K : Nat} {T : Nat → AnnotTerm}
    (hT : ∀ mm, mm < k → Term.bvarsBelow K (T mm).erase) :
    ∀ (n p : Nat), p + n = k →
      FieldsBelow (K + p) (((List.range k).drop p).map fun mm => (T mm).liftN mm 0)
  | 0, p, hp => by
    rw [blockTs_drop_nil T (p := p) (by omega)]
    trivial
  | n + 1, p, hp => by
    rw [blockTs_drop_cons T (p := p) (by omega)]
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN p _ K 0 (hT p (by omega))
    · exact fieldsBelow_blockTs_go hT n (p + 1) (by omega)

omit [SetTheory V] in
/-- The `k` lifted component types, each bounded at its own depth. -/
theorem fieldsBelow_blockTs {k K : Nat} {T : Nat → AnnotTerm}
    (hT : ∀ mm, mm < k → Term.bvarsBelow K (T mm).erase) :
    FieldsBelow K (blockTsAV k T) := by
  have := fieldsBelow_blockTs_go hT k 0 (by omega)
  simpa [blockTsAV] using this

/-! ## The leaf -/

omit [SetTheory V] in
/-- **The block's recursor leaf is bounded** wherever the `k` recursor
types are, the equations being bounded under the `k` tuple binders. -/
theorem blockRecAVI_below {s k K : Nat} {T : Nat → AnnotTerm} {eqs : List AnnotTerm}
    (hT : ∀ mm, mm < k → Term.bvarsBelow K (T mm).erase)
    (heqs : ∀ e ∈ eqs, Term.bvarsBelow (K + k) e.erase) (mm : Nat) :
    Term.bvarsBelow K (blockRecAVI s k T eqs mm).erase := by
  refine projChainAV_below (i := mm) (selChainAV_below ?_)
  refine sigChainAV_below (fieldsBelow_blockTs hT) ?_
  rw [blockTsAV_length]
  exact andChainAV_below heqs

end ConLeche.Semantics
