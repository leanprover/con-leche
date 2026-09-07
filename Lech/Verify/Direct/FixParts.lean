import Lech.Verify.Direct.SumInv
import Lech.Kernel.Direct.RecParts

/-!
# The direct recursive recogniser, inverted (task #188)

`directFixShape?` is the sum route's core recogniser without the
one-constructor exclusion; `directFixParts?` adds the field kinds
(`directFixKinds?`, one list per constructor).  The inversions give
the pins the P tier consumes: the `isProp` datum, the recursor's
name and level parameters, the constructors' level parameters and
residual shapes, the rules' count, and the kinds' count.
-/

namespace Lech

variable {mode : CheckMode}

/-- `directFixShape?` pins the sum route's data (no one-constructor
exclusion). -/
theorem directFixShape?_inv {block : List ConstantInfo} {p : DirectSumParts}
    (h : directFixShape? block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) ∧
    p.rhss.length = p.ctors.length ∧
    (∀ c ∈ p.ctors, ∃ cbs es, c.1.type.stripPis (p.nP + c.2)
      = some (cbs, Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (directPsAt c.2 p.nP ++ es)) ∧ es.length = p.nIdx) := by
  unfold directFixShape? at h
  split at h
  · next cvT caps rest =>
    split at h
    · next cs cvR mI rP rules hsplit =>
      try dsimp only at h
      split at h
      · exact nomatch h
      · next hbnd =>
        try dsimp only at h
        split at h
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
          cases hstripP : Expr.stripPis (rP - (cs.length + 1) + (mI - rP)) cvT.type with
          | none => rw [hstripP] at h; exact nomatch h
          | some q =>
            obtain ⟨fstP, body⟩ := q
            rw [hstripP] at h
            cases body
            case sort s =>
              try dsimp only at h
              have hrules : rules.length = cs.length := hc.1.2
              have hcs : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)),
                  c.1.levelParams = cvT.levelParams ∧
                  reservedBasisNames.contains c.1.name = false := by
                intro c hc'
                obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
                have := hc.1.1.2 c' hc''
                try simp only [Bool.and_eq_true, beq_iff_eq] at this
                exact ⟨this.1.1.2, this.1.2⟩
              have hres : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)),
                  ∃ cbs es, c.1.type.stripPis (rP - (cs.length + 1) + c.2)
                    = some (cbs, Expr.mkAppN (.const cvT.name (cvT.levelParams.map .param))
                      (directPsAt c.2 (rP - (cs.length + 1)) ++ es)) ∧
                    es.length = mI - rP := by
                intro c hc'
                obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
                have hcc := hc.1.1.2 c' hc''
                try simp only [Bool.and_eq_true, beq_iff_eq] at hcc
                have hm := hcc.2
                split at hm
                · next cbs cbody hstrip =>
                  simp only [directCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hm
                  obtain ⟨es, hes, hesl⟩ := residual_shape hm.1.1 hm.2 hm.1.2
                  exact ⟨cbs, es, by rw [hstrip, hes], hesl⟩
                · exact absurd hm Bool.false_ne_true
              split at h
              · next lq elim' hlarge =>
                obtain rfl := Option.some.inj h
                have hlps : ∀ q ∈ cvT.levelParams, q ∈ cvR.levelParams := by
                  split at hlarge
                  · next e relps hlp =>
                    split at hlarge
                    · next hcond =>
                      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                      intro q hq
                      rw [hlp]
                      exact List.mem_cons_of_mem _ (by rw [hcond.1]; exact hq)
                    · exact nomatch hlarge
                  · exact nomatch hlarge
                refine ⟨rfl, hc.1.1.1.1.1, hcs, hc.1.1.1.1.2, hc.1.1.1.2, ?_, hlps, ?_, hres⟩
                · intro _
                  show elim' ∈ cvR.levelParams
                  split at hlarge
                  · next e relps hlp =>
                    split at hlarge
                    · obtain rfl := Option.some.inj hlarge
                      rw [hlp]
                      exact List.mem_cons_self
                    · exact nomatch hlarge
                  · exact nomatch hlarge
                · simp [hrules]
              · next lq hlarge =>
                split at h
                · next hcond =>
                  obtain rfl := Option.some.inj h
                  refine ⟨rfl, hc.1.1.1.1.1, hcs, hc.1.1.1.1.2, hc.1.1.1.2, ?_, ?_, ?_, hres⟩
                  · intro hl
                    exact absurd hl Bool.false_ne_true
                  · intro q hq
                    simp only [beq_iff_eq] at hcond
                    show q ∈ cvR.levelParams
                    rw [hcond]; exact hq
                  · simp [hrules]
                · exact nomatch h
            all_goals first | exact nomatch h | simp at h
        · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- A successful `mapM` in `Option` yields as many results. -/
theorem List.mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [List.mapM_option_length hbs]

/-- `directFixParts?` pins the shape and the kinds; a reflexive field
is taken only at a `Prop`-valued block (task #202, Stage A) unless the
block is negative. -/
theorem directFixParts?_inv {block : List ConstantInfo} {p : DirectFixParts}
    (h : directFixParts? block = some p) :
    directFixShape? block = some p.toDirectSumParts ∧
    directFixKinds? p.toDirectSumParts = some p.kinds ∧
    p.kinds.length = p.ctors.length ∧
    (p.kinds.any (fun ks => ks.any (· == .negative)) = true ∨
      (p.kinds.any (fun ks => ks.any (· == .reflexive)) = true → p.isProp = true)) := by
  unfold directFixParts? at h
  split at h
  · next p' hshape =>
    split at h
    · next kinds hkinds =>
      have hlen : kinds.length = p'.ctors.length := by
        unfold directFixKinds? at hkinds
        exact List.mapM_option_length hkinds
      split at h
      · next hneg =>
        obtain rfl := Option.some.inj h
        exact ⟨hshape, hkinds, hlen, Or.inl hneg⟩
      · split at h
        · exact nomatch h
        · split at h
          · exact nomatch h
          · next hguard =>
            split at h
            · split at h
              · obtain rfl := Option.some.inj h
                refine ⟨hshape, hkinds, hlen, Or.inr fun hr => ?_⟩
                have hr' : kinds.any (fun ks => ks.any (· == .reflexive)) = true := hr
                show p'.isProp = true
                revert hguard
                cases p'.isProp <;> simp [hr']
              · exact nomatch h
            · exact nomatch h
    · exact nomatch h
  · exact nomatch h

end Lech
