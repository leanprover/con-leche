module

public import ConLeche.Kernel.Inductives.GenRec
public import ConLeche.Verify.Inductives.NestCallSyn
public import ConLeche.Verify.Inductives.ClassMatchRun
public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.ExceptBind

public section

/-!
# K.53′ moved from the datum's frame to the rule's (lane GENREC-B2)

The generated stage runs node agreement (`classNodesAgree`, `targetK53`)
with the datum's fields opened at the DATUM's variables (`fvar (nP + k + l)`,
`openPisAtFvars nF e0.ty (nP + k)`), while the generated rule reads the
same walked telescope at the RULE's field variables (`fvar (rP + l)`,
the declared fields `openPisAtFvars nF tyD rP`).  Both telescopes name no
other variable at or above the datum's base (the walk's normal forms are
read back over the canonical parameters), so the rule's reading is the
datum's with the fields renamed (`Expr.substFvars a bR s`, `s` the
identity below `a`), up to the variables' annotations, and K.53′'s
comparison — an erasure equation plus a class match on the leaf's
parameters, which name only the parameters — moves along
(`k53_rename`).
-/

namespace ConLeche

/-! ## Telescopes, substituted and erased -/

/-- Opening a telescope at variables gives the variables' types as its
domains. -/
theorem openPisAtFvars_targetPiDomsWith :
    ∀ {n : Nat} {T : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n T d = some (fvs, o) →
      targetPiDomsWith fvs T = some (fvs.map Expr.fvarTypeD) := by
  intro n
  induction n with
  | zero =>
    intro T d fvs o h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro T d fvs o h
    match T, h with
    | .forallE dom body bm, h =>
      simp only [openPisAtFvars] at h
      split at h
      · rename_i fvs' e' hop
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [targetPiDomsWith, ih hop, Expr.fvarTypeD]
      · exact nomatch h

/-- **`targetPiDomsWith` commutes with a parallel substitution.** -/
theorem targetPiDomsWith_substFvars {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → (s v).looseBVarsBounded 0 = true) :
    ∀ {fvs : List Expr} {T : Expr} {ws : List Expr}, targetPiDomsWith fvs T = some ws →
      targetPiDomsWith (fvs.map (Expr.substFvars b D s)) (Expr.substFvars b D s T)
        = some (ws.map (Expr.substFvars b D s)) := by
  intro fvs
  induction fvs with
  | nil =>
    intro T ws h
    simp only [targetPiDomsWith, Option.some.injEq] at h
    subst h; rfl
  | cons x xs ih =>
    intro T ws h
    cases T with
    | forallE d body bm =>
      simp only [targetPiDomsWith] at h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      have := ih hr
      rw [Expr.substFvars_instantiate1 hs x body 0] at this
      simp [Expr.substFvars, targetPiDomsWith, this]
    | _ => simp [targetPiDomsWith] at h

/-- **`targetPiDomsWith` respects erasure.** -/
theorem targetPiDomsWith_erasedEq :
    ∀ {fvs fvs' : List Expr} {T T' : Expr} {ws : List Expr}, ErasedEqs fvs fvs' →
      Expr.ErasedEq T T' → targetPiDomsWith fvs T = some ws →
      ∃ ws', targetPiDomsWith fvs' T' = some ws' ∧ ErasedEqs ws ws' := by
  intro fvs
  induction fvs with
  | nil =>
    intro fvs' T T' ws hf _ h
    cases fvs' with
    | nil =>
      simp only [targetPiDomsWith, Option.some.injEq] at h
      subst h; exact ⟨[], rfl, trivial⟩
    | cons _ _ => simp [ErasedEqs] at hf
  | cons x xs ih =>
    intro fvs' T T' ws hf hT h
    cases fvs' with
    | nil => simp [ErasedEqs] at hf
    | cons x' xs' =>
      obtain ⟨hx, hxs⟩ := hf
      cases T with
      | forallE d b m =>
        cases T' with
        | forallE d' b' m' =>
          obtain ⟨-, hd, hb⟩ := hT
          simp only [targetPiDomsWith] at h
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r', hr', hrr⟩ := ih hxs (Expr.ErasedEq.instantiate1 hb hx) hr
          exact ⟨d' :: r', by simp [targetPiDomsWith, hr'], hd, hrr⟩
        | _ => simp [Expr.ErasedEq] at hT
      | _ => simp [targetPiDomsWith] at h

/-- `stripPis` commutes with a parallel substitution that sends the
variables below its bound to variables. -/
theorem stripPis_substFvars {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → ∃ ty, s v = .fvar v ty) :
    ∀ (n : Nat) (e : Expr), (Expr.substFvars b D s e).stripPis n
      = (e.stripPis n).map fun q =>
          (q.1.map fun p => (Expr.substFvars b D s p.1, p.2), Expr.substFvars b D s q.2) := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    cases e with
    | forallE ty body m =>
      simp only [Expr.substFvars, Expr.stripPis, ih body, Option.map_map]
      rfl
    | fvar i ty =>
      by_cases hi : i < b
      · obtain ⟨ty', hty⟩ := hs i hi
        rw [Expr.substFvars_fvar_lt hi, hty]; rfl
      · rw [Expr.substFvars_fvar_ge (by omega)]; rfl
    | _ => rfl

/-- **`stripPis` respects erasure.** -/
theorem stripPis_erasedEq :
    ∀ {n : Nat} {A B : Expr} {tA : List (Expr × BinderMeta)} {lA : Expr},
      Expr.ErasedEq A B → A.stripPis n = some (tA, lA) →
      ∃ tB lB, B.stripPis n = some (tB, lB) ∧ tA.length = tB.length ∧
        (∀ (l : Nat) (q q' : Expr × BinderMeta), tA[l]? = some q → tB[l]? = some q' →
          q.2 = q'.2 ∧ Expr.ErasedEq q.1 q'.1) ∧ Expr.ErasedEq lA lB := by
  intro n
  induction n with
  | zero =>
    intro A B tA lA h hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨[], B, rfl, rfl, fun l q q' hq _ => by simp at hq, h⟩
  | succ n ih =>
    intro A B tA lA h hs
    cases A with
    | forallE ty body m =>
      cases B with
      | forallE ty' body' m' =>
        obtain ⟨hm, hty, hb⟩ := h
        simp only [Expr.stripPis] at hs
        obtain ⟨⟨t1, l1⟩, h1, h2⟩ := Option.map_eq_some_iff.mp hs
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨tB, lB, hB, hlen, hall, hl⟩ := ih hb h1
        refine ⟨(ty', m') :: tB, lB, by simp [Expr.stripPis, hB], by simp [hlen], ?_, hl⟩
        intro l q q' hq hq'
        cases l with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq hq'
          subst hq; subst hq'
          exact ⟨hm, hty⟩
        | succ l => exact hall l q q' (by simpa using hq) (by simpa using hq')
      | _ => simp [Expr.ErasedEq] at h
    | _ => simp [Expr.stripPis] at hs

/-- **A substitution that is the identity below its bound** changes a term
whose variables are all below the bound only in its annotations. -/
theorem substFvars_erasedEq_self {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → ∃ ty, s v = .fvar v ty) :
    ∀ (e : Expr), e.fvarsBelow b → Expr.ErasedEq (Expr.substFvars b D s e) e := by
  intro e
  induction e with
  | bvar i => intro _; exact Expr.ErasedEq.rfl _
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    obtain ⟨ty', hty⟩ := hs i h
    rw [Expr.substFvars_fvar_lt h, hty]
    simp [Expr.ErasedEq]
  | sort u => intro _; exact Expr.ErasedEq.rfl _
  | const n us => intro _; exact Expr.ErasedEq.rfl _
  | lit l => intro _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam t body m iht ihb => intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | forallE t body m iht ihb => intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb => intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj n i e ih => intro h; exact ⟨rfl, rfl, ih h⟩

/-! ## K.53′ at the rule's fields -/

/-- **K.53′, moved from the datum's variables to the rule's** (see the
module docstring): node agreement ran at the datum's opening `fvs0`
(base `a`) of the datum's telescope `T0`, against an entry's telescope
`T` (field `i`, `tele` binders, the datum's leaf headed by the ih's
class `Mt`, `classLeafAt`).  At the rule's field variables `fvsR` (base
`bR`) the datum's field `ws[i]` strips to a telescope `teleR` and a leaf
headed by `Mt.ind`, and the entry's field is, up to annotations, that
telescope over the container at the entry leaf's levels `us'` and
parameters `Pw` (matching `Mt`) and the datum leaf's index arguments. -/
theorem k53_rename {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys : List Expr} {Mt : TargetMajor}
    {n a bR : Nat} {fvs0 fvsR : List Expr} {T T0 o0 : Expr} {i tele : Nat}
    (hop0 : openPisAtFvars n T0 a = some (fvs0, o0))
    (hR : ∀ l, l < n → ∃ ty, fvsR[l]? = some (.fvar (bR + l) ty)) (hlR : fvsR.length = n)
    (hT : T.fvarsBelow a) (hT0 : T0.fvarsBelow a)
    {teleB : List (Expr × BinderMeta)} {leaf : Expr}
    (hst : (fvs0.getD i default).fvarTypeD.stripPis tele = some (teleB, leaf))
    (hleaf : classLeafAt Mt leaf = true)
    {f0 : Expr} (hf0 : ((targetPiDomsWith fvs0 T).getD [])[i]? = some f0)
    (hK : targetK53 ops env p formerTys Mt teleB leaf f0 = .ok true) :
    ∃ (ws : List Expr) (teleR : List (Expr × BinderMeta)) (leafR : Expr) (I : Name)
      (us us' : List Level) (Pw : List Expr) (fR : Expr),
      targetPiDomsWith fvsR T0 = some ws ∧
      (ws.getD i default).stripPis tele = some (teleR, leafR) ∧
      leafR.getAppFn = .const I us ∧ I = Mt.ind ∧
      ((targetPiDomsWith fvsR T).getD [])[i]? = some fR ∧
      fR.eraseFVarTys = (Expr.mkPisOf teleR
        (Expr.mkAppN (.const I us') (Pw ++ leafR.getAppArgs.drop Mt.nPc))).eraseFVarTys ∧
      (Expr.mkAppN (.const I us') Pw).nestOcc p.memberNames 0 0 = true ∧
      targetClassMatch ops env p formerTys Mt.pfvs Mt.lvls Mt.ds us' Pw = .ok true ∧
      (∀ x ∈ Pw, x.looseBVarsBounded 0 = true) := by
  sorry

/-! ## The generated rule's inductive hypotheses -/

/-- **A generated rule's `ih` at a recursive field**, as the generator
built it: the declared fields opened at the prefix, the walked telescope
instantiated at them, the `ih`'s parts, and its callee named. -/
theorem classGenRule_ih {g : ClassGen} {recOf : Nat → Option Name} {rlvls : List Level}
    {c : Nat} {x : ClassCtor} {gen : Expr}
    (h : classGenRule g recOf rlvls c x = some gen) {i t tele : Nat} (hi : i < x.nF)
    (hk : x.kinds.getD i .ordinary = .recursive t tele) :
    ∃ fvs o ws xsO idx r, openPisAtFvars x.nF x.tyD g.pre.length = some (fvs, o) ∧
      targetPiDomsWith fvs x.tyN = some ws ∧
      g.ihParts t tele (ws.getD i default) (g.pre.length + x.nF) = some (xsO, idx) ∧
      recOf t = some r := by
  sorry

/-- **Node agreement at an entry** (`classFieldsAgree`, inverted at a
recursive field `i` and an entry `e ∈ E`): the datum's field `i` strips
to its ih's telescope and a leaf headed by the ih's class, and the
entry's field `i` passed K.53′ against it. -/
theorem classFieldsAgree_at {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys : List Expr} {Ms : List TargetMajor} {fvs : List Expr} {ctor : Name}
    {E : List NestCtorNf} {ks : List ClassField} {i₀ : Nat}
    (h : classFieldsAgree ops env p formerTys Ms fvs ctor E i₀ ks = .ok ())
    {i t tele : Nat} (hk : ks[i - i₀]? = some (.recursive t tele)) (hi : i₀ ≤ i)
    {e : NestCtorNf} (he : e ∈ E) :
    ∃ teleB leaf f, (fvs.getD i default).fvarTypeD.stripPis tele = some (teleB, leaf) ∧
      classLeafAt (Ms.getD t default) leaf = true ∧
      ((targetPiDomsWith fvs e.ty).getD [])[i]? = some f ∧
      targetK53 ops env p formerTys (Ms.getD t default) teleB leaf f = .ok true := by
  sorry

end ConLeche
