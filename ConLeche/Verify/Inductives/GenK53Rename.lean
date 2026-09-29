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

/-! ## Erasure, spines and towers -/

private theorem gk_erase_mkAppN : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).eraseFVarTys = Expr.mkAppN f.eraseFVarTys (as.map Expr.eraseFVarTys)
  | [], _ => rfl
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).eraseFVarTys = _
    rw [gk_erase_mkAppN as]; rfl

private theorem gk_erase_mkPisOf : ∀ (bs : List (Expr × BinderMeta)) (b : Expr),
    (Expr.mkPisOf bs b).eraseFVarTys
      = Expr.mkPisOf (bs.map fun x => (x.1.eraseFVarTys, x.2)) b.eraseFVarTys
  | [], _ => rfl
  | (ty, m) :: bs, b => by
    show Expr.eraseFVarTys (.forallE ty (Expr.mkPisOf bs b) m) = _
    rw [List.map_cons, Expr.mkPisOf, ← gk_erase_mkPisOf bs b]; rfl

private theorem gk_stripPis_eq_mkPisOf : ∀ {n : Nat} {e r : Expr} {bs : List (Expr × BinderMeta)},
    e.stripPis n = some (bs, r) → e = Expr.mkPisOf bs r
  | 0, e, r, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, e, r, bs, h => by
    cases e with
    | forallE ty b m =>
      simp only [Expr.stripPis] at h
      obtain ⟨⟨bs', r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [gk_stripPis_eq_mkPisOf h1]; rfl
    | _ => simp [Expr.stripPis] at h

private theorem gk_erase_getAppFn :
    ∀ (x : Expr), x.eraseFVarTys.getAppFn = x.getAppFn.eraseFVarTys := by
  intro x
  induction x with
  | app f a ihf _ => exact ihf
  | _ => rfl

private theorem gk_erase_getAppArgs :
    ∀ (x : Expr), x.eraseFVarTys.getAppArgs = x.getAppArgs.map Expr.eraseFVarTys := by
  intro x
  induction x with
  | app f a ihf _ =>
    show (Expr.app f.eraseFVarTys a.eraseFVarTys).getAppArgs = _
    simp only [Expr.getAppArgs, ihf, List.map_append, List.map_cons, List.map_nil]
  | _ => rfl

private theorem gk_erase_erase : ∀ (x : Expr), x.eraseFVarTys.eraseFVarTys = x.eraseFVarTys := by
  intro x
  induction x <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars]

private theorem gk_erase_eq_const {x : Expr} {I : Name} {us : List Level}
    (h : x.eraseFVarTys = .const I us) : x = .const I us := by
  cases x <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars]

private theorem gk_erasedEqs_iff : ∀ {as bs : List Expr},
    ErasedEqs as bs ↔ as.map Expr.eraseFVarTys = bs.map Expr.eraseFVarTys
  | [], [] => by simp [ErasedEqs]
  | [], _ :: _ => by simp [ErasedEqs]
  | _ :: _, [] => by simp [ErasedEqs]
  | a :: as, b :: bs => by
    simp only [ErasedEqs, List.map_cons, List.cons.injEq, Expr.eraseFVarTys_eq_iff,
      gk_erasedEqs_iff]

private theorem gk_erasedEqs_get : ∀ {as bs : List Expr}, ErasedEqs as bs →
    ∀ {l : Nat} {x : Expr}, as[l]? = some x → ∃ y, bs[l]? = some y ∧ Expr.ErasedEq x y
  | [], [], _, l, x, h => by simp at h
  | [], _ :: _, hf, _, _, _ => by simp [ErasedEqs] at hf
  | _ :: _, [], hf, _, _, _ => by simp [ErasedEqs] at hf
  | a :: as, b :: bs, hf, l, x, h => by
    obtain ⟨hab, hr⟩ := hf
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact ⟨b, rfl, hab⟩
    | succ l => exact gk_erasedEqs_get hr (by simpa using h)

private theorem gk_teleMap_eq : ∀ {tA tB : List (Expr × BinderMeta)}, tA.length = tB.length →
    (∀ (l : Nat) (q q' : Expr × BinderMeta), tA[l]? = some q → tB[l]? = some q' →
      q.2 = q'.2 ∧ Expr.ErasedEq q.1 q'.1) →
    tA.map (fun b => (b.1.eraseFVarTys, b.2)) = tB.map (fun b => (b.1.eraseFVarTys, b.2))
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | q :: tA, q' :: tB, hl, h => by
    obtain ⟨h2, h1⟩ := h 0 q q' rfl rfl
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq]
    exact ⟨⟨Expr.eraseFVarTys_eq_iff.mpr h1, h2⟩, gk_teleMap_eq (by simpa using hl)
      (fun l p p' hp hp' => h (l + 1) p p' (by simpa using hp) (by simpa using hp'))⟩

private theorem gk_substFvars_mkAppN {b D : Nat} {s : Nat → Expr} : ∀ (as : List Expr) (f : Expr),
    Expr.substFvars b D s (Expr.mkAppN f as)
      = Expr.mkAppN (Expr.substFvars b D s f) (as.map (Expr.substFvars b D s))
  | [], _ => rfl
  | a :: as, f => by
    show Expr.substFvars b D s (Expr.mkAppN (.app f a) as) = _
    rw [gk_substFvars_mkAppN as]; rfl

private theorem gk_erase_substFvars_erase {b D : Nat} {s : Nat → Expr} (x : Expr) :
    (Expr.substFvars b D s x.eraseFVarTys).eraseFVarTys = (Expr.substFvars b D s x).eraseFVarTys :=
  Expr.eraseFVarTys_eq_iff.mpr
    (Expr.ErasedEq.substFvars (Expr.eraseFVarTys_eq_iff.mp (gk_erase_erase x)))

private theorem gk_teleSubst_erase {b D : Nat} {s : Nat → Expr} (t : List (Expr × BinderMeta)) :
    (t.map fun p => (Expr.substFvars b D s p.1, p.2)).map (fun q => (q.1.eraseFVarTys, q.2))
      = (t.map fun q => (q.1.eraseFVarTys, q.2)).map
          (fun p => ((Expr.substFvars b D s p.1).eraseFVarTys, p.2)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp [gk_erase_substFvars_erase]

private theorem gk_argsSubst_erase {b D : Nat} {s : Nat → Expr} (t : List Expr) :
    (t.map (Expr.substFvars b D s)).map Expr.eraseFVarTys
      = (t.map Expr.eraseFVarTys).map (fun x => (Expr.substFvars b D s x).eraseFVarTys) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp [gk_erase_substFvars_erase]

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
    (hT : T.fvarsBelow a) (hT0 : T0.fvarsBelow a) (hpf : Mt.pfvs.length ≤ a)
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
  obtain ⟨s, hsd⟩ : ∃ s : Nat → Expr, s = fun v => .fvar v (.sort .zero) := ⟨_, rfl⟩
  have hsF : ∀ v, v < a → ∃ ty, s v = .fvar v ty := fun v _ => ⟨.sort .zero, by rw [hsd]⟩
  have hsB : ∀ v, v < a → (s v).looseBVarsBounded 0 = true := fun v _ => by rw [hsd]; rfl
  -- the datum's opening
  have hl0 : fvs0.length = n := Verify.openPisAtFvars_length n hop0
  have hidx0 := openPisAtFvars_index n T0 a hop0
  have hws0 := openPisAtFvars_targetPiDomsWith hop0
  -- the renamed fields are the rule's
  have hF : ErasedEqs (fvs0.map (Expr.substFvars a bR s)) fvsR := by
    rw [gk_erasedEqs_iff]
    apply List.ext_getElem?
    intro l
    simp only [List.getElem?_map]
    by_cases hl : l < n
    · obtain ⟨ty', hR'⟩ := hR l hl
      obtain ⟨x, hx⟩ : ∃ x, fvs0[l]? = some x := ⟨fvs0[l], List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := hidx0 l x hx
      rw [hx, hR']
      simp only [Option.map_some, Option.some.injEq]
      rw [Expr.substFvars_fvar_ge (by omega)]
      simp only [Expr.eraseFVarTys, Expr.replaceFVars, Option.getD_some, Expr.fvar.injEq, and_true]
      omega
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      rfl
  -- the entry's field, renamed
  obtain ⟨wT, hwT⟩ : ∃ wT, targetPiDomsWith fvs0 T = some wT := by
    cases h : targetPiDomsWith fvs0 T with
    | none => rw [h] at hf0; simp at hf0
    | some wT => exact ⟨wT, rfl⟩
  rw [hwT, Option.getD_some] at hf0
  have hwTl : wT.length = n := by rw [targetPiDomsWith_length _ _ _ hwT, hl0]
  have hi : i < n := by
    have := (List.getElem?_eq_some_iff.mp hf0).1
    omega
  have hwTσ := targetPiDomsWith_substFvars (D := bR) hsB hwT
  obtain ⟨wR, hwR, hwRe⟩ :=
    targetPiDomsWith_erasedEq hF (substFvars_erasedEq_self hsF T hT) hwTσ
  obtain ⟨fR, hfR, hfRe⟩ := gk_erasedEqs_get hwRe (l := i) (by rw [List.getElem?_map, hf0]; rfl)
  -- the datum's field, renamed
  have hws0σ := targetPiDomsWith_substFvars (D := bR) hsB hws0
  obtain ⟨ws, hws, hwse⟩ :=
    targetPiDomsWith_erasedEq hF (substFvars_erasedEq_self hsF T0 hT0) hws0σ
  have hx0 : fvs0[i]? = some (fvs0.getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  obtain ⟨wi, hwi, hwie⟩ := gk_erasedEqs_get hwse (l := i)
    (x := Expr.substFvars a bR s (fvs0.getD i default).fvarTypeD)
    (by rw [List.getElem?_map, List.getElem?_map, hx0]; rfl)
  have hwsD : ws.getD i default = wi := by rw [List.getD_eq_getElem?_getD, hwi]; rfl
  have hstσ := stripPis_substFvars (D := bR) hsF tele (fvs0.getD i default).fvarTypeD
  rw [hst, Option.map_some] at hstσ
  simp only at hstσ
  obtain ⟨teleR, leafR, hstR, hlenR, hallR, hleafR⟩ := stripPis_erasedEq hwie hstσ
  -- K.53′ at the datum
  obtain ⟨teleW, leafW, I, us', us, hstrip, htele, hW, hM, -, hidx, hment, hcm⟩ :=
    targetK53_true hK
  have hI : I = Mt.ind := by
    unfold classLeafAt at hleaf
    rw [hM] at hleaf
    simpa using hleaf
  have hPw : ∀ x ∈ leafW.getAppArgs.take Mt.nPc, x.bvarB = 0 ∧ x.fvarB ≤ Mt.pfvs.length := by
    intro x hx
    obtain ⟨-, hpd⟩ := targetClassMatch_true hcm
    obtain ⟨hl, hall⟩ := targetParamsDefEq_true hpd
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨y, hy⟩ : ∃ y, Mt.ds[j]? = some y := ⟨Mt.ds[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hb, -, hbf, -⟩ := hall j y _ hy (List.getElem?_eq_getElem hj)
    exact ⟨hb, hbf⟩
  -- the leaf's spine, renamed
  have hleafE : leaf = Expr.mkAppN (.const I us) leaf.getAppArgs := by
    rw [← hM, Expr.mkAppN_getApp]
  have hσleaf : Expr.substFvars a bR s leaf
      = Expr.mkAppN (.const I us) (leaf.getAppArgs.map (Expr.substFvars a bR s)) := by
    conv => lhs; rw [hleafE]
    rw [gk_substFvars_mkAppN]; rfl
  have hEleafR : leafR.eraseFVarTys = (Expr.substFvars a bR s leaf).eraseFVarTys :=
    (Expr.eraseFVarTys_eq_iff.mpr hleafR).symm
  have hRfn : leafR.getAppFn = .const I us := by
    apply gk_erase_eq_const
    rw [← gk_erase_getAppFn, hEleafR, hσleaf, gk_erase_mkAppN, Expr.getAppFn_mkAppN]; rfl
  have hRargs : leafR.getAppArgs.map Expr.eraseFVarTys
      = (leaf.getAppArgs.map (Expr.substFvars a bR s)).map Expr.eraseFVarTys := by
    rw [← gk_erase_getAppArgs, hEleafR, hσleaf, gk_erase_mkAppN, Expr.getAppArgs_mkAppN]; rfl
  refine ⟨ws, teleR, leafR, I, us, us', leafW.getAppArgs.take Mt.nPc, fR, hws,
    by rw [hwsD]; exact hstR, hRfn, hI,
    by rw [hwR, Option.getD_some]; exact hfR, ?_, hment, hcm, fun x hx => ?_⟩
  · rw [← Expr.eraseFVarTys_eq_iff.mpr hfRe, gk_stripPis_eq_mkPisOf hstrip]
    have hleafW : leafW = Expr.mkAppN (.const I us')
        (leafW.getAppArgs.take Mt.nPc ++ leafW.getAppArgs.drop Mt.nPc) := by
      rw [List.take_append_drop, ← hW, Expr.mkAppN_getApp]
    conv => lhs; rw [hleafW]
    rw [Expr.substFvars_mkPisOf, gk_substFvars_mkAppN, gk_erase_mkPisOf, gk_erase_mkPisOf,
      gk_erase_mkAppN, gk_erase_mkAppN]
    congr 1
    · rw [gk_teleSubst_erase, htele, ← gk_teleSubst_erase]
      exact gk_teleMap_eq hlenR hallR
    · congr 1
      rw [List.map_append, List.map_append, List.map_append]
      congr 1
      · rw [List.map_map]
        apply List.map_congr_left
        intro x hx
        obtain ⟨-, hf⟩ := hPw x hx
        exact Expr.eraseFVarTys_eq_iff.mpr (substFvars_erasedEq_self hsF x
          (Expr.fvarsBelow_iff.mpr (by rw [← Expr.fvarB_eq]; omega)))
      · rw [gk_argsSubst_erase, hidx, ← gk_argsSubst_erase, List.map_drop, List.map_drop,
          ← hRargs, List.map_drop]
  · obtain ⟨hb, -⟩ := hPw x hx
    exact Expr.looseBVarsBounded_iff.mpr (by rw [← Expr.bvarB_eq]; omega)

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
