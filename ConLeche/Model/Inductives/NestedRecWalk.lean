module

public import ConLeche.Verify.Inductives.NestedRecWalk
public import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitErase
import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.EraseAnnots
import ConLeche.Verify.Level
public section

/-!
# The reading law of the restore WALK (task #315, M7-2, PLAN-M7 §1b)

`restoreWalk` replaces, top-down, every application headed by an
auxiliary type (`pins`) or an auxiliary constructor (`ctorPins`) by the
pin — the container at the block's parameters — lifted to the depth,
renames the auxiliary recursors (`recMap`), and leaves everything else
as it is.  **The readings agree**: at any model of the restored
environment and any model of the scratch one whose leaves agree off the
auxiliary names (`RestoreAgree`), the opened restored term and the
opened auxiliary term interpret alike at every frame at which the
restored reading is graded — not as the same `AnnotTerm` (the
auxiliary leaf is the copy's, the restored one the container's at the
components) but as the same set (`denoteMeta_restoreWalk`).  The
per-key agreements are the structure's fields: a pin's is
`nestedIdent_of` (`NestedCore.lean`), a constructor pin's its twin
(`nestedCtorIdent_of`), a recursor's a hypothesis (the rules' stage
supplies it).  The shape the walk relies on — every key-headed
application at the parameter variables — is `AuxAppsOk`
(`Verify/Inductives/NestedRecWalk.lean`, the model's face of the K.34
record); the induction is on it.

This is the SEMANTIC version of §U.21b's restore reading law, at every
term the walk visits — the recursor types (motives, minors, index
telescopes, majors) and the rules' λ-towers alike.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps fueledOps BinderMeta PropWhen
  RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Openers -/

/-- The standard openers of `n` binders from index `k₀`: the `i`-th is `fvar (k₀ + i)`. -/
@[expose] def OpenersFrom (fvs : List Expr) (k₀ n : Nat) : Prop :=
  fvs.length = n ∧ ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = Expr.fvar (k₀ + i) ty

omit [SetTheory V] in
theorem OpenersFrom.closed {fvs : List Expr} {k₀ n : Nat} (h : OpenersFrom fvs k₀ n) :
    ∀ a ∈ fvs, a.looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
  obtain ⟨ty, rfl⟩ := h.2 i a hi
  rfl

omit [SetTheory V] in
theorem OpenersFrom.snoc {fvs : List Expr} {k₀ n : Nat} (h : OpenersFrom fvs k₀ n) (ty : Expr) :
    OpenersFrom (fvs ++ [Expr.fvar (k₀ + n) ty]) k₀ (n + 1) := by
  refine ⟨by rw [List.length_append, List.length_singleton, h.1], ?_⟩
  intro i x hx
  rcases Nat.lt_or_ge i fvs.length with hi | hi
  · rw [List.getElem?_append_left hi] at hx
    exact h.2 i x hx
  · rw [List.getElem?_append_right hi] at hx
    have : i = fvs.length := by
      have hl := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_singleton] at hl
      omega
    subst this
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
    rw [← hx, h.1]
    exact ⟨ty, rfl⟩

omit [SetTheory V] in
theorem OpenersFrom.append {fvsP fvs : List Expr} {nP d : Nat} (hP : OpenersFrom fvsP 0 nP)
    (h : OpenersFrom fvs nP d) : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := by
  refine ⟨by rw [List.length_append, hP.1, h.1], ?_⟩
  intro i x hx
  rcases Nat.lt_or_ge i fvsP.length with hi | hi
  · rw [List.getElem?_append_left hi] at hx
    exact hP.2 i x hx
  · rw [List.getElem?_append_right hi] at hx
    obtain ⟨ty, rfl⟩ := h.2 _ x hx
    have hl := hP.1
    exact ⟨ty, by congr 1; omega⟩

omit [SetTheory V] in
/-- A bound variable instantiated along closed openers is an opener or stays bound. -/
theorem instSeq_bvar_cases : ∀ (Vs : List Expr) (t i : Nat),
    (∀ a ∈ Vs, a.looseBVarsBounded 0 = true) →
    (∃ x ∈ Vs, Expr.instSeq Vs t (.bvar i) = x) ∨ ∃ j, Expr.instSeq Vs t (.bvar i) = .bvar j
  | [], _, i, _ => Or.inr ⟨i, rfl⟩
  | a :: Vs, t, i, hcl => by
    show (∃ x ∈ a :: Vs, Expr.instSeq Vs (t - 1) ((Expr.bvar i).instantiate1 a t) = x) ∨
      ∃ j, Expr.instSeq Vs (t - 1) ((Expr.bvar i).instantiate1 a t) = .bvar j
    by_cases hit : i = t
    · rw [show (Expr.bvar i).instantiate1 a t = a from by simp [Expr.instantiate1, hit],
        Expr.instSeq_eq_self _ _ (hcl a List.mem_cons_self)]
      exact Or.inl ⟨a, List.mem_cons_self, rfl⟩
    · have hb : (Expr.bvar i).instantiate1 a t = .bvar (if i > t then i - 1 else i) := by
        simp only [Expr.instantiate1, hit, if_false]
        split <;> rfl
      rw [hb]
      rcases instSeq_bvar_cases Vs (t - 1) (if i > t then i - 1 else i)
          (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) with ⟨x, hx, hxe⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨x, List.mem_cons_of_mem _ hx, hxe⟩
      · exact Or.inr ⟨j, hj⟩

omit [SetTheory V] in
/-- A free variable keeps its index along an instantiation sequence. -/
theorem instSeq_fvar_idx : ∀ (Vs : List Expr) (t i : Nat) (ty : Expr),
    Expr.instSeq Vs t (.fvar i ty) = .fvar i ty
  | [], _, _, _ => rfl
  | a :: Vs, t, i, ty => by
    show Expr.instSeq Vs (t - 1) ((Expr.fvar i ty).instantiate1 a t) = _
    rw [Expr.instantiate1_fvar]
    exact instSeq_fvar_idx Vs (t - 1) i ty

omit [SetTheory V] in
/-- A `let` keeps its head along an instantiation sequence. -/
theorem instSeq_letE : ∀ (Vs : List Expr) (t : Nat) (ty v b : Expr),
    ∃ ty' v' b', Expr.instSeq Vs t (.letE ty v b) = .letE ty' v' b'
  | [], t, ty, v, b => ⟨ty, v, b, rfl⟩
  | a :: Vs, t, ty, v, b => by
    show ∃ ty' v' b', Expr.instSeq Vs (t - 1) ((Expr.letE ty v b).instantiate1 a t) = _
    exact instSeq_letE Vs (t - 1) _ _ _

omit [SetTheory V] in
/-- A projection keeps its structure name and index along an
instantiation sequence, its subject instantiated. -/
theorem instSeq_proj : ∀ (Vs : List Expr) (t : Nat) (sn : Name) (i : Nat) (x : Expr),
    Expr.instSeq Vs t (.proj sn i x) = .proj sn i (Expr.instSeq Vs t x)
  | [], _, _, _, _ => rfl
  | a :: Vs, t, sn, i, x => by
    show Expr.instSeq Vs (t - 1) ((Expr.proj sn i x).instantiate1 a t) = _
    exact instSeq_proj Vs (t - 1) sn i _

/-! ## The leaf agreements -/

/-- **The leaf agreements the walk's reading law consumes**, at two carriers
`acvalA`/`envA` (the scratch install's) and `acvalR`/`envR` (the restored
environment's), a level assignment `φ`, the block's parameter count and its
parameter telescope reading `params` (at `φ`):

* off the auxiliary names the two environments answer alike WHEREVER THE
  AUXILIARY ONE FINDS THE NAME: it is found at the restored environment too,
  with the same level parameters and the same leaf (`leafSome`); the
  auxiliary names are absent from `envR`.

  The agreement is stated at a name the auxiliary side FINDS, and not as two
  unconditional `∀ n ∉ R.auxNames` clauses (an `envA.find? n = none →
  envR.find? n = none` and a bare `acvalA n = acvalR n`), because the two
  clauses are FALSE at the pair of PROVISIONED environments the rules' law
  runs at (task #315 M7-2): the restored side stores the mimics' recursors
  under `p.mimicRecName j` while the auxiliary side stores them under the
  SCRATCH names `q.aux.str "rec"`, and `p.mimicRecName j` is no auxiliary
  name — `R.auxNames`' third component is the `recMap`'s KEYS, not its
  values.  So at `n = p.mimicRecName j` the restored environment finds a
  recursor where the auxiliary one finds nothing, and its leaf is the
  chosen tuple's projection where the auxiliary carrier's is arbitrary.
  The walk never needs either: a name it reads is one the auxiliary
  reading FOUND;
* a `recMap` key's leaf is its restored name's, with the same level parameters;
* a `pins` key `n` (levels `lps`, the copy's index count `arityOf n`): its
  abstracted pin is bounded at `nP`, re-opened at the parameters it reads at
  any depth `nP + d` as the container `J` at the components lifted by `d`,
  and — THE PIN IDENTITY (`nestedIdent_of`) — that application at any index
  readings `Es` interprets, wherever it is graded at a frame whose parameter
  slots fit `params`, like the copy at the parameter variables and `Es`;
* a `ctorPins` key likewise, with the constructor's field count as arity, the
  restored head `newName` at the lifted components, and the constructor
  identity (`nestedCtorIdent_of`). -/
structure RestoreAgree (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (acvalA acvalR : Name → (Name → Nat) → AnnotTerm) (envA envR : Env) (φ : Name → Nat)
    (nP : Nat) (params : List AnnotTerm) : Prop where
  nPEq : R.nP = nP
  leafSome : ∀ n, n ∉ R.auxNames → ∀ ci : ConstantInfo, envA.find? n = some ci →
    ∃ ci' : ConstantInfo, envR.find? n = some ci' ∧
      ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams ∧ acvalA n = acvalR n
  auxFresh : ∀ n ∈ R.auxNames, envR.find? n = none
  recKey : ∀ n n', R.recMap.lookup n = some n' → ∀ ci : ConstantInfo, envA.find? n = some ci →
    ∃ ci' : ConstantInfo, envR.find? n' = some ci' ∧
      ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams ∧ acvalA n = acvalR n'
  recNone : ∀ n n', R.recMap.lookup n = some n' → envA.find? n = none → envR.find? n' = none
  keyNotRec : ∀ n, R.IsKey n → R.recMap.lookup n = none
  /-- the two environments carry the same projection tables (the walk
  descends into a projection's subject, K.35's Bool with it) -/
  projEq : ∀ (sn : Name) (i : Nat), envA.findProj? sn i = envR.findProj? sn i
  /-- and read a literal alike WHEREVER BOTH READ (the walk prunes at a
  literal; a reading names the basis constants, which are then found in
  the RESTORED environment and so are not auxiliary names, and off those
  the two carriers' leaves agree) -/
  litEq : ∀ (D : Nat) (l : ConLeche.Literal) {A A' : AnnotTerm},
    denoteMeta acvalA envA φ D (.lit l) = some A →
    denoteMeta acvalR envR φ D (.lit l) = some A' → A = A'
  pin : ∀ n pin, R.pins.lookup n = some pin →
    pin.looseBVarsBounded nP = true ∧
    ∃ (ci : ConstantInfo) (J : Name) (ψJ : Name → Nat) (Ds : List AnnotTerm) (nIdx : Nat),
      envA.find? n = some ci ∧ ci.toConstantVal.levelParams = lps ∧ arityOf n = some nIdx ∧
      (∀ (fvsP : List Expr) (d : Nat), OpenersFrom fvsP 0 nP →
        denoteMeta acvalR envR φ (nP + d) (Expr.instSeq fvsP (nP - 1) pin)
          = some (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0)))) ∧
      ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Es : List AnnotTerm),
        SpineFit ρ₀ params as → xs.length = d → Es.length = nIdx →
        WellDenoted V (consList xs (consList as ρ₀))
          (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0) ++ Es)) →
        interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0) ++ Es))
          = interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalA n φ) (paramBvarsAt nP (nP + d) ++ Es))
  ctor : ∀ n pin newName, R.ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName) →
    pin.looseBVarsBounded nP = true ∧ R.pins.lookup n = none ∧
    ∃ (ci : ConstantInfo) (J : Name) (ilvls : List Level) (ψJ : Name → Nat) (Ds : List AnnotTerm)
      (nF : Nat),
      envA.find? n = some ci ∧ ci.toConstantVal.levelParams = lps ∧ arityOf n = some nF ∧
      (∀ d, (pin.liftLooseBVars d 0).getAppFn = .const J ilvls) ∧
      (∀ (fvsP fvs : List Expr) (d : Nat), OpenersFrom fvsP 0 nP → OpenersFrom fvs nP d →
        denoteMeta acvalR envR φ (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1)
            (Expr.mkAppN (.const newName ilvls) (pin.liftLooseBVars d 0).getAppArgs))
          = some (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0)))) ∧
      ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Fs : List AnnotTerm),
        SpineFit ρ₀ params as → xs.length = d → Fs.length = nF →
        WellDenoted V (consList xs (consList as ρ₀))
          (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0) ++ Fs)) →
        interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0) ++ Fs))
          = interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalA n φ) (paramBvarsAt nP (nP + d) ++ Fs))

/-! ## The auxiliary-free congruence -/

section Congr

variable {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat}
  {acvalA acvalR : Name → (Name → Nat) → AnnotTerm} {envA envR : Env} {φ : Name → Nat}
  {nP : Nat} {params : List AnnotTerm}
  (hk : R.KeysInAux)
  (hag : RestoreAgree (V := V) R lps arityOf acvalA acvalR envA envR φ nP params)
include hk hag

/-- **An auxiliary-free term reads alike at the two carriers**, opened at
any closed variables `Vs` (as many as the depth `D`), WHEREVER BOTH READ:
the auxiliary names never occur, so every constant is one the two
environments answer alike with agreeing leaves; a `let` reads `none` on
both sides, and a projection and a literal are the two new shapes the
weakened `AuxAppsOk` admits (`RestoreAgree.projEq`/`.litEq`).

The two readings are compared only where both are `some`.  That is what
a literal forces: whether a literal reads at all is decided by the
environment's basis constants (`natLitSupported`), and the scratch
environment carries the block's copies while the restored one does not,
so the two supports need not agree — but wherever both read, the basis
constants are found in the RESTORED environment, hence are not auxiliary
names, hence carry agreeing leaves. -/
theorem denoteMeta_congr_auxFree :
    ∀ {d : Nat} {e : Expr}, AuxAppsOk R lps arityOf d e →
      (∀ m ∈ R.auxNames, e.mentionsConst m = false) →
      ∀ (Vs : List Expr) (D : Nat), Vs.length = D → (∀ a ∈ Vs, ∃ i ty, a = Expr.fvar i ty) →
      ∀ {A A' : AnnotTerm},
        denoteMeta acvalA envA φ D (Expr.instSeq Vs (D - 1) e) = some A →
        denoteMeta acvalR envR φ D (Expr.instSeq Vs (D - 1) e) = some A' → A = A' := by
  intro d e h
  induction h with
  | @key _ n args _ hkey _ _ _ _ _ =>
    intro hfree
    exfalso
    have hn : n ∈ R.auxNames := by
      rcases hkey with hp | hc
      · obtain ⟨pin, hpin⟩ := Option.isSome_iff_exists.mp hp
        exact hk.1 n pin hpin
      · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hc
        exact hk.2.1 n q hq
    have := hfree n hn
    rw [Expr.mentionsConst_mkAppN_head args _ (by simp [Expr.mentionsConst])] at this
    exact Bool.noConfusion this
  | @app _ f a _ _ _ ihf iha =>
    intro hfree Vs D hV hcl A A' hA hA'
    have hfa := fun m hm => Expr.mentionsConst_app_false (hfree m hm)
    rw [Expr.instSeq_app] at hA hA'
    obtain ⟨fa, aa, hfa1, haa1, rfl⟩ := denoteMeta_app_inv hA
    obtain ⟨fa', aa', hfa2, haa2, rfl⟩ := denoteMeta_app_inv hA'
    rw [ihf (fun m hm => (hfa m hm).1) Vs D hV hcl hfa1 hfa2,
      iha (fun m hm => (hfa m hm).2) Vs D hV hcl haa1 haa2]
  | @lam _ ty b bm _ _ ihty ihb =>
    intro hfree Vs D hV hcl A A' hA hA'
    have hfb := fun m hm => Expr.mentionsConst_lam_false (hfree m hm)
    rw [ConLeche.instSeq_lam Vs (D - 1) ty b bm (by omega)] at hA hA'
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv hA
    obtain ⟨ta', ba', hta', hba', rfl⟩ := denoteMeta_lam_inv hA'
    obtain rfl : ta = ta' := ihty (fun m hm => (hfb m hm).1) Vs D hV hcl hta hta'
    have hopen : (Expr.instSeq Vs (D - 1 + 1) b).instantiate1
          (.fvar D (Expr.instSeq Vs (D - 1) ty)) 0
        = Expr.instSeq (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1 - 1) b := by
      rw [Nat.add_sub_cancel, ConLeche.instSeq_snoc_at hV]
      rcases Nat.eq_zero_or_pos D with h0 | hpos
      · subst h0
        obtain rfl : Vs = [] := List.eq_nil_of_length_eq_zero hV
        rfl
      · rw [show D - 1 + 1 = D from by omega]
    rw [hopen] at hba hba'
    obtain rfl : ba = ba' :=
      ihb (fun m hm => (hfb m hm).2) (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1)
        (by rw [List.length_append, List.length_singleton, hV])
        (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact hcl a h
          · rw [List.mem_singleton] at h; exact ⟨_, _, h⟩)
        hba hba'
    rfl
  | @forallE _ ty b bm _ _ ihty ihb =>
    intro hfree Vs D hV hcl A A' hA hA'
    have hfb := fun m hm => Expr.mentionsConst_forallE_false (hfree m hm)
    rw [Expr.instSeq_forallE Vs (D - 1) ty b bm (by omega)] at hA hA'
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hA
    obtain ⟨ta', ba', hta', hba', rfl⟩ := denoteMeta_forallE_inv hA'
    obtain rfl : ta = ta' := ihty (fun m hm => (hfb m hm).1) Vs D hV hcl hta hta'
    have hopen : (Expr.instSeq Vs (D - 1 + 1) b).instantiate1
          (.fvar D (Expr.instSeq Vs (D - 1) ty)) 0
        = Expr.instSeq (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1 - 1) b := by
      rw [Nat.add_sub_cancel, ConLeche.instSeq_snoc_at hV]
      rcases Nat.eq_zero_or_pos D with h0 | hpos
      · subst h0
        obtain rfl : Vs = [] := List.eq_nil_of_length_eq_zero hV
        rfl
      · rw [show D - 1 + 1 = D from by omega]
    rw [hopen] at hba hba'
    obtain rfl : ba = ba' :=
      ihb (fun m hm => (hfb m hm).2) (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1)
        (by rw [List.length_append, List.length_singleton, hV])
        (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact hcl a h
          · rw [List.mem_singleton] at h; exact ⟨_, _, h⟩)
        hba hba'
    rfl
  | @letE _ ty v b _ _ _ _ _ _ =>
    intro _ Vs D _ _ A A' hA _
    obtain ⟨ty', v', b', hle⟩ := instSeq_letE Vs (D - 1) ty v b
    rw [hle, denoteMeta] at hA
    exact nomatch hA
  | @proj _ sn i x _ ihx =>
    intro hfree Vs D hV hcl A A' hA hA'
    have hfx : ∀ m ∈ R.auxNames, x.mentionsConst m = false :=
      fun m hm => ConLeche.Expr.mentionsConst_proj_false (hfree m hm)
    rw [instSeq_proj] at hA hA'
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv hA
    obtain ⟨ia', hia', hcase'⟩ := denoteMeta_proj_inv hA'
    obtain rfl : ia = ia' := ihx hfx Vs D hV hcl hia hia'
    rcases hcase with ⟨entry, hfpA, rfl⟩ | ⟨hfpA, hdec⟩ <;>
      rcases hcase' with ⟨entry', hfpR, rfl⟩ | ⟨hfpR, hdec'⟩
    · rw [hag.projEq sn i, hfpR] at hfpA
      obtain rfl := Option.some.inj hfpA
      rfl
    · rw [hag.projEq sn i, hfpR] at hfpA; exact nomatch hfpA
    · rw [hag.projEq sn i, hfpR] at hfpA; exact nomatch hfpA
    · exact Option.some.inj (hdec.symm.trans hdec')
  | @lit _ l =>
    intro _ Vs D _ _ A A' hA hA'
    rw [Expr.instSeq_eq_self _ _ (e := Expr.lit l) rfl] at hA hA'
    exact hag.litEq D l hA hA'
  | @const _ n us _ =>
    intro hfree Vs D _ _ A A' hA hA'
    have hnaux : n ∉ R.auxNames := by
      intro hn
      have := hfree n hn
      simp [Expr.mentionsConst] at this
    rw [Expr.instSeq_eq_self _ _ (e := Expr.const n us) rfl] at hA hA'
    cases hfA : envA.find? n with
    | none => rw [denoteMeta, hfA] at hA; exact nomatch hA
    | some ci =>
      obtain ⟨ci', hfR, hlps, hleaf⟩ := hag.leafSome n hnaux ci hfA
      rw [denoteMeta, hfA] at hA
      rw [denoteMeta, hfR] at hA'
      dsimp only at hA hA'
      by_cases hl : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hl] at hA
        rw [if_pos (by rw [hlps]; exact hl)] at hA'
        obtain rfl := Option.some.inj hA
        obtain rfl := Option.some.inj hA'
        rw [hlps, hleaf]
      · rw [if_neg hl] at hA; exact nomatch hA
  | @bvar _ i =>
    intro _ Vs D _ hfv A A' hA hA'
    have hcl : ∀ a ∈ Vs, a.looseBVarsBounded 0 = true := fun a ha => by
      obtain ⟨i, ty, rfl⟩ := hfv a ha
      rfl
    rcases instSeq_bvar_cases Vs (D - 1) i hcl with ⟨x, hx, hxe⟩ | ⟨j, hj⟩
    · obtain ⟨i', ty, rfl⟩ := hfv x hx
      rw [hxe, denoteMeta_fvar] at hA hA'
      rw [← Option.some.inj hA, ← Option.some.inj hA']
    · rw [hj, denoteMeta_bvar] at hA
      exact nomatch hA
  | @sort _ u =>
    intro _ Vs D _ _ A A' hA hA'
    rw [Expr.instSeq_eq_self _ _ (e := Expr.sort u) rfl, denoteMeta_sort] at hA hA'
    rw [← Option.some.inj hA, ← Option.some.inj hA']
  | @fvar _ i ty =>
    intro _ Vs D _ _ A A' hA hA'
    rw [instSeq_fvar_idx, denoteMeta_fvar] at hA hA'
    rw [← Option.some.inj hA, ← Option.some.inj hA']

end Congr

/-! ## The reading law of the walk -/

omit [SetTheory V] in
/-- A spine's arguments resolve where the spine does. -/
theorem constsResolve_mkAppN_args {env : Env} :
    ∀ (args : List Expr) (f : Expr), (Expr.mkAppN f args).constsResolve env = true →
      f.constsResolve env = true ∧ ∀ a ∈ args, a.constsResolve env = true
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    have h' : (Expr.mkAppN (.app f a) as).constsResolve env = true := h
    obtain ⟨hfa, hall⟩ := constsResolve_mkAppN_args as (.app f a) h'
    simp only [Expr.constsResolve, Bool.and_eq_true] at hfa
    exact ⟨hfa.1, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hfa.2
      · exact hall x hx'⟩

omit [SetTheory V] in
theorem paramBvarsAt_eq_range (nP D : Nat) :
    ((List.range nP).map fun k => AnnotTerm.bvar (D - 1 - (0 + k))) = paramBvarsAt nP D := by
  unfold paramBvarsAt
  exact List.map_congr_left fun k _ => by rw [Nat.zero_add]

omit [SetTheory V] in
/-- **Two read spines over ONE argument list agree** when the arguments'
readings agree wherever both read — the shape the reading law's
congruence delivers. -/
theorem DenoteMetaSpine.eq_of_pointwise {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {D : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval₁ env₁ φ D as vs → DenoteMetaSpine acval₂ env₂ φ D as vs' →
      (∀ a ∈ as, ∀ {x y : AnnotTerm}, denoteMeta acval₁ env₁ φ D a = some x →
        denoteMeta acval₂ env₂ φ D a = some y → x = y) → vs = vs'
  | _, _, _, .nil, h', _ => by cases h'; rfl
  | _, _, _, .cons ha hrest, h', hag => by
    cases h' with
    | cons ha' hrest' =>
      rw [hag _ List.mem_cons_self ha ha',
        DenoteMetaSpine.eq_of_pointwise hrest hrest'
          fun a ha'' => hag a (List.mem_cons_of_mem _ ha'')]

omit [SetTheory V] in
/-- A read spine at one carrier is one at another when every argument reads alike. -/
theorem DenoteMetaSpine.congr_envs {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {D : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval₁ env₁ φ D as vs →
      (∀ a ∈ as, denoteMeta acval₁ env₁ φ D a = denoteMeta acval₂ env₂ φ D a) →
      DenoteMetaSpine acval₂ env₂ φ D as vs
  | _, _, .nil, _ => .nil
  | _, _, .cons ha hrest, hag =>
    .cons (by rw [← hag _ List.mem_cons_self]; exact ha)
      (DenoteMetaSpine.congr_envs hrest fun a ha' => hag a (List.mem_cons_of_mem _ ha'))

section Walk

variable {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat}
  {acvalA acvalR : Name → (Name → Nat) → AnnotTerm} {envA envR : Env} {φ : Name → Nat}
  {nP : Nat} {params : List AnnotTerm}
  (hk : R.KeysInAux)
  (hag : RestoreAgree (V := V) R lps arityOf acvalA acvalR envA envR φ nP params)
include hk hag

/-- **THE READING LAW OF THE WALK** (PLAN-M7 §1b): at a term of the shape
`AuxAppsOk` at depth `d` below the parameters, its walk `e'` resolving at
the restored environment, and the two terms opened at the parameter
openers `fvsP` and the depth's openers `fvs`, the restored reading
interprets like the auxiliary one at every frame `consList xs (consList
as ρ₀)` — `as` fitting the parameters, `xs` the `d` values — at which
the restored reading is graded.  Induction on the shape: a key-headed
application by the leaf agreements (`RestoreAgree.pin`/`.ctor`, the
arguments unvisited by the walk and auxiliary-free, hence read alike by
`denoteMeta_congr_auxFree`), a binder by `piR_congr`/`lamR_congr` under
`WellDenoted`'s own clauses, an application componentwise, a constant by
the leaf agreements, a variable and a sort as themselves. -/
theorem denoteMeta_restoreWalk :
    ∀ {d : Nat} {e : Expr}, AuxAppsOk R lps arityOf d e →
      ∀ {e' : Expr}, ConLeche.restoreWalk R d e = .ok e' → e'.constsResolve envR = true →
      ∀ {fvsP fvs : List Expr}, OpenersFrom fvsP 0 nP → OpenersFrom fvs nP d →
      ∀ {A A' : AnnotTerm},
        denoteMeta acvalA envA φ (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) e) = some A →
        denoteMeta acvalR envR φ (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) e') = some A' →
        ∀ (as xs : List V) (ρ₀ : Nat → V), SpineFit ρ₀ params as → xs.length = d →
          WellDenoted V (consList xs (consList as ρ₀)) A' →
          interp V (consList xs (consList as ρ₀)) A' = interp V (consList xs (consList as ρ₀)) A := by
  intro d e h
  induction h with
  | @key d n args ar hkey har hlen htake hall _ =>
    intro e' hw hres fvsP fvs hP hF A A' hA hA' as xs ρ₀ hsp hxs hwd
    have hnP := hag.nPEq
    have hV : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := hP.append hF
    have hfvV : ∀ a ∈ fvsP ++ fvs, ∃ i ty, a = Expr.fvar i ty := fun a ha => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
      obtain ⟨ty, rfl⟩ := hV.2 i a hi
      exact ⟨_, _, rfl⟩
    have hclV := hV.closed
    have hrec := hag.keyNotRec n hkey
    -- the arguments past the parameters
    have hargs : args = args.take R.nP ++ args.drop R.nP := (List.take_append_drop _ _).symm
    have hrestLen : (args.drop R.nP).length = ar := by rw [List.length_drop, hlen]; omega
    have hPs : (args.take R.nP).map (Expr.instSeq (fvsP ++ fvs) (nP + d - 1)) = fvsP := by
      rw [htake, hnP]
      exact ConLeche.map_instSeq_structPsAt_prefix fvsP fvs nP d hclV hP.1 hF.1
    -- the auxiliary reading
    rw [Expr.instSeq_mkAppN, hargs, List.map_append, hPs] at hA
    obtain ⟨fa, vs, hfa, hspine, rfl⟩ := denoteMeta_mkAppN_inv hA
    obtain ⟨vsP, Es, rfl, hspP, hspE⟩ := DenoteMetaSpine.append_inv hspine
    have hvsP : vsP = paramBvarsAt nP (nP + d) := by
      have h1 := denoteMetaSpine_fvars (acval := acvalA) (env := envA) (φ := φ) (nP + d) fvsP 0
        (fun k x hx => hP.2 k x hx)
      rw [hP.1, paramBvarsAt_eq_range] at h1
      exact DenoteMetaSpine.unique hspP h1
    subst hvsP
    -- every argument past the parameters resolves at the restored environment, hence is
    -- auxiliary-free, hence reads alike
    have hcongr : ∀ x ∈ (args.drop R.nP).map (Expr.instSeq (fvsP ++ fvs) (nP + d - 1)),
        ∀ {u v : AnnotTerm}, denoteMeta acvalA envA φ (nP + d) x = some u →
          denoteMeta acvalR envR φ (nP + d) x = some v → u = v := by
      intro x hx u v hu hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      have hresA : a.constsResolve envR = true := by
        rcases AuxAppsOk.key_inv (d := d) (lps := lps) hk hkey har hlen hrec with
            ⟨pin, hpin, hw'⟩ | ⟨hp0, pin, newName, hc, hw'⟩
        · rw [hw'] at hw
          obtain rfl := Except.ok.inj hw
          exact (constsResolve_mkAppN_args _ _ hres).2 a ha
        · obtain ⟨-, -, ci, J, ilvls, ψJ, Ds, nF, -, -, -, hhead, -, -⟩ := hag.ctor n pin newName hc
          rw [hw' J ilvls (hhead d)] at hw
          obtain rfl := Except.ok.inj hw
          exact (constsResolve_mkAppN_args _ _ hres).2 a ha
      have hfree : ∀ m ∈ R.auxNames, a.mentionsConst m = false := fun m hm =>
        ConLeche.rk_mentionsConst_false_of_constsResolve hresA (hag.auxFresh m hm)
      have hD : (fvsP ++ fvs).length = nP + d := hV.1
      exact denoteMeta_congr_auxFree hk hag (hall a ha) hfree (fvsP ++ fvs) (nP + d) hD hfvV hu hv
    have hEsLen : Es.length = ar := by
      rw [← DenoteMetaSpine.length hspE, List.length_map, hrestLen]
    -- the head's reading
    rcases AuxAppsOk.key_inv (d := d) (lps := lps) hk hkey har hlen hrec with
        ⟨pin, hpin, hw'⟩ | ⟨hp0, pin, newName, hc, hw'⟩
    · -- a pin
      obtain ⟨hbound, ci, J, ψJ, Ds, nIdx, hfA, hlpsA, harN, hread, hident⟩ := hag.pin n pin hpin
      have hfa' : fa = acvalA n φ := by
        rw [Expr.instSeq_eq_self _ _ (e := Expr.const n (lps.map .param)) rfl,
          denoteMeta_const hfA (by rw [List.length_map, hlpsA])] at hfa
        have := Option.some.inj hfa
        rw [← this, hlpsA]
        congr 1
        funext q
        exact Level.substFn_map_param
      subst hfa'
      rw [hw'] at hw
      obtain rfl := Except.ok.inj hw
      rw [Expr.instSeq_mkAppN] at hA'
      have hlift : Expr.instSeq (fvsP ++ fvs) (nP + d - 1) (pin.liftLooseBVars d 0)
          = Expr.instSeq fvsP (nP - 1) pin := by
        have := Expr.instSeq_liftLooseBVars_prefix fvsP fvs (q := pin) hP.closed
          (by rw [hP.1]; exact hbound)
        rw [hP.1, hF.1] at this
        exact this
      rw [hlift] at hA'
      obtain ⟨fa', vs', hfa', hspine', rfl⟩ := denoteMeta_mkAppN_inv hA'
      rw [hread fvsP d hP] at hfa'
      obtain rfl := Option.some.inj hfa'
      obtain rfl := DenoteMetaSpine.eq_of_pointwise hspE hspine' hcongr
      rw [← AnnotTerm.mkAppN_append] at hwd ⊢
      have hnIdx : nIdx = ar := by
        rw [harN] at har
        exact Option.some.inj har
      exact hident d as xs ρ₀ Es hsp hxs (by rw [hEsLen, hnIdx]) hwd
    · -- a constructor pin
      obtain ⟨hbound, -, ci, J, ilvls, ψJ, Ds, nF, hfA, hlpsA, harN, hhead, hread, hident⟩ :=
        hag.ctor n pin newName hc
      have hfa' : fa = acvalA n φ := by
        rw [Expr.instSeq_eq_self _ _ (e := Expr.const n (lps.map .param)) rfl,
          denoteMeta_const hfA (by rw [List.length_map, hlpsA])] at hfa
        have := Option.some.inj hfa
        rw [← this, hlpsA]
        congr 1
        funext q
        exact Level.substFn_map_param
      subst hfa'
      rw [hw' J ilvls (hhead d)] at hw
      obtain rfl := Except.ok.inj hw
      rw [Expr.instSeq_mkAppN] at hA'
      obtain ⟨fa', vs', hfa', hspine', rfl⟩ := denoteMeta_mkAppN_inv hA'
      rw [hread fvsP fvs d hP hF] at hfa'
      obtain rfl := Option.some.inj hfa'
      obtain rfl := DenoteMetaSpine.eq_of_pointwise hspE hspine' hcongr
      rw [← AnnotTerm.mkAppN_append] at hwd ⊢
      have hnF : nF = ar := by
        rw [harN] at har
        exact Option.some.inj har
      exact hident d as xs ρ₀ Es hsp hxs (by rw [hEsLen, hnF]) hwd
  | @app d f a hnk _ _ ihf iha =>
    intro e' hw hres fvsP fvs hP hF A A' hA hA' as xs ρ₀ hsp hxs hwd
    obtain ⟨f', a', hwf, hwa, rfl⟩ := ConLeche.restoreWalk_app_inv hnk hw
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [Expr.instSeq_app] at hA hA'
    obtain ⟨fA, aA, hfA, haA, rfl⟩ := denoteMeta_app_inv hA
    obtain ⟨fA', aA', hfA', haA', rfl⟩ := denoteMeta_app_inv hA'
    rw [WellDenoted_app] at hwd
    rw [interp_app, interp_app, ihf hwf hres.1 hP hF hfA hfA' as xs ρ₀ hsp hxs hwd.1,
      iha hwa hres.2 hP hF haA haA' as xs ρ₀ hsp hxs hwd.2.1]
  | @lam d ty b bm _ _ ihty ihb =>
    intro e' hw hres fvsP fvs hP hF A A' hA hA' as xs ρ₀ hsp hxs hwd
    obtain ⟨ty', b', hwty, hwb, rfl⟩ := ConLeche.restoreWalk_lam_inv hw
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    have hV : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := hP.append hF
    rw [ConLeche.instSeq_lam _ _ _ _ _ (by rw [hV.1]; omega)] at hA hA'
    obtain ⟨tA, bA, htA, hbA, rfl⟩ := denoteMeta_lam_inv hA
    obtain ⟨tA', bA', htA', hbA', rfl⟩ := denoteMeta_lam_inv hA'
    rw [WellDenoted_lam] at hwd
    have hty := ihty hwty hres.1 hP hF htA htA' as xs ρ₀ hsp hxs hwd.1
    -- the bodies at the same opener (the annotation is invisible to the reading)
    have hopen : ∀ (X TY : Expr),
        (Expr.instSeq (fvsP ++ fvs) (nP + d - 1 + 1) X).instantiate1 (.fvar (nP + d) TY) 0
          = Expr.instSeq (fvsP ++ (fvs ++ [Expr.fvar (nP + d) TY])) (nP + (d + 1) - 1) X := by
      intro X TY
      rw [← List.append_assoc, show nP + (d + 1) - 1 = nP + d from by omega,
        ConLeche.instSeq_snoc_at hV.1]
      rcases Nat.eq_zero_or_pos (nP + d) with h0 | hpos
      · have hnil : fvsP ++ fvs = [] := List.eq_nil_of_length_eq_zero (by rw [hV.1, h0])
        rw [hnil]
        rfl
      · rw [show nP + d - 1 + 1 = nP + d from by omega]
    rw [hopen] at hbA
    rw [denoteMeta_congr_eraseAnnots _ _
        ((Expr.instSeq (fvsP ++ fvs) (nP + d - 1 + 1) b').instantiate1
          (.fvar (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) ty)) 0)
        (by rw [ConLeche.Expr.eraseAnnots_instantiate1, ConLeche.Expr.eraseAnnots_instantiate1]; rfl),
      hopen] at hbA'
    have hF' := hF.snoc (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) ty)
    rw [interp_lam, interp_lam, hty]
    refine lamR_congr fun x hx => ?_
    have hwdb := hwd.2.1 x (by rw [hty]; exact hx)
    have := ihb hwb hres.2 hP hF' hbA hbA' as (xs ++ [x]) ρ₀ hsp
      (by rw [List.length_append, List.length_singleton, hxs])
      (by rw [consList_append, consList_cons, consList_nil]; exact hwdb)
    rw [consList_append, consList_cons, consList_nil] at this
    exact this
  | @forallE d ty b bm _ _ ihty ihb =>
    intro e' hw hres fvsP fvs hP hF A A' hA hA' as xs ρ₀ hsp hxs hwd
    obtain ⟨ty', b', hwty, hwb, rfl⟩ := ConLeche.restoreWalk_forallE_inv hw
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    have hV : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := hP.append hF
    rw [Expr.instSeq_forallE _ _ _ _ _ (by rw [hV.1]; omega)] at hA hA'
    obtain ⟨tA, bA, htA, hbA, rfl⟩ := denoteMeta_forallE_inv hA
    obtain ⟨tA', bA', htA', hbA', rfl⟩ := denoteMeta_forallE_inv hA'
    rw [WellDenoted_pi] at hwd
    have hty := ihty hwty hres.1 hP hF htA htA' as xs ρ₀ hsp hxs hwd.1
    have hopen : ∀ (X TY : Expr),
        (Expr.instSeq (fvsP ++ fvs) (nP + d - 1 + 1) X).instantiate1 (.fvar (nP + d) TY) 0
          = Expr.instSeq (fvsP ++ (fvs ++ [Expr.fvar (nP + d) TY])) (nP + (d + 1) - 1) X := by
      intro X TY
      rw [← List.append_assoc, show nP + (d + 1) - 1 = nP + d from by omega,
        ConLeche.instSeq_snoc_at hV.1]
      rcases Nat.eq_zero_or_pos (nP + d) with h0 | hpos
      · have hnil : fvsP ++ fvs = [] := List.eq_nil_of_length_eq_zero (by rw [hV.1, h0])
        rw [hnil]
        rfl
      · rw [show nP + d - 1 + 1 = nP + d from by omega]
    rw [hopen] at hbA
    rw [denoteMeta_congr_eraseAnnots _ _
        ((Expr.instSeq (fvsP ++ fvs) (nP + d - 1 + 1) b').instantiate1
          (.fvar (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) ty)) 0)
        (by rw [ConLeche.Expr.eraseAnnots_instantiate1, ConLeche.Expr.eraseAnnots_instantiate1]; rfl),
      hopen] at hbA'
    have hF' := hF.snoc (Expr.instSeq (fvsP ++ fvs) (nP + d - 1) ty)
    rw [interp_pi, interp_pi, hty]
    refine piR_congr fun x hx => ?_
    have hwdb := hwd.2 x (by rw [hty]; exact hx)
    have := ihb hwb hres.2 hP hF' hbA hbA' as (xs ++ [x]) ρ₀ hsp
      (by rw [List.length_append, List.length_singleton, hxs])
      (by rw [consList_append, consList_cons, consList_nil]; exact hwdb)
    rw [consList_append, consList_cons, consList_nil] at this
    exact this
  | @letE d ty v b _ _ _ _ _ _ =>
    intro e' hw _ fvsP fvs _ _ A A' hA _ as xs ρ₀ _ _ _
    obtain ⟨ty', v', b', hle⟩ := instSeq_letE (fvsP ++ fvs) (nP + d - 1) ty v b
    rw [hle, denoteMeta] at hA
    exact nomatch hA
  | @proj d sn i x _ ihx =>
    intro e' hw hres fvsP fvs hP hF A A' hA hA' as xs ρ₀ hsp hxs hwd
    obtain ⟨x', hwx, rfl⟩ := ConLeche.restoreWalk_proj_inv hw
    rw [instSeq_proj] at hA hA'
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv hA
    obtain ⟨ia', hia', hcase'⟩ := denoteMeta_proj_inv hA'
    have hresx : x'.constsResolve envR = true := by
      have h : ((envR.find? sn).isSome && x'.constsResolve envR) = true := hres
      simp only [Bool.and_eq_true] at h
      exact h.2
    rcases hcase' with ⟨entry, hfpR, rfl⟩ | ⟨hfpR, hdec'⟩
    · have hfpA : envA.findProj? sn i = some entry := by rw [hag.projEq]; exact hfpR
      rcases hcase with ⟨entry₁, hfpA₁, rfl⟩ | ⟨hfpA₁, -⟩
      · obtain rfl : entry₁ = entry := Option.some.inj (hfpA₁.symm.trans hfpA)
        exact interp_projAV_congr
          (ihx hwx hresx hP hF hia hia' as xs ρ₀ hsp hxs
            (WellDenoted_projAV_hoist hwd))
      · rw [hfpA] at hfpA₁; exact nomatch hfpA₁
    · have hfpA : envA.findProj? sn i = none := by rw [hag.projEq]; exact hfpR
      rcases hcase with ⟨entry₁, hfpA₁, -⟩ | ⟨-, hdec⟩
      · rw [hfpA] at hfpA₁; exact nomatch hfpA₁
      · -- the pair decoder: `i` is `0` or `1`, and both nodes are congruences
        rcases i with _ | _ | i
        · obtain rfl : A = .fst ia := (Option.some.inj hdec).symm
          obtain rfl : A' = .fst ia' := (Option.some.inj hdec').symm
          rw [interp_fst, interp_fst, ihx hwx hresx hP hF hia hia' as xs ρ₀ hsp hxs
            (by rw [WellDenoted_fst] at hwd; exact hwd.1)]
        · obtain rfl : A = .snd ia := (Option.some.inj hdec).symm
          obtain rfl : A' = .snd ia' := (Option.some.inj hdec').symm
          rw [interp_snd, interp_snd, ihx hwx hresx hP hF hia hia' as xs ρ₀ hsp hxs
            (by rw [WellDenoted_snd] at hwd; exact hwd.1)]
        · exact nomatch hdec
  | @lit d l =>
    intro e' hw hres fvsP fvs _ _ A A' hA hA' as xs ρ₀ _ _ _
    rw [ConLeche.restoreWalk_lit] at hw
    obtain rfl := Except.ok.inj hw
    rw [Expr.instSeq_eq_self _ _ (e := Expr.lit l) rfl] at hA hA'
    obtain rfl := hag.litEq _ l hA hA'
    rfl
  | @const d n us hkeyn =>
    intro e' hw hres fvsP fvs _ _ A A' hA hA' as xs ρ₀ _ _ _
    by_cases hn : n ∈ R.auxNames
    · cases hr' : R.recMap.lookup n with
      | none =>
        -- an auxiliary name that is neither a key nor a renaming: the walk
        -- leaves it, and it does not resolve at the restored environment
        exfalso
        rw [ConLeche.restoreWalk_const_nonkey hkeyn hr'] at hw
        obtain rfl := Except.ok.inj hw
        have hcr : (Expr.const n us).constsResolve envR = true := hres
        rw [show (Expr.const n us).constsResolve envR
            = (envR.find? n).isSome from rfl, hag.auxFresh n hn] at hcr
        exact nomatch hcr
      | some n' =>
        rw [ConLeche.restoreWalk_const_rec hr' hn] at hw
        obtain rfl := Except.ok.inj hw
        rw [Expr.instSeq_eq_self _ _ (e := Expr.const n us) rfl] at hA
        rw [Expr.instSeq_eq_self _ _ (e := Expr.const n' us) rfl] at hA'
        cases hfA : envA.find? n with
        | none => rw [denoteMeta, hfA] at hA; exact nomatch hA
        | some ci =>
          obtain ⟨ci', hfR, hlps, hleaf⟩ := hag.recKey n n' hr' ci hfA
          rw [denoteMeta, hfA] at hA
          rw [denoteMeta, hfR] at hA'
          dsimp only at hA hA'
          by_cases hl : us.length = ci.toConstantVal.levelParams.length
          · rw [if_pos hl] at hA
            rw [if_pos (by rw [hlps]; exact hl)] at hA'
            obtain rfl := Option.some.inj hA
            obtain rfl := Option.some.inj hA'
            rw [hlps, hleaf]
          · rw [if_neg hl] at hA; exact nomatch hA
    · rw [ConLeche.restoreWalk_const_free hn] at hw
      obtain rfl := Except.ok.inj hw
      rw [Expr.instSeq_eq_self _ _ (e := Expr.const n us) rfl] at hA hA'
      cases hfA : envA.find? n with
      | none => rw [denoteMeta, hfA] at hA; exact nomatch hA
      | some ci =>
        obtain ⟨ci', hfR, hlps, hleafn⟩ := hag.leafSome n hn ci hfA
        rw [denoteMeta, hfA] at hA
        rw [denoteMeta, hfR] at hA'
        dsimp only at hA hA'
        by_cases hl : us.length = ci.toConstantVal.levelParams.length
        · rw [if_pos hl] at hA
          rw [if_pos (by rw [hlps]; exact hl)] at hA'
          obtain rfl := Option.some.inj hA
          obtain rfl := Option.some.inj hA'
          rw [hlps, hleafn]
        · rw [if_neg hl] at hA; exact nomatch hA
  | @bvar d i =>
    intro e' hw _ fvsP fvs hP hF A A' hA hA' as xs ρ₀ _ _ _
    rw [ConLeche.restoreWalk_bvar] at hw
    obtain rfl := Except.ok.inj hw
    have hV : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := hP.append hF
    rcases instSeq_bvar_cases (fvsP ++ fvs) (nP + d - 1) i hV.closed with ⟨x, hx, hxe⟩ | ⟨j, hj⟩
    · obtain ⟨k, hk'⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hV.2 k x hk'
      rw [hxe, denoteMeta_fvar] at hA hA'
      obtain rfl := Option.some.inj hA
      obtain rfl := Option.some.inj hA'
      rfl
    · rw [hj, denoteMeta_bvar] at hA
      exact nomatch hA
  | @sort d u =>
    intro e' hw _ fvsP fvs _ _ A A' hA hA' as xs ρ₀ _ _ _
    rw [ConLeche.restoreWalk_sort] at hw
    obtain rfl := Except.ok.inj hw
    rw [Expr.instSeq_eq_self _ _ (e := Expr.sort u) rfl, denoteMeta_sort] at hA hA'
    obtain rfl := Option.some.inj hA
    obtain rfl := Option.some.inj hA'
    rfl
  | @fvar d i ty =>
    intro e' hw _ fvsP fvs _ _ A A' hA hA' as xs ρ₀ _ _ _
    rw [ConLeche.restoreWalk_fvar] at hw
    obtain rfl := Except.ok.inj hw
    rw [instSeq_fvar_idx, denoteMeta_fvar] at hA hA'
    obtain rfl := Option.some.inj hA
    obtain rfl := Option.some.inj hA'
    rfl

end Walk

end ConLeche.Model
