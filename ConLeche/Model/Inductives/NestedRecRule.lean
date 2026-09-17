module

public import ConLeche.Model.Inductives.NestedRecsStore
public import ConLeche.Model.Inductives.MutualRecsLaw
public import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.MutualRecsProvision
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Inductives.MutualRecsSwap
import ConLeche.Model.Inductives.MutualRecsStore
import ConLeche.Model.Inductives.BlockRecBridge
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Verify.Inductives.NestedRecRuleKit
import ConLeche.Verify.Inductives.NestedRecFramesKit
import ConLeche.Verify.Inductives.NestedElimInv
public section

/-!
# The scratch recursors provisioned at OUR leaves (task #315, M7-2, item 5 step 2a)

The recursors' rule law (item 5 step 2) needs the auxiliary (scratch)
rule's right-hand side to READ at a model whose recursor leaves are
OUR chosen tuple's projections: the walk's reading law
`denoteMeta_restoreWalk` identifies the restored right-hand side with
the auxiliary one only when the two sides' recursor leaves agree
(`RestoreAgree.recKey`/`.leafSome`), and the restored side's leaves are
ours (`NestedTailIn.provisioned`).  The scratch install's own recursor
tuple is the auxiliary block model's; what the law wants is the scratch
environment consed with OURS.

That is legitimate because the two Π-towers are ONE SET at every frame
(`NestedTailIn.towerAgree`): our leaf, typed at the RESTORED reading,
is typed at the SCRATCH reading too.  Everything else is the mutual
provision's own assembly (`mutualRecsProvision`): the leaf's three laws
are `nestedRecLeaf_typed`/`_below`/`_params`, the front door is the
scratch run's shape (`checkMutualRecTys_inv`, `checkMutualRecTy_shape`)
with the names' freedom `nestedRecNames_of`, and the conses are
`recsProvision`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The restored recursors' provision, as a reading crossing

`BlockRepCross.lean`'s instance (i) (`provision_hde`) at the NESTED
route's loop.  The three extension facts are
`provisionNestedRecs_extend` (`Verify/Inductives/NestedRecRuleKit.lean`,
which needs no `SetTheory`); here they are fed to
`denoteMeta_env_mono`, exactly as the mutual twin does.
-/

/-- **The provisioned recursors, as an environment extension**
(`provisionMutualRecs_extend`'s twin over the read-back's TRIPLE list):
every stored lookup survives, the literal guards only grow, and no
projection table appears — the three facts `provisionNestedRecs_hde`
rests on.  It lives here, and not beside the kit's other
`provisionNestedRecs` lookup lemmas, because `LitGuardsMono` is a
MODEL-tier definition (`Model/Annot/BitExtend.lean`) — which is why
the mutual twin sits in `BlockRepCross.lean` too. -/
theorem provisionNestedRecs_extend :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env},
      (∀ x ∈ l, env.find? x.1.name = none) →
      (l.map (·.1.name)).Nodup →
      FindPreserved env (ConLeche.provisionNestedRecs l env) ∧
      LitGuardsMono env (ConLeche.provisionNestedRecs l env) ∧
      (∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.provisionNestedRecs l env).findProj? sn i = none)
  | [], _, _, _ => ⟨fun h => h, ⟨fun h => h, fun h => h⟩, fun _ _ h => h⟩
  | x :: rest, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hx : env.find? x.1.name = none := hfresh x List.mem_cons_self
    have hfresh' : ∀ g ∈ rest,
        (Env.mk (ConstantInfo.recInfo x.1 x.2.1 x.2.2 [] :: env.consts)).find? g.1.name = none := by
      intro g hg
      refine (find?_cons_of_name_ne (c := .recInfo x.1 x.2.1 x.2.2 [])
        (fun hh => ?_)).trans (hfresh g (List.mem_cons_of_mem _ hg))
      refine hnd.1 ?_
      have hnm : x.1.name = g.1.name := hh
      rw [hnm]
      exact List.mem_map_of_mem hg
    obtain ⟨hFp, hL, -⟩ := provisionNestedRecs_extend hfresh' hnd.2
    show FindPreserved env
        (ConLeche.provisionNestedRecs rest ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env.consts⟩) ∧ _
    exact ⟨fun h => hFp (findPreserved_cons hx h),
      ⟨fun h => hL.1 ((litGuardsMono_cons hx).1 h),
        fun h => hL.2 ((litGuardsMono_cons hx).2 h)⟩,
      fun sn i h => ConLeche.provisionNestedRecs_findProj?_none sn i h⟩

/-- **`hde` AT THE RESTORED PROVISION** (`provision_hde`'s twin over
the read-back's triples): the models' valuations agree at every stored
name, so a successful reading at the restored constructors'
environment is reproduced at the provisioned one. -/
theorem provisionNestedRecs_hde {l : List (ConstantVal × Nat × Nat)} {env : Env}
    {m : EnvModel V env} {mP : EnvModel V (ConLeche.provisionNestedRecs l env)}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none)
    (hnd : (l.map (·.1.name)).Nodup)
    (hag : ∀ n : Name, (env.find? n).isSome = true → mP.acval n = m.acval n) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m.acval env ψ dp e = some ea →
        denoteMeta mP.acval (ConLeche.provisionNestedRecs l env) ψ dp e = some ea := by
  obtain ⟨hFp, hG, hproj⟩ := provisionNestedRecs_extend hfresh hnd
  intro ψ dp e ea hread
  refine denoteMeta_env_mono hFp hG hproj dp e ?_
  rw [← denoteMeta_acval_congr (acval₂ := mP.acval) (fun n hn => (hag n hn).symm) dp e]
  exact hread

/-- **Class `c`'s restored rule list**: the member run's below `k`, the
mimic run's above (`nestedRecCvAt`'s twin at the rules). -/
@[expose] def nestedRulesAt (k : Nat) (rulesM rulesN : List (List RecRule)) (c : Nat) :
    List RecRule :=
  if c < k then rulesM.getD c [] else rulesN.getD (c - k) []

omit [SetTheory V] in
/-- The anonymous openers ARE openers. -/
theorem openersFrom_openFvars (k₀ n : Nat) : OpenersFrom (openFvars k₀ n) k₀ n :=
  ⟨openFvars_length k₀ n, fun i x hx => by
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [openFvars_getElem? hi] at hx
      exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
    · rw [List.getElem?_eq_none (by rw [openFvars_length]; exact hi)] at hx
      exact nomatch hx⟩

/-! ## A λ-tower's reading, with its bits (item 5 step 2e, the tower glue)

`stripLams_denotePTele` (`Model/IndProjKit.lean`) reads a λ-tower into
a `LamTele`, whose bits are EXISTENTIAL — and the fired equality folds
the tower, which needs them.  These two are the same move with the
bits kept: the reading of `λ bs, body` is `mkLamsAV` over the binders'
own codomain bits (one numeral, since the rule's parameter prefix
carries ONE binder datum) and the domains' readings.
-/

omit [SetTheory V] in
/-- **Instantiation distributes over a λ-tower's rebuild** (`stripLams_instantiate1_eq`
at the REBUILT form, which keeps the binder data on the nose). -/
theorem instantiate1_foldrLam (v : Expr) :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr) (j : Nat),
      ∃ bs' : List (Expr × BinderMeta),
        bs'.length = bs.length ∧
        (∀ (i : Nat) (x x' : Expr × BinderMeta), bs[i]? = some x → bs'[i]? = some x' →
          x'.1 = x.1.instantiate1 v (j + i) ∧ x'.2 = x.2) ∧
        (bs.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body).instantiate1 v j
          = bs'.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2)
              (body.instantiate1 v (j + bs.length))
  | [], body, j => by
    refine ⟨[], rfl, (fun i x x' hx _ => nomatch hx), ?_⟩
    show body.instantiate1 v j = body.instantiate1 v (j + 0)
    rw [Nat.add_zero]
  | x :: rest, body, j => by
    obtain ⟨bs'', hlen, hrel, heq⟩ := instantiate1_foldrLam v rest body (j + 1)
    refine ⟨(x.1.instantiate1 v j, x.2) :: bs'', by simp [hlen], ?_, ?_⟩
    · intro i y y' hy hy'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy hy'
        subst hy; subst hy'
        exact ⟨by rw [Nat.add_zero], rfl⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hy hy'
        obtain ⟨h1, h2⟩ := hrel i y y' hy hy'
        exact ⟨by rw [h1, show j + 1 + i = j + (i + 1) from by omega], h2⟩
    · show Expr.lam _ _ _ = _
      simp only [List.foldr_cons]
      rw [heq, show j + 1 + rest.length = j + (x :: rest).length from by simp; omega]

/-- **A λ-TOWER'S READING, WITH ITS BITS**: at a tower whose binders
carry ONE codomain bit, the reading is the `mkLamsAV` tower over that
bit and the domains' readings, each read at its own depth under the
standard openers, with the body read at the tower's depth. -/
theorem denoteMeta_foldrLam {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} (bt : Nat) :
    ∀ (n : Nat) (bs : List (Expr × BinderMeta)), bs.length = n →
      ∀ {body : Expr} {j : Nat} {E : AnnotTerm},
      (∀ y ∈ bs, pwBit φ y.2.pw = bt) →
      denoteMeta acval env φ j
          (bs.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body) = some E →
      ∃ (Γ : List AnnotTerm) (C : AnnotTerm),
        Γ.length = bs.length ∧
        E = mkLamsAV (Γ.map fun A => (bt, A)) C ∧
        (∀ (i : Nat) (y : Expr × BinderMeta), bs[i]? = some y →
          denoteMeta acval env φ (j + i)
            (Expr.instSeq (openFvars j i) (i - 1) y.1) = some (Γ.getD i default)) ∧
        denoteMeta acval env φ (j + bs.length)
          (Expr.instSeq (openFvars j bs.length) (bs.length - 1) body) = some C := by
  intro n
  induction n with
  | zero =>
    intro bs hlen body j E _ hE
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨[], E, rfl, rfl, (fun i y hy => nomatch hy), hE⟩
  | succ n ih =>
    intro bs hlen body j E hbt hE
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, bs = x :: rest := by
      cases bs with
      | nil => simp at hlen
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hrestlen : rest.length = n := by simpa using hlen
    rw [show (x :: rest).foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body
        = Expr.lam x.1 (rest.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body)
          x.2 from rfl, denoteMeta_lam] at hE
    cases hA : denoteMeta acval env φ j x.1 with
    | none => rw [hA] at hE; exact nomatch hE
    | some A => ?_
    rw [hA] at hE
    cases hB : denoteMeta acval env φ (j + 1)
        ((rest.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body).instantiate1
          (.fvar j x.1)) with
    | none => rw [hB] at hE; exact nomatch hE
    | some B => ?_
    rw [hB] at hE
    obtain rfl : E = .lam (pwBit φ x.2.pw) A B := by simpa using hE.symm
    -- re-open at the anonymous opener (the reading is blind to it)
    have hB' : denoteMeta acval env φ (j + 1)
        ((rest.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body).instantiate1
          (.fvar j (.sort .zero))) = some B := by
      rw [denoteMeta_erasedEq (ConLeche.Expr.ErasedEq.instantiate1
        (ConLeche.Expr.ErasedEq.rfl _) (show ConLeche.Expr.ErasedEq
            (.fvar j (.sort .zero)) (.fvar j x.1) from by constructor)) (j + 1)]
      exact hB
    obtain ⟨bs', hlen', hrel', heq'⟩ :=
      instantiate1_foldrLam (Expr.fvar j (.sort .zero)) rest body 0
    rw [heq'] at hB'
    have hbt' : ∀ y ∈ bs', pwBit φ y.2.pw = bt := by
      intro y hy
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
      obtain ⟨z, hz⟩ : ∃ z, rest[i]? = some z :=
        ⟨_, List.getElem?_eq_getElem (by
          have := (List.getElem?_eq_some_iff.mp hi).1
          rw [hlen'] at this; exact this)⟩
      rw [(hrel' i z y hz hi).2]
      exact hbt z (List.mem_cons_of_mem _ (List.mem_of_getElem? hz))
    obtain ⟨Γ', C, hΓlen, hshape, hdoms, hbody⟩ :=
      ih bs' (by rw [hlen', hrestlen]) hbt' hB'
    rw [hlen'] at hΓlen hbody
    refine ⟨A :: Γ', C, by simp [hΓlen], ?_, ?_, ?_⟩
    · rw [List.map_cons, mkLamsAV, hshape, hbt x List.mem_cons_self]
    · intro i y hy
      cases i with
      | zero =>
        obtain rfl : x = y := by simpa using hy
        exact hA
      | succ i =>
        rw [List.getElem?_cons_succ] at hy
        obtain ⟨y', hy'⟩ : ∃ y', bs'[i]? = some y' :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.mp hy).1
            rw [hlen']; exact this)⟩
        have h1 := hdoms i y' hy'
        rw [(hrel' i y y' hy hy').1, Nat.zero_add] at h1
        show denoteMeta acval env φ (j + (i + 1))
          (Expr.instSeq (openFvars j (i + 1)) (i + 1 - 1) y.1)
            = some ((A :: Γ').getD (i + 1) default)
        rw [show openFvars j (i + 1) = Expr.fvar j (.sort .zero) :: openFvars (j + 1) i from rfl,
          show Expr.instSeq (Expr.fvar j (.sort .zero) :: openFvars (j + 1) i) (i + 1 - 1) y.1
            = Expr.instSeq (openFvars (j + 1) i) (i - 1)
              (y.1.instantiate1 (Expr.fvar j (.sort .zero)) i) from rfl,
          show j + (i + 1) = j + 1 + i from by omega,
          show (A :: Γ').getD (i + 1) default = Γ'.getD i default from rfl]
        exact h1
    · show denoteMeta acval env φ (j + (rest.length + 1))
        (Expr.instSeq (openFvars j (rest.length + 1)) (rest.length + 1 - 1) body) = some C
      rw [show openFvars j (rest.length + 1)
          = Expr.fvar j (.sort .zero) :: openFvars (j + 1) rest.length from rfl,
        show Expr.instSeq (Expr.fvar j (.sort .zero) :: openFvars (j + 1) rest.length)
            (rest.length + 1 - 1) body
          = Expr.instSeq (openFvars (j + 1) rest.length) (rest.length - 1)
            (body.instantiate1 (Expr.fvar j (.sort .zero)) rest.length) from rfl,
        show j + (rest.length + 1) = j + 1 + rest.length from by omega]
      rw [Nat.zero_add] at hbody
      exact hbody

omit [SetTheory V] in
/-- A `stripLams` run exhibits its subject as the rebuilt λ-tower
(`stripPis_mkPisB`'s λ twin at the `foldr` form). -/
theorem stripLams_foldr : ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
    e.stripLams k = some (bs, body) →
      e = bs.foldr (fun (y : Expr × BinderMeta) acc => Expr.lam y.1 acc y.2) body
  | 0, e, bs, body, h => by
    simp only [ConLeche.Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]
    rfl
  | k + 1, e, bs, body, h => by
    match e, h with
    | .lam ty bodyE bm, h =>
      simp only [ConLeche.Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hs, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [List.foldr_cons, ← stripLams_foldr k hs]

omit [SetTheory V] in
/-- Two λ-towers of one length are equal only entry by entry
(`mkPisAV_inj`'s λ twin). -/
theorem mkLamsAV_inj :
    ∀ {l₁ l₂ : List (Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      l₁.length = l₂.length → mkLamsAV l₁ b₁ = mkLamsAV l₂ b₂ → l₁ = l₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: l₁, d₂ :: l₂, b₁, b₂, hlen, h => by
    simp only [mkLamsAV, AnnotTerm.lam.injEq] at h
    obtain ⟨hv, hA, hB⟩ := h
    obtain ⟨rfl, rfl⟩ := mkLamsAV_inj (by simpa using hlen) hB
    exact ⟨by congr 1; exact Prod.ext hv hA, rfl⟩

/-- **A λ-TOWER'S BODY IS GRADED** at every fitting spine's frame: the
tower's own grading, peeled along the fit. -/
theorem wellDenoted_mkLamsAV_body :
    ∀ {ds : List (Nat × AnnotTerm)} {C : AnnotTerm} {ρ : Nat → V} {as : List V},
      SpineFit ρ (ds.map (·.2)) as → WellDenoted V ρ (mkLamsAV ds C) →
        WellDenoted V (consList as ρ) C
  | [], _, _, [], _, h => h
  | [], _, _, _ :: _, hsp, _ => hsp.elim
  | _ :: _, _, _, [], hsp, _ => hsp.elim
  | d :: ds, C, ρ, a :: as, hsp, h => by
    have h' : WellDenoted V ρ (.lam d.1 d.2 (mkLamsAV ds C)) := h
    exact wellDenoted_mkLamsAV_body (ρ := cons a ρ) hsp.2 (h'.2.1 a hsp.1)

omit [SetTheory V] in
/-- The first of four appended segments is what the prefix takes. -/
theorem take_append₄ {α : Type} (l₁ l₂ l₃ l₄ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂ ++ l₃ ++ l₄).take n = l₁ := by
  rw [List.append_assoc, List.append_assoc, List.take_left' h]

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "ENV2" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- the COMPOSED nested block's block model -/
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- the SCRATCH (auxiliary) block's block model — the MUTUAL one -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

/-- the pins' constructors at the nested block model -/
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- the pin groups at the restored environment's model -/
local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-- **THE SCRATCH RECURSORS PROVISIONED AT OUR LEAVES** (PLAN-M7 §4b,
item 5 step 2a): the scratch block's `k` recursors consed RULE-LESS
onto the SCRATCH constructors' environment — the environment the
auxiliary rules were checked at — but with class `c`'s leaf OUR chosen
tuple's `c`-th projection (`nestedRecLeaf`) instead of the scratch
install's own.

The one thing to see is that our leaf is typed there: it is typed at
the RESTORED reading (`nestedRecLeaf_typed`), and the restored and the
scratch Π-towers are ONE SET at every frame
(`NestedTailIn.towerAgree`).  The rest is `mutualRecsProvision`'s
assembly at the scratch run's shape. -/
theorem NestedTailIn.scratchProv {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    (E : NestedRecEqs (D) PC (fun ψ => b.elimLevel.eval ψ) rdsM concM eqs)
    (Tu : NestedRecTuple (D) s rdsM concM eqs) :
    ∃ mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ∧
      (∀ c, c < b.k → MutualRecData mpP.base2 (cvRas.getD c default) (DA).nP (DA).k (DA).nCtors
        ((DA).nIdxAt c) c b.elimLevel ((DA).blockRds mpA.base2 b.elimLevel c)) ∧
      (∀ c, c < b.k → ∀ ψ : Name → Nat, mpP.base2.acval (cvRas.getD c default).name ψ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ) ∧
      (∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
        (cvRas.getD c default).levelParams = b.rlps) ∧
      (∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
        mpP.base2.acval nm = mpA.base2.acval nm) := by
  have hdk : (DA).k = b.k := S.record.k
  have hkT : (D).kT = b.k := I.kT
  have hlt : ∀ c, c < (DA).k → c < b.k := fun c hc => by rw [← hdk]; exact hc
  -- **the run shape** of the scratch recursor types (`mutualRecsProvision`'s `hshape`)
  obtain ⟨-, hallR⟩ := ConLeche.checkMutualRecTys_inv S.rectys
  have hshape : ∀ c, c < b.k →
      (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps ∧
      (cvRas.getD c default).type.hasFvar = false ∧
      (cvRas.getD c default).type.allLevelParamsDefined b.rlps = true ∧
      (cvRas.getD c default).type.looseBVarsBounded 0 = true ∧
      (cvRas.getD c default).type.constsResolve (ENVA) = true := by
    intro c hc
    obtain ⟨cvRa, hget, hrun⟩ := hallR c hc
    obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, -, rfl⟩ :=
      ConLeche.checkMutualRecTy_shape hrun
    rw [List.getD_eq_getElem?_getD, hget]
    exact ⟨rfl, rfl, hfv, hlp, hbv, hres⟩
  -- **the recursor names** are free at the scratch environment, reserved-free, not proj-shaped
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  -- **the names are distinct** (`mutualRecsProvision`'s `hnd`)
  have hnd : (cvRas.map (·.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun c => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases hc : c < b.k
      · have hcl : c < cvRas.length := by rw [S.cvLen]; exact hc
        rw [List.getElem?_range hc, List.getElem?_eq_getElem hcl]
        have hn := (hshape c hc).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **OUR leaf is typed at the SCRATCH reading**: the tower agreement
  have hleaf : ∀ c, c < (DA).k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ) ∧
      interp V ρ (nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ)
        ∈ˢ interp V ρ (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel c ψ)
          (mutualConcAV (DA).k (DA).nCtors ((DA).nIdxAt c) c)) := by
    intro c hc' ψ ρ
    have hc : c < b.k := hlt c hc'
    have hcT : c < (D).kT := by rw [hkT]; exact hc
    have h := nestedRecLeaf_typed R E Tu c hcT ψ ρ
    refine ⟨h.1, ?_⟩
    have hconc : (DA).blockConc c = mutualConcAV (DA).k (DA).nCtors ((DA).nIdxAt c) c := rfl
    have ht := I.towerAgree S hnames hctorsJ hK35 hc ψ ρ (NestedTailIn.readAtOf R hcT ψ)
      (I.lenAtOf R hc ψ)
    rw [← hconc, ← ht]
    exact h.2
  -- **the conses**
  obtain ⟨mpP, hEP, -, hRDP, hleafP, hagP⟩ :=
    recsProvision (k := (DA).k) (nP := (DA).nP) (n := (DA).nCtors) (nIdxOf := (DA).nIdxAt)
      (elimL := b.elimLevel) (rds := (DA).blockRds mpA.base2 b.elimLevel)
      (A := nestedRecLeaf (D).kT s rdsM concM eqs b.rlps) (b := b) (fms := fms) mpA
      (by rw [S.cvLen, hdk]) hleaf
      (fun c _ ψ => nestedRecLeaf_below R E c ψ)
      (fun c hc ψ₁ ψ₂ hφ =>
        nestedRecLeaf_params (by rw [← (hshape c (hlt c hc)).2.1]; exact hφ))
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).2.1)
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).2.2)
      (fun c hc => ⟨(hshape c (hlt c hc)).2.2.1,
        by rw [(hshape c (hlt c hc)).2.1]; exact (hshape c (hlt c hc)).2.2.2.1,
        (hshape c (hlt c hc)).2.2.2.2.1⟩)
      hnd
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).1)
      (fun c hc => (hshape c (hlt c hc)).2.2.2.2.2)
      S.etaA
      (fun c hc => (S.recData c (hlt c hc)).1)
  exact ⟨mpP, hEP, fun c hc => hRDP c (by rw [hdk]; exact hc),
    fun c hc ψ => hleafP c (by rw [hdk]; exact hc) ψ,
    fun c hc => ⟨(hshape c hc).1, (hshape c hc).2.1⟩,
    fun nm hn => hagP nm fun c hc => hn c (hlt c hc)⟩

/-! ## The rule's reading law: the two PROVISIONED environments (item 5 step 2c)

`NestedTailIn.restoreAgree` (`NestedRecFrames.lean`) is the walk's leaf
agreement at the SCRATCH constructors' model against the RESTORED
constructors' one.  That is the right pair for the recursor TYPES,
which mention no recursor name.  A RULE's right-hand side mentions all
`k + nPins` of them, so its law runs one environment later on each
side: the scratch recursors provisioned rule-less at OUR leaves
(`scratchProv`) against the restored ones (`NestedTailIn.provisioned`).

Every clause is either the old record's, transported by the two
provisions' "off the new names the model is the old one" reports, or a
new-name clause discharged by the two leaf reports being ONE function
of the class.  The class bridge is the names: below `p.k` a member's
restored recursor carries the SCRATCH name `b.recName c`
(`recCvNameM`), above it the mimic's carries `p.mimicRecName j`
(`recCvNameN`) while the scratch side keeps `q.aux.str "rec"` — which
is why `recKey` exists and why `leafSome` is stated at a name the
scratch side FINDS (`NestedRecWalk.lean`'s note).
-/

omit I in
/-- An answered key is an entry (`NestedRecFrames.lean`'s own, `private`
there). -/
private theorem rrLookupMem {β : Type} {a : Name} {v : β} :
    ∀ {l : List (Name × β)}, l.lookup a = some v → (a, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, w) :: l, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i he
      rw [beq_iff_eq] at he
      subst he
      rw [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (rrLookupMem h)

/-- **A COPY'S RECURSOR NAME IS ITS CLASS'S** (`pinAuxMem`'s
computation, named): the pin at `q` is the scratch block's member
`p.k + q` (`PinsAligned`), so that member's recursor name is
`q.aux.str "rec"`. -/
theorem NestedTailIn.recNameAux {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn) :
    b.recName (p.k + q) = qn.aux.str "rec" := by
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  obtain ⟨t, ht, htn⟩ := I.aligned.2 q qn hqn
  obtain ⟨nIdx, hfo, -⟩ := hform (p.k + q) t ht
  simp only [ConLeche.MutualBlock.recName, List.getD_eq_getElem?_getD, hfo, Option.getD_some, htn]

omit I in
/-- A copy's recursor name IS an auxiliary name — `auxNames`' third
component is that list, which is why the reading law's `const` case
reaches `recKey` and not `leafSome` at a mimic's scratch recursor. -/
theorem NestedTailIn.auxRecMem {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn) :
    qn.aux.str "rec" ∈ (ConLeche.restoreTbl p st).auxNames := by
  simp only [ConLeche.restoreTbl]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨qn, List.mem_of_getElem? hqn, rfl⟩)

/-- Below `p.k` the scratch block's member name is the DECLARED
member's (`auxBlock_memberNames`). -/
theorem NestedTailIn.memberNameAt {c : Nat} (hc : c < p.k) :
    (b.formers.getD c default).1.name = (p.formers.getD c default).1.name := by
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  obtain ⟨f, hf⟩ : ∃ f, b.formers[c]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by show c < b.k; omega)⟩
  obtain ⟨g, hg⟩ : ∃ g, p.formers[c]? = some g :=
    ⟨_, List.getElem?_eq_getElem (by exact hc)⟩
  have h1 : (b.memberNames.take p.k)[c]? = some f.1.name := by
    rw [List.getElem?_take_of_lt hc]
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hf, Option.map_some]
  have h2 : p.memberNames[c]? = some g.1.name := by
    simp only [ConLeche.NestedParts.memberNames, List.getElem?_map, hg, Option.map_some]
  rw [ConLeche.auxBlock_memberNames I.hfA I.helim I.hb, h2] at h1
  rw [List.getD_eq_getElem?_getD, hf, List.getD_eq_getElem?_getD, hg]
  exact (Option.some.inj h1).symm

/-- **A MEMBER'S RESTORED RECURSOR CARRIES THE SCRATCH NAME**: the
restore checked it at `T_c.rec` for the DECLARED member `T_c`
(`restoreRecTys_door`'s name clause), and below `p.k` the scratch
block's member IS that member (`memberNameAt`).  This is what makes
`leafSome` — not `recKey` — the clause a member's recursor goes
through. -/
theorem NestedTailIn.recCvNameM {c : Nat} (hc : c < p.k) :
    (nestedRecCvAt p.k cvRms cvRns c).name = b.recName c := by
  obtain ⟨o, ho⟩ : ∃ o, cvRms[c]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.lenM]; exact hc)⟩
  have hcv : nestedRecCvAt p.k cvRms cvRns c = o := by
    unfold nestedRecCvAt
    rw [if_pos hc, List.getD_eq_getElem?_getD, ho]
    rfl
  have hnm : ((List.range p.k).map fun mIdx =>
      ((p.formers.getD mIdx default).1.name.str "rec"))[c]?
      = some ((p.formers.getD c default).1.name.str "rec") := by
    rw [List.getElem?_map, List.getElem?_range hc]
    rfl
  obtain ⟨hname, -, -, -⟩ := ConLeche.restoreRecTys_door I.hrm c _ o hnm ho
  rw [hcv, hname]
  unfold ConLeche.MutualBlock.recName
  rw [I.memberNameAt hc]

/-- **A MIMIC'S RESTORED RECURSOR CARRIES THE MINTED NAME**
`p.mimicRecName j` — the `recMap`'s value at the scratch key
`q.aux.str "rec"`. -/
theorem NestedTailIn.recCvNameN {j : Nat} (hj : j < pinsS.length) :
    (nestedRecCvAt p.k cvRms cvRns (p.k + j)).name = p.mimicRecName j := by
  have hck : ¬ (p.k + j < p.k) := by omega
  obtain ⟨o, ho⟩ : ∃ o, cvRns[j]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.lenN]; exact hj)⟩
  have hcv : nestedRecCvAt p.k cvRms cvRns (p.k + j) = o := by
    unfold nestedRecCvAt
    rw [if_neg hck, show p.k + j - p.k = j from by omega, List.getD_eq_getElem?_getD, ho]
    rfl
  have hqn : j < p.numNested := by rw [← I.hcount, ← I.out.stage.pinsLen]; exact hj
  have hnm : ((List.range p.numNested).map p.mimicRecName)[j]? = some (p.mimicRecName j) := by
    rw [List.getElem?_map, List.getElem?_range hqn]
    rfl
  obtain ⟨hname, -, -, -⟩ := ConLeche.restoreRecTys_door I.hrn j _ o hnm ho
  rw [hcv, hname]

/-- The provision list's entries are FREE at the restored
constructors' environment (`recCvDoor`, positionally). -/
theorem NestedTailIn.provListFresh :
    ∀ x ∈ nestedProvList p stored cvRms cvRns,
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env)).find? x.1.name = none := by
  intro x hx
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hx
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  have hcb : c < b.k := by
    have hlt := (List.getElem?_eq_some_iff.mp hc).1
    rw [hlen] at hlt
    rw [I.out.bk]
    exact hlt
  rw [nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hc]
  exact (I.recCvDoor hcb).1

/-- The provision list's entry at class `c` (`nestedProvList_fst`, with
the position supplied). -/
theorem NestedTailIn.provListAt {c : Nat} (hc : c < b.k) :
    ∃ x ∈ nestedProvList p stored cvRms cvRns, x.1 = nestedRecCvAt p.k cvRms cvRns c := by
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  obtain ⟨x, hx⟩ : ∃ x, (nestedProvList p stored cvRms cvRns)[c]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen, ← I.out.bk]; exact hc)⟩
  exact ⟨x, List.mem_of_getElem? hx, nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hx⟩

/-- An entry of the provision list is some class's restored recursor. -/
theorem NestedTailIn.provListMem {x : ConstantVal × Nat × Nat}
    (hx : x ∈ nestedProvList p stored cvRms cvRns) :
    ∃ c, c < b.k ∧ x.1 = nestedRecCvAt p.k cvRms cvRns c := by
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hx
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  have hcb : c < b.k := by
    have hlt := (List.getElem?_eq_some_iff.mp hc).1
    rw [hlen] at hlt
    rw [I.out.bk]
    exact hlt
  exact ⟨c, hcb, nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hc⟩

/-- **THE RULE'S READING LAW: `RestoreAgree` AT THE TWO PROVISIONED
MODELS** (PLAN-M7 §4b, item 5 step 2c).

The scratch side is the auxiliary rules' own environment — the scratch
constructors' consed with the `k` scratch recursors, rule-less, AT OUR
LEAVES (`scratchProv`) — and the restored side the restored rules' own
(`NestedTailIn.provisioned`).  Every clause is the tail's record
(`NestedTailIn.restoreAgree`) transported by the two provisions'
"off the new names the model is the old one" reports, plus the
new-name clauses: a MEMBER's recursor is stored under the SAME name on
both sides and goes through `leafSome` (`recCvNameM`), a MIMIC's under
the scratch key on one side and `p.mimicRecName j` on the other and
goes through `recKey` (`recCvNameN`), and both carry OUR leaf at the
class, so the two leaf reports close them.

Two residues are hypotheses:

* `hauxNe` — no auxiliary name is a restored recursor name.  This is
  the KERNEL's to check (K.43, beside K.39): the mint's copy names and
  the mimics' `T₁.rec_j` are both `Name.appendIndexAfter`-shaped, so
  separating them needs `Nat.repr` injectivity, which is exactly why
  K.39 is a `decide` rather than a proof.  The Bool
  `decide ((restoreTbl p st).auxNames.all fun n =>
  !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n))` discharges
  it verbatim.
* `hlitP` — the literal readings agree at the provisioned pair.  The
  tail's `litAgree` is the same fact one environment down; crossing it
  needs the basis constants separated from the provisioned recursor
  names, which is the guards' own business (a recursor never satisfies
  `natIndOk`/`listConsTyOk`/…).
The pin arm's container and the constructor arm's restored
constructor are STORED at the restored constructors' environment —
a fact the arms know and, since they package `J`/`newName` inside an
existential, could not be asked for from outside: it is now ONE EXTRA
CONJUNCT of `NestedTailIn.pinArm`/`ctorArm` (the record's own field
drops it), which is why those two arms are consumed here directly
rather than through `hOld`. -/
theorem NestedTailIn.restoreAgreeP {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    (hleafR : ∀ c, c < (D).kT → ∀ φ : Name → Nat,
      mpP.base2.acval (nestedRecCvAt p.k cvRms cvRns c).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    (hauxNe : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, ∀ c, c < b.k →
      n ≠ (nestedRecCvAt p.k cvRms cvRns c).name)
    (ψ : Name → Nat) :
    RestoreAgree (V := V) (ConLeche.restoreTbl p st) b.lps (nestedArityK p st)
      mpAP.base2.acval mpP.base2.acval
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)
      ψ b.nP ((D).params ψ) := by
  have hkT : (D).kT = b.k := I.kT
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  have hOld := I.restoreAgree S hnames hctorsJ ψ
  have hpinArm := I.pinArm S ψ
  have hctorArm := I.ctorArm S hnames hctorsJ ψ
  rw [I.arityK] at hOld hpinArm hctorArm
  -- **the scratch recursor names are FREE** at the scratch constructors' environment
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  -- **the scratch provision's list**: its entries, their freshness, their distinctness
  have hzipMem : ∀ x ∈ cvRas.zipIdx, x.2 < b.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← S.cvLen]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hfreshA : ∀ x ∈ cvRas.zipIdx, (ENVA).find? x.1.name = none := by
    intro x hx
    rw [(hzipMem x hx).2, (hshapeA x.2 (hzipMem x hx).1).1]
    exact (hrecNames x.2 (hzipMem x hx).1).1
  have hndA : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun c => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases hc : c < b.k
      · have hcl : c < cvRas.length := by rw [S.cvLen]; exact hc
        rw [List.getElem?_range hc, List.getElem?_eq_getElem hcl]
        have hn := (hshapeA c hc).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **the restored provision's list**
  have hfresh3 := I.provListFresh
  have hnd3 : ((nestedProvList p stored cvRms cvRns).map (fun x => x.1.name)).Nodup := by
    rw [nestedProvList_names I.lenM I.lenN I.storedLen I.out.bk]
    exact hndR
  -- **the two provisions' lookups**
  have hfindA_ne : ∀ n : Name, (∀ c, c < b.k → n ≠ (cvRas.getD c default).name) →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? n = (ENVA).find? n := by
    intro n hn
    refine provisionMutualRecs_find?_of_ne (fun x hx => ?_)
    rw [(hzipMem x hx).2]
    exact hn x.2 (hzipMem x hx).1
  have hfindA_mem : ∀ c, c < b.k → ∃ mI rP : Nat,
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? (cvRas.getD c default).name
        = some (.recInfo (cvRas.getD c default) mI rP []) := by
    intro c hc
    have hmem : (cvRas.getD c default, c) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [S.cvLen]; exact hc)]
      rfl
    exact ⟨_, _, provisionMutualRecs_find?_mem hndA hmem⟩
  have hfindR_ne : ∀ n : Name, (∀ c, c < b.k → n ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find? n
        = (ENV2).find? n := by
    intro n hn
    refine ConLeche.provisionNestedRecs_find?_of_ne (fun x hx => ?_)
    obtain ⟨c, hc, hxe⟩ := I.provListMem hx
    rw [hxe]
    exact hn c hc
  have hfindR_mem : ∀ c, c < b.k → ∃ mI rP : Nat,
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
          (nestedRecCvAt p.k cvRms cvRns c).name
        = some (.recInfo (nestedRecCvAt p.k cvRms cvRns c) mI rP []) := by
    intro c hc
    obtain ⟨x, hx, hxe⟩ := I.provListAt hc
    refine ⟨x.2.1, x.2.2, ?_⟩
    rw [← hxe]
    exact ConLeche.provisionNestedRecs_find?_mem hnd3 hx
  -- **the two agreements at a STORED name** (a provisioned name is fresh below)
  have hagA2 : ∀ nm : Name, ((ENVA).find? nm).isSome = true →
      mpAP.base2.acval nm = mpA.base2.acval nm := by
    intro nm hnm
    refine hagA nm (fun c hc he => ?_)
    rw [he, (hshapeA c hc).1, (hrecNames c hc).1] at hnm
    simp at hnm
  have hagR2 : ∀ nm : Name, ((ENV2).find? nm).isSome = true →
      mpP.base2.acval nm = mp₂.base2.acval nm := by
    intro nm hnm
    refine hagR nm (fun c hc he => ?_)
    rw [hkT] at hc
    rw [he, (I.recCvDoor hc).1] at hnm
    simp at hnm
  -- **the restored reading crosses the restored provision**
  have hdeR := provisionNestedRecs_hde (m := mp₂.base2) (mP := mpP.base2) hfresh3 hnd3 hagR2
  -- **a mimic's SCRATCH recursor name is an auxiliary name**
  have hmimAux : ∀ c, c < b.k → ¬ c < p.k →
      (cvRas.getD c default).name ∈ (ConLeche.restoreTbl p st).auxNames := by
    intro c hc hck
    obtain ⟨j, rfl⟩ : ∃ j, c = p.k + j := ⟨c - p.k, by omega⟩
    have hjS : j < pinsS.length := by rw [hbk] at hc; omega
    have hjl : j < st.pins.length := by rw [← I.out.stage.pinsLen]; exact hjS
    obtain ⟨qn, hqn⟩ : ∃ qn, st.pins[j]? = some qn := ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [(hshapeA _ hc).1, I.recNameAux hqn]
    exact NestedTailIn.auxRecMem hqn
  -- **a restored recursor name that is no scratch one is FRESH below**
  have hrestFresh : ∀ (n : Name) (c : Nat), c < b.k →
      n = (nestedRecCvAt p.k cvRms cvRns c).name →
      (∀ c', c' < b.k → n ≠ (cvRas.getD c' default).name) → (ENV2).find? n = none := by
    intro n c hc hne hnotA
    by_cases hck : c < p.k
    · exact absurd (hne.trans ((I.recCvNameM hck).trans ((hshapeA c hc).1).symm)) (hnotA c hc)
    · obtain ⟨j, rfl⟩ : ∃ j, c = p.k + j := ⟨c - p.k, by omega⟩
      have hjS : j < pinsS.length := by rw [hbk] at hc; omega
      rw [hne, I.recCvNameN hjS]
      exact I.mimicRecFresh hjS
  -- **THE TWO CARRIERS AGREE AT A NAME BOTH PROVISIONED ENVIRONMENTS
  -- FIND** — which is what a literal's reading gives on both sides.  A
  -- MEMBER's recursor is the one name both provisions add, and there the
  -- two leaf reports are one function of the class; off it the name is
  -- stored below on both sides and the tail's record moves it.
  have hbothAg : ∀ m : Name,
      ((ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? m).isSome = true →
      ((ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
        (ENV2)).find? m).isSome = true →
      mpAP.base2.acval m = mpP.base2.acval m ∧
        ConLeche.Verify.levelParamsAt (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) m
          = ConLeche.Verify.levelParamsAt
            (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) m := by
    intro m hmA hmR
    -- an auxiliary name is absent from the restored provision
    have hnaux : m ∉ (ConLeche.restoreTbl p st).auxNames := by
      intro hmem
      rw [hfindR_ne m (fun c hc => hauxNe m hmem c hc), I.auxFresh m hmem] at hmR
      simp at hmR
    by_cases hrec : ∃ c, c < b.k ∧ m = (cvRas.getD c default).name
    · -- a SCRATCH recursor name, hence a MEMBER's (a mimic's is auxiliary)
      obtain ⟨c, hc, rfl⟩ := hrec
      have hck : c < p.k := by
        rcases Nat.lt_or_ge c p.k with hck | hck
        · exact hck
        · exact absurd (hmimAux c hc (by omega)) hnaux
      obtain ⟨mI, rP, hfA⟩ := hfindA_mem c hc
      obtain ⟨mI', rP', hfR⟩ := hfindR_mem c hc
      have hnmEq : (nestedRecCvAt p.k cvRms cvRns c).name = (cvRas.getD c default).name := by
        rw [I.recCvNameM hck, ← (hshapeA c hc).1]
      rw [hnmEq] at hfR
      refine ⟨?_, ?_⟩
      · funext φ
        rw [hleafA c hc φ, ← hnmEq]
        exact (hleafR c (by rw [hkT]; exact hc) φ).symm
      · show (match (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find?
              (cvRas.getD c default).name with
            | some ci => ci.toConstantVal.levelParams | none => [])
          = (match (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
              (ENV2)).find? (cvRas.getD c default).name with
            | some ci => ci.toConstantVal.levelParams | none => [])
        rw [hfA, hfR]
        show (cvRas.getD c default).levelParams = (nestedRecCvAt p.k cvRms cvRns c).levelParams
        rw [(hshapeA c hc).2, (I.classRecTy hc).1]
    · -- no provisioned name: the tail's record, transported
      have hne : ∀ c, c < b.k → m ≠ (cvRas.getD c default).name := fun c hc he => hrec ⟨c, hc, he⟩
      rw [hfindA_ne m hne] at hmA
      obtain ⟨ci, hfA⟩ := Option.isSome_iff_exists.mp hmA
      obtain ⟨ci', hf2, hlps, hleaf2⟩ := hOld.leafSome m hnaux ci hfA
      have hfR : (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ENV2)).find? m = some ci' := by
        rw [hfindR_ne m ?_]
        · exact hf2
        · intro c hc he
          rw [hrestFresh m c hc he hne] at hf2
          exact nomatch hf2
      refine ⟨?_, ?_⟩
      · rw [hagA2 m (by rw [hfA]; rfl), hagR2 m (by rw [hf2]; rfl)]
        exact hleaf2
      · show (match (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? m with
            | some ci => ci.toConstantVal.levelParams | none => [])
          = (match (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
              (ENV2)).find? m with
            | some ci => ci.toConstantVal.levelParams | none => [])
        rw [hfindA_ne m hne, hfA, hfR]
        exact hlps.symm
  -- a guard that fails at `none` answers only where the name is stored
  have hsomeOf : ∀ (f : Option ConstantInfo → Bool), f none = false →
      ∀ (e : Env) (m : Name), f (e.find? m) = true → (e.find? m).isSome = true := by
    intro f hf e m h
    cases hm : e.find? m with
    | none => rw [hm, hf] at h; exact nomatch h
    | some _ => rfl
  -- **`litEq` AT THE PROVISIONED PAIR** (`litAgree`'s shape: the
  -- readings are compared only where BOTH are `some`, and each side's
  -- guard is what says its environment finds the basis constant)
  have hlitP : ∀ (dpt : Nat) (l : ConLeche.Literal) {A A' : AnnotTerm},
      denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA) ψ dpt
          (.lit l) = some A →
      denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2) ψ dpt
          (.lit l) = some A' → A = A' := by
    intro dpt l A A' hA hA'
    cases l with
    | natVal n =>
      rw [denoteMeta] at hA hA'
      split at hA'
      · next hsupp =>
        split at hA
        · next hsuppA =>
          obtain rfl := Option.some.inj hA
          obtain rfl := Option.some.inj hA'
          simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hsupp hsuppA
          rw [(hbothAg _ (hsomeOf _ rfl _ _ hsuppA.1.2) (hsomeOf _ rfl _ _ hsupp.1.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hsuppA.2) (hsomeOf _ rfl _ _ hsupp.2)).1]
        · exact nomatch hA
      · exact nomatch hA'
    | strVal str =>
      rw [denoteMeta] at hA hA'
      split at hA'
      · next hsupp =>
        split at hA
        · next hsuppA =>
          obtain rfl := Option.some.inj hA
          obtain rfl := Option.some.inj hA'
          simp only [ConLeche.strLitSupported, ConLeche.natLitSupported,
            Bool.and_eq_true] at hsupp hsuppA
          obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hstr⟩, hsol⟩, hlist⟩, hnil⟩, hcons⟩, hchar⟩, hcon⟩ := hsupp
          obtain ⟨⟨⟨⟨⟨⟨⟨hnatA, hstrA⟩, hsolA⟩, hlistA⟩, hnilA⟩, hconsA⟩, hcharA⟩, hconA⟩ := hsuppA
          rw [(hbothAg _ (hsomeOf _ rfl _ _ hsolA) (hsomeOf _ rfl _ _ hsol)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnilA) (hsomeOf _ rfl _ _ hnil)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hconsA) (hsomeOf _ rfl _ _ hcons)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hcharA) (hsomeOf _ rfl _ _ hchar)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hconA) (hsomeOf _ rfl _ _ hcon)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnatA.1.2) (hsomeOf _ rfl _ _ hnat.1.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnatA.2) (hsomeOf _ rfl _ _ hnat.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnilA) (hsomeOf _ rfl _ _ hnil)).2,
            (hbothAg _ (hsomeOf _ rfl _ _ hconsA) (hsomeOf _ rfl _ _ hcons)).2]
        · exact nomatch hA
      · exact nomatch hA'
  refine
    { nPEq := I.tblNP
      leafSome := ?_
      auxFresh := ?_
      recKey := ?_
      recNone := ?_
      keyNotRec := I.keyNotRec
      projEq := ?_
      litEq := fun dpt l => hlitP dpt l
      pin := ?_
      ctor := ?_ }
  · -- **`leafSome`**
    intro n hn ci hfind
    by_cases hrec : ∃ c, c < b.k ∧ n = (cvRas.getD c default).name
    · -- a SCRATCH recursor name, hence (off the auxiliary names) a MEMBER's
      obtain ⟨c, hc, rfl⟩ := hrec
      have hck : c < p.k := by
        rcases Nat.lt_or_ge c p.k with hck | hck
        · exact hck
        · exact absurd (hmimAux c hc (by omega)) hn
      obtain ⟨mI, rP, hfR⟩ := hfindR_mem c hc
      obtain ⟨mI', rP', hfA⟩ := hfindA_mem c hc
      refine ⟨.recInfo (nestedRecCvAt p.k cvRms cvRns c) mI rP [], ?_, ?_, ?_⟩
      · rw [(hshapeA c hc).1, ← I.recCvNameM hck]
        exact hfR
      · obtain rfl : ConstantInfo.recInfo (cvRas.getD c default) mI' rP' [] = ci :=
          Option.some.inj (hfA.symm.trans hfind)
        show (nestedRecCvAt p.k cvRms cvRns c).levelParams = (cvRas.getD c default).levelParams
        rw [(I.classRecTy hc).1, (hshapeA c hc).2]
      · funext φ
        rw [hleafA c hc φ, (hshapeA c hc).1, ← I.recCvNameM hck]
        exact (hleafR c (by rw [hkT]; exact hc) φ).symm
    · -- not a scratch recursor name: the tail's record, transported
      have hne : ∀ c, c < b.k → n ≠ (cvRas.getD c default).name := fun c hc he => hrec ⟨c, hc, he⟩
      rw [hfindA_ne n hne] at hfind
      obtain ⟨ci', hf2, hlps, hleaf2⟩ := hOld.leafSome n hn ci hfind
      refine ⟨ci', ?_, hlps, ?_⟩
      · rw [hfindR_ne n ?_]
        · exact hf2
        · intro c hc he
          rw [hrestFresh n c hc he hne] at hf2
          exact nomatch hf2
      · rw [hagA2 n (by rw [hfind]; rfl), hagR2 n (by rw [hf2]; rfl)]
        exact hleaf2
  · -- **`auxFresh`**: the provision adds only the restored recursor names (K.43)
    intro n hn
    rw [hfindR_ne n (fun c hc => hauxNe n hn c hc)]
    exact I.auxFresh n hn
  · -- **`recKey`**: the class the two names share
    intro n n' hr ci hfind
    obtain ⟨j, qn, hqn, hnE, hn'E, hjS, hc⟩ :
        ∃ (j : Nat) (qn : NestedPin), st.pins[j]? = some qn ∧
          n = (cvRas.getD (p.k + j) default).name ∧
          n' = (nestedRecCvAt p.k cvRms cvRns (p.k + j)).name ∧
          j < pinsS.length ∧ p.k + j < b.k := by
      have hmem := rrLookupMem hr
      simp only [ConLeche.restoreTbl, List.mem_map] at hmem
      obtain ⟨⟨q', jq⟩, hqj, hpair⟩ := hmem
      obtain ⟨hn, hn'⟩ := Prod.mk.inj hpair
      have hqn : st.pins[jq]? = some q' := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hqj)
      have hjl : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqn).1
      have hjS : jq < pinsS.length := by rw [I.out.stage.pinsLen]; exact hjl
      have hc : p.k + jq < b.k := by rw [hbk]; omega
      exact ⟨jq, q', hqn,
        (((hshapeA _ hc).1.trans (I.recNameAux hqn)).trans hn).symm,
        ((I.recCvNameN hjS).trans hn').symm, hjS, hc⟩
    obtain ⟨mI, rP, hfR⟩ := hfindR_mem _ hc
    obtain ⟨mI', rP', hfA⟩ := hfindA_mem _ hc
    refine ⟨.recInfo (nestedRecCvAt p.k cvRms cvRns (p.k + j)) mI rP [], ?_, ?_, ?_⟩
    · rw [hn'E]; exact hfR
    · rw [hnE] at hfind
      obtain rfl : ConstantInfo.recInfo (cvRas.getD (p.k + j) default) mI' rP' [] = ci :=
        Option.some.inj (hfA.symm.trans hfind)
      show (nestedRecCvAt p.k cvRms cvRns (p.k + j)).levelParams
        = (cvRas.getD (p.k + j) default).levelParams
      rw [(I.classRecTy hc).1, (hshapeA _ hc).2]
    · funext φ
      rw [hnE, hn'E, hleafA _ hc φ]
      exact (hleafR _ (by rw [hkT]; exact hc) φ).symm
  · -- **`recNone`**: the scratch provision STORED the key
    intro n n' hr hnone
    exfalso
    have hmem := rrLookupMem hr
    simp only [ConLeche.restoreTbl, List.mem_map] at hmem
    obtain ⟨⟨q', jq⟩, hqj, hpair⟩ := hmem
    obtain ⟨hn, -⟩ := Prod.mk.inj hpair
    have hqn : st.pins[jq]? = some q' := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hqj)
    have hjl : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqn).1
    have hc : p.k + jq < b.k := by rw [hbk, ← I.out.stage.pinsLen] at *; omega
    obtain ⟨mI', rP', hfA⟩ := hfindA_mem _ hc
    rw [← hn, ← I.recNameAux hqn, ← (hshapeA _ hc).1, hfA] at hnone
    exact nomatch hnone
  · -- **`projEq`**: neither provision is a projection table
    intro sn i
    have hprojA : (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).findProj? sn i
        = (ENVA).findProj? sn i := by
      cases h : (ENVA).findProj? sn i with
      | none => exact (provisionMutualRecs_extend hfreshA hndA).2.2 sn i h
      | some entry =>
        obtain ⟨tbl, h0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
        exact ConLeche.Env.findProj?_of_table
          (provisionMutualRecs_findPreserved hfreshA _ _ h0) hi
    rw [hprojA, ConLeche.provisionNestedRecs_findProj?_eq hfresh3 sn i]
    exact hOld.projEq sn i
  · -- **`pin`**: the tail's arm, crossed to the two provisioned environments
    intro n pin hlook
    obtain ⟨hbnd, ci, J, ψJ, Ds, nIdx, hstJ, hfA, hlpsA, harity, hread, hident⟩ :=
      hpinArm n pin hlook
    have hJ : mpP.base2.acval J = mp₂.base2.acval J := hagR2 J hstJ
    have hnA : mpAP.base2.acval n = mpA.base2.acval n := hagA2 n (by rw [hfA]; rfl)
    refine ⟨hbnd, ci, J, ψJ, Ds, nIdx,
      provisionMutualRecs_findPreserved hfreshA n ci hfA, hlpsA, harity, ?_, ?_⟩
    · intro fvsP d hP
      rw [hJ]
      exact hdeR ψ (b.nP + d) _ (hread fvsP d hP)
    · intro d as xs ρ₀ Es hsp hxs hEs hwd
      rw [hJ] at hwd ⊢
      rw [hnA]
      exact hident d as xs ρ₀ Es hsp hxs hEs hwd
  · -- **`ctor`**: likewise, at the restored constructor's name
    intro n pin newName hfindc
    obtain ⟨hbnd, hpinNone, ci, J, ilvls, ψJ, Ds, nF, hstN, hfA, hlpsA, harity, hhead, hread,
      hident⟩ := hctorArm n pin newName hfindc
    have hJ : mpP.base2.acval newName = mp₂.base2.acval newName := hagR2 newName hstN
    have hnA : mpAP.base2.acval n = mpA.base2.acval n := hagA2 n (by rw [hfA]; rfl)
    refine ⟨hbnd, hpinNone, ci, J, ilvls, ψJ, Ds, nF,
      provisionMutualRecs_findPreserved hfreshA n ci hfA, hlpsA, harity, hhead, ?_, ?_⟩
    · intro fvsP fvs d hP hF
      rw [hJ]
      exact hdeR ψ (b.nP + d) _ (hread fvsP fvs d hP hF)
    · intro d as xs ρ₀ Fs hsp hxs hFs hwd
      rw [hJ] at hwd ⊢
      rw [hnA]
      exact hident d as xs ρ₀ Fs hsp hxs hFs hwd

/-! ## K.35's face AT THE RULES -/

omit I in
/-- **K.35's model face at the RULES** (the type half is
`NestedRecTysAuxOk`, `NestedRecFrames.lean`): every read-back rule's
right-hand side, below its `λ p⃗` prefix, has the shape the restore
walk relies on.  The restore strips exactly `R.nP` binders
(`restoreNested_lams`), so the walk's depth-`0` shape and the Bool's
`stripLams p.nP` agree on the nose. -/
@[expose] def NestedRulesAuxOk (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (stored : List AuxStored) : Prop :=
  ∀ (c : Nat) (a : AuxStored), stored[c]? = some a → ∀ rl ∈ a.rules,
    ∃ (lbs : List (Expr × BinderMeta)) (body : Expr),
      rl.rhs.stripLams b.nP = some (lbs, body) ∧
      ConLeche.AuxAppsOk (ConLeche.restoreTbl p st) b.lps (nestedArityK p st) 0 body

omit I in
/-- **AND IT COMES FROM THE SAME BOOL**: K.35's `nestedAuxAppsOk` is a
conjunction — the recursor type's shape AND every rule's
(`Kernel/Inductives/NestedInstall.lean:1359`) — so the rules' half is
`hall.2` where `nestedRecTysAuxOk_of_bool` reads `hall.1`.  No kernel
work: the record already covers the rules. -/
theorem nestedRulesAuxOk_of_bool (hb : ConLeche.auxBlock p st = some b)
    (h : ConLeche.nestedAuxAppsOk p st stored = true) :
    NestedRulesAuxOk p st b stored := by
  obtain ⟨hnP, hlps, -, -⟩ := ConLeche.auxBlock_fields hb
  intro c a ha rl hrl
  have hmem : a ∈ stored := List.mem_of_getElem? ha
  have hall : ((match a.cvRa.type.stripPis p.nP with
      | some (_, body) => ConLeche.auxAppsOk (ConLeche.restoreTbl p st) p.lps
          (nestedArityK p st) 0 body
      | none => false) &&
      a.rules.all fun rl =>
        match rl.rhs.stripLams p.nP with
        | some (_, body) => ConLeche.auxAppsOk (ConLeche.restoreTbl p st) p.lps
            (nestedArityK p st) 0 body
        | none => false) = true := List.all_eq_true.mp h a hmem
  simp only [Bool.and_eq_true] at hall
  have hrule := List.all_eq_true.mp hall.2 rl hrl
  cases hs : rl.rhs.stripLams p.nP with
  | none => rw [hs] at hrule; exact nomatch hrule
  | some pr =>
    obtain ⟨lbs, body⟩ := pr
    rw [hs] at hrule
    refine ⟨lbs, body, by rw [hnP]; exact hs, ?_⟩
    rw [hlps]
    exact ConLeche.auxAppsOk_reflect body 0 hrule

/-! ## The auxiliary rule, generated and read (item 5 step 2d)

The rule law runs between the TWO PROVISIONED models (§U.29 (ee)), and
its right-hand side is the AUXILIARY rule's restored.  So the auxiliary
rule has to be identified with the scratch install's generated one
(`auxStored_rules_eq`, the door's twin at the rules) and read at the
scratch provision AT OUR LEAVES (`ruleRhs_read_of`, which is already
stated at an arbitrary `EnvModel`).
-/

/-- **THE READ-BACK'S RULE IS THE SCRATCH INSTALL'S GENERATED ONE**:
a rule of the read-back's recursor at class `c` is one of class `c`'s
constructors' — the block model's constructor at some position `i`,
the rule's own six fields, and the generated right-hand side at the
block position `minorIdx c i` (`auxStored_rules_eq` for the rule list,
`mutualRules_mem_shape` for the fields, `memberRule_of` for the
generator), with the formers'/constructors'/kinds' runs identified with
the tail's by determinism. -/
theorem NestedTailIn.auxRuleGen {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {c : Nat} (hc : c < b.k) {a : AuxStored} (ha : stored[c]? = some a)
    {rl : RecRule} (hrl : rl ∈ a.rules) :
    ∃ (i : Nat) (cA : ConstantVal × Nat), ((DA).ctorsM c)[i]? = some cA ∧
      rl.ctor = cA.1.name ∧ rl.nfields = cA.2 ∧ rl.ctorParams = b.nP ∧
      rl.paramsBlind = true ∧ cA.1.levelParams = b.lps ∧
      ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
          (ConLeche.mutualGenData b fms ctorsA kinds).1
          (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
          (b.rlps.map Level.param) ((DA).minorIdx c i) = some rl.rhs ∧
      rl.rhs.allLevelParamsDefined b.rlps = true ∧
      rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.hasFvar = false := by
  obtain ⟨fms', f₀', ctorsA', sortss', kinds', cvRas', rulesOf, hformers', hf₀', hctors', hkinds',
    hrules, -, -, hrulesEq⟩ := ConLeche.auxStored_rules_eq I.haux I.hstored ha
  -- the runs are the tail's own
  have hfms : fms = fms' := congrArg Prod.snd (Except.ok.inj (I.out.formers.symm.trans hformers'))
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀')
  subst hf0
  have hctA : (ctorsA, sortss) = (ctorsA', sortss') :=
    Except.ok.inj (I.out.ctors.symm.trans hctors')
  have hcA : ctorsA = ctorsA' := congrArg Prod.fst hctA
  subst hcA
  have hkd : kinds = kinds' := Except.ok.inj (I.out.kindsRun.symm.trans hkinds')
  subst hkd
  -- the member's own stage of the rules' run
  obtain ⟨-, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
  obtain ⟨rules, hget, hrun⟩ := hallU c hc
  have hrulesD : rulesOf.getD c [] = rules := by rw [List.getD_eq_getElem?_getD, hget]; rfl
  rw [hrulesEq, hrulesD] at hrl
  obtain ⟨cr, hcr, kb, eb, rfl⟩ := mutualRules_mem_shape hrl
  -- the constructor and the generator
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  obtain ⟨i, cA, hi, hnm, hnF, hlps, hgen, hlpsRhs, -, hbv, hfv⟩ :=
    memberRule_of S.record (ConLeche.checkMutualCore_inv I.haux).2.2.2.1 hlenA hnamesA hc hrun hcr
  exact ⟨i, cA, hi, hnm.symm, hnF.symm, rfl, rfl, hlps, hgen, hlpsRhs, hbv, hfv⟩

/-- **THE AUXILIARY RULE'S RIGHT-HAND SIDE READS AT OUR LEAVES**: at
the SCRATCH provision (`scratchProv` — the scratch constructors'
environment consed with the `k` scratch recursors carrying OUR chosen
tuple's projections) the generated right-hand side reads to the
λ-tower `ruleRhsAV` over the rule's binder data with `nestedRecLeaf`
as the recursors.  Pure assembly: `ruleRhs_read_of` is stated at an
arbitrary `EnvModel`, its three model hypotheses are the scratch
ones crossed over the provision (`IsBlockModels.crossEnv`,
`MemberStored.crossEnv`, whose four premises are
`provisionMutualRecs_extend`, `constsResolve_of_findPreserved`,
`scratchProv`'s own agreement and `provision_hde`), and the leaves are
rewritten by `scratchProv`'s leaf report. -/
theorem NestedTailIn.auxRuleRead {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    {c : Nat} (hc : c < b.k) {i : Nat} {cA : ConstantVal × Nat}
    (hi : ((DA).ctorsM c)[i]? = some cA) {rhs : Expr}
    (hgen : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
      (ConLeche.mutualGenData b fms ctorsA kinds).1
      (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
      (b.rlps.map Level.param) ((DA).minorIdx c i) = some rhs)
    (ψ : Name → Nat) :
    denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ψ 0 rhs
      = some ((DA).ruleRhsAV mpA.base2 b.elimLevel
          (fun t' => nestedRecLeaf (D).kT s rdsM concM eqs b.rlps t' ψ) c i cA.2 ψ) := by
  have hkT : (D).kT = b.k := I.kT
  have hdk : (DA).k = b.k := S.record.k
  have h0k : 0 < b.k := by
    have := I.kpos
    have := I.out.bk
    omega
  -- **the scratch provision's list**: its entries, their freshness, their distinctness
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  have hzipMem : ∀ x ∈ cvRas.zipIdx, x.2 < b.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← S.cvLen]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hfreshA : ∀ x ∈ cvRas.zipIdx, (ENVA).find? x.1.name = none := by
    intro x hx
    rw [(hzipMem x hx).2, (hshapeA x.2 (hzipMem x hx).1).1]
    exact (hrecNames x.2 (hzipMem x hx).1).1
  have hndA : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun t => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases ht : t < b.k
      · have htl : t < cvRas.length := by rw [S.cvLen]; exact ht
        rw [List.getElem?_range ht, List.getElem?_eq_getElem htl]
        have hn := (hshapeA t ht).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **the crossing** of the scratch model over the provision
  obtain ⟨hFP, -, -⟩ := provisionMutualRecs_extend (b := b) (fms := fms) hfreshA hndA
  have hF₁ : ∀ (n : Name) (ci : ConstantInfo), (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (ENVA).find? n = some ci →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? n = some ci :=
    fun _ _ _ h => hFP h
  have hagA2 : ∀ nm : Name, ((ENVA).find? nm).isSome = true →
      mpAP.base2.acval nm = mpA.base2.acval nm := by
    intro nm hnm
    refine hagA nm (fun c' hc' he => ?_)
    rw [he, (hshapeA c' hc').1, (hrecNames c' hc').1] at hnm
    simp at hnm
  have hdeA := provision_hde (m := mpA.base2) (mP := mpAP.base2) hfreshA hndA hagA2
  have hrepsP : IsBlockModels mpAP.base2 (DA) :=
    S.reps.crossEnv hF₁ (constsResolve_of_findPreserved hFP) hagA2 hdeA
  have hstoredP : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mpAP.base2 b.lps b.nP f (DA).resSort ((DA).ppsM t) :=
    fun t f hf => (S.memberStored t f hf).crossEnv hF₁ hdeA
  -- **the recursor table at the provision**, with OUR leaves
  have hfR : ∀ t, t < (DA).k → ∃ ci : ConstantInfo,
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? (b.recName t) = some ci ∧
      ci.toConstantVal.levelParams = b.rlps := by
    intro t ht
    rw [hdk] at ht
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [S.cvLen]; exact ht)]
      rfl
    refine ⟨.recInfo (cvRas.getD t default) (b.rulePrefix + (fms.getD t default).nIdx)
      b.rulePrefix [], ?_, (hshapeA t ht).2⟩
    rw [← (hshapeA t ht).1]
    exact provisionMutualRecs_find?_mem hndA hmem
  -- **the reading**, and then the leaves rewritten
  rw [ruleRhs_read_of S.record rfl I.out.facts.lenFms h0k
    (ConLeche.checkMutualCore_inv I.haux).2.2.1 (ConLeche.checkMutualCore_inv I.haux).2.2.2.1
    I.out.facts.lenA I.out.facts.lenK
    (ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1).2
    (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩) hrepsP hstoredP hfR (by rw [hdk]; exact hc) hi hgen ψ]
  unfold BlockModel.ruleRhsAV BlockModel.ruleData
  congr 2
  · -- the binder data: the members' and constructors' leaves are the scratch model's
    rw [mutualRuleDataAV_congr (m₂ := mpA.base2) fun cd hcd => by
      obtain ⟨c', j', cA', hc', hj', hname⟩ := (DA).mem_recCds hcd
      obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := S.reps c' hc'
      rw [hname]
      exact congrFun (hagA2 _ (by rw [(hrep.ctors c' j' cA' hc' hj').1]; rfl)) ψ]
    congr 1
    unfold BlockModel.recLs
    refine List.map_congr_left fun t' ht' => ?_
    have ht'' : t' < (DA).k := List.mem_range.mp ht'
    rw [hdk] at ht''
    have ht''' : t' < fms.length := by rw [I.out.facts.lenFms]; exact ht''
    have hfind := (S.memberStored t' (fms.getD t' default)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht''']; rfl)).find
    have hname : (DA).memberName t' = (fms.getD t' default).cvTa.name :=
      mutualBlockModel_memberName
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht''']; rfl)
    exact congrFun (hagA2 _ (by rw [hname, hfind]; rfl)) ψ
  · -- the core: the recursors are OUR leaves
    refine mutualRuleCoreAV_congr_Rof fun i' hi'' => ?_
    obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := S.reps c (by rw [hdk]; exact hc)
    have hj' : i < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hi).1
    have htgt := hrep.tgt_lt hj' (mem_recIdxOf.mp hi'').1 S.record.pins
    rw [hdk] at htgt
    rw [← (hshapeA _ htgt).1]
    exact hleafA _ htgt ψ

/-! ## The restored rule, at the run and read (item 5 step 2d (C)) -/

/-- **THE RESTORED RULES OF CLASS `c` ARE THE RUN'S**: the two `mapM`s
of `restoreRules` (`hrulesM` below `k`, `hrulesN` above) at class `c`,
stated once through `nestedRecCvAt`/`nestedRulesAt` with the mimic flag
`decide (p.k ≤ c)` and the environment the provision's
(`I.henv` moving the formers' spelling). -/
theorem NestedTailIn.restRulesRun {c : Nat} (hc : c < b.k) {a : AuxStored}
    (ha : stored[c]? = some a) :
    ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2))
        (ConLeche.restoreTbl p st) (nestedRecCvAt p.k cvRms cvRns c).levelParams
        (nestedRecCvAt p.k cvRms cvRns c).name (decide (p.k ≤ c))
        (nestedRecCvAt p.k cvRms cvRns c).type a.mI a.rP a.rules
      = .ok (nestedRulesAt p.k rulesM rulesN c) := by
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  by_cases hck : c < p.k
  · -- a MEMBER's recursor
    have hcvl : c < cvRms.length := by rw [I.lenM]; exact hck
    have hcv : cvRms[c]? = some (nestedRecCvAt p.k cvRms cvRns c) := by
      unfold nestedRecCvAt
      rw [if_pos hck, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcvl]
      rfl
    have hst : (stored.take p.k)[c]? = some a := by
      rw [List.getElem?_take_of_lt hck]; exact ha
    have hzip : (cvRms.zip (stored.take p.k))[c]? = some (nestedRecCvAt p.k cvRms cvRns c, a) := by
      rw [List.zip, List.getElem?_zipWith, hcv, hst]
    obtain ⟨-, hall⟩ := ConLeche.mapM_except_inv I.hrulesM
    obtain ⟨x, out, hx, hout, hrun⟩ := hall c (by
      rw [List.length_zip, List.length_take, I.lenM, I.storedLen, hbk]
      omega)
    obtain rfl : x = (nestedRecCvAt p.k cvRms cvRns c, a) := Option.some.inj (hx.symm.trans hzip)
    rw [show nestedRulesAt p.k rulesM rulesN c = out from by
      unfold nestedRulesAt
      rw [if_pos hck, List.getD_eq_getElem?_getD, hout]
      rfl,
      show (decide (p.k ≤ c)) = false from by simp only [decide_eq_false_iff_not]; omega]
    rw [I.henv] at hrun
    exact hrun
  · -- a MIMIC's
    have hq : c - p.k < pinsS.length := by omega
    have hcvl : c - p.k < cvRns.length := by rw [I.lenN]; exact hq
    have hcv : cvRns[c - p.k]? = some (nestedRecCvAt p.k cvRms cvRns c) := by
      unfold nestedRecCvAt
      rw [if_neg hck, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcvl]
      rfl
    have hst : (stored.drop p.k)[c - p.k]? = some a := by
      rw [List.getElem?_drop, show p.k + (c - p.k) = c from by omega]
      exact ha
    have hzip : (cvRns.zip (stored.drop p.k))[c - p.k]?
        = some (nestedRecCvAt p.k cvRms cvRns c, a) := by
      rw [List.zip, List.getElem?_zipWith, hcv, hst]
    obtain ⟨-, hall⟩ := ConLeche.mapM_except_inv I.hrulesN
    obtain ⟨x, out, hx, hout, hrun⟩ := hall (c - p.k) (by
      rw [List.length_zip, List.length_drop, I.lenN, I.storedLen, hbk]
      omega)
    obtain rfl : x = (nestedRecCvAt p.k cvRms cvRns c, a) := Option.some.inj (hx.symm.trans hzip)
    rw [show nestedRulesAt p.k rulesM rulesN c = out from by
      unfold nestedRulesAt
      rw [if_neg hck, List.getD_eq_getElem?_getD, hout]
      rfl,
      show (decide (p.k ≤ c)) = true from by simp only [decide_eq_true_eq]; omega]
    rw [I.henv] at hrun
    exact hrun

/-! ## The transfer at the rule's body (item 5 step 2d (D)) -/

omit I in
/-- A λ-tower resolves exactly when its body and domains do. -/
private theorem constsResolve_lamTower {envR : Env} :
    ∀ (bs : List (Expr × BinderMeta)) {body : Expr},
      (bs.foldr (fun (b : Expr × BinderMeta) acc => Expr.lam b.1 acc b.2) body).constsResolve envR
        = true → body.constsResolve envR = true
  | [], _, h => h
  | x :: rest, body, h => by
    have h' : (Expr.lam x.1
        (rest.foldr (fun (b : Expr × BinderMeta) acc => Expr.lam b.1 acc b.2) body) x.2).constsResolve
          envR = true := h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h'
    exact constsResolve_lamTower rest h'.2

/-- **THE RULE'S TRANSFER** (item 5 step 2d (D), the step's only new
mathematics): the restored rule's right-hand side is the auxiliary
one's λ prefix put back over the WALK of its body
(`restoreNested_lams`, the prefix untouched), and the two bodies —
read at the two PROVISIONED models under any parameter openers —
interpret alike at every frame fitting the block's parameters at which
the restored body is graded.  That is `denoteMeta_restoreWalk` at
`restoreAgreeP` and K.35's rules face (`NestedRulesAuxOk`), with
`d := 0` and no openers below the parameters.

The two readings are the consumer's to supply, exactly as
`domAgree_transfer`'s `hread` is at the recursor type: the λ prefix's
own tower is the fired equality's business (step 2e), which folds it. -/
theorem NestedTailIn.ruleAgree {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    (hleafR : ∀ c, c < (D).kT → ∀ φ : Name → Nat,
      mpP.base2.acval (nestedRecCvAt p.k cvRms cvRns c).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    (hauxNe : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, ∀ c, c < b.k →
      n ≠ (nestedRecCvAt p.k cvRms cvRns c).name)
    (hK35r : NestedRulesAuxOk p st b stored)
    (ψ : Name → Nat)
    {c : Nat} {a : AuxStored} (ha : stored[c]? = some a)
    {rl o : RecRule} (hrl : rl ∈ a.rules)
    (hres : ConLeche.restoreNested (ConLeche.restoreTbl p st) rl.rhs = .ok o.rhs)
    (hresolve : o.rhs.constsResolve
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) = true) :
    ∃ (bs : List (Expr × BinderMeta)) (bodyA bodyR : Expr),
      rl.rhs.stripLams b.nP = some (bs, bodyA) ∧
      o.rhs = bs.foldr (fun (x : Expr × BinderMeta) acc => Expr.lam x.1 acc x.2) bodyR ∧
      ∀ (fvsP : List Expr), OpenersFrom fvsP 0 b.nP →
      ∀ {A A' : AnnotTerm},
        denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ψ
            b.nP (Expr.instSeq fvsP (b.nP - 1) bodyA) = some A →
        denoteMeta mpP.base2.acval
            (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ
            b.nP (Expr.instSeq fvsP (b.nP - 1) bodyR) = some A' →
        ∀ (as : List V) (ρ₀ : Nat → V), SpineFit ρ₀ ((D).params ψ) as →
          WellDenoted V (consList as ρ₀) A' →
          interp V (consList as ρ₀) A' = interp V (consList as ρ₀) A := by
  have hnP : (ConLeche.restoreTbl p st).nP = b.nP := I.tblNP
  obtain ⟨bs, bodyA, hstrip, hshape⟩ := hK35r c a ha rl hrl
  -- the rule's own λ prefix, at a positive parameter count
  have hlam : 0 < (ConLeche.restoreTbl p st).nP → ∃ ty bb bm, rl.rhs = .lam ty bb bm := by
    intro hpos
    rw [hnP] at hpos
    obtain ⟨n', hn'⟩ : ∃ n', b.nP = n' + 1 := ⟨b.nP - 1, by omega⟩
    rw [hn'] at hstrip
    cases hrhs : rl.rhs <;> rw [hrhs] at hstrip <;>
      first
        | exact ⟨_, _, _, rfl⟩
        | simp [Expr.stripLams] at hstrip
  obtain ⟨bodyR, hw, hfold⟩ :=
    ConLeche.restoreNested_lams (by rw [hnP]; exact hstrip) hlam hres
  refine ⟨bs, bodyA, bodyR, hstrip, hfold, ?_⟩
  intro fvsP hP A A' hA hA' as ρ₀ hsp hwd
  have hresBody : bodyR.constsResolve
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) = true := by
    rw [hfold] at hresolve
    exact constsResolve_lamTower bs hresolve
  have hag := I.restoreAgreeP S hnames hctorsJ hndR hshapeA hleafA hagA hleafR hagR hauxNe ψ
  have hF : OpenersFrom ([] : List Expr) b.nP 0 := ⟨rfl, fun i x hx => nomatch hx⟩
  have hA2 : denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ψ
      (b.nP + 0) (Expr.instSeq (fvsP ++ []) (b.nP + 0 - 1) bodyA) = some A := by
    rw [List.append_nil, Nat.add_zero]; exact hA
  have hA2' : denoteMeta mpP.base2.acval
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ
      (b.nP + 0) (Expr.instSeq (fvsP ++ []) (b.nP + 0 - 1) bodyR) = some A' := by
    rw [List.append_nil, Nat.add_zero]; exact hA'
  have h := denoteMeta_restoreWalk (ConLeche.restoreTbl_keysInAux p st) hag hshape hw hresBody
    hP hF hA2 hA2' as [] ρ₀ hsp rfl (by rw [consList_nil]; exact hwd)
  rw [consList_nil] at h
  exact h

/-! ## The λ prefix, read (item 5 step 2e, step 1 — the tower glue) -/

/-- **THE RESTORED PROVISION'S READING CROSSING**: `provisionNestedRecs_hde`
at the tail's own freshness (`provListFresh`) and distinctness reports —
`restoreAgreeP`'s own `hdeR`, named so that the tower glue can take it
too. -/
theorem NestedTailIn.provCross
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mp₂.base2.acval (ENV2) ψ dp e = some ea →
        denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ dp e
          = some ea := by
  have hnd3 : ((nestedProvList p stored cvRms cvRns).map (fun x => x.1.name)).Nodup := by
    rw [nestedProvList_names I.lenM I.lenN I.storedLen I.out.bk]
    exact hndR
  refine provisionNestedRecs_hde (m := mp₂.base2) (mP := mpP.base2) I.provListFresh hnd3 ?_
  intro nm hnm
  refine hagR nm (fun c hc he => ?_)
  rw [I.kT] at hc
  rw [he, (I.recCvDoor hc).1] at hnm
  simp at hnm

/-- **THE GENERATED RULE'S λ PREFIX IS THE FIRST FORMER'S PARAMETER
TELESCOPE** (`auxRecParamDoms`'s twin at the rules): the prefix's
domains are `f₀.cvTa.type`'s (`mutualRecRhs_paramPrefix` at the tail's
own generated data) and every one of its binders carries the
elimination's datum. -/
theorem NestedTailIn.ruleParamDoms {i : Nat} {rhs : Expr}
    (hgen : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
      (ConLeche.mutualGenData b fms ctorsA kinds).1
      (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
      (b.rlps.map Level.param) i = some rhs)
    {bs : List (Expr × BinderMeta)} {bodyA : Expr}
    (hstrip : rhs.stripLams b.nP = some (bs, bodyA)) :
    ∃ (pbs : List (Expr × BinderMeta)) (bodyF : Expr),
      f₀.cvTa.type.stripPis b.nP = some (pbs, bodyF) ∧
      bs.map (·.1) = pbs.map (·.1) ∧
      ∀ y ∈ bs, y.2 = (⟨Level.zeronessOf b.elimLevel⟩ : BinderMeta) := by
  have hfirst : (ConLeche.mutualGenData b fms ctorsA kinds).1[0]?
      = some ⟨f₀.cvTa.name, f₀.nIdx, f₀.cvTa.type⟩ := by
    show (fms.map _)[0]? = _
    rw [List.getElem?_map, I.out.facts.first]
    rfl
  obtain ⟨pbs, bodyF, motives, hq, hl⟩ := ConLeche.mutualRecRhs_paramPrefix hgen hfirst
  obtain rfl : bs = pbs.map fun x =>
      (x.1, (⟨Level.zeronessOf (ConLeche.structElimLevel b.elim b.large)⟩ : BinderMeta)) :=
    (Prod.mk.inj (Option.some.inj (hl.symm.trans hstrip))).1.symm
  refine ⟨pbs, bodyF, hq, by rw [List.map_map]; rfl, fun y hy => ?_⟩
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
  rfl

/-- **THE RESTORED RULE'S λ PREFIX READS TO THE BLOCK'S PARAMETERS**
(`recTyPrefix`'s twin at the rules, item 5 step 2e's first step): the
restore leaves the `λ p⃗` prefix VERBATIM (`restoreNested_lams`), its
domains are the FIRST former's parameter telescope (`ruleParamDoms`),
and that type reads at `mp₂` to `ppsF 0` (`NestedStageFacts.FD`),
which crosses to the restored provision (`provCross`).  So the
restored right-hand side reads as the `mkLamsAV` tower over
`(D).params ψ` at the elimination's own bit — the shape the fired
equality folds — with the walked body read at depth `nP` under the
anonymous openers, which is what the transfer (`ruleAgree`) compares. -/
theorem NestedTailIn.rulePrefix
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    {pbs bs : List (Expr × BinderMeta)} {bodyF bodyR : Expr}
    (hpbs : f₀.cvTa.type.stripPis b.nP = some (pbs, bodyF))
    (hdom : bs.map (·.1) = pbs.map (·.1))
    (hmeta : ∀ y ∈ bs, y.2 = (⟨Level.zeronessOf b.elimLevel⟩ : BinderMeta))
    (ψ : Name → Nat) {E : AnnotTerm}
    (hread : denoteMeta mpP.base2.acval
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ 0
      (bs.foldr (fun (x : Expr × BinderMeta) acc => Expr.lam x.1 acc x.2) bodyR) = some E) :
    ∃ C : AnnotTerm,
      E = mkLamsAV (((D).params ψ).map fun A =>
        (pwBit ψ (Level.zeronessOf b.elimLevel), A)) C ∧
      denoteMeta mpP.base2.acval
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ b.nP
        (Expr.instSeq (openFvars 0 b.nP) (b.nP - 1) bodyR) = some C := by
  have hlenP : pbs.length = b.nP := ConLeche.Expr.stripPis_length _ hpbs
  have hlenBs : bs.length = b.nP := by
    have h := congrArg List.length hdom
    simp only [List.length_map] at h
    rw [h, hlenP]
  obtain ⟨Γ, C, hΓlen, hshape, hdoms, hbody⟩ :=
    denoteMeta_foldrLam (pwBit ψ (Level.zeronessOf b.elimLevel)) b.nP bs hlenBs
      (fun y hy => by rw [hmeta y hy]) hread
  rw [hlenBs, Nat.zero_add] at hbody
  rw [hlenBs] at hΓlen
  refine ⟨C, ?_, hbody⟩
  -- **Γ IS the block's parameter telescope**
  have hFD := I.out.stage.FD 0 f₀ I.kpos I.out.facts.first
  have hlenPP : (ppsF 0 ψ).length = b.nP + f₀.nIdx := hFD.len ψ
  have hreadF : denoteMeta mp₂.base2.acval (ENV2) ψ 0 f₀.cvTa.type
      = some (mkPisAV ((ppsF 0 ψ).take b.nP)
          (mkPisAV ((ppsF 0 ψ).drop b.nP) (.sort (f₀.s.eval ψ)))) := by
    rw [← mkPisAV_append, List.take_append_drop]
    exact hFD.read ψ
  obtain ⟨fvsP, hopenP, hbindP, -⟩ :=
    piTele_read_openers mpP.base2 hpbs (by rw [List.length_take]; omega)
      (I.provCross hndR hagR ψ 0 f₀.cvTa.type hreadF)
  have hΓeq : Γ = (D).params ψ := by
    show Γ = ((ppsF 0 ψ).take b.nP).map (·.2.2)
    refine List.ext_getElem? fun i => ?_
    rcases Nat.lt_or_ge i b.nP with hi | hi
    · obtain ⟨y, hy⟩ : ∃ y, bs[i]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)⟩
      obtain ⟨x, hx⟩ : ∃ x, pbs[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenP]; exact hi)⟩
      have hdomI : y.1 = x.1 := by
        have h1 := congrArg (fun l => l[i]?) hdom
        simp only [List.getElem?_map, hy, hx, Option.map_some, Option.some.injEq] at h1
        exact h1
      have hR := hdoms i y hy
      rw [Nat.zero_add, hdomI,
        denoteMeta_instSeq_openers_congr (acval := mpP.base2.acval)
          (env := ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2))
          (φ := ψ) (openersFrom_openFvars 0 i) (hopenP.take (i := i) (by omega)) (i - 1) i x.1,
        hbindP i x hx] at hR
      have hiΓ : i < Γ.length := by rw [hΓlen]; exact hi
      have hiP : i < ((ppsF 0 ψ).take b.nP).length := by
        rw [List.length_take]; omega
      rw [List.getElem?_map, List.getElem?_eq_getElem hiΓ, List.getElem?_eq_getElem hiP]
      simp only [Option.map_some, Option.some.injEq]
      have := (Option.some.inj hR).symm
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiΓ,
        List.getElem?_eq_getElem hiP, Option.getD_some] using this
    · rw [List.getElem?_eq_none (by rw [hΓlen]; exact hi),
        List.getElem?_eq_none (by rw [List.length_map, List.length_take]; omega)]
  rw [hshape, hΓeq]


/-! ## The two towers' folds (item 5 step 2e, step 1 assembled) -/

/-- **THE TWO RULE TOWERS HAVE ONE VALUE**: the restored right-hand
side's reading and the auxiliary tower interpret alike at EVERY frame
— not merely along fitting spines.

The two towers share their `λ p⃗` prefix — the restored one's is
`(D).params ψ` at the elimination's bit (`rulePrefix`), the auxiliary
one's is `mutualRuleDataAV`'s own `rebit pw (recPps ψ)`
(`BlockReadings.ppsDom`), and `mkLamsAV_inj` identifies them — and
below it the two bodies interpret alike at every frame fitting the
block's parameters (`ruleAgree`).  The restored body's grading is
peeled off `hwdR`, which is the DOOR's (`ClaimsAt.inferRow` at
`restoreRules_at`'s own `inferTypeCore` run): `WellDenoted` is
structural and the walk's reading law consumes it rather than carrying
it. -/
theorem NestedTailIn.ruleVal {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    (hleafR : ∀ c, c < (D).kT → ∀ φ : Name → Nat,
      mpP.base2.acval (nestedRecCvAt p.k cvRms cvRns c).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    (hauxNe : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, ∀ c, c < b.k →
      n ≠ (nestedRecCvAt p.k cvRms cvRns c).name)
    (hK35r : NestedRulesAuxOk p st b stored)
    (ψ : Name → Nat)
    {c : Nat} (hc : c < b.k) {a : AuxStored} (ha : stored[c]? = some a)
    {rl o : RecRule} (hrl : rl ∈ a.rules)
    {i : Nat} {cA : ConstantVal × Nat} (hi : ((DA).ctorsM c)[i]? = some cA)
    (hgen : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
      (ConLeche.mutualGenData b fms ctorsA kinds).1
      (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
      (b.rlps.map Level.param) ((DA).minorIdx c i) = some rl.rhs)
    (hres : ConLeche.restoreNested (ConLeche.restoreTbl p st) rl.rhs = .ok o.rhs)
    (hresolve : o.rhs.constsResolve
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) = true)
    {Ra : AnnotTerm}
    (hRa : denoteMeta mpP.base2.acval
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ 0 o.rhs
      = some Ra)
    (hwdR : ∀ ρ' : Nat → V, WellDenotedV V ρ' Ra)
    (ρ : Nat → V) :
    interp V ρ Ra
      = interp V ρ ((DA).ruleRhsAV mpA.base2 b.elimLevel
          (fun t' => nestedRecLeaf (D).kT s rdsM concM eqs b.rlps t' ψ) c i cA.2 ψ) := by
  have hk : 0 < (DA).k := by
    rw [S.record.k]
    have h1 := I.kpos
    have h2 := I.out.bk
    omega
  have hR := S.readings ψ
  have hppsLen : ((DA).recPps ψ).length = b.nP := by
    have hl := congrArg List.length hR.ppsDom
    rw [List.length_map, S.reps.params_length hk ψ] at hl
    exact hl
  have hparamsLen : ((D).params ψ).length = b.nP := by
    have hl := congrArg List.length hR.ppsDom
    rw [List.length_map, hppsLen] at hl
    exact hl.symm
  -- **the rule's λ prefix**, on both sides
  obtain ⟨bs, bodyA, bodyR, hstrip, hfoldR, hagree⟩ :=
    I.ruleAgree S hnames hctorsJ hndR hshapeA hleafA hagA hleafR hagR hauxNe hK35r ψ ha hrl hres
      hresolve
  obtain ⟨pbs, bodyF, hpbs, hdomE, hmeta⟩ := I.ruleParamDoms hgen hstrip
  have hlenBs : bs.length = b.nP := ConLeche.Expr.stripLams_length b.nP hstrip
  obtain ⟨CR, hRshape, hCR⟩ :=
    I.rulePrefix hndR hagR hpbs hdomE hmeta ψ (by rw [← hfoldR]; exact hRa)
  have hreadA := I.auxRuleRead S hshapeA hleafA hagA hc hi hgen ψ
  rw [stripLams_foldr b.nP hstrip] at hreadA
  obtain ⟨ΓA, CA, hΓAlen, hAshape, -, hCA⟩ :=
    denoteMeta_foldrLam (pwBit ψ (Level.zeronessOf b.elimLevel)) b.nP bs hlenBs
      (fun y hy => by rw [hmeta y hy]) hreadA
  rw [hlenBs, Nat.zero_add] at hCA
  rw [hlenBs] at hΓAlen
  -- **the auxiliary tower's prefix IS the parameters'**
  have hpref : ((DA).ruleData mpA.base2 b.elimLevel c i ψ).take b.nP
      = ((D).params ψ).map fun A => (pwBit ψ (Level.zeronessOf b.elimLevel), A) := by
    unfold BlockModel.ruleData mutualRuleDataAV
    rw [← List.map_take, take_append₄ _ _ _ _ _ (by rw [rebit_length]; exact hppsLen),
      rebit_map_lam, show (D).params ψ = (DA).params ψ from rfl, ← hR.ppsDom, List.map_map]
    rfl
  have hAA : ∀ CORE : AnnotTerm,
      mkLamsAV ((DA).ruleData mpA.base2 b.elimLevel c i ψ) CORE
        = mkLamsAV (((D).params ψ).map fun A => (pwBit ψ (Level.zeronessOf b.elimLevel), A))
            (mkLamsAV (((DA).ruleData mpA.base2 b.elimLevel c i ψ).drop b.nP) CORE) := by
    intro CORE
    have h1 := mkLamsAV_append (((DA).ruleData mpA.base2 b.elimLevel c i ψ).take b.nP)
      (((DA).ruleData mpA.base2 b.elimLevel c i ψ).drop b.nP) CORE
    rw [List.take_append_drop, hpref] at h1
    exact h1
  have hAA2 : (DA).ruleRhsAV mpA.base2 b.elimLevel
      (fun t' => nestedRecLeaf (D).kT s rdsM concM eqs b.rlps t' ψ) c i cA.2 ψ
      = mkLamsAV (((D).params ψ).map fun A => (pwBit ψ (Level.zeronessOf b.elimLevel), A)) CA := by
    have hinj := mkLamsAV_inj
      (l₁ := ΓA.map fun A => (pwBit ψ (Level.zeronessOf b.elimLevel), A))
      (l₂ := ((D).params ψ).map fun A => (pwBit ψ (Level.zeronessOf b.elimLevel), A))
      (by rw [List.length_map, List.length_map, hΓAlen, hparamsLen])
      (hAshape.symm.trans (by unfold BlockModel.ruleRhsAV; exact hAA _))
    rw [hAshape, hinj.1]
  -- **the two towers, layer by layer**
  have hbitDoms : (((D).params ψ).map fun A =>
      (pwBit ψ (Level.zeronessOf b.elimLevel), A)).map (·.2) = (D).params ψ := by
    simp [List.map_map, Function.comp_def]
  rw [hRshape, hAA2]
  refine interp_mkLamsAV_congr (ds := ((D).params ψ).map fun A =>
    (pwBit ψ (Level.zeronessOf b.elimLevel), A)) fun bs _hlen hfit => ?_
  have hfitP : SpineFit ρ ((D).params ψ) bs := by rw [hbitDoms] at hfit; exact hfit
  have hwd : WellDenoted V (consList bs ρ) CR :=
    wellDenoted_mkLamsAV_body hfit (by rw [← hRshape]; exact (hwdR ρ).1)
  exact hagree (openFvars 0 b.nP) (openersFrom_openFvars 0 b.nP) hCA hCR bs ρ hfitP hwd


/-! ## The restored recursor's row at the provision (item 5 step 2e) -/

/-- **THE RESTORED RECURSOR'S ARGUMENT SUMS** — `RecRuleLaw`'s first
conjunct and the fired equality's arithmetic: the read-back's stored
major index and rule prefix are the SCRATCH install's
(`auxStored_rules_eq`), i.e. the block's own `rulePrefix` and that
plus class `c`'s index count. -/
theorem NestedTailIn.recArgSums {c : Nat} {a : AuxStored} (ha : stored[c]? = some a) :
    a.rP = b.rulePrefix ∧ a.mI = b.rulePrefix + (fms.getD c default).nIdx := by
  obtain ⟨fms', -, -, -, -, -, -, hformers', -, -, -, -, hmI, hrP, -⟩ :=
    ConLeche.auxStored_rules_eq I.haux I.hstored ha
  have hfms : fms = fms' := congrArg Prod.snd (Except.ok.inj (I.out.formers.symm.trans hformers'))
  subst hfms
  exact ⟨hrP, hmI⟩

/-- **THE RESTORED RECURSOR TYPE READS AT THE PROVISION**: the tail's
own reading (`NestedRecReadings`' `readM`/`readN`, `readAtOf`) crossed
by `provCross` — the form `RecRuleLaw`'s `TVa` hypothesis takes. -/
theorem NestedTailIn.recTyReadP
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    {c : Nat} (hc : c < (D).kT) (ψ : Name → Nat) :
    denoteMeta mpP.base2.acval
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ 0
        (nestedRecCvAt p.k cvRms cvRns c).type
      = some (mkPisAV (rdsM c ψ) (concM c)) :=
  I.provCross hndR hagR ψ 0 _ (NestedTailIn.readAtOf R hc ψ)


/-! ## The recursor's spine, decomposed (item 5 step 2e, the LEFT side) -/

/-- **THE RECURSOR'S SPINE**: a `TeleFitPA` fit of the RESTORED
recursor type's reading — the form `RecRuleLaw` hands the arm, `TVa`
being that reading by `recTyReadP` — is a `SpineFit` of it
(`teleFitPA_to_chain`, `spineFit_of_chain`), hence BY THE TRANSFER
(`spineFit_transfer`) of the SCRATCH tower.

This is exactly `blockRecRuleLawG`'s `hspine` at the nested arm: the
generalised law asks for the fit and inverts it itself
(`IsBlockModels.spineFit_recData_inv`), which is why the decomposition
(`recSpine`) is a corollary rather than the statement. -/
theorem NestedTailIn.recSpineFit {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    {c : Nat} (hc : c < b.k) (ψ : Name → Nat) (ρ : Nat → V)
    {ws : List AnnotTerm} {restR : AnnotTerm}
    (hwl : ws.length = (rdsM c ψ).length)
    (hfitR : TeleFitPA V ρ (mkPisAV (rdsM c ψ) (concM c)) ws restR) :
    SpineFit ρ (((DA).blockRds mpA.base2 b.elimLevel c ψ).map (·.2.2))
      (ws.map (interp V ρ)) := by
  have hcT : c < (D).kT := by rw [I.kT]; exact hc
  -- the fit, as a spine at the RESTORED reading
  have hst := stripPisAV_mkPisAV (rdsM c ψ) (concM c)
  have htele := piTeleAV_of_stripPisAV hst
  have hchain := teleFitPA_to_chain (rdsM c ψ).length htele hwl hfitR
  have hsp : SpineFit ρ ((rdsM c ψ).map (·.2.2)) (ws.map (interp V ρ)) := by
    refine spineFit_of_chain (by rw [hwl, List.length_map]) ?_
    intro q hq
    rw [List.length_map] at hq
    have h := hchain q hq
    simpa using h
  -- …and therefore at the SCRATCH one
  exact (I.spineFit_transfer S hnames hctorsJ hK35 hc ψ ρ
    (NestedTailIn.readAtOf R hcT ψ) (I.lenAtOf R hc ψ) (ws.map (interp V ρ))).mp hsp

/-- **…AND DECOMPOSED**: the fit inverted — the block's parameters,
motives and minors (a `PrefixFrame`), class `c`'s index spine and a
major in the carrier's fibre at its tuple. -/
theorem NestedTailIn.recSpine {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    {c : Nat} (hc : c < b.k) (ψ : Name → Nat) (ρ : Nat → V)
    {ws : List AnnotTerm} {restR : AnnotTerm}
    (hwl : ws.length = (rdsM c ψ).length)
    (hfitR : TeleFitPA V ρ (mkPisAV (rdsM c ψ) (concM c)) ws restR) :
    ∃ (ps Msl msl is : List V) (tv : V),
      ws.map (interp V ρ) = ps ++ Msl ++ msl ++ is ++ [tv] ∧
      PrefixFrame mpA.base2 (DA) ψ b.elimLevel ρ ps Msl msl ∧
      SpineFit (consList ps ρ) ((DA).IdsM c ψ) is ∧
      tv ∈ˢ SetTheory.app (lfpTuple ((DA).w ψ) (DA).k ((DA).idx ψ (consList ps ρ))
          ((DA).Φ ψ (consList ps ρ)) c) ((DA).tup ψ c is) :=
  S.reps.spineFit_recData_inv (S.readings ψ) (by rw [S.record.k]; exact hc)
    (I.recSpineFit S hnames hctorsJ hK35 R hc ψ ρ hwl hfitR)


/-! ## The ι step at the chosen tuple (item 5 step 2e, the LEFT side) -/

/-- **THE ι STEP AT THE CHOSEN TUPLE**: the recursors' leaves are a
`schoice` over the equations, so the ONLY handle on a leaf's value is
that its tuple satisfies THEM (`NestedRecTuple`) — which is why the
stage's equations are NAMED rather than existential (DESIGN §U.29
(yy)).  Named, they are the SCRATCH block's, and rule `(c, j)`'s
equation is one of them (`BlockModel.mem_specEqs_of`), so
`nestedRecs_iota` fires: at every spine fitting the rule's binder data
at the tuple frame the equation's two sides interpret alike.

This is `blockRecRuleLaw`'s `hEq` at the nested block's leaves, and
the fired equality's left half rests on it. -/
theorem NestedTailIn.ruleIota {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (Tu : NestedRecTuple (D) s rdsM concM (fun φ => (DA).recEqs mpA.base2 b.elimLevel φ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∃ a : Nat → V,
      (∀ t, t < (DA).k →
        interp V ρ (nestedRecLeaf (D).kT s rdsM concM
            (fun φ => (DA).recEqs mpA.base2 b.elimLevel φ) b.rlps t ψ) = a t ∧
        a t ∈ˢ interp V ρ (mkPisAV (rdsM t (restrictΨ b.rlps ψ)) (concM t))) ∧
      ∀ (c j : Nat) (cA : ConstantVal × Nat), c < (DA).k → ((DA).ctorsM c)[j]? = some cA →
        ∀ xs : List V,
          SpineFit (consList ((List.range (DA).k).map a) ρ)
              (((DA).ruleData mpA.base2 b.elimLevel c j (restrictΨ b.rlps ψ)).map (·.2)) xs →
          interp V (consList xs (consList ((List.range (DA).k).map a) ρ))
              (specLhsAV (DA).k (DA).nP (DA).nCtors cA.2 c
                ((DA).esF c j (restrictΨ b.rlps ψ))
                (mpA.base2.acval cA.1.name (restrictΨ b.rlps ψ)))
            = interp V (consList xs (consList ((List.range (DA).k).map a) ρ))
              (specRuleCoreAV (pwBit (restrictΨ b.rlps ψ) (Level.zeronessOf b.elimLevel)) (DA).k
                ((DA).tgts c j) (DA).nP (DA).nCtors cA.2 ((DA).minorIdx c j)
                (ConLeche.recIdxOf ((DA).ksF c j)) ((DA).tssF c j (restrictΨ b.rlps ψ))
                ((DA).eissF c j (restrictΨ b.rlps ψ))) := by
  have hkT : (D).kT = (DA).k := by rw [I.kT, S.record.k]
  obtain ⟨a, ha, heqs⟩ := Tu (restrictΨ b.rlps ψ) ρ
  rw [hkT] at ha heqs
  refine ⟨a, fun t ht => ⟨?_, (ha t ht).1⟩, fun c j cA hc hj xs hsp => ?_⟩
  · unfold nestedRecLeaf
    rw [hkT]
    exact (ha t ht).2.1
  · exact blockRecs_iota (k := (DA).k)
      (heqs _ ((DA).mem_specEqs_of (m := mpA.base2) (ψ := restrictΨ b.rlps ψ) hc hj)) xs hsp


/-! ## The major at a MEMBER arm (item 5 step 2e, `hmajor`'s first instance) -/

/-- **THE MAJOR AT A MEMBER ARM** — `blockRecRuleLawG`'s fourth
obligation at a rule of a MEMBER's recursor, whose constructor is the
declaration's own.  The decode is the NESTED block model's
`IsBlockModel.ctor`, not the scratch one's: `(D)`'s constructor
telescope is the RESTORED domain list (`IsBlockModel.Fss_getD` at
`(D).dsF = dsR`), which is exactly what the major's arguments fit,
while the two block models' injections are ONE function —
`BlockModel.ofNested` and `BlockModel.ofMutual` both inject at the
block's own sort, so `(D).inj ψ c i fs` and `(DA).inj ψ c i fs` are the
same term.  *This is why §U.29 (hhh)'s constructor-telescope transfer
is NOT needed: the position-by-position agreement it would have fed to
`spineFit_iff_agree` is already inside `(D)`'s own representation
(`nestedCoreModeled_of` spent it there).*

Everything else is `blockRecRuleLaw`'s own argument at the nested
data: the value crosses `mpP → mp₂` off the restored recursors' names
(`hagR` at `recCvDoor` — a constructor of the block is stored where a
restored recursor is fresh), the two level assignments agree on the
constructor's parameters (`substFn_agree_of_comparand` at the
comparands clause, `b.lps ⊆ b.rlps`), and the constructor type's
reading crosses the provision (`provCross`). -/
theorem NestedTailIn.memberMajor
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    {c : Nat} (hc : c < p.k) {i : Nat} {cA : ConstantVal × Nat}
    (hi : ((DA).ctorsM c)[i]? = some cA)
    {o : RecRule} (hfire : o.fire = .plain) (hctor : o.ctor = cA.1.name)
    (hnf : o.nfields = cA.2)
    (hcp : ∃ (cv : ConstantVal) (cnF : Nat),
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find? o.ctor
        = some (.ctorInfo cv o.ctorParams cnF))
    {mI rP : Nat} (φ : Name → Nat) :
    ∀ (us : List Level), us.length = (nestedRecCvAt p.k cvRms cvRns c).levelParams.length →
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
          (RecRule.ctor o) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
        (TVa TVja restC : AnnotTerm),
        xs.length = mI →
        ys.length = RecRule.ctorParams o + RecRule.nfields o →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands o (nestedRecCvAt p.k cvRms cvRns c).levelParams us
                cvj.levelParams [] rP).1 →
        (∀ lvls pins, RecRule.fire o = .nested lvls pins →
          ∀ ii, ii < RecRule.ctorParams o →
          ∀ vpa : AnnotTerm,
            denoteMeta mpP.base2.acval
              (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ rP
              (ConLeche.Verify.openRev 0 rP
                ((pins.getD ii default).instantiateLevelParams
                  (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) = some vpa →
            interp V ρ (ys.getD ii default)
              = interp V ρ (ConLeche.Model.AnnotTerm.instRevChain (xs.take rP) vpa)) →
        IotaIndexPin (V := V) ρ restC (RecRule.ctorParams o) mI rP xs →
        denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          ((nestedRecCvAt p.k cvRms cvRns c).type.instantiateLevelParams
            (nestedRecCvAt p.k cvRms cvRns c).levelParams us) = some TVa →
        denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        TeleFitPA V ρ TVja ys restC →
        ∀ ps : List V,
          SpineFit ρ ((DA).params (restrictΨ b.rlps
            (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us))) ps →
          ∃ fsY : List V, fsY.length = cA.2 ∧
            (ys.map (interp V ρ)).drop (RecRule.ctorParams o) = fsY ∧
            interp V ρ (AnnotTerm.mkAppN (mpP.base2.acval (RecRule.ctor o)
                (Level.substFn φ cvj.levelParams usj)) ys)
              = (DA).inj (restrictΨ b.rlps
                  (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) c i fsY := by
  intro us hus cvj cnP cnF hfcj usj ρ xs ys TVa TVja restC _ hyl husjl hψ _ _ _ hTVja hfitC ps _
  -- **the restored constructor** at member `c`, position `i`
  have hcD : c < (D).k := hc
  have hgrouped := I.out.grouped
  have hlenA := I.out.facts.lenA
  obtain ⟨-, hiA, -⟩ := mutualBlockModel_ctorsM_get hgrouped hlenA hi
  have hlenOwn : ((DA).ctorsM c).length = (b.ownCtors c).length := by
    show ((b.ownCtors c).map fun q => ctorsA.getD q.1 default).length = _
    simp
  have hiOwn : i < (b.ownCtors c).length := by
    rw [← hlenOwn]; exact (List.getElem?_eq_some_iff.mp hi).1
  have hjR : i < (ctorsR.getD c []).length := by
    rw [I.out.stage.ctorsLen c hc]
    exact hiOwn
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, (ctorsR.getD c [])[i]? = some c₀ := ⟨_, List.getElem?_eq_getElem hjR⟩
  obtain ⟨cA', hcA', hnF', -, -, hBF⟩ := I.out.stage.ctorFacts c i c₀ hc hc₀
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hiA)
  have hnF₀ : c₀.2.2 = cA.2 := by rw [hnF', hcAeq]
  obtain ⟨cA'', hcA'', hnmR⟩ := I.ctorsRName (I.ctorsRget hc) hc₀
  have hnmC : c₀.1.name = cA.1.name := by
    rw [hnmR, Option.some.inj (hcA''.symm.trans hiA)]
  have hjD : ((D).ctorsM c)[i]? = some (c₀.1, c₀.2.2) := by
    show ((ctorsR.getD c []).map fun cc => (cc.1, cc.2.2))[i]? = _
    rw [List.getElem?_map, hc₀]
    rfl
  have hfC₀ : (ENV2).find? c₀.1.name = some (.ctorInfo c₀.1 b.nP c₀.2.2) := hBF.1
  have hlpsC : c₀.1.levelParams = b.lps := hBF.2.1
  have hname : RecRule.ctor o = c₀.1.name := by rw [hctor, hnmC]
  -- **the constructor is found across the provision**, and fixes `cvj`, `cnP` and `o.ctorParams`
  have hfindP : (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
      c₀.1.name = some (.ctorInfo c₀.1 b.nP c₀.2.2) := by
    refine (ConLeche.provisionNestedRecs_find?_of_ne (fun x hx hxn => ?_)).trans hfC₀
    have hfresh := I.provListFresh x hx
    rw [← hxn, hfC₀] at hfresh
    exact nomatch hfresh
  rw [hname, hfindP] at hfcj
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfcj.symm)
  obtain ⟨cv', cnF', hcp'⟩ := hcp
  rw [hname, hfindP] at hcp'
  obtain ⟨-, hnP', -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hcp'.symm)
  -- **the block model's representation** at member `c`
  obtain ⟨cvT, cvR, mI', rP', rules, h⟩ := I.out.reps c hcD
  have hcd := h.ctorData hjD
  have hk : 0 < (D).k := by omega
  -- the level assignments agree on the constructor's parameters
  have hagree : ∀ q ∈ c₀.1.levelParams,
      Level.substFn φ c₀.1.levelParams usj q
        = Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us q := by
    have h' := hψ
    simp only [ConLeche.recFireComparands, hfire] at h'
    exact substFn_agree_of_comparand h'
  have hCψ : ∀ q ∈ c₀.1.levelParams, Level.substFn φ c₀.1.levelParams usj q
      = restrictΨ b.rlps
        (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us) q := fun q hq =>
    (hagree q hq).trans (restrictΨ_agree b.rlps _ q
      (MutualBlock.mem_rlps_of_mem_lps b (by rw [← hlpsC]; exact hq))).symm
  have hpl := I.out.reps.params_length hk (restrictΨ b.rlps
    (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us))
  generalize hψ'0 : restrictΨ b.rlps
    (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us) = ψ' at hCψ hpl ⊢
  generalize hψC : Level.substFn φ c₀.1.levelParams usj = ψC at hCψ hTVja hfitC ⊢
  have hdsEq : (D).dsF c i ψC = (D).dsF c i ψ' := (hcd.params ψC ψ' hCψ).1
  have hesEq : (D).esF c i ψC = (D).esF c i ψ' := (hcd.params ψC ψ' hCψ).2
  -- **the value crosses** `mpP → mp₂`, then the level assignments
  have hoff : ∀ c' : Nat, c' < (D).kT → c₀.1.name ≠ (nestedRecCvAt p.k cvRms cvRns c').name := by
    intro c' hc' he
    have hd := (I.recCvDoor (by rw [← I.kT]; exact hc')).1
    rw [← he, hfC₀] at hd
    exact nomatch hd
  have hCac : mpP.base2.acval c₀.1.name ψC = mp₂.base2.acval c₀.1.name ψ' := by
    rw [congrFun (hagR c₀.1.name hoff) ψC]
    exact mp₂.base2.acval_params _ _ hfC₀ ψC ψ' hCψ
  -- **the constructor type's reading**, and the spine it fits
  have hTVja' : TVja = mkPisAV ((D).dsF c i ψ')
      (ctorBodyAVI mp₂.base2 ((D).memberName c) (D).nP c₀.2.2 ψC ((D).esF c i ψ')) := by
    have h' := hTVja
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mpP.base2) φ 0 c₀.1.type, hψC] at h'
    rw [Option.some.inj (h'.symm.trans (I.provCross hndR hagR ψC 0 c₀.1.type (hcd.read ψC))),
      hdsEq, hesEq]
  have hstC := stripPisAV_mkPisAV ((D).dsF c i ψ')
    (ctorBodyAVI mp₂.base2 ((D).memberName c) (D).nP c₀.2.2 ψC ((D).esF c i ψ'))
  rw [hcd.len ψ'] at hstC
  have hteleC := piTeleAV_of_stripPisAV hstC
  have hylD : ys.length = (D).nP + c₀.2.2 := by
    rw [hyl, hnf, hnF₀, hnP', nestedBlockModel_nP]
  have hspC : SpineFit ρ (((D).dsF c i ψ').map (·.2.2)) (ys.map (interp V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain ((D).nP + c₀.2.2) hteleC (by simpa using hylD) hfit
    refine spineFit_of_chain (by simp [hylD, hcd.len ψ']) ?_
    intro q hq
    have := hchain q (by simpa [hcd.len ψ'] using hq)
    simpa [hcd.len ψ'] using this
  have hdsSplit : ((D).dsF c i ψ').map (·.2.2)
      = (((D).dsF c i ψ').take (D).nP).map (·.2.2) ++ (((D).dsF c i ψ').drop (D).nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨psY, fsY, hys, hspY₁, hspY₂⟩ := spineFit_append_inv hspC
  have hlenPY : psY.length = (D).nP := by
    rw [hspY₁.length_eq, List.length_map, List.length_take, hcd.len ψ']
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlenFY : fsY.length = cA.2 := by
    rw [hspY₂.length_eq, List.length_map, List.length_drop, hcd.len ψ', ← hnF₀]
    omega
  have hpsY : SpineFit ρ ((D).params ψ') psY := by
    have hsat := sat_of_spineFit (Sat_nil V ρ) hspY₁
    rw [List.append_nil] at hsat
    exact spineFit_of_sat_len (by rw [hlenPY, hpl])
      ((h.paramsIff c i (c₀.1, c₀.2.2) hcD hjD ψ' _).mpr hsat)
  have hfsY : SpineFit (consList psY ρ) (((D).Fss c ψ').getD i []) fsY := by
    rw [IsBlockModel.Fss_getD hjD]; exact hspY₂
  refine ⟨fsY, hlenFY, ?_, ?_⟩
  · rw [hys, hnP']
    exact List.drop_left' (by rw [hlenPY]; exact nestedBlockModel_nP)
  · rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hys, hname, hCac]
    exact h.ctor c i (c₀.1, c₀.2.2) hcD hjD ψ' ρ psY fsY hpsY hfsY


/-! ## The major at a MIMIC arm (item 5 step 2e, `hmajor`'s second instance) -/

omit I in
/-- Two entries of a nodup list sit at one index. -/
theorem nodup_getElem?_inj {α : Type} {l : List α} (hnd : l.Nodup) {i j : Nat} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j :=
  (List.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 hnd).mp (hi.trans hj.symm)

/-- **THE MAJOR AT A MIMIC ARM** — `blockRecRuleLawG`'s fourth
obligation at a rule of a MIMIC recursor, whose constructor is the
CONTAINER's.  The decode is the pin group's own block model `dJ`
(`NestedPinGroup.rep`): the major's arguments fit the container
constructor's telescope, so `IsBlockModel.ctor` at `dJ` — AT THE
RULE'S OWN LEVEL ASSIGNMENT, the clause holding at every one — turns
the fold into `dJ.inj`, and a pin group's injection is the tagged
tower (`NestedPinGroup.inj`), which is the scratch block's own
(`BlockModel.ofMutual` injects alike).  *So the copy-constructor
identification `ctorArm` carries is NOT needed here: `hmajor` asks for
the VALUE, and the value is the tag and the fields.*

The levels are needed for one thing only, the tag's universe: the
group's `w` clause pins `dJ.w` at the PIN's assignment, and
`hfireLvls` — the mimic rule's fire levels ARE its pin's, the restore
having rewritten the copy's former application into the container's —
moves it to the rule's (`substFn_map_subst`, `substFn_ext`, and the
former's own level stability `FormerData.params`).

The rule's class and constructor index are identified with the pin's
by the constructor's NAME: the scratch block's constructor names are
pairwise distinct, so a name fixes its position, and the position
fixes the member (`mutualBlockModel_ctorsM_get`). -/
theorem NestedTailIn.mimicMajor
    (hnames : NestedCtorPinNames env p st)
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    {c : Nat} {jc : Nat} {cA : ConstantVal × Nat}
    (hi : ((DA).ctorsM c)[jc]? = some cA)
    {o : RecRule} {lvls : List Level} {pins : List Expr}
    (hfire : RecRule.fire o = .nested lvls pins)
    (hnf : RecRule.nfields o = cA.2)
    (hlvlsScoped : ∀ u ∈ lvls, Level.allParamsDefined b.rlps u = true)
    (hpin : ∃ pn : Expr, (ConLeche.restoreTbl p st).ctorPins.find? (fun z => z.1 == cA.1.name)
      = some (cA.1.name, pn, RecRule.ctor o))
    (hcp : ∃ (cv : ConstantVal) (cnF : Nat),
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
        (RecRule.ctor o) = some (.ctorInfo cv (RecRule.ctorParams o) cnF))
    (hfireLvls : ∀ (q : Nat) (qn : NestedPin), q < pinsS.length → st.pins[q]? = some qn →
      (ConLeche.restoreTbl p st).ctorPins.find? (fun z => z.1 == cA.1.name)
        = some (cA.1.name, Expr.abstractRange qn.pin 0 p.nP 0, RecRule.ctor o) →
      lvls = ((D).pinAt q).lvls)
    {mI rP : Nat} (φ : Name → Nat) :
    ∀ (us : List Level), us.length = (nestedRecCvAt p.k cvRms cvRns c).levelParams.length →
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
          (RecRule.ctor o) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
        (TVa TVja restC : AnnotTerm),
        xs.length = mI →
        ys.length = RecRule.ctorParams o + RecRule.nfields o →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands o (nestedRecCvAt p.k cvRms cvRns c).levelParams us
                cvj.levelParams [] rP).1 →
        (∀ lvls' pins', RecRule.fire o = .nested lvls' pins' →
          ∀ ii, ii < RecRule.ctorParams o →
          ∀ vpa : AnnotTerm,
            denoteMeta mpP.base2.acval
              (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ rP
              (ConLeche.Verify.openRev 0 rP
                ((pins'.getD ii default).instantiateLevelParams
                  (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) = some vpa →
            interp V ρ (ys.getD ii default)
              = interp V ρ (ConLeche.Model.AnnotTerm.instRevChain (xs.take rP) vpa)) →
        IotaIndexPin (V := V) ρ restC (RecRule.ctorParams o) mI rP xs →
        denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          ((nestedRecCvAt p.k cvRms cvRns c).type.instantiateLevelParams
            (nestedRecCvAt p.k cvRms cvRns c).levelParams us) = some TVa →
        denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        TeleFitPA V ρ TVja ys restC →
        ∀ ps : List V,
          SpineFit ρ ((DA).params (restrictΨ b.rlps
            (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us))) ps →
          ∃ fsY : List V, fsY.length = cA.2 ∧
            (ys.map (interp V ρ)).drop (RecRule.ctorParams o) = fsY ∧
            interp V ρ (AnnotTerm.mkAppN (mpP.base2.acval (RecRule.ctor o)
                (Level.substFn φ cvj.levelParams usj)) ys)
              = (DA).inj (restrictΨ b.rlps
                  (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) c jc fsY := by
  intro us hus cvj cnP cnF hfcj usj ρ xs ys TVa TVja restC _ hyl husjl hψ _ _ _ hTVja hfitC ps _
  -- **the constructor pin, inverted**: the copy, its container and its group
  obtain ⟨pn, hfindc⟩ := hpin
  obtain ⟨q, qn, t, jcI, cnm, ci, J, cc, hqn, ht, hcnm, htn, hn1, hpn, hq, hci, hJmem, hJname,
    hccj, hccn, hnFc⟩ := I.ctorPinInv hnames hfindc
  obtain ⟨q₀, kJ, i, dJ, rfl, hiJ, G⟩ := I.out.stage.groups q hq
  obtain ⟨hnP, -, -, -⟩ := ConLeche.auxBlock_fields I.hb
  have hassoc : p.k + (q₀ + i) = p.k + q₀ + i := (Nat.add_assoc _ _ _).symm
  have hct := ConLeche.auxBlock_ctors_getElem? I.hb I.out.grouped (p.k + (q₀ + i)) jcI t cnm
    ht hcnm
  rw [hassoc] at hct
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  have hJlt : b.ownOffset (p.k + q₀ + i) + jcI < ctorsA.length := by
    rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hct).1
  obtain ⟨cAx, hcAget⟩ : ∃ cAx, ctorsA[b.ownOffset (p.k + q₀ + i) + jcI]? = some cAx :=
    ⟨_, List.getElem?_eq_getElem hJlt⟩
  have hcAname : cAx.1.name = cnm.1 := (hnamesA _ _ _ hcAget hct).1
  have hcAnF : cAx.2 = cnm.2.2 := (hnamesA _ _ _ hcAget hct).2.1
  -- **the rule's class and index ARE the copy's**: a name fixes its position
  obtain ⟨-, hiA, hmemC⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hi
  have hposEq : b.ownOffset (p.k + q₀ + i) + jcI = b.ownOffset c + jc := by
    refine nodup_getElem?_inj I.ctorsANodup (x := cA.1.name) ?_ ?_
    · simp only [List.getElem?_map, hcAget, Option.map_some, hcAname, hn1]
    · simp only [List.getElem?_map, hiA, Option.map_some]
  have hmemA : mutMemF b (b.ownOffset (p.k + q₀ + i) + jcI) = p.k + q₀ + i := by
    show (b.ctors.getD (b.ownOffset (p.k + q₀ + i) + jcI) default).member = _
    rw [List.getD_eq_getElem?_getD, hct]
    rfl
  have hcEq : c = p.k + q₀ + i := by
    rw [← hposEq, hmemA] at hmemC
    exact hmemC.symm
  have hjcEq : jcI = jc := by rw [hcEq] at hposEq; omega
  subst hjcEq
  have hcAeq : cAx = cA := by
    rw [← hposEq] at hiA
    exact Option.some.inj (hcAget.symm.trans hiA)
  -- **the container member's constructor**, at the group's block model
  have hi' : i < dJ.k := by rw [G.kEq]; exact hiJ
  obtain ⟨cvT', cvR', mI', rP', rules', hIJ⟩ := G.rep i hiJ
  have hPJ := (I.out.stage.pinRec (q₀ + i) qn hqn).1
  have hmapJ := (G.ctorsOf i hiJ ci J (by rw [hPJ]; exact hci) hJmem
    (by rw [hPJ]; exact hJname)).1
  have hjcJ : jcI < (dJ.ctorsM i).length := by
    have hl := congrArg List.length hmapJ
    simp only [List.length_map] at hl
    rw [hl]
    exact (List.getElem?_eq_some_iff.mp hccj).1
  obtain ⟨cAJ, hjJ⟩ : ∃ cAJ, (dJ.ctorsM i)[jcI]? = some cAJ :=
    ⟨_, List.getElem?_eq_getElem hjcJ⟩
  have hnameJ : cAJ.1.name = cc.name := by
    have h1 : ((dJ.ctorsM i).map (·.1.name))[jcI]? = some cAJ.1.name := by
      rw [List.getElem?_map, hjJ]; rfl
    have h2 : ((J.ctors).map (·.name))[jcI]? = some cc.name := by
      rw [List.getElem?_map, hccj]; rfl
    rw [hmapJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  -- **the container's own records**: the level parameters and the pin's assignment
  have hndNames : (fms.map (·.cvTa.name)).Nodup := by
    rw [I.out.facts.names]
    have h0 := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hFE1 : FindPreserved env (ConLeche.consMutualFormers (fms.take p.k) env) :=
    (consMutualFormers_extend (fms := fms.take p.k) (env := env)
      (fun f hf => by
        obtain ⟨t', ht'⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf)
        exact I.out.facts.fresh t' f ht')
      (by
        have h := hndNames
        rw [← List.take_append_drop p.k fms, List.map_append] at h
        exact (List.nodup_append.mp h).1)).1
  obtain ⟨cvTci, capsci, cvRci, mIci, rPci, rulesci, hfindIci, -, -, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, hJlps, -, hlpsEq, -, hccs⟩ := hmembers J hJmem
  obtain ⟨r, cvc, -, hccr, hfindcc, -⟩ := hccs jcI cc hccj
  rw [← hccr] at hfindcc
  have hcvcT : cvc.levelParams = cvTci.levelParams := by
    rw [I.ctorPinLps hqn hci hJmem hccj hfindcc, hJlps, hlpsEq]
  have hfind2 : (ENV2).find? cc.name = some (.ctorInfo cvc ci.nP cc.nFields) :=
    I.out.stage.find (hFE1 hfindcc)
  have hfindI1 : (ConLeche.consMutualFormers (fms.take p.k) env).find? ((D).pinAt (q₀ + i)).J
      = some (.indInfo cvTci capsci) := by
    rw [hPJ]; exact hFE1 hfindIci
  obtain ⟨hlvlsLen0, hψJ00⟩ := I.out.stage.pinψ (q₀ + i) hq cvTci capsci hfindI1
  have hlvlsLen : ((D).pinAt (q₀ + i)).lvls.length = cvTci.levelParams.length := hlvlsLen0
  have hψJ0 : ∀ ψ : Name → Nat, ((D).pinAt (q₀ + i)).ψJ ψ
      = Level.substFn ψ cvTci.levelParams ((D).pinAt (q₀ + i)).lvls := hψJ00
  obtain ⟨hfindJ2, hlpsJ, hcdJ⟩ := hIJ.ctors i jcI cAJ hi' hjJ
  have hcvcJ : cAJ.1 = cvc ∧ dJ.nP = ci.nP ∧ cAJ.2 = cc.nFields := by
    have h := hfindJ2
    rw [hnameJ, hfind2] at h
    exact ConstantInfo.ctorInfo.inj (Option.some.inj h.symm)
  have hnFJ : cAJ.2 = cA.2 := by rw [hcvcJ.2.2, hnFc, ← hcAnF, hcAeq]
  -- **the container's constructor is found across the provision**
  have hctorName : RecRule.ctor o = cAJ.1.name := by rw [hnameJ, hccn]
  have hfindP : (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
      cAJ.1.name = some (.ctorInfo cAJ.1 dJ.nP cAJ.2) := by
    refine (ConLeche.provisionNestedRecs_find?_of_ne (fun x hx hxn => ?_)).trans hfindJ2
    have hfresh := I.provListFresh x hx
    rw [← hxn, hfindJ2] at hfresh
    exact nomatch hfresh
  rw [hctorName, hfindP] at hfcj
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfcj.symm)
  obtain ⟨cv', cnF', hcp'⟩ := hcp
  rw [hctorName, hfindP] at hcp'
  obtain ⟨-, hnP', -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hcp'.symm)
  -- **the rule's level assignment is the pin's**, at the container's parameters
  have hlvlsEq : lvls = ((D).pinAt (q₀ + i)).lvls := by
    refine hfireLvls (q₀ + i) qn hq hqn ?_
    rw [← hpn]; exact hfindc
  have hlpsCT : cAJ.1.levelParams = cvTci.levelParams := by rw [hcvcJ.1]; exact hcvcT
  have hagreeLvl : ∀ qq ∈ cvT'.levelParams,
      Level.substFn φ cAJ.1.levelParams usj qq
        = ((D).pinAt (q₀ + i)).ψJ (restrictΨ b.rlps
            (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) qq := by
    intro qq hqq
    have hqq' : qq ∈ cAJ.1.levelParams := by rw [hlpsJ]; exact hqq
    have hlen : lvls.length = cAJ.1.levelParams.length := by
      rw [hlvlsEq, hlpsCT]; exact hlvlsLen
    have h1 : Level.substFn φ cAJ.1.levelParams usj qq
        = Level.substFn φ cAJ.1.levelParams
            (lvls.map (Level.subst (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) qq := by
      have h' := hψ
      simp only [ConLeche.recFireComparands, hfire] at h'
      exact congrFun h' qq
    rw [h1, Level.substFn_map_subst hlen hqq',
      Level.substFn_ext (ps := b.rlps)
        (fun pp hpp => (restrictΨ_agree b.rlps
          (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us) pp hpp).symm)
        hlvlsScoped hlen qq hqq',
      hψJ0, hlvlsEq, hlpsCT]
  have hwJ : dJ.w (Level.substFn φ cAJ.1.levelParams usj)
      = f₀.s.eval (restrictΨ b.rlps
        (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) := by
    have hpar := (hIJ.former.params (Level.substFn φ cAJ.1.levelParams usj)
      (((D).pinAt (q₀ + i)).ψJ (restrictΨ b.rlps
        (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us))) hagreeLvl).2
    show dJ.resSort.eval _ = _
    rw [hpar]
    exact G.w i hiJ _
  -- **the major's arguments fit the container constructor's telescope**
  have hTVja' : TVja = mkPisAV (dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj))
      (ctorBodyAVI mp₂.base2 (dJ.memberName i) dJ.nP cAJ.2
        (Level.substFn φ cAJ.1.levelParams usj)
        (dJ.esF i jcI (Level.substFn φ cAJ.1.levelParams usj))) := by
    have h' := hTVja
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mpP.base2) φ 0 cAJ.1.type] at h'
    exact Option.some.inj (h'.symm.trans (I.provCross hndR hagR _ 0 cAJ.1.type
      (hcdJ.read (Level.substFn φ cAJ.1.levelParams usj))))
  have hstC := stripPisAV_mkPisAV (dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj))
    (ctorBodyAVI mp₂.base2 (dJ.memberName i) dJ.nP cAJ.2
      (Level.substFn φ cAJ.1.levelParams usj)
      (dJ.esF i jcI (Level.substFn φ cAJ.1.levelParams usj)))
  rw [hcdJ.len _] at hstC
  have hteleC := piTeleAV_of_stripPisAV hstC
  have hylD : ys.length = dJ.nP + cAJ.2 := by rw [hyl, hnf, hnFJ, hnP']
  have hspC : SpineFit ρ ((dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj)).map (·.2.2))
      (ys.map (interp V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (dJ.nP + cAJ.2) hteleC (by simpa using hylD) hfit
    refine spineFit_of_chain (by simp [hylD, hcdJ.len]) ?_
    intro z hz
    have := hchain z (by simpa [hcdJ.len] using hz)
    simpa [hcdJ.len] using this
  have hdsSplit : (dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj)).map (·.2.2)
      = ((dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj)).take dJ.nP).map (·.2.2)
        ++ ((dJ.dsF i jcI (Level.substFn φ cAJ.1.levelParams usj)).drop dJ.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨psJ, fsJ, hys, hspY₁, hspY₂⟩ := spineFit_append_inv hspC
  have hlenPY : psJ.length = dJ.nP := by
    rw [hspY₁.length_eq, List.length_map, List.length_take, hcdJ.len]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlenFY : fsJ.length = cA.2 := by
    rw [hspY₂.length_eq, List.length_map, List.length_drop, hcdJ.len, ← hnFJ]
    omega
  have hkJ : 0 < dJ.k := by omega
  have hpsJ : SpineFit ρ (dJ.params (Level.substFn φ cAJ.1.levelParams usj)) psJ := by
    have hsat := sat_of_spineFit (Sat_nil V ρ) hspY₁
    rw [List.append_nil] at hsat
    exact spineFit_of_sat_len (by rw [hlenPY, G.reps.params_length hkJ _])
      ((hIJ.paramsIff i jcI cAJ hi' hjJ _ _).mpr hsat)
  have hfsJ : SpineFit (consList psJ ρ)
      ((dJ.Fss i (Level.substFn φ cAJ.1.levelParams usj)).getD jcI []) fsJ := by
    rw [IsBlockModel.Fss_getD hjJ]; exact hspY₂
  refine ⟨fsJ, hlenFY, ?_, ?_⟩
  · rw [hys, hnP']
    exact List.drop_left' hlenPY
  · rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hys, hctorName,
      congrFun (hagR cAJ.1.name (fun c' hc' he => by
        have hd := (I.recCvDoor (by rw [← I.kT]; exact hc')).1
        rw [← he, hfindJ2] at hd
        exact nomatch hd)) _,
      hIJ.ctor i jcI cAJ hi' hjJ _ ρ psJ fsJ hpsJ hfsJ, G.inj, hwJ]
    rfl


/-! ## The rule law at the nested block (item 5 step 2e, the instantiation) -/

/-- **THE RULE LAW AT A RESTORED RULE** — `blockRecRuleLawG` at the
nested data.  Of the four things the generalised law asks of an arm,
THREE are in the tree: the LEAF is `nestedRecLeaf`, closed
(`nestedRecLeaf_below`), typed at the SCRATCH readings (the two
Π-towers are one set, `towerAgree`) and satisfying the scratch
equations (`NestedRecTuple`, the equations NAMED — §U.29 (yy)); the
SPINE is `recSpineFit`; the RIGHT-HAND SIDE is `ruleVal`.  The
fourth — the MAJOR — is the two arms' own, and is the hypothesis
`hmajor` here, with the mimic's outer `vpa` conjunct `hvpa`. -/
theorem NestedTailIn.recRuleLawOf {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    (E : NestedRecEqs (D) PC (fun ψ => b.elimLevel.eval ψ) rdsM concM
      (fun φ' => (DA).recEqs mpA.base2 b.elimLevel φ'))
    (Tu : NestedRecTuple (D) s rdsM concM (fun φ' => (DA).recEqs mpA.base2 b.elimLevel φ'))
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    (hleafR : ∀ c, c < (D).kT → ∀ φ' : Name → Nat,
      mpP.base2.acval (nestedRecCvAt p.k cvRms cvRns c).name φ'
        = nestedRecLeaf (D).kT s rdsM concM
            (fun φ'' => (DA).recEqs mpA.base2 b.elimLevel φ'') b.rlps c φ')
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    {c : Nat} (hc : c < b.k) {i : Nat} {cA : ConstantVal × Nat}
    (hi : ((DA).ctorsM c)[i]? = some cA)
    {a : AuxStored} (ha : stored[c]? = some a)
    {o : RecRule} (hnf : o.nfields = cA.2)
    {Ra : (Name → Nat) → AnnotTerm}
    (hreadRa : ∀ ψ : Name → Nat,
      denoteMeta mpP.base2.acval
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) ψ 0 o.rhs
        = some (Ra ψ))
    (hwdRa : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Ra ψ))
    (hRaVal : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (Ra ψ)
      = interp V ρ ((DA).ruleRhsAV mpA.base2 b.elimLevel
          (fun t' => nestedRecLeaf (D).kT s rdsM concM
            (fun φ'' => (DA).recEqs mpA.base2 b.elimLevel φ'') b.rlps t' ψ) c i cA.2
          (restrictΨ b.rlps ψ)))
    (φ : Name → Nat)
    (hvpa : ∀ us : List Level, us.length = (nestedRecCvAt p.k cvRms cvRns c).levelParams.length →
      ∀ lvls pins, RecRule.fire o = .nested lvls pins →
      ∀ ii, ii < RecRule.ctorParams o →
      ∃ vpa : AnnotTerm,
        denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ a.rP
          (ConLeche.Verify.openRev 0 a.rP
            ((pins.getD ii default).instantiateLevelParams (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) = some vpa ∧
        ∀ (ρ : Nat → V) (zs : List AnnotTerm) (TVa restR : AnnotTerm),
          zs.length = a.rP → (∀ z ∈ zs, WellDenotedV V ρ z) →
          denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
            ((nestedRecCvAt p.k cvRms cvRns c).type.instantiateLevelParams (nestedRecCvAt p.k cvRms cvRns c).levelParams us) = some TVa →
          TeleFitPA V ρ TVa zs restR →
          WellDenotedV V ρ (ConLeche.Model.AnnotTerm.instRevChain zs vpa))
    (hmajor : ∀ (us : List Level), us.length = (nestedRecCvAt p.k cvRms cvRns c).levelParams.length →
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find? (RecRule.ctor o) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
        (TVa TVja restC : AnnotTerm),
        xs.length = a.mI →
        ys.length = RecRule.ctorParams o + RecRule.nfields o →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands o (nestedRecCvAt p.k cvRms cvRns c).levelParams us cvj.levelParams [] a.rP).1 →
        (∀ lvls pins, RecRule.fire o = .nested lvls pins →
          ∀ ii, ii < RecRule.ctorParams o →
          ∀ vpa : AnnotTerm,
            denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ a.rP
              (ConLeche.Verify.openRev 0 a.rP
                ((pins.getD ii default).instantiateLevelParams (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) = some vpa →
            interp V ρ (ys.getD ii default)
              = interp V ρ (ConLeche.Model.AnnotTerm.instRevChain (xs.take a.rP) vpa)) →
        IotaIndexPin (V := V) ρ restC (RecRule.ctorParams o) a.mI a.rP xs →
        denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          ((nestedRecCvAt p.k cvRms cvRns c).type.instantiateLevelParams (nestedRecCvAt p.k cvRms cvRns c).levelParams us) = some TVa →
        denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        TeleFitPA V ρ TVja ys restC →
        ∀ ps : List V,
          SpineFit ρ ((DA).params (restrictΨ b.rlps
            (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us))) ps →
          ∃ fsY : List V, fsY.length = cA.2 ∧
            (ys.map (interp V ρ)).drop (RecRule.ctorParams o) = fsY ∧
            interp V ρ (AnnotTerm.mkAppN (mpP.base2.acval (RecRule.ctor o)
                (Level.substFn φ cvj.levelParams usj)) ys)
              = (DA).inj (restrictΨ b.rlps (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us)) c i fsY) :
    RecRuleLaw mpP.base2 φ (nestedRecCvAt p.k cvRms cvRns c).name (nestedRecCvAt p.k cvRms cvRns c) a.mI a.rP o := by
  have hkT : (D).kT = b.k := I.kT
  have hdk : (DA).k = b.k := S.record.k
  have hcT : c < (D).kT := by rw [hkT]; exact hc
  have hcA : c < (DA).k := by rw [hdk]; exact hc
  have hnP : (DA).nP = b.nP := rfl
  have hnC : (DA).nCtors = b.ctors.length := I.nCtorsA_eq S
  have hnI : (DA).nIdxAt c = (fms.getD c default).nIdx := by
    obtain ⟨f, hf⟩ : ∃ f, fms[c]? = some f :=
      ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact hc)⟩
    rw [mutualBlockModel_nIdxAt hf, List.getD_eq_getElem?_getD, hf]
    rfl
  have hrdsR : ∀ t, t < (DA).k → ∀ ψ : Name → Nat,
      (DA).blockRds mpA.base2 b.elimLevel t (restrictΨ b.rlps ψ)
        = (DA).blockRds mpA.base2 b.elimLevel t ψ := by
    intro t ht ψ
    refine (S.recData t (by rw [← hdk]; exact ht)).1.params _ _ fun q hq => ?_
    rw [(hshapeA t (by rw [← hdk]; exact ht)).2] at hq
    exact restrictΨ_agree b.rlps ψ q hq
  obtain ⟨hrPa, hmIa⟩ := I.recArgSums ha
  refine blockRecRuleLawG mpP.base2 S.reps S.record.pins (fun ψ => (S.typed ψ).1)
    (fun ψ => (S.typed ψ).2) (fun n ψ ρ => mpA.acval_validV n ψ ρ)
    (fun ψ hw => ConLeche.Model.elimLevel_zero_of_w_zero I.large ψ hw) (fun ψ => S.readings ψ)
    (fun ψ mm hmm ρ => (S.recData mm (by rw [← hdk]; exact hmm)).1.okTy ψ ρ) hrdsR
    (Leaf := fun t' ψ => nestedRecLeaf (D).kT s rdsM concM
      (fun φ'' => (DA).recEqs mpA.base2 b.elimLevel φ'') b.rlps t' ψ)
    (fun t' _ ψ => nestedRecLeaf_below R E t' ψ) ?_ ?_ hcA hi ((S.recData c hcA).1.len)
    (fun ψ q hq h0 => ((S.recData c hcA).1.bits ψ q hq).mp h0)
    (fun ψ => hleafR c hcT ψ) ?_ ?_ hnf hreadRa hwdRa hRaVal φ ?_ hvpa hmajor
  · -- **the leaf is typed at the SCRATCH readings** (`towerAgree`)
    intro t' ht' ψ ρ
    have ht'b : t' < b.k := by rw [← hdk]; exact ht'
    have ht'T : t' < (D).kT := by rw [hkT]; exact ht'b
    have h := nestedRecLeaf_typed R E Tu t' ht'T ψ ρ
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [I.towerAgree S hnames hctorsJ hK35 ht'b ψ ρ (NestedTailIn.readAtOf R ht'T ψ)
      (I.lenAtOf R ht'b ψ)] at h2
    exact h2
  · -- **the equations hold at the tuple of leaves**
    intro ψ ρ e he
    obtain ⟨A, hA, heqs⟩ := Tu (restrictΨ b.rlps ψ) ρ
    have hlist : (List.range (DA).k).map (fun t' => interp V ρ (nestedRecLeaf (D).kT s rdsM concM
          (fun φ'' => (DA).recEqs mpA.base2 b.elimLevel φ'') b.rlps t' ψ))
        = (List.range (D).kT).map A := by
      rw [hkT, ← hdk]
      refine List.map_congr_left fun t' ht' => ?_
      have ht'T : t' < (D).kT := by rw [hkT, ← hdk]; exact List.mem_range.mp ht'
      unfold nestedRecLeaf
      rw [hdk, ← hkT]
      exact (hA t' ht'T).2.1
    rw [hlist]
    exact heqs e he
  · -- **the major index**
    rw [hmIa, hnP, hdk, hnC, hnI]
    unfold ConLeche.MutualBlock.rulePrefix ConLeche.MutualBlock.n
    rfl
  · -- **the rule prefix**
    rw [hrPa, hnP, hdk, hnC]
    unfold ConLeche.MutualBlock.rulePrefix ConLeche.MutualBlock.n
    rfl
  · -- **the recursor's spine** (`recSpineFit`, through the transfer)
    intro us hus cvj usj ρ xs ys TVa restR hxl hTVa hfitR
    have hinstR : ∀ (dp : Nat) (e : Expr),
        denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) φ dp
            (e.instantiateLevelParams (nestedRecCvAt p.k cvRms cvRns c).levelParams us)
          = denoteMeta mpP.base2.acval (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2))
            (Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us) dp e :=
      fun dp e => denoteMeta_instLevels (acvalParamsAt_of_core mpP.base2) φ dp e
    generalize hψR : Level.substFn φ (nestedRecCvAt p.k cvRms cvRns c).levelParams us = ψR at hinstR ⊢
    have hTVa' : TVa = mkPisAV (rdsM c ψR) (concM c) := by
      have h' := hTVa
      rw [hinstR] at h'
      exact Option.some.inj (h'.symm.trans (I.recTyReadP hndR hagR R hcT ψR))
    have hwl : (xs ++ [AnnotTerm.mkAppN (mpP.base2.acval (RecRule.ctor o)
        (Level.substFn φ cvj.levelParams usj)) ys]).length = (rdsM c ψR).length := by
      rw [List.length_append, List.length_singleton, hxl, I.lenAtOf R hc ψR, hmIa]
      unfold ConLeche.MutualBlock.rulePrefix ConLeche.MutualBlock.n
      omega
    have hfit := I.recSpineFit S hnames hctorsJ hK35 R hc ψR ρ hwl (by rw [← hTVa']; exact hfitR)
    rw [← hrdsR c hcA ψR] at hfit
    exact hfit


end Run

end ConLeche.Model
