module

public import ConLeche.Model.Inductives.NestedCtorLeaf
public import ConLeche.Model.Inductives.WhnfContentRun
public import ConLeche.Model.Inductives.CopyWalkFactsRun
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedRestore
import ConLeche.Model.Inductives.RestoreRead
import ConLeche.Model.Inductives.FixData

public section

/-!
# The restored constructor, READ (task #279 M-D′ D2/D3, DESIGN §M.52)

ONE per-constructor reading serves both assemblies left in M-D′: D2's
`whnfContent_of_run` asks, at every copy constructor's field, the
reading at the formers' model `mp₁` of the RESTORED stored field as
`restoreAV`'s arm (`whnfContent_field`'s `hrest`), and D3's
`NestedCtorLeaf.read` asks the reading of a real member's restored
constructor type as `mkPisAV dsRestored body`.  Both are the SAME
per-field plumbing — this module states it once, generic in the
constructor:

* **`RestoredFieldsRead`** — every field of constructor `Ja`, restored
  at the constructor's own parameter openers, reads at `mp₁` as
  `restoreAV`'s arm;
* **`restoredCtor_read`** — from it, the parameter openers' readings
  and the residual's, the restored constant reads as the Π-tower over
  `dsRestored` (`restoreNested_openPis` + `denoteMeta_of_openPis`; the
  binder data kept by the restore give the auxiliary bits);
* **`restoredFieldsRead_of_stored`** — `RestoredFieldsRead` from the
  constructor's STORED data by field kind: an ordinary field is its
  own restoration and transfers down whole (it resolves before the
  block); a field recursive or reflexive into a REAL member is its own
  restoration and is read from its PIECES (`restoredCopyField_read` at
  the member's own head: the telescope domains and index arguments
  resolve before the block and transfer down, the parameter openers
  read as `paramBvarsAt`, the head is stored at `env₁`); a field into a
  COPY is `restoredField_read_copy` at the target pin's data.

The downward transfer is task #310's: a term resolving BEFORE the
block satisfies all three of its subject conditions at once
(`down_of_resolve`).  The target pins' components' readings at `mp₁`
are a hypothesis here (`hpinAll`): the run supplies them from the
pins' inference at the scratch model, transferred down under the
pins' blind mentions (K.15/`PinsMentionReal`), `NoProjAt` (task #309)
and the pins' literal support — the last a NAMED run fact.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind NestedPin ElimState
  MutualBlock)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Kit: resolution up an extension, and the transfer of a resolving term -/

omit [SetTheory V] in
/-- Resolution is monotone in the environment's stored names. -/
theorem Expr.constsResolve_of_find?_mono {env env' : Env}
    (hup : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ e : Expr, e.constsResolve env = true → e.constsResolve env' = true
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit (.natVal _), h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hup _ h.1.1, hup _ h.1.2⟩, hup _ h.2⟩
  | .lit (.strVal _), h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hup _ h.1.1.1.1.1.1.1.1.1, hup _ h.1.1.1.1.1.1.1.1.2⟩,
      hup _ h.1.1.1.1.1.1.1.2⟩, hup _ h.1.1.1.1.1.1.2⟩, hup _ h.1.1.1.1.1.2⟩,
      hup _ h.1.1.1.1.2⟩, hup _ h.1.1.1.2⟩, hup _ h.1.1.2⟩, hup _ h.1.2⟩, hup _ h.2⟩
  | .const n _, h => hup n h
  | .fvar _ ty, h => Expr.constsResolve_of_find?_mono hup ty h
  | .app f a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.constsResolve_of_find?_mono hup f h.1, Expr.constsResolve_of_find?_mono hup a h.2⟩
  | .lam ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.constsResolve_of_find?_mono hup ty h.1, Expr.constsResolve_of_find?_mono hup b h.2⟩
  | .forallE ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.constsResolve_of_find?_mono hup ty h.1, Expr.constsResolve_of_find?_mono hup b h.2⟩
  | .letE t v b, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Expr.constsResolve_of_find?_mono hup t h.1.1,
      Expr.constsResolve_of_find?_mono hup v h.1.2⟩, Expr.constsResolve_of_find?_mono hup b h.2⟩
  | .proj s _ e, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hup s h.1, Expr.constsResolve_of_find?_mono hup e h.2⟩

/-- **A term resolving before the block transfers down** (task #310's
three subject conditions at once): its blind mentions are stored
before the block, hence at `env₁`; its literals' support names
likewise; and it has no projection node at a slot of a name fresh
before the block — which is every slot `envAux` tables and `env₁` does
not (`hTbl`).  The reading moves to `mp₁`'s carrier by the agreement on
`env₁`'s names. -/
theorem down_of_resolve {μ : CheckMode} {env env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    (hF : FindPreserved env₁ envAux)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hup : ∀ n, (env.find? n).isSome = true → (env₁.find? n).isSome = true)
    {ψ : Name → Nat} {dpt : Nat} {e : Expr} (hres : e.constsResolve env = true)
    {ea : AnnotTerm} (h : denoteMeta mpAux.base2.acval envAux ψ dpt e = some ea) :
    denoteMeta mp₁.base2.acval env₁ ψ dpt e = some ea := by
  rw [denoteMeta_acval_congr hag]
  exact denoteMeta_down_blind hF dpt e
    (fun T hT => hup T (Expr.find?_isSome_of_mentionsConst e hres
      (Expr.mentionsConst_of_mentionsConstE e hT)))
    (litsResolve_of_constsResolve _ (Expr.constsResolve_of_find?_mono hup e hres))
    (fun sn i h1 h2 => Expr.noProjAt_blank _ (Expr.noProjAt_of_constsResolve (hTbl sn i h1 h2) _ hres))
    h

/-- A read spine of terms resolving before the block transfers down. -/
theorem denoteMetaSpine_down_of_resolve {μ : CheckMode} {env env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    (hF : FindPreserved env₁ envAux)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hup : ∀ n, (env.find? n).isSome = true → (env₁.find? n).isSome = true)
    {ψ : Name → Nat} {dpt : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ a ∈ as, a.constsResolve env = true) →
      DenoteMetaSpine mpAux.base2.acval envAux ψ dpt as vs →
      DenoteMetaSpine mp₁.base2.acval env₁ ψ dpt as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hres, .cons ha hrest =>
    .cons (down_of_resolve mp₁ mpAux hF hag hTbl hup (hres a List.mem_cons_self) ha)
      (denoteMetaSpine_down_of_resolve mp₁ mpAux hF hag hTbl hup
        (fun a' ha' => hres a' (List.mem_cons_of_mem _ ha')) hrest)

/-! ## The per-constructor reading -/

namespace IndRepData

variable (d : IndRepData V)

/-- **Every field of constructor `Ja`, restored, reads as `restoreAV`'s
arm at the formers' model** — the currency both `whnfContent_field`
(`hrest`) and `restoredCtor_read` consume. -/
@[expose] def RestoredFieldsRead {μ : CheckMode} {env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux) (ψ : Name → Nat) (k₀ Ja : Nat)
    (R : ConLeche.RestoreTbl) (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat)
    (tgtDsA : Nat → List AnnotTerm) : Prop :=
  ∀ (i : Nat) (x : Expr), (d.xFvsF Ja)[i]? = some x →
    denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i)
        (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD)
      = some (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i)

/-- A restored entry, positionally: the auxiliary bits; the auxiliary
domain below the parameter count, `restoreAV` at a field position. -/
theorem dsRestored_getElem? (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm)
    (k : Nat) :
    (d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA)[k]?
      = ((d.dsF Ja ψ)[k]?).map fun e =>
          (e.1, e.2.1, if k < d.nP then e.2.2 else d.restoreAV m ψ k₀ Ja tgtCont tgtLps tgtDsA (k - d.nP)) := by
  unfold dsRestored
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases (d.dsF Ja ψ)[k]? with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add]
    split <;> rfl

end IndRepData

/-- **The restored constructor type reads as the Π-tower over
`dsRestored`** (M-D′ D3's `NestedCtorLeaf.read`, generic in the
constructor): the restored constant opens at the auxiliary openers
with the restore at every field position (`restoreNested_openPis`),
the parameter openers read at `mp₁` as the auxiliary domains, the
fields as `restoreAV`'s arms (`RestoredFieldsRead`), the residual as
`body`; the restored binders keep the auxiliary binder data
(`restoreWalk_stripPis`), which carry the auxiliary reading's bits
(`denoteMeta_openPis'`). -/
theorem restoredCtor_read {μ : CheckMode} {env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    {ψ : Name → Nat} {d : IndRepData V} {k₀ Ja nF : Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    {R : ConLeche.RestoreTbl} {ty tyR crest : Expr} {bodyA body : AnnotTerm}
    (hRwf : R.WF) (hRnP : R.nP = d.nP)
    (hres : ConLeche.restoreNested R ty = .ok tyR) (hnf : ty.hasFvar = false)
    (hop₁ : ConLeche.openPisAtFvars d.nP ty 0 = some (d.fvsPF Ja, crest))
    (hop₂ : ConLeche.openPisAtFvars nF crest d.nP = some (d.xFvsF Ja, d.xrestF Ja))
    (hreadA : denoteMeta mpAux.base2.acval envAux ψ 0 ty = some (mkPisAV (d.dsF Ja ψ) bodyA))
    (hlen : (d.dsF Ja ψ).length = d.nP + nF)
    (hreadP : ∀ (k : Nat) (y : Expr), (d.fvsPF Ja)[k]? = some y →
      denoteMeta mp₁.base2.acval env₁ ψ k y.fvarTypeD = some ((d.dsF Ja ψ).getD k default).2.2)
    (hfields : d.RestoredFieldsRead mp₁ mpAux ψ k₀ Ja R tgtCont tgtLps tgtDsA)
    (hresid : denoteMeta mp₁.base2.acval env₁ ψ (d.nP + nF)
      (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) (d.xrestF Ja)) = some body) :
    denoteMeta mp₁.base2.acval env₁ ψ 0 tyR
      = some (mkPisAV (d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA) body) := by
  -- the auxiliary type opened at all its binders
  have hop : ConLeche.openPisAtFvars (d.nP + nF) ty 0 = some (d.fvsPF Ja ++ d.xFvsF Ja, d.xrestF Ja) :=
    ConLeche.openPisAtFvars_add' d.nP hop₁ (by rw [Nat.zero_add]; exact hop₂)
  have hpLen : (d.fvsPF Ja).length = d.nP := openPisAtFvars_length _ hop₁
  have hxLen : (d.xFvsF Ja).length = nF := openPisAtFvars_length _ hop₂
  have htakeP : (d.fvsPF Ja ++ d.xFvsF Ja).take d.nP = d.fvsPF Ja := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  -- the restored type opened alike
  obtain ⟨fvsR, restR, hopR, hlenR, htake, hfieldR, hrestE⟩ :=
    ConLeche.restoreNested_openPis hRwf hres hnf (n := d.nP + nF) (by omega) hop
  rw [hRnP, htakeP] at htake hfieldR hrestE
  -- the binders: the auxiliary type's, and the restored type's keep the metas
  obtain ⟨bsA, rA, hsA, -, -, -⟩ := Verify.openPisAtFvars_stripPis (d.nP + nF) hop
  obtain ⟨bsR, rR, hsR, -, -, -⟩ := Verify.openPisAtFvars_stripPis (d.nP + nF) hopR
  have hbsLenA : bsA.length = d.nP + nF := stripPis_length' _ hsA
  have hbsLenR : bsR.length = d.nP + nF := stripPis_length' _ hsR
  have hmeta : ∀ (k : Nat) (bA bR : Expr × ConLeche.BinderMeta), bsA[k]? = some bA →
      bsR[k]? = some bR → bR.2 = bA.2 := by
    obtain ⟨mid, hpA, hmA⟩ := ConLeche.stripPis_split d.nP (m := nF) hsA
    have hpA' : ty.stripPis R.nP = some (bsA.take d.nP, mid) := by rw [hRnP]; exact hpA
    obtain ⟨mid', hwalk, hsR'⟩ := ConLeche.restoreNested_stripPis hres hpA'
    obtain ⟨bs', r', hs', -, hall', -⟩ := ConLeche.restoreWalk_stripPis nF hwalk hmA
    have hsRn : tyR.stripPis (d.nP + nF) = some (bsA.take d.nP ++ bs', r') := by
      have := ConLeche.stripPis_append' R.nP hsR' hs'
      rwa [hRnP] at this
    rw [hsRn] at hsR
    obtain ⟨hbsR, -⟩ := Prod.mk.inj (Option.some.inj hsR)
    intro k bA bR hbA hbR
    rw [← hbsR] at hbR
    have hlt : (bsA.take d.nP).length = d.nP := by rw [List.length_take]; omega
    by_cases hk : k < d.nP
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hk, hbA] at hbR
      rw [Option.some.inj hbR]
    · rw [List.getElem?_append_right (by omega), hlt] at hbR
      have hbA' : (bsA.drop d.nP)[k - d.nP]? = some bA := by
        rw [List.getElem?_drop, show d.nP + (k - d.nP) = k by omega]; exact hbA
      exact (hall' (k - d.nP) bA bR hbA' hbR).1
  -- the auxiliary reading's bits are the auxiliary binders'
  obtain ⟨pps, b₀, heq, -, hlenpps, hbind⟩ := denoteMeta_openPis' (d.nP + nF) hop hsA hreadA
  obtain ⟨hpps, -⟩ := mkPisAV_inj (by rw [hlenpps, hlen]) heq
  -- the forward reading of the restored type
  have hts : ((d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA).map (·.2.2)).length
      = d.nP + nF := by
    rw [List.length_map, d.dsRestored_length, hlen]
  have hmain := denoteMeta_of_openPis (d.nP + nF) hopR hsR hts (fun k x t hx ht => by
      rw [Nat.zero_add]
      rw [List.getElem?_map, d.dsRestored_getElem?] at ht
      by_cases hk : k < d.nP
      · -- a parameter opener: the auxiliary one, read as the auxiliary domain
        have hxP : (d.fvsPF Ja)[k]? = some x := by
          rw [← htake, List.getElem?_take_of_lt hk]; exact hx
        have hr := hreadP k x hxP
        rw [List.getD_eq_getElem?_getD] at hr
        cases hdk : (d.dsF Ja ψ)[k]? with
        | none => rw [hdk] at ht; exact nomatch ht
        | some e =>
          rw [hdk] at ht hr
          simp only [Option.map_some, Option.some.injEq, if_pos hk] at ht
          rw [← ht]; exact hr
      · -- a field opener: the restored one, read as `restoreAV`'s arm
        obtain ⟨i, rfl⟩ : ∃ i, k = d.nP + i := ⟨k - d.nP, by omega⟩
        have hi : i < nF := by
          have := (List.getElem?_eq_some_iff.mp hx).1; omega
        obtain ⟨xA, hxA⟩ : ∃ xA, (d.xFvsF Ja)[i]? = some xA :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hxA' : (d.fvsPF Ja ++ d.xFvsF Ja)[d.nP + i]? = some xA := by
          rw [List.getElem?_append_right (by omega), hpLen, Nat.add_sub_cancel_left]; exact hxA
        obtain ⟨tyX, rfl, hE⟩ := hfieldR (d.nP + i) xA x (by omega) hxA' hx
        cases hdk : (d.dsF Ja ψ)[d.nP + i]? with
        | none => rw [hdk] at ht; exact nomatch ht
        | some e =>
          rw [hdk] at ht
          simp only [Option.map_some, Option.some.injEq, if_neg hk, Nat.add_sub_cancel_left] at ht
          rw [← ht, denoteMeta_erasedEq hE]
          exact hfields i xA hxA)
    (by rw [Nat.zero_add, denoteMeta_erasedEq hrestE]; exact hresid)
  rw [hmain]
  congr 2
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_zipWith, List.getElem?_map, d.dsRestored_getElem?]
  cases hdk : (d.dsF Ja ψ)[k]? with
  | none =>
    have hbR : bsR[k]? = none := by
      rw [List.getElem?_eq_none_iff] at hdk ⊢; omega
    simp [hbR]
  | some e =>
    have hk : k < d.nP + nF := by
      have := (List.getElem?_eq_some_iff.mp hdk).1; omega
    obtain ⟨bR, hbR⟩ : ∃ bR, bsR[k]? = some bR := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨x, hx⟩ : ∃ x, (d.fvsPF Ja ++ d.xFvsF Ja)[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_append]; omega)⟩
    obtain ⟨p, hp, hp1, ⟨bm, hbm, hp2⟩, -⟩ := hbind k x hx
    rw [← hpps, hdk] at hp
    obtain rfl := Option.some.inj hp
    have hmk := hmeta k bm bR hbm hbR
    simp only [hbR, Option.map_some, hmk, ← hp2, ← hp1]


/-! ## `RestoredFieldsRead` from the stored data, by field kind -/

set_option maxHeartbeats 800000 in
/-- **Every field of a stored constructor, restored, reads as
`restoreAV`'s arm** (DESIGN §M.52).  By the field's kind at the
auxiliary datum: an ORDINARY field mentions no table name (it resolves
before the block), so it is its own restoration and its reading
transfers down whole; a field RECURSIVE or REFLEXIVE into a REAL
member likewise restores to itself (its telescope domains and index
arguments resolve before the block, its head is a real member's name)
and is read from its pieces at the member's stored former at `env₁`
(`restoredCopyField_read` with the parameter openers reading as
`paramBvarsAt`), which is the datum's entry (`recEntry`/`reflEntry`) at
the formers' carrier; a field into a COPY is `restoredField_read_copy`
at the target pin's data (`hpinAll`: the pin's shape and its
components' readings at `mp₁`, the container's leaf at the pin's level
substitution agreeing with the auxiliary carrier at the pin's
assignment). -/
theorem restoredFieldsRead_of_stored {μ : CheckMode} {env env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    (hF : FindPreserved env₁ envAux)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hup : ∀ n, (env.find? n).isSome = true → (env₁.find? n).isSome = true)
    {st : ElimState} {b : MutualBlock}
    {d : IndRepData V} {k₀ Ja : Nat} {cA : ConstantVal × Nat} {lpsT : List Name}
    {ks : List (RecFieldKind × Nat)} {R : ConLeche.RestoreTbl} {ψ : Name → Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    -- the constructor at the auxiliary datum, and its kernel kinds
    (hD : FixCtorDataI mpAux.base2 d.env₀ (d.memberName (d.mems Ja)) lpsT cA.1 d.nP cA.2
      (d.nIdxAt (d.mems Ja)) d.resSort d.isProp d.large (d.idxF Ja) (d.dsF Ja) (d.esF Ja)
      (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja) (d.eissF Ja) (d.tssF Ja)
      (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hMO : MutualOpened env b.members3 b.lps b.nP cA.2 ks (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja))
    (hbnP : b.nP = d.nP)
    (hks : ∀ i, i < cA.2 → (d.ksF Ja).getD i .ordinary = kindAt ks i)
    (hview : d.ksR Ja = d.ksF Ja ∧ d.tgtsR Ja = d.tgts Ja ∧ d.eissR Ja = d.eissF Ja ∧
      d.tssR Ja = d.tssF Ja)
    (htgtLt : ∀ i, d.tgts Ja i < d.k) (hdk : d.k = k₀ + st.pins.length)
    -- the real members at the formers' environment, the table's names
    (hrealStored : ∀ t, t < k₀ → (env₁.find? (d.memberName t)).isSome = true)
    (hrealLps : ∀ t, t < k₀ → ∀ ci : ConstantInfo, env₁.find? (d.memberName t) = some ci →
      ci.toConstantVal.levelParams = lpsT)
    (hauxFresh : ∀ n ∈ R.auxNames, env.find? n = none ∧ ∀ t, t < k₀ → d.memberName t ≠ n)
    -- the table at the constructor's parameter openers
    (hRS : (R.instAt (d.fvsPF Ja)).Named) (hRnP : R.nP = d.nP)
    (hpinName : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q →
      d.memberName (k₀ + jq) = q.aux)
    (hlookS : ∀ q ∈ st.pins, ∃ pin', (R.instAt (d.fvsPF Ja)).pins.lookup q.aux = some pin' ∧
      Expr.ErasedEq pin' q.pin ∧ pin'.looseBVarsBounded 0 = true)
    (hrecS : ∀ q ∈ st.pins, (R.instAt (d.fvsPF Ja)).recMap.lookup q.aux = none)
    -- the target pins' data, at the formers' model
    (hpinAll : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q →
      ∃ (J'' : Name) (lvls'' : List Level) (Ds'' : List Expr) (ci : ConstantInfo),
        q.pin = Expr.mkAppN (.const J'' lvls'') Ds'' ∧ tgtCont jq = J'' ∧
        env₁.find? J'' = some ci ∧ lvls''.length = ci.toConstantVal.levelParams.length ∧
        mp₁.base2.acval J'' (Level.substFn ψ ci.toConstantVal.levelParams lvls'')
          = mpAux.base2.acval J'' (tgtLps jq) ∧
        (∀ a ∈ Ds'', Expr.WScoped d.nP a) ∧
        DenoteMetaSpine mp₁.base2.acval env₁ ψ d.nP Ds'' (tgtDsA jq)) :
    d.RestoredFieldsRead mp₁ mpAux ψ k₀ Ja R tgtCont tgtLps tgtDsA := by
  intro i x hx
  have hi : i < cA.2 := by rw [← hD.xLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hpLen : (d.fvsPF Ja).length = d.nP := hD.pLen
  have hlenP : (d.fvsPF Ja).length = R.nP := by rw [hpLen, hRnP]
  have hfvsPBlind : ∀ (T : Name), ∀ a ∈ d.fvsPF Ja, a.mentionsConstE T = false := by
    intro T a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hD.pIdx k a hk
    rfl
  have hksLen : (d.ksF Ja).length = cA.2 := hD.ksLen
  have hcopyIff : d.copyPos k₀ Ja i ↔
      (i ∈ ConLeche.recIdxOf (d.ksF Ja) ∧ k₀ ≤ d.tgts Ja i) := by
    unfold IndRepData.copyPos; rw [hview.1, hview.2.1]
  -- ## the continuation at a recursive or reflexive field, from its pieces
  have key : ∀ (n : Nat) (afvs idx : List Expr),
      ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
        Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (lpsT.map Level.param))
          (d.fvsPF Ja ++ idx)) →
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true) →
      (∀ e ∈ idx, e.constsResolve env = true) →
      ((d.tssF Ja ψ).getD i []).length = n →
      (∀ (k : Nat) (a : Expr), afvs[k]? = some a →
        denoteMeta mpAux.base2.acval envAux ψ (d.nP + i + k) a.fvarTypeD
          = some (((d.tssF Ja ψ).getD i []).getD k default).2.2) →
      DenoteMetaSpine mpAux.base2.acval envAux ψ (d.nP + i + n) idx ((d.eissF Ja ψ).getD i []) →
      ((d.dsF Ja ψ).getD (d.nP + i) default).2.2
        = mkPisAV ((d.tssF Ja ψ).getD i [])
            (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts Ja i)) ψ)
              (paramBvarsAt d.nP (d.nP + i + n) ++ (d.eissF Ja ψ).getD i [])) →
      i ∈ ConLeche.recIdxOf (d.ksF Ja) →
      denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i)
          (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD)
        = some (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
    intro n afvs idx hop hdomsRes hidxRes htss hdomsReadA hidxReadA hentry hmemRec
    -- the pieces, at the formers' model
    have hdomsRead : ∀ (k : Nat) (a : Expr), afvs[k]? = some a →
        denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i + k) a.fvarTypeD
          = some (((d.tssF Ja ψ).getD i []).getD k default).2.2 :=
      fun k a ha => down_of_resolve mp₁ mpAux hF hag hTbl hup (hdomsRes a (List.mem_of_getElem? ha))
        (hdomsReadA k a ha)
    have hidxRead : DenoteMetaSpine mp₁.base2.acval env₁ ψ (d.nP + i + n) idx
        ((d.eissF Ja ψ).getD i []) :=
      denoteMetaSpine_down_of_resolve mp₁ mpAux hF hag hTbl hup hidxRes hidxReadA
    -- the binders' bits: the auxiliary reading peeled against the entry
    obtain ⟨bs, r, hs, -, hshA, -⟩ := Verify.openPisAtFvars_stripPis n hop
    obtain ⟨pps, b, heq, -, hlenpps, hbind⟩ := denoteMeta_openPis' n hop hs (hD.domRead ψ i x hx)
    rw [hentry] at heq
    obtain ⟨hpps, -⟩ := mkPisAV_inj (by rw [hlenpps, htss]) heq
    have hbits : ∀ (k : Nat) (p : Nat × Nat × AnnotTerm) (bm : Expr × ConLeche.BinderMeta),
        ((d.tssF Ja ψ).getD i [])[k]? = some p → bs[k]? = some bm →
        p.1 = 0 ∧ p.2.1 = pwBit ψ bm.2.pw := by
      intro k p bm hp hbm
      have hk : k < n := by rw [← htss]; exact (List.getElem?_eq_some_iff.mp hp).1
      obtain ⟨ty, hty⟩ := hshA k hk
      obtain ⟨p', hp', h1, ⟨bm', hbm', h2⟩, -⟩ := hbind k _ hty
      rw [hpps] at hp
      rw [hp'] at hp
      rw [hbm'] at hbm
      rw [← Option.some.inj hp, ← Option.some.inj hbm]
      exact ⟨h1, h2⟩
    have hdomsRead' : ∀ (k : Nat) (a : Expr) (q : Nat × Nat × AnnotTerm), afvs[k]? = some a →
        ((d.tssF Ja ψ).getD i [])[k]? = some q →
        denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i + k) a.fvarTypeD = some q.2.2 := by
      intro k a q ha hq
      rw [hdomsRead k a ha, List.getD_eq_getElem?_getD, hq]
      rfl
    by_cases hlt : d.tgts Ja i < k₀
    · -- ## into a REAL member: its own restoration, read from its pieces
      have hnotCopy : ¬ d.copyPos k₀ Ja i := by
        rw [hcopyIff]; intro h; omega
      have hself : ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD = x.fvarTypeD := by
        refine ConLeche.restoreI_eq_self hRS _ fun m hm => ?_
        refine mentionsConstE_eq_false_of_opened hop
          (fun a ha => Expr.mentionsConstE_eq_false_of_fresh (hdomsRes a ha) (hauxFresh m hm).1) ?_
        cases hB : (Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (lpsT.map Level.param))
            (d.fvsPF Ja ++ idx)).mentionsConstE m with
        | false => rfl
        | true =>
          exfalso
          rcases (ConLeche.mentionsConstE_mkAppN_const_iff _ _ _).mp hB with h | ⟨a, ha, ham⟩
          · exact (hauxFresh m hm).2 _ hlt h
          · rcases List.mem_append.mp ha with ha | ha
            · rw [hfvsPBlind m a ha] at ham; exact nomatch ham
            · rw [Expr.mentionsConstE_eq_false_of_fresh (hidxRes a ha) (hauxFresh m hm).1] at ham
              exact nomatch ham
      rw [hself, d.restoreAV_of_not_copy _ hnotCopy, hentry]
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hrealStored _ hlt)
      have hciLps := hrealLps _ hlt ci hci
      have hmain := restoredCopyField_read (acval := mp₁.base2.acval) (env := env₁) (φ := ψ) hop hs
        (Ds := d.fvsPF Ja) (idx := idx) (by rw [Expr.mkAppN_append]; exact Expr.ErasedEq.rfl _)
        hci (by rw [hciLps, List.length_map]) htss hbits hdomsRead'
        (denoteMetaSpine_params (d.nP + i + n) hpLen hD.pIdx) hidxRead
      rw [hmain]
      have hacv : mp₁.base2.acval (d.memberName (d.tgts Ja i))
          (Level.substFn ψ ci.toConstantVal.levelParams (lpsT.map Level.param))
          = mpAux.base2.acval (d.memberName (d.tgts Ja i)) ψ := by
        rw [← hag _ (by rw [hci]; rfl)]
        refine mp₁.base2.acval_params _ ci hci _ _ fun q _ => ?_
        rw [hciLps]
        exact Level.substFn_map_param
      rw [hacv]
    · -- ## into a COPY: the fired arm at the target pin's data
      have hcopy : d.copyPos k₀ Ja i := hcopyIff.mpr ⟨hmemRec, by omega⟩
      have hjq : d.tgts Ja i - k₀ < st.pins.length := by have := htgtLt i; omega
      obtain ⟨q, hq⟩ : ∃ q, st.pins[d.tgts Ja i - k₀]? = some q :=
        ⟨_, List.getElem?_eq_getElem hjq⟩
      have hqa : q.aux = d.memberName (d.tgts Ja i) := by
        rw [← hpinName _ q hq, show k₀ + (d.tgts Ja i - k₀) = d.tgts Ja i by omega]
      have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
      obtain ⟨pin', hlook, hpinE, hpinC⟩ := hlookS q hqmem
      have hrec := hrecS q hqmem
      rw [hqa] at hlook hrec
      obtain ⟨J'', lvls'', Ds'', ci, hqp, hcontE, hJ, hlvls, hacv, hDsW, hDsRead⟩ := hpinAll _ q hq
      have hpinE' : Expr.ErasedEq pin' (Expr.mkAppN (.const J'' lvls'') Ds'') := by
        rw [← hqp]; exact hpinE
      have htgtR : d.tgtsR Ja i = d.tgts Ja i := by rw [hview.2.1]
      have harm : i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i := by
        rw [hview.1, htgtR]; exact ⟨hmemRec, by omega⟩
      have hDs : DenoteMetaSpine mp₁.base2.acval env₁ ψ (d.nP + i + n) Ds''
          ((tgtDsA (d.tgtsR Ja i - k₀)).map (·.liftN (i + n) 0)) := by
        rw [htgtR, Nat.add_assoc]
        exact DenoteMetaSpine.weaken_by mp₁.base2 (i + n) hDsRead hDsW
      have hopR : ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
          Expr.mkAppN (.const (d.memberName (d.tgtsR Ja i)) (lpsT.map Level.param))
            (d.fvsPF Ja ++ idx)) := by
        rw [htgtR]; exact hop
      refine restoredField_read_copy mp₁ mpAux hRS hlenP hopR
        (fun a ha m hm => Expr.not_mentionsConst_of_fresh (hdomsRes a ha) (hauxFresh m hm).1)
        (by rw [htgtR]; exact hlook) hpinC (by rw [htgtR]; exact hrec) hpinE' harm
        (by rw [htgtR]; exact hcontE) hJ hlvls (by rw [htgtR]; exact hacv)
        (by rw [hview.2.2.2]; exact htss) (B := AnnotTerm.mkAppN
          (mpAux.base2.acval (d.memberName (d.tgts Ja i)) ψ)
          (paramBvarsAt d.nP (d.nP + i + n) ++ (d.eissF Ja ψ).getD i []))
        (by rw [hD.domRead ψ i x hx, hentry, hview.2.2.2])
        (fun k a ha => by rw [hview.2.2.2]; exact hdomsRead k a ha)
        hDs (by rw [hview.2.2.1]; exact hidxRead)
  -- ## by the field's kind
  rcases hD.opened.kinds i hi with hord | hrec | hrefl
  · -- ORDINARY: its own restoration, transferred down whole
    have hnotCopy : ¬ d.copyPos k₀ Ja i := by
      rw [hcopyIff]
      intro h
      obtain ⟨hmem, -⟩ := h
      rcases (mem_recIdxOf.mp hmem).2 with h | h <;> rw [hord] at h <;> exact nomatch h
    have hres := hMO.ord i x hx (by rw [← hks i hi]; exact hord)
    have hself : ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD = x.fvarTypeD :=
      ConLeche.restoreI_eq_self hRS _ (fun m hm =>
        Expr.mentionsConstE_eq_false_of_fresh hres (hauxFresh m hm).1)
    rw [hself, d.restoreAV_of_not_copy _ hnotCopy]
    exact down_of_resolve mp₁ mpAux hF hag hTbl hup hres (hD.domRead ψ i x hx)
  · -- RECURSIVE: the field IS the member application
    obtain ⟨hhead, htake, -, -, -, -⟩ := hD.opened.recF i x hx hrec
    obtain ⟨-, -, -, hres, -, -⟩ := hMO.recF i x hx (by rw [← hks i hi]; exact hrec)
    rw [hbnP] at hres
    have hxE : x.fvarTypeD = Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (lpsT.map Level.param))
        (d.fvsPF Ja ++ x.fvarTypeD.getAppArgs.drop d.nP) := by
      rw [← htake, List.take_append_drop, ← hhead, Expr.mkAppN_getApp]
    have htss : ((d.tssF Ja ψ).getD i []).length = 0 := by
      rw [hD.tssNone ψ i (by rw [hrec]; decide)]; rfl
    refine key 0 [] (x.fvarTypeD.getAppArgs.drop d.nP) ?_ (fun a ha => absurd ha (by simp)) hres
      htss (fun k a ha => by simp at ha) ?_ ?_ ?_
    · show some ([], x.fvarTypeD) = _
      exact congrArg (fun z => some ([], z)) hxE
    · rw [Nat.add_zero]; exact hD.eisRead ψ i x hx hrec
    · rw [hD.recEntry ψ i hrec hi, hD.tssNone ψ i (by rw [hrec]; decide), Nat.add_zero]
      rfl
    · exact mem_recIdxOf.mpr ⟨by rw [hksLen]; exact hi, Or.inl hrec⟩
  · -- REFLEXIVE: the field opens over its telescope to the member application
    obtain ⟨afvs, body, hop, -, -, hhead, htake, -, -, -, -⟩ := hD.opened.reflF i x hx hrefl
    obtain ⟨afvs', body', hop', -, hres₁, -, -, -, hres₂, -, -⟩ :=
      hMO.reflF i x hx (by rw [← hks i hi]; exact hrefl)
    rw [hbnP, hop] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop')
    rw [hbnP] at hres₂
    obtain ⟨afvs'', body'', hopT, htssLen, hdomsReadA, hidxReadA⟩ := hD.reflOpen ψ i x hx hrefl
    rw [htssLen, hop] at hopT
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopT)
    have hbodyE : body = Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (lpsT.map Level.param))
        (d.fvsPF Ja ++ body.getAppArgs.drop d.nP) := by
      rw [← htake, List.take_append_drop, ← hhead, Expr.mkAppN_getApp]
    refine key _ afvs (body.getAppArgs.drop d.nP) (by rw [hop, ← hbodyE]) hres₁ hres₂ htssLen
      hdomsReadA (by rw [← htssLen]; exact hidxReadA) ?_ ?_
    · rw [hD.reflEntry ψ i hrefl hi, htssLen]
    · exact mem_recIdxOf.mpr ⟨by rw [hksLen]; exact hi, Or.inr hrefl⟩

end ConLeche.Model
