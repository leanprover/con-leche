module

public import ConLeche.Model.Inductives.CopyCtorWalk
public import ConLeche.Verify.Inductives.NestedRestore

public section

/-!
# The restored field, READ (task #279 M-D′ D1, the Model half)

`Verify/Inductives/NestedRestore.lean` evaluates the restore at the
opened level: a copy field `Π afvs, auxJ params idx` restores to a field
that opens at the SAME variables to a residual erasure-equal to
`pin idx`, the table's pin `J lvls Ds` at the index arguments
(`restoreI_copyField`), and a restored constant's openers are `restoreI`
of the auxiliary openers up to erasure (`restoreNested_openPis`).  This
module reads such a field:

* **`denoteMeta_of_openPis`** — the FORWARD Π-reading: a telescope whose
  openers and residual read, reads as `mkPisAV` of the openers' readings
  (bits off the binder data) over the residual's — the converse of
  `denoteMeta_openPis'`.
* **`restoredCopyField_read`** — the restored copy field reads as
  `mkPisAV tss (mkAppN ⟦J⟧ (DsA ++ eiss))`: `restoreAV`'s copy-recursive
  arm (`CopyCtorWalk.lean`) once the pin's readings are weakened to the
  field's depth (`DenoteMetaSpine.weaken_by`) and the container's leaf
  is read at the pin's level substitution.

The readings are taken at an ARBITRARY `acval`/`env` (the model of
`env₁` M-D′ D2 builds): the lemma assembles a reading from readings of
the pieces and asks nothing about how those were obtained — the
agreement between `env₁`'s model and the auxiliary one on the names a
field mentions is the caller's (D2's) fact, not a restriction lemma.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo)

/-! ## The forward Π-reading -/

/-- **A telescope reads from its pieces**: with the `n` openers reading
to `ts` (position by position, at their own depths) and the residual
reading to `b`, the telescope reads as `mkPisAV` of the entries
`(0, pwBit φ bm.pw, t)` — the binder data off `stripPis`. -/
theorem denoteMeta_of_openPis {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
      {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr} {ts : List AnnotTerm} {b : AnnotTerm},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → e.stripPis n = some (bs, r) →
      ts.length = n →
      (∀ (k : Nat) (x : Expr) (t : AnnotTerm), fvs[k]? = some x → ts[k]? = some t →
        denoteMeta acval env φ (d + k) x.fvarTypeD = some t) →
      denoteMeta acval env φ (d + n) o = some b →
      denoteMeta acval env φ d e
        = some (mkPisAV (List.zipWith (fun (bm : Expr × ConLeche.BinderMeta) (t : AnnotTerm) =>
            (0, pwBit φ bm.2.pw, t)) bs ts) b)
  | 0, d, e, fvs, o, bs, r, ts, b, hop, hs, hts, _, hb => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rw [Nat.add_zero] at hb
    simpa [mkPisAV] using hb
  | n + 1, d, e, fvs, o, bs, r, ts, b, hop, hs, hts, hfvs, hb => by
    match e, hop, hs with
    | .forallE ty body bm, hop, hs =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
        obtain ⟨⟨bs₁, r₁⟩, hs₁, hbs⟩ := hs
        simp only [Prod.mk.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        -- the instantiated body strips to binders with the same data
        have hsome : ((body.instantiate1 (.fvar d ty) 0).stripPis n).isSome :=
          Expr.stripPis_instantiate1_isSome n 0 (by rw [hs₁]; rfl)
        obtain ⟨⟨bs₂, r₂⟩, hs₂⟩ := Option.isSome_iff_exists.mp hsome
        have hmeta := stripPis_instantiate1_meta (v := .fvar d ty) n 0 hs₁ hs₂
        have hlen₁ : bs₁.length = n := stripPis_length' n hs₁
        have hlen₂ : bs₂.length = n := stripPis_length' n hs₂
        cases ts with
        | nil => simp at hts
        | cons t ts' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hts
          have hty : denoteMeta acval env φ d ty = some t := by
            have := hfvs 0 (.fvar d ty) t rfl rfl
            simpa [Expr.fvarTypeD] using this
          have hrest := denoteMeta_of_openPis n hop' hs₂ hts
            (fun k x t' hx ht' => by
              have := hfvs (k + 1) x t' (by simpa using hx) (by simpa using ht')
              rw [show d + (k + 1) = d + 1 + k by omega] at this
              exact this)
            (by rw [show d + 1 + n = d + (n + 1) by omega]; exact hb)
          rw [denoteMeta_forallE, hty, hrest]
          show some (AnnotTerm.pi 0 (pwBit φ bm.pw) t
            (mkPisAV (List.zipWith (fun (bm : Expr × ConLeche.BinderMeta) (t : AnnotTerm) =>
              (0, pwBit φ bm.2.pw, t)) bs₂ ts') b)) = _
          simp only [List.zipWith_cons_cons, mkPisAV, Option.some.injEq]
          congr 2
          apply List.ext_getElem?
          intro k
          rw [List.getElem?_zipWith, List.getElem?_zipWith]
          cases hk₁ : bs₁[k]? with
          | none =>
            have hk₂ : bs₂[k]? = none := by
              rw [List.getElem?_eq_none_iff] at hk₁ ⊢; omega
            rw [hk₂]
          | some b₁ =>
            obtain ⟨b₂, hk₂⟩ : ∃ b₂, bs₂[k]? = some b₂ :=
              ⟨_, List.getElem?_eq_getElem (by rw [hlen₂, ← hlen₁]; exact (List.getElem?_eq_some_iff.mp hk₁).1)⟩
            rw [hk₂]
            cases ts'[k]? <;> simp [hmeta k b₁ b₂ hk₁ hk₂]
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _ | .const _ _, hop, _
    | .app _ _, hop, _ | .lam _ _ _, hop, _ | .letE _ _ _, hop, _ | .lit _, hop, _
    | .proj _ _ _, hop, _ => simp [ConLeche.openPisAtFvars] at hop

/-! ## The restored copy field, read -/

/-- **The restored copy field reads as `restoreAV`'s copy-recursive
arm**: a field opening at `n` variables (readings `tss`, bits off the
binder data) to a residual erasure-equal to `J lvls Ds idx`, with the
pin's components reading to `DsA` and the index arguments to `eiss` at
the field's depth, reads as
`mkPisAV tss (mkAppN ⟦J⟧ (DsA ++ eiss))` with `⟦J⟧` the container's leaf
at the pin's level substitution. -/
theorem restoredCopyField_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {xR o : Expr} {n dpt : Nat} {afvs idx Ds : List Expr} {J : Name}
    {lvls : List Level} {ci : ConstantInfo} {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr}
    {tss : List (Nat × Nat × AnnotTerm)} {DsA eiss : List AnnotTerm}
    (hopR : ConLeche.openPisAtFvars n xR dpt = some (afvs, o)) (hsR : xR.stripPis n = some (bs, r))
    (hoE : Expr.ErasedEq o (Expr.mkAppN (Expr.mkAppN (.const J lvls) Ds) idx))
    (hJ : env.find? J = some ci) (hlvls : lvls.length = ci.toConstantVal.levelParams.length)
    (htss : tss.length = n)
    (hbits : ∀ (k : Nat) (p : Nat × Nat × AnnotTerm) (bm : Expr × ConLeche.BinderMeta),
      tss[k]? = some p → bs[k]? = some bm → p.1 = 0 ∧ p.2.1 = pwBit φ bm.2.pw)
    (hdoms : ∀ (k : Nat) (x : Expr) (p : Nat × Nat × AnnotTerm), afvs[k]? = some x → tss[k]? = some p →
      denoteMeta acval env φ (dpt + k) x.fvarTypeD = some p.2.2)
    (hDs : DenoteMetaSpine acval env φ (dpt + n) Ds DsA)
    (hidx : DenoteMetaSpine acval env φ (dpt + n) idx eiss) :
    denoteMeta acval env φ dpt xR
      = some (mkPisAV tss (AnnotTerm.mkAppN (acval J (Level.substFn φ ci.toConstantVal.levelParams lvls))
          (DsA ++ eiss))) := by
  -- the residual
  have hres : denoteMeta acval env φ (dpt + n) o
      = some (AnnotTerm.mkAppN (acval J (Level.substFn φ ci.toConstantVal.levelParams lvls)) (DsA ++ eiss)) := by
    rw [denoteMeta_erasedEq hoE, ← Expr.mkAppN_append]
    exact denoteMeta_mkAppN_of _ (denoteMeta_const hJ hlvls) (hDs.append hidx)
  have hbsLen : bs.length = n := stripPis_length' n hsR
  have hmain := denoteMeta_of_openPis n hopR hsR (ts := tss.map (·.2.2)) (by rw [List.length_map, htss])
    (fun k x t hx ht => by
      rw [List.getElem?_map] at ht
      cases hp : tss[k]? with
      | none => rw [hp] at ht; exact nomatch ht
      | some p =>
        rw [hp] at ht
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        exact hdoms k x p hx hp)
    hres
  rw [hmain]
  congr 2
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_zipWith, List.getElem?_map]
  cases hp : tss[k]? with
  | none =>
    have hk : bs[k]? = none := by
      rw [List.getElem?_eq_none_iff] at hp ⊢; omega
    simp [hk]
  | some p =>
    obtain ⟨bm, hbm⟩ : ∃ bm, bs[k]? = some bm :=
      ⟨_, List.getElem?_eq_getElem (by rw [hbsLen, ← htss]; exact (List.getElem?_eq_some_iff.mp hp).1)⟩
    obtain ⟨h1, h2⟩ := hbits k p bm hp hbm
    obtain ⟨p1, p2, p3⟩ := p
    simp only at h1 h2
    subst h1 h2
    simp [hbm]

end ConLeche.Model
