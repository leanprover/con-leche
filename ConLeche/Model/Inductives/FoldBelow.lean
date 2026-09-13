module

public import ConLeche.Model.Inductives.PsiBody
import ConLeche.Semantics.Tower.FixWire
import ConLeche.Semantics.Tower.SumWire
import ConLeche.Model.Inductives.MutualRecPre
import ConLeche.Model.Inductives.StructData

public section

/-!
# The fold terms are closed above the parameters (task #279 M-C′ step 2 (i), DESIGN §M.33)

A fold term (ψ's `psiTerm`, ψ⁻¹'s recursor at `invL`/`invPinsT`/`invHead`)
is the recursor applied to the block's parameters `ps`, the motives
(`motChoiceAVs`) and the minors (`minChoiceAVs`).  The round trips
(`RoundTrip.lean`) need the fold to fire at a spine of VALUES; the kit's
ι (`InvSetup.fold_iota`/`PsiSetup.fold_iota`) fires at field TERMS read
at the setup's frame.  The route (§M.33): read the same fold term at
the "double push" frame `consList psvals (consList vs σ)` — the
parameter values pushed again above the field values — where field
variables `bvar (nP + nF - 1 - i)` read the values and the parameter
variables read the parameters; the setup at that frame comes from the
run-level `∀ ρ ps` for free, and the fold term reads ALIKE at `σ` and
at the pushed frame by `interp_congr_below` — provided the fold term is
`Term.bvarsBelow nP` (mentions the frame only through its `nP`
parameter variables).

This module is that bound: `bvarsBelow` through substitution
(`bvarsBelow_inst`/`bvarsBelow_instSeq`) and through every builder of
the choice — `famAppAV`, `motDataAV`/`motChoiceAV`, `invTgAV`, the
minor data (`ihDomAVM`/`ihDataAVM`/`minorDataAV`), `minChoiceAV(s)`,
the two bodies (`invBodyAV`, `psiBodyAV` with its transports
`viaEntryAV`) — and the fold term itself, `foldTermAV_below`.  The
datum's own readings are bounded by its clauses (`FixCtorDataI.below`/
`belowE`/`eissBelow`/`tssBelow`, `FormerData.below`); the choice's
terms (`L`, `pinsT`, the heads, the transports' table terms) are the
consumer's hypotheses, uniformly "bounded at the container depth plus
an outer margin `mm`" so that ψ's instance (the container's datum under
the scratch block's `d.nP` parameters, `mm = d.nP`) is the same lemma
as ψ⁻¹'s (`mm = d.nP` too, with the container = the block itself).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock)

universe w

/-! ## Substitution keeps a bound -/

open ConLeche.Term.Term in
/-- Instantiating variable `k` of a term bounded at `k + 1 + m` by a
term bounded at `m` gives a term bounded at `k + m`. -/
theorem bvarsBelow_inst : ∀ (e a : Term) (k m : Nat),
    Term.bvarsBelow (k + 1 + m) e → Term.bvarsBelow m a →
    Term.bvarsBelow (k + m) (Term.inst e a k)
  | .bvar i, a, k, m, he, ha => by
    show Term.bvarsBelow (k + m)
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1))
    have hi : i < k + 1 + m := he
    by_cases h1 : i < k
    · rw [if_pos h1]; show i < k + m; omega
    · rw [if_neg h1]
      by_cases h2 : i = k
      · rw [if_pos h2]
        have := VExprAux.bvarsBelow_liftN k a m 0 ha
        rwa [Nat.add_comm] at this
      · rw [if_neg h2]; show i - 1 < k + m; omega
  | .sort _, _, _, _, _, _ => trivial
  | .const _ _, _, _, _, _, _ => trivial
  | .prf, _, _, _, _, _ => trivial
  | .app f b, a, k, m, he, ha =>
    ⟨bvarsBelow_inst f a k m he.1 ha, bvarsBelow_inst b a k m he.2 ha⟩
  | .lam A b, a, k, m, he, ha =>
    ⟨bvarsBelow_inst A a k m he.1 ha, by
      have := bvarsBelow_inst b a (k + 1) m
        (by rw [show k + 1 + 1 + m = k + 1 + m + 1 by omega]; exact he.2) ha
      rwa [show k + 1 + m = k + m + 1 by omega] at this⟩
  | .pi A B, a, k, m, he, ha =>
    ⟨bvarsBelow_inst A a k m he.1 ha, by
      have := bvarsBelow_inst B a (k + 1) m
        (by rw [show k + 1 + 1 + m = k + 1 + m + 1 by omega]; exact he.2) ha
      rwa [show k + 1 + m = k + m + 1 by omega] at this⟩
  | .eqE b c, a, k, m, he, ha =>
    ⟨bvarsBelow_inst b a k m he.1 ha, bvarsBelow_inst c a k m he.2 ha⟩
  | .fst e, a, k, m, he, ha => bvarsBelow_inst e a k m he ha
  | .snd e, a, k, m, he, ha => bvarsBelow_inst e a k m he ha

/-- An instantiation sequence at cut `t` of a term bounded at
`t + 1 + m`, by terms bounded at `m`, is bounded at
`t + 1 - ws.length + m`. -/
theorem bvarsBelow_instSeq :
    ∀ (ws : List AnnotTerm) (t m : Nat) (e : AnnotTerm), ws.length ≤ t + 1 →
      Term.bvarsBelow (t + 1 + m) e.erase → (∀ w ∈ ws, Term.bvarsBelow m w.erase) →
      Term.bvarsBelow (t + 1 - ws.length + m) (ConLeche.Model.AnnotTerm.instSeq ws t e).erase
  | [], t, m, e, _, he, _ => by simpa using he
  | w :: ws, t, m, e, hlen, he, hws => by
    rw [AnnotTerm.instSeq_cons]
    simp only [List.length_cons] at hlen
    have h1 : Term.bvarsBelow (t + m) (e.inst w t).erase := by
      rw [AnnotTerm.erase_inst]
      exact bvarsBelow_inst _ _ t m he (hws w (.head _))
    cases ws with
    | nil => simpa using h1
    | cons w' ws' =>
      simp only [List.length_cons] at hlen
      have := bvarsBelow_instSeq (w' :: ws') (t - 1) m (e.inst w t)
        (by simp only [List.length_cons]; omega)
        (by rw [show t - 1 + 1 + m = t + m by omega]; exact h1)
        (fun x hx => hws x (.tail _ hx))
      rw [show t - 1 + 1 - (w' :: ws').length + m = t + 1 - (w :: w' :: ws').length + m by
        simp only [List.length_cons]; omega] at this
      exact this

/-- The base instantiation of a term bounded at `n + m` by `n` terms
bounded at `m` is bounded at `m`. -/
theorem bvarsBelow_instSeq_full {ws : List AnnotTerm} {n m : Nat} {e : AnnotTerm}
    (hlen : ws.length = n) (he : Term.bvarsBelow (n + m) e.erase)
    (hws : ∀ w ∈ ws, Term.bvarsBelow m w.erase) :
    Term.bvarsBelow m (ConLeche.Model.AnnotTerm.instSeq ws (n - 1) e).erase := by
  cases n with
  | zero =>
    have : ws = [] := List.eq_nil_of_length_eq_zero hlen
    subst this; simpa using he
  | succ n =>
    have := bvarsBelow_instSeq ws n m e (by omega) (by simpa using he) hws
    rw [hlen, Nat.sub_self, Nat.zero_add] at this
    simpa using this

/-! ## Variables and binder data -/

theorem paramBvarsAt_below {nP D : Nat} (h : nP ≤ D) :
    ∀ a ∈ paramBvarsAt nP D, Term.bvarsBelow D a.erase := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hk
  show D - 1 - k < D
  omega

theorem fieldBvars_below {nF : Nat} : ∀ a ∈ fieldBvars nF, Term.bvarsBelow nF a.erase := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hk
  show nF - 1 - k < nF
  omega

theorem teleVarsAV_below {n : Nat} : ∀ a ∈ teleVarsAV n, Term.bvarsBelow n a.erase := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hk
  show n - 1 - k < n
  omega

theorem rebit_below (b : Nat) :
    ∀ {k : Nat} (ds : List (Nat × Nat × AnnotTerm)), DomsBelow k (rebit b ds) ↔ DomsBelow k ds
  | _, [] => Iff.rfl
  | k, d :: ds => by
    rw [rebit_cons]
    show Term.bvarsBelow k d.2.2.erase ∧ DomsBelow (k + 1) (rebit b ds) ↔
      Term.bvarsBelow k d.2.2.erase ∧ DomsBelow (k + 1) ds
    rw [rebit_below b ds]

theorem liftDoms_below {n : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {K k : Nat}, DomsBelow K ds →
      DomsBelow (K + n) (liftDoms n k ds)
  | [], _, _, _ => trivial
  | d :: ds, K, k, h => by
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN n _ _ _ h.1
    · have := liftDoms_below (n := n) (ds := ds) (K := K + 1) (k := k + 1) h.2
      rwa [show K + 1 + n = K + n + 1 by omega] at this

theorem DomsBelow.map21 {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds →
      LamDomsBelow k (ds.map fun x => (x.2.1, x.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.map21 h.2⟩

/-- The family applied to pins and index variables: bounded at the
tower's depth plus the pins' outer margin. -/
theorem famAppAV_below {L : AnnotTerm} {pins : List AnnotTerm} {nP D nIdx m : Nat}
    (hL : Term.bvarsBelow 0 L.erase) (hpins : ∀ p ∈ pins, Term.bvarsBelow (nP + m) p.erase)
    (hD : nP ≤ D) (hI : nIdx ≤ D) :
    Term.bvarsBelow (D + m) (famAppAV L pins nP D nIdx).erase := by
  unfold famAppAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) hL) ?_
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp ha' with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN (D - nP) _ _ 0 (hpins p hp)
    rwa [show nP + m + (D - nP) = D + m by omega] at this
  · exact Term.bvarsBelow.mono (by omega) (fieldBvars_below a' h)

theorem mixedVarsAV_below {recIdx : List Nat} {useIh : Nat → Bool} {nF : Nat} :
    ∀ a ∈ mixedVarsAV recIdx useIh nF, Term.bvarsBelow (nF + recIdx.length) a.erase := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hi
  by_cases h : useIh i = true
  · rw [if_pos h]; show recIdx.length - 1 - recIdx.idxOf i < nF + recIdx.length; omega
  · rw [if_neg h]; show nF + recIdx.length - 1 - i < nF + recIdx.length; omega

/-! ## The ih binder data -/

/-- An ih binder's domain, bounded at the minor's frame (`nP` block
parameters and an outer margin `mm` below the `o` prefix entries, the
`nF` fields and the `l` earlier hypotheses). -/
theorem ihDomAVM_below {mot nF o i l nP mm : Nat} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} (hi : i < nF) (htl : DomsBelow (nP + i + mm) tl)
    (hEis : ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length + mm) E.erase) :
    Term.bvarsBelow (nP + mm + o + nF + l) (ihDomAVM mot nF o i l tl Eis).erase := by
  unfold ihDomAVM
  refine mkPisAV_below_of ?_ ?_
  · have := ihTeleAtGo_below (nF := nF) (o := o) (i := i) (l := l) (K := nP + i + mm) (k := 0)
      (by simpa using htl)
    unfold ihTeleAtR
    rw [show nP + i + mm + (nF - i + l) + o + 0 = nP + mm + o + nF + l by omega] at this
    exact this
  · rw [ihTeleAtR_length, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · show nF + o - 1 + l + tl.length - mot < nP + mm + o + nF + l + tl.length
      omega
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      rcases List.mem_append.mp ha' with h | h
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h
        have := ihIdxAtM_below (nF := nF) (o := o) (i := i) (l := l) (m := tl.length) (hEis E hE)
        rwa [show nP + i + tl.length + mm + (nF - i + l) + o = nP + mm + o + nF + l + tl.length by
          omega] at this
      · rw [List.mem_singleton] at h
        subst h
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · show nF - 1 - i + l + tl.length < nP + mm + o + nF + l + tl.length
          omega
        · intro b hb
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
          exact Term.bvarsBelow.mono (by omega) (teleVarsAV_below b' hb')

/-- The per-field facts the ih data's bound needs: the field is one of
the constructor's, its telescope and its index expressions are bounded
at the field's depth (plus the outer margin). -/
@[expose] def RecFieldsBelow (nP nF mm : Nat) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : Prop :=
  ∀ i ∈ recIdx, i < nF ∧ DomsBelow (nP + i + mm) (tls.getD i []) ∧
    ∀ E ∈ Eiss.getD i [], Term.bvarsBelow (nP + i + (tls.getD i []).length + mm) E.erase

theorem ihDataAVM_below {moti : Nat → Nat} {nF o b nP mm : Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    ∀ {recIdx : List Nat} {l : Nat}, RecFieldsBelow nP nF mm recIdx tls Eiss →
      DomsBelow (nP + mm + o + nF + l) (ihDataAVM moti nF o b tls Eiss recIdx l)
  | [], _, _ => trivial
  | i :: is, l, h => by
    obtain ⟨hi, htl, hE⟩ := h i (.head _)
    simp only [ihDataAVM]
    refine ⟨?_, ?_⟩
    · show Term.bvarsBelow _ (ihDomAVM (moti i) nF o i l (rebit b (tls.getD i [])) (Eiss.getD i [])).erase
      refine ihDomAVM_below hi ((rebit_below _ _).mpr htl) ?_
      rw [rebit_length]; exact hE
    · have := ihDataAVM_below (moti := moti) (o := o) (b := b) (recIdx := is) (l := l + 1)
        fun j hj => h j (.tail _ hj)
      rwa [show nP + mm + o + nF + (l + 1) = nP + mm + o + nF + l + 1 by omega] at this

theorem minorDataAV_length {moti : Nat → Nat} {nP nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hlen : ds.length = nP + nF) :
    (minorDataAV moti nP nF b o ds recIdx tls Eiss).length = nF + recIdx.length := by
  unfold minorDataAV
  rw [List.length_append, rebit_length, liftDoms_length, List.length_drop, hlen,
    Nat.add_sub_cancel_left, ihDataAVM_length]

/-- The minor's binder data, bounded at the minor's frame. -/
theorem minorDataAV_below {moti : Nat → Nat} {nP nF b o mm : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hds : DomsBelow 0 ds) (hlen : ds.length = nP + nF)
    (hrec : RecFieldsBelow nP nF mm recIdx tls Eiss) :
    DomsBelow (nP + mm + o) (minorDataAV moti nP nF b o ds recIdx tls Eiss) := by
  unfold minorDataAV
  refine domsBelow_append ?_ ?_
  · refine (rebit_below _ _).mpr ?_
    have := liftDoms_below (n := o) (k := 0) (DomsBelow.drop nP hds)
    exact domsBelow_mono (by omega) this
  · rw [rebit_length, liftDoms_length, List.length_drop, hlen, Nat.add_sub_cancel_left]
    have := ihDataAVM_below (moti := moti) (o := o) (b := b) (l := 0) hrec
    rwa [Nat.add_zero] at this

/-! ## The transports -/

/-- A transport entry, bounded at the minor's frame like an ih domain. -/
theorem viaEntryAV_below {Ψ : AnnotTerm} {nF o i l nP mm : Nat} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} (hi : i < nF) (hΨ : Term.bvarsBelow (nP + mm) Ψ.erase)
    (htl : DomsBelow (nP + i + mm) tl)
    (hEis : ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length + mm) E.erase) :
    Term.bvarsBelow (nP + mm + o + nF + l) (viaEntryAV Ψ nF o i l tl Eis).erase := by
  unfold viaEntryAV
  refine mkLamsAV_below (DomsBelow.map21 ?_) ?_
  · have := ihTeleAtGo_below (nF := nF) (o := o) (i := i) (l := l) (K := nP + i + mm) (k := 0)
      (by simpa using htl)
    unfold ihTeleAtR
    rw [show nP + i + mm + (nF - i + l) + o + 0 = nP + mm + o + nF + l by omega] at this
    exact this
  · rw [List.length_map, ihTeleAtR_length]
    unfold viaBodyAV
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (o + nF + l + tl.length) _ _ 0 hΨ
      rwa [show nP + mm + (o + nF + l + tl.length) = nP + mm + o + nF + l + tl.length by omega]
        at this
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      rcases List.mem_append.mp ha' with h | h
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h
        have := ihIdxAtM_below (nF := nF) (o := o) (i := i) (l := l) (m := tl.length) (hEis E hE)
        rwa [show nP + i + tl.length + mm + (nF - i + l) + o = nP + mm + o + nF + l + tl.length by
          omega] at this
      · rw [List.mem_singleton] at h
        subst h
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · show nF - 1 - i + l + tl.length < nP + mm + o + nF + l + tl.length
          omega
        · intro b hb
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
          exact Term.bvarsBelow.mono (by omega) (teleVarsAV_below b' hb')

/-- ψ's body variables: the fields' and hypotheses' variables, and the
transports. -/
theorem psiVarsAV_below {recIdx : List Nat} {useIh : Nat → Bool} {via : Nat → Option ViaSpec}
    {nF o nP mm : Nat}
    (hvia : ∀ i, i < nF → ∀ Ψ Eis tl, via i = some (Ψ, Eis, tl) →
      Term.bvarsBelow (nP + mm) Ψ.erase ∧ DomsBelow (nP + i + mm) tl ∧
      ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length + mm) E.erase) :
    ∀ a ∈ psiVarsAV recIdx useIh via nF o,
      Term.bvarsBelow (nP + mm + o + nF + recIdx.length) a.erase := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have hiF := List.mem_range.mp hi
  cases hv : via i with
  | some x =>
    obtain ⟨Ψ, Eis, tl⟩ := x
    obtain ⟨hΨ, htl, hE⟩ := hvia i hiF Ψ Eis tl hv
    exact viaEntryAV_below hiF hΨ htl hE
  | none =>
    by_cases h : useIh i = true
    · simp only [if_pos h]
      show recIdx.length - 1 - recIdx.idxOf i < nP + mm + o + nF + recIdx.length
      omega
    · simp only [if_neg h]
      show nF + recIdx.length - 1 - i < nP + mm + o + nF + recIdx.length
      omega

namespace IndRepData

variable (d : IndRepData V) [SetTheory V]

/-! ## The motives -/

theorem motDataAV_length (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    (d.motDataAV m ψ t).length = ((d.ipss ψ).getD t []).length + 1 := by
  unfold IndRepData.motDataAV
  rw [List.length_append, rebit_length, List.length_singleton]

/-- The motive's binder data, bounded at the parameter frame plus the
pins' outer margin. -/
theorem motDataAV_below (m : EnvModel V env) {ψ : Name → Nat} {t mm : Nat} (ht : t < d.k)
    (hips : DomsBelow d.nP ((d.ipss ψ).getD t []))
    (hipsLen : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    (hpins : ∀ p ∈ d.pinsOf ψ t, Term.bvarsBelow (d.nP + mm) p.erase) :
    DomsBelow (d.nP + mm) (d.motDataAV m ψ t) := by
  unfold IndRepData.motDataAV
  refine domsBelow_append ((rebit_below _ _).mpr (domsBelow_mono (Nat.le_add_right _ _) hips)) ?_
  rw [rebit_length, hipsLen]
  refine ⟨?_, trivial⟩
  have hL : Term.bvarsBelow 0 ((d.Ls m ψ).getD t default).erase := by
    have hget : (d.Ls m ψ).getD t default = m.acval (d.memberName t) ψ := by
      simp [IndRepData.Ls, List.getD_eq_getElem?_getD, List.getElem?_range ht, IndRepData.memberName]
    rw [hget]; exact m.cval_closedL _ ψ
  have := famAppAV_below (D := d.nP + d.nIdxs.getD t 0) (nIdx := d.nIdxs.getD t 0) (m := mm) hL
    hpins (by omega) (by omega)
  rwa [show d.nP + d.nIdxs.getD t 0 + mm = d.nP + mm + d.nIdxs.getD t 0 by omega] at this

/-- A motive of the choice, bounded at the outer margin when the
parameters and the target are. -/
theorem motChoiceAV_below (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {t mm : Nat} (hps : ps.length = d.nP)
    (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase)
    (hmot : DomsBelow (d.nP + mm) (d.motDataAV m ψ t))
    (hipsLen : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    (hTg : Term.bvarsBelow mm (Tg t).erase) :
    Term.bvarsBelow mm (d.motChoiceAV m ψ ps Tg t).erase := by
  unfold IndRepData.motChoiceAV
  refine bvarsBelow_instSeq_full hps ?_ hpsB
  refine mkLamsAV_below (DomsBelow.map21 hmot) ?_
  rw [List.length_map, d.motDataAV_length, hipsLen, AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN (d.nP + d.nIdxs.getD t 0 + 1) _ _ 0 hTg
    rwa [show mm + (d.nP + d.nIdxs.getD t 0 + 1) = d.nP + mm + (d.nIdxs.getD t 0 + 1) by omega]
      at this
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    have := idxVarsAV_below (K := d.nP + mm + d.nIdxs.getD t 0) (D' := 1) (by omega) a' ha'
    rwa [show d.nP + mm + d.nIdxs.getD t 0 + 1 = d.nP + mm + (d.nIdxs.getD t 0 + 1) by omega]
      at this

omit [SetTheory V] in
/-- A target of the choice (the leaf at the pins over the index
binders), bounded at the outer margin. -/
theorem invTgAV_below {ψ : Name → Nat} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {t mm : Nat} (hps : ps.length = d.nP)
    (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase)
    (hips : DomsBelow d.nP ((d.ipss ψ).getD t []))
    (hipsLen : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    (hL : Term.bvarsBelow 0 (L t).erase)
    (hpinsT : ∀ p ∈ pinsT t, Term.bvarsBelow (d.nP + mm) p.erase) :
    Term.bvarsBelow mm (d.invTgAV ψ ps L pinsT t).erase := by
  unfold IndRepData.invTgAV
  rw [hps]
  refine bvarsBelow_instSeq_full hps ?_ hpsB
  refine mkLamsAV_below
    (DomsBelow.map21 ((rebit_below _ _).mpr (domsBelow_mono (Nat.le_add_right _ _) hips))) ?_
  rw [List.length_map, rebit_length, hipsLen]
  have := famAppAV_below (D := d.nP + d.nIdxs.getD t 0) (nIdx := d.nIdxs.getD t 0) (m := mm) hL
    hpinsT (by omega) (by omega)
  rwa [show d.nP + d.nIdxs.getD t 0 + mm = d.nP + mm + d.nIdxs.getD t 0 by omega] at this

/-! ## The minors -/

omit [SetTheory V] in
/-- A minor of the choice, bounded at the outer margin when the prefix
(parameters, motives, earlier minors), the minor data and the body
are. -/
theorem minChoiceAV_below {ψ : Name → Nat} {ps Ms prior : List AnnotTerm} {J mm : Nat}
    {body : AnnotTerm} (hlen : (ps ++ Ms ++ prior).length = d.nP + d.k + J)
    (hB : ∀ p ∈ ps ++ Ms ++ prior, Term.bvarsBelow mm p.erase)
    (hmin : DomsBelow (d.nP + mm + (d.k + J))
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1))
    (hbody : Term.bvarsBelow (d.nP + mm + (d.k + J) +
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1).length)
      body.erase) :
    Term.bvarsBelow mm (d.minChoiceAV ψ ps Ms prior J body).erase := by
  unfold IndRepData.minChoiceAV
  refine bvarsBelow_instSeq_full hlen ?_ hB
  refine mkLamsAV_below (DomsBelow.map21 ?_) ?_
  · rwa [show d.nP + d.k + J + mm = d.nP + mm + (d.k + J) by omega]
  · rw [List.length_map]
    rwa [show d.nP + d.k + J + mm = d.nP + mm + (d.k + J) by omega]

omit [SetTheory V] in
theorem mem_minChoiceAVs {ψ : Name → Nat} {ps Ms : List AnnotTerm} {bodies : Nat → AnnotTerm} :
    ∀ {n : Nat} {x : AnnotTerm}, x ∈ d.minChoiceAVs ψ ps Ms bodies n →
      ∃ J, J < n ∧ x = d.minChoiceAV ψ ps Ms (d.minChoiceAVs ψ ps Ms bodies J) J (bodies J)
  | 0, _, h => nomatch h
  | n + 1, x, h => by
    simp only [IndRepData.minChoiceAVs, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨J, hJ, rfl⟩ := mem_minChoiceAVs h
      exact ⟨J, by omega, rfl⟩
    · exact ⟨n, by omega, rfl⟩

omit [SetTheory V] in
/-- The minors of the choice, bounded when the parameters, the motives
and every body are (with the minor data bounded per constructor). -/
theorem minChoiceAVs_below {ψ : Name → Nat} {ps Ms : List AnnotTerm} {bodies : Nat → AnnotTerm}
    {mm n : Nat} (hps : ps.length = d.nP) (hMs : Ms.length = d.k)
    (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase) (hMsB : ∀ p ∈ Ms, Term.bvarsBelow mm p.erase)
    (hmin : ∀ J, J < n → DomsBelow (d.nP + mm + (d.k + J))
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1))
    (hbody : ∀ J, J < n → Term.bvarsBelow (d.nP + mm + (d.k + J) +
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1).length)
      (bodies J).erase) :
    ∀ x ∈ d.minChoiceAVs ψ ps Ms bodies n, Term.bvarsBelow mm x.erase := by
  induction n with
  | zero => intro x hx; exact absurd hx (List.not_mem_nil)
  | succ n ih =>
    intro x hx
    simp only [IndRepData.minChoiceAVs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (fun J hJ => hmin J (by omega)) (fun J hJ => hbody J (by omega)) x hx
    · refine d.minChoiceAV_below ?_ ?_ (hmin n (by omega)) (hbody n (by omega))
      · rw [List.length_append, List.length_append, hps, hMs, d.minChoiceAVs_length]
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_append.mp hp with hp | hp
          · exact hpsB p hp
          · exact hMsB p hp
        · exact ih (fun J hJ => hmin J (by omega)) (fun J hJ => hbody J (by omega)) p hp

/-! ## The bodies -/

omit [SetTheory V] in
/-- ψ⁻¹'s body at constructor `J`: bounded at the minor's leaf frame
when the head is bounded at the parameter frame plus the margin. -/
theorem invBodyAV_below {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {J mm : Nat}
    (hhead : Term.bvarsBelow (d.nP + mm) (head J).erase) :
    Term.bvarsBelow (d.nP + mm + (d.k + J) +
        ((d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length))
      (d.invBodyAV head useIh J).erase := by
  unfold IndRepData.invBodyAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN
      (d.k + J + (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length) _ _ 0 hhead
    rwa [show d.nP + mm + (d.k + J + (d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length)
      = d.nP + mm + (d.k + J) + ((d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length) by omega] at this
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact Term.bvarsBelow.mono (by omega) (mixedVarsAV_below a' ha')

omit [SetTheory V] in
/-- ψ's body at constructor `J`: bounded at the minor's leaf frame when
the head and the transports are. -/
theorem psiBodyAV_below {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}
    {via : Nat → Nat → Option ViaSpec} {J mm : Nat}
    (hhead : Term.bvarsBelow (d.nP + mm) (head J).erase)
    (hvia : ∀ i, i < (d.ctorsAll.getD J default).2 → ∀ Ψ Eis tl, via J i = some (Ψ, Eis, tl) →
      Term.bvarsBelow (d.nP + mm) Ψ.erase ∧ DomsBelow (d.nP + i + mm) tl ∧
      ∀ E ∈ Eis, Term.bvarsBelow (d.nP + i + tl.length + mm) E.erase) :
    Term.bvarsBelow (d.nP + mm + (d.k + J) +
        ((d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length))
      (d.psiBodyAV head useIh via J).erase := by
  unfold IndRepData.psiBodyAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN
      (d.k + J + (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length) _ _ 0 hhead
    rwa [show d.nP + mm + (d.k + J + (d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length)
      = d.nP + mm + (d.k + J) + ((d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length) by omega] at this
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    have := psiVarsAV_below (nP := d.nP) (mm := mm) (o := d.k + J) hvia a' ha'
    rwa [show d.nP + mm + (d.k + J) + (d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length
      = d.nP + mm + (d.k + J) + ((d.ctorsAll.getD J default).2 +
        (ConLeche.recIdxOf (d.ksR J)).length) by omega] at this

/-! ## The fold term -/

/-- **The fold term** at a choice: member `mm`'s recursor at the
parameters, the motives at the targets `invTgAV ψ ps L pinsT` and the
minors at `bodies` — ψ⁻¹'s (`bodies = invBodyAV head useIh`) and ψ's
(`bodies = psiBodyAV head useIh via`, `psiTerm`) are its instances. -/
@[expose] def foldTermAV (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (bodies : Nat → AnnotTerm) (mm : Nat) :
    AnnotTerm :=
  AnnotTerm.mkAppN (m.acval (d.recNames mm) ψ)
    (ps ++ d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT) ++
      d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT)) bodies d.nAll)

/-- The kit's ι term is the fold term applied. -/
theorem mkAppN_foldTermAV (m : EnvModel V env) (ψ : Name → Nat) (ps : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (bodies : Nat → AnnotTerm) (mm : Nat)
    (rest : List AnnotTerm) :
    AnnotTerm.mkAppN (m.acval (d.recNames mm) ψ)
        (ps ++ d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT)) bodies d.nAll ++ rest)
      = AnnotTerm.mkAppN (d.foldTermAV m ψ ps L pinsT bodies mm) rest := by
  unfold IndRepData.foldTermAV
  generalize ps ++ d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT) ++
    d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT)) bodies d.nAll = pre
  generalize m.acval (d.recNames mm) ψ = R
  induction pre generalizing R with
  | nil => rfl
  | cons a pre ih => simp only [List.cons_append, AnnotTerm.mkAppN_cons]; exact ih _

/-- **The fold term is bounded at the outer margin** when the
parameters, the leaves, the pins, the members' index data, the
constructors' data and the bodies are.  With `ps` the parameter
variables and `mm = d.nP`, the fold term mentions the frame only
through the block's parameters. -/
theorem foldTermAV_below (m : EnvModel V env) {ψ : Name → Nat} {ps : List AnnotTerm}
    {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm} {bodies : Nat → AnnotTerm} {mm t : Nat}
    (hps : ps.length = d.nP) (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase)
    (hips : ∀ t, t < d.k → DomsBelow d.nP ((d.ipss ψ).getD t []))
    (hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    (hL : ∀ t, t < d.k → Term.bvarsBelow 0 (L t).erase)
    (hpinsT : ∀ t, t < d.k → ∀ p ∈ pinsT t, Term.bvarsBelow (d.nP + mm) p.erase)
    (hpins : ∀ t, t < d.k → ∀ p ∈ d.pinsOf ψ t, Term.bvarsBelow (d.nP + mm) p.erase)
    (hmin : ∀ J, J < d.nAll → DomsBelow (d.nP + mm + (d.k + J))
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1))
    (hbody : ∀ J, J < d.nAll → Term.bvarsBelow (d.nP + mm + (d.k + J) +
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1).length)
      (bodies J).erase) :
    Term.bvarsBelow mm (d.foldTermAV m ψ ps L pinsT bodies t).erase := by
  unfold IndRepData.foldTermAV
  rw [AnnotTerm.erase_mkAppN]
  have hMsB : ∀ p ∈ d.motChoiceAVs m ψ ps (d.invTgAV ψ ps L pinsT), Term.bvarsBelow mm p.erase := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have ht := List.mem_range.mp ht
    exact d.motChoiceAV_below m hps hpsB (d.motDataAV_below m ht (hips t ht) (hipsLen t ht) (hpins t ht))
      (hipsLen t ht)
      (d.invTgAV_below hps hpsB (hips t ht) (hipsLen t ht) (hL t ht) (hpinsT t ht))
  refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) (m.cval_closedL _ ψ)) ?_
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp ha' with h | h
  · rcases List.mem_append.mp h with h | h
    · exact hpsB a' h
    · exact hMsB a' h
  · exact d.minChoiceAVs_below hps (d.motChoiceAVs_length _ _ _ _) hpsB hMsB hmin hbody a' h

end IndRepData

end ConLeche.Model
