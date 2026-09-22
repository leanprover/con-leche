module

public import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.BlockRecRegimes

public section

/-!
# The `ih` OPENER's stored type, read (task #315, milestone M5)

`checkBlockRule`'s third opening
(`openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse) …`)
puts one free variable per `ih` key into the rule's frame, and its
STORED TYPE is the matching binder of `blockIhPis`
(`ConLeche/Kernel/Inductives/BlockRec.lean`):

```
∀ a⃗, <the CALLEE's stored type at the rule's prefix, at the field's
      index expressions and at `f_i a⃗`>
```

— a `Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i)) concl` tower.

The `hfit` discharge of the M5M rule lane needs that type's READING,
and needs it as a `mkPisAV` tower: `spineFit_of_teleFitPA`
(`BlockRecLaw.lean`) is stated at one, and `TeleFitPA` at an arbitrary
`Ta` says nothing about the domains the certified spine has to fit.

## What is generalised

`denoteMeta_ihSpineAt` (`Model/Inductives/FixRecRead.lean`) already
reads a `structTeleAt` tower — but only with the CONCLUSION spelled:
a head applied to leading arguments, the field's index expressions and
the field at its own telescope variables.  The opener's conclusion is
not of that shape (it is a callee's stored TYPE instantiated at that
spine), so the theorem is re-cut one level lower:

* `denoteMeta_structTeleAtPis` — the tower over `structTeleAt` with an
  ARBITRARY conclusion, whose reading is a premise.  The whole content
  is the telescope, binderwise (`denoteMeta_ihIdxAtM` at each binder),
  and it lands at `ihTeleAtR`, which is what the consumer needs.
* `denoteMeta_ihSpineAt_ofGen` — the k = 1 statement, verbatim, as an
  INSTANCE of it: the conclusion premise is discharged by
  `denoteMeta_mkAppN` at the head, the leading arguments
  (`denoteMetaSpine_ihIdx`) and the applied field.  `FixRecRead`'s own
  proof of `denoteMeta_ihSpineAt` may be replaced by this one.
* `denoteMeta_blockIhOpenerTy` — the same statement at the CHECK's own
  opening list (`FvarList`, `instantiateList`), which is the shape the
  rule lane's premises are spelled in; the twin of
  `denoteMeta_blockIhSpinePis` (`BlockRecRule.lean`), which reads the
  guarded CALL's tower rather than the opener's.

## The frame's tail and the tower's `l`

`structTeleAt nF o i l` moves the field's data under `l` binders
standing between the fields and the telescope, and the reading is only
correct at a frame whose tail has exactly `l` entries
(`instSeq_structIdxAtM` couples them: the second lift's cut is
`nF + l + j`, which is where the frame's `o` extras sit).  So the
opener at `ih` position `r`, whose binder is generated at `l = r`,
reads at the frame `p⃗ x⃗ f⃗ ih⃗_{<r}` — depth `nP + o + nF + r` — and a
consumer reading it at the walk's deeper frame pays the `d`-shift
(`ihIdxAtM_shift`, `BlockRecRule.lean`), exactly as
`ihSpineFold_blockRec` already does for the call's tower.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe uv

variable {V : Type uv} [SetTheory V] {env : Env}

/-! ## The tower over `structTeleAt`, at an arbitrary conclusion -/

set_option maxHeartbeats 3200000 in
/-- **A `structTeleAt` tower reads to the `ihTeleAtR` tower**, whatever
its conclusion: the field's telescope moved binderwise
(`denoteMeta_ihIdxAtM` at each binder), the body read under all of
them.  This is `denoteMeta_ihSpineAt` with the conclusion abstracted —
the generated guarded CALL (`blockIhSpinePis`) and the `ih` OPENER's
stored type (`blockIhPis`' binder, a callee's stored type instantiated
at the call's arguments) are the two instances, and they differ in
nothing else. -/
theorem denoteMeta_structTeleAtPis {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i : Nat}
    {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty)
    {concl : Expr} {conclA : AnnotTerm}
    (hconcl : denoteMeta m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) concl)
      = some conclA) :
    denoteMeta m.acval env ψ (nP + o + nF + l)
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Expr.mkPisOf (ConLeche.structTeleAt nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i))
            concl))
      = some (mkPisAV (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl)) conclA) := by
  obtain ⟨hlenTl, hbind, hspSrc⟩ := hfr
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (x : Expr), (fvs0.take (nP + i))[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take, if_pos hk] at hx
    exact hidx0 k x hx
  have hprops := structFieldTele_props hCf hCb hstripC hi
  have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hI]
  have hLidx := frameIdx hP hX hF hidxP hidxX hidxF hidxI
  refine denoteMeta_instSeq_mkPisOf _ (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl)) _ _
    (P ++ X ++ F ++ I) (nP + o + nF + l) hlenL hLidx
    (by rw [ihTeleAtR_length, rebit_length, structTeleAt_length, hlenTl]) ?_ ?_
  · -- the telescope, binderwise
    intro k b p hb hp
    have hk : k < (ConLeche.structFieldTeleOf cty nP nF i).length := by
      rw [← structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
      exact (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b₀ :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    rw [structTeleAt_getElem? (pw := pw) hb₀] at hb
    obtain rfl := (Option.some.inj hb).symm
    obtain ⟨d, hd⟩ : ∃ d, tl[k]? = some d := ⟨_, List.getElem?_eq_getElem (by rw [hlenTl]; exact hk)⟩
    rw [ihTeleAtR, ihTeleAtGo_getElem? nF o i l 0 _ k, rebit, List.getElem?_map, hd] at hp
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
    obtain rfl := hp.symm
    obtain ⟨h1, -, h3⟩ := hbind k b₀ d hb₀ hd
    obtain ⟨hef, heb⟩ := hprops.1 k b₀ hb₀
    exact ⟨h1, rfl, denoteMeta_ihIdxAtM hef heb (Nat.le_of_lt hi) hS hidxS hP hX hF hI hidxP hidxF h3⟩
  · -- the conclusion, under the whole telescope
    rw [structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
    exact hconcl

/-! ## The k = 1 statement, as an instance

`denoteMeta_ihSpineAt` (`Model/Inductives/FixRecRead.lean`) is the
theorem above at the conclusion `mkAppN hd (pre ++ e⃗_i ++ [f_i a⃗])`,
and this is that derivation: the conclusion's reading premise is
`denoteMeta_mkAppN` at the head (`hhd`), the leading arguments
(`hpre`), the field's index expressions (`denoteMetaSpine_ihIdx`) and
the field at its own telescope variables.  Nothing else of the
original proof survives, which is the check that the generalisation
lost nothing. -/

set_option maxHeartbeats 3200000 in
/-- **`denoteMeta_ihSpineAt`, from `denoteMeta_structTeleAtPis`** —
the same statement, verbatim. -/
theorem denoteMeta_ihSpineAt_ofGen {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i : Nat}
    {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty)
    {hd : Expr} {pre : List Expr} {hdA : AnnotTerm} {preA : List AnnotTerm}
    (hhd : denoteMeta m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) hd)
        = some hdA)
    (hpre : DenoteMetaSpine m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (pre.map (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1))) preA) :
    denoteMeta m.acval env ψ (nP + o + nF + l)
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Expr.mkPisOf (ConLeche.structTeleAt nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i))
            (Expr.mkAppN hd
              (pre ++ (ConLeche.structFieldIdxOf cty nP nF i).map
                  (ConLeche.structIdxAt nF o i l (ConLeche.structFieldTeleOf cty nP nF i).length) ++
                [Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
                  (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)]))))
      = some (mkPisAV (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl))
          (AnnotTerm.mkAppN hdA
            (preA ++ Eis.map (ihIdxAtM nF o i l (ConLeche.structFieldTeleOf cty nP nF i).length) ++
              [AnnotTerm.mkAppN
                (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
                (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)]))) := by
  obtain ⟨hlenTl, hbind, hspSrc⟩ := hfr
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (x : Expr), (fvs0.take (nP + i))[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take, if_pos hk] at hx
    exact hidx0 k x hx
  have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hI]
  have hLidx := frameIdx hP hX hF hidxP hidxX hidxF hidxI
  have hbvarA : ∀ q : Nat, q < nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length →
      denoteMeta m.acval env ψ (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) (Expr.bvar q))
        = some (AnnotTerm.bvar q) :=
    fun q hq => denoteMeta_instSeq_ext_bvar hlenL hLidx hq
  refine denoteMeta_structTeleAtPis (pw := pw) hop0 hCf hCb hstripC hi
    ⟨hlenTl, hbind, hspSrc⟩ hP hX hF hI hidxP hidxX hidxF hidxI ?_
  have hspI := denoteMetaSpine_ihIdx (m := m) (ψ := ψ) (o := o) (l := l) hCf hCb hstripC hi rfl
    hS hidxS (by rw [hlenTl] at hspSrc; exact hspSrc) hP hX hF hI hidxP hidxF
  have hfieldApp : denoteMeta m.acval env ψ
      (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)
          (Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
            (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)))
      = some (AnnotTerm.mkAppN
          (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
          (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)) := by
    rw [Expr.instSeq_mkAppN]
    refine denoteMeta_mkAppN ?_ (hbvarA _ (by omega))
    unfold ConLeche.structTeleVars teleVarsAV
    rw [List.map_map]
    simp only [Function.comp_def]
    exact DenoteMetaSpine.of_map (List.range (ConLeche.structFieldTeleOf cty nP nF i).length)
      (fun k hk => hbvarA _ (by rw [List.mem_range] at hk; omega))
  rw [Expr.instSeq_mkAppN, List.map_append, List.map_append, List.map_map, List.map_cons,
    List.map_nil]
  simp only [Function.comp_def]
  rw [denoteMeta_mkAppN ((hpre.append hspI).append (.cons hfieldApp .nil)) hhd]

/-! ## The opener's stored type, at the CHECK's own opening list

The rule lane spells its frames as `FvarList E as1` and opens with
`Expr.instantiateList` (`checkBlockRule`'s `(fvsPref ++ fvsF).reverse`),
not as the battery's ascending split — `instantiateList_eq_instSeq_of_fvarList`
and `ascFrame_split` (`BlockRecRule.lean`) are the bridge, and this is
`denoteMeta_blockIhSpinePis`' twin on the other side of it: the
generated CALL's tower there, the `ih` OPENER's stored type here. -/

/-- **A frame opening, extended by a telescope's own openers.**  The
`k` fresh variables stand INNERMOST, so they head the opening list
reversed; `FvarList`'s descending index is what makes the two halves
line up (`E + k - 1 - j` on both). -/
theorem FvarList.openExtend {E : Nat} {xs : List Expr} (h : FvarList E xs) (k : Nat) :
    FvarList (E + k) ((openFvars E k).reverse ++ xs) := by
  refine ⟨by rw [List.length_append, List.length_reverse, openFvars_length, h.1]; omega,
    fun j hj => ?_, fun x hx => ?_⟩
  · by_cases hjk : j < k
    · refine ⟨.sort .zero, ?_⟩
      rw [List.getElem?_append_left (by rw [List.length_reverse, openFvars_length]; omega),
        List.getElem?_reverse (by rw [openFvars_length]; omega), openFvars_length,
        openFvars_getElem? (show k - 1 - j < k from by omega)]
      congr 2
      omega
    · obtain ⟨ty, hty⟩ := h.2.1 (j - k) (by omega)
      refine ⟨ty, ?_⟩
      rw [List.getElem?_append_right (by rw [List.length_reverse, openFvars_length]; omega),
        List.length_reverse, openFvars_length, hty]
      congr 2
      omega
  · rcases List.mem_append.mp hx with hx' | hx'
    · rw [List.mem_reverse] at hx'
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
      have hqk : q < k := by
        rcases Nat.lt_or_ge q k with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hq
          exact nomatch hq
      rw [openFvars_getElem? hqk] at hq
      obtain rfl := (Option.some.inj hq).symm
      simp only [Expr.WScoped]
      exact ⟨by omega, trivial⟩
    · exact Expr.WScoped.mono (by omega) (h.2.2 x hx')

/-- **The `ih` opener's stored type, READ.**  At the rule's frame —
the `nP` parameters, the `o` extras between them and the fields, the
`nF` fields and the `d` binders standing between the fields and this
opener — the binder `blockIhPis` generates for the key `(i, c')`,
opened along the check's own opening list, reads to the `mkPisAV`
tower over `ihTeleAtR nF o i d (rebit (pwBit ψ pw) tl)`: the field's
telescope moved to this frame, with the binder data's bits and
lengths (`ihTeleAtR_length`), over whatever the callee's instantiated
conclusion reads to.

That is the shape `spineFit_of_teleFitPA` (`BlockRecLaw.lean`)
consumes — it is stated at a `mkPisAV` and takes only the domains, so
the conclusion stays a parameter here and the consumer may read it
with `denoteMeta_instPisAtLift_peel` (`BlockRecRead.lean`), which is
what the run's `Expr.instPisAtLift … (recTyOf c') = some concl` gives
it. -/
theorem denoteMeta_blockIhOpenerTy {m : EnvModel V env} {ψ : Name → Nat} {nP nF o d i : Nat}
    {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {as1 : List Expr} (h1 : FvarList (nP + o + nF + d) as1)
    {concl : Expr} {conclA : AnnotTerm}
    (hconcl : denoteMeta m.acval env ψ
        (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (concl.instantiateList
          ((openFvars (nP + o + nF + d)
            (ConLeche.structFieldTeleOf cty nP nF i).length).reverse ++ as1) 0)
      = some conclA) :
    denoteMeta m.acval env ψ (nP + o + nF + d)
        ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw (ConLeche.structFieldTeleOf cty nP nF i))
          concl).instantiateList as1 0)
      = some (mkPisAV (ihTeleAtR nF o i d (rebit (pwBit ψ pw) tl)) conclA) := by
  have hE : 0 < nP + o + nF + d := by omega
  have hEM : 0 < nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length := by omega
  rw [instantiateList_eq_instSeq_of_fvarList h1 hE]
  obtain ⟨P, X, F, I, hLsplit, hP, hX, hF, hI, hidxP, hidxX, hidxF, hidxI⟩ :=
    ascFrame_split (a := nP) (b := o) (c := nF) (e := d) h1.reverse_length h1.reverse_idx
  rw [instantiateList_eq_instSeq_of_fvarList
    (h1.openExtend (ConLeche.structFieldTeleOf cty nP nF i).length) hEM,
    List.reverse_append, List.reverse_reverse, hLsplit] at hconcl
  rw [hLsplit]
  exact denoteMeta_structTeleAtPis (pw := pw) hop0 hCf hCb hstripC hi hfr hP hX hF hI
    hidxP hidxX hidxF hidxI hconcl

/-! ## The `ih` position's shift

The opener at `ih` position `r` is generated at `l = r` and reads at
the frame whose tail has `r` entries; a consumer standing `δ` binders
deeper reads the same data at `l = r + δ`.  `ihIdxAtM_shift`
(`BlockRecRule.lean`) is the elementwise `0 → d` case of the move;
these three are the whole telescope's, in the `liftDoms` form
`liftN_mkPisAV` (`StructRecSpine.lean`) states a lifted Π-tower in —
so a consumer transports between the two readings with ONE `liftN`,
the same way `ihSpineFold_blockRec` transports the guarded call's. -/

/-- **`ihIdxAtM`'s shift at any base position** — `ihIdxAtM_shift`
generalised from `l = 0`. -/
theorem ihIdxAtM_shiftAt (nF o i l δ m : Nat) (E : AnnotTerm) :
    ihIdxAtM nF o i (l + δ) m E = (ihIdxAtM nF o i l m E).liftN δ m := by
  unfold ihIdxAtM
  rw [liftN_shift_comm (A := nF - i + l) (o := o) (d := δ) E m (nF + l + m) (by omega),
    show nF - i + l + δ = nF - i + (l + δ) from by omega,
    show nF + l + m + δ = nF + (l + δ) + m from by omega]

/-- **The moved telescope's shift**: `δ` positions deeper is the
telescope lifted binderwise. -/
theorem ihTeleAtR_shiftAt (nF o i l δ : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    ihTeleAtR nF o i (l + δ) tl = liftDoms δ 0 (ihTeleAtR nF o i l tl) := by
  refine List.ext_getElem? fun q => ?_
  rw [liftDoms_getElem?, ihTeleAtR, ihTeleAtR, ihTeleAtGo_getElem? nF o i l 0 tl q,
    ihTeleAtGo_getElem? nF o i (l + δ) 0 tl q, Option.map_map]
  cases tl[q]? with
  | none => rfl
  | some d =>
    simp only [Option.map_some, Function.comp_def, ihIdxAtM_shiftAt]

/-- **The opener's reading, `δ` positions deeper**: the whole
`mkPisAV` tower lifted. -/
theorem mkPisAV_ihTeleAtR_shift (nF o i l δ : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (B : AnnotTerm) :
    mkPisAV (ihTeleAtR nF o i (l + δ) tl) (B.liftN δ tl.length)
      = (mkPisAV (ihTeleAtR nF o i l tl) B).liftN δ 0 := by
  rw [liftN_mkPisAV, ihTeleAtR_shiftAt, ihTeleAtR_length, Nat.zero_add]

/-! ## The same reading, at a deeper frame

The consumer of the `ih` opener's type is the rule body's WALK, which
stands `δ` binders below the opener's own position — and reading the
SAME (opened, hence `fvar`-carrying) term at a deeper frame is
reading it at the shallow one and lifting, because `denoteMeta` reads
`fvar k` at depth `D` as `bvar (D - 1 - k)`
(`denoteMeta_shiftFromN` at the cut `p = D`).  Composed with the ih
position's shift, that is the statement at the walk's frame with no
work left for the consumer. -/

/-- A `shiftFromN` above every reachable `fvar` is the identity —
`Expr.shiftFrom_eq_self`, iterated. -/
theorem shiftFromN_eq_self {p : Nat} :
    ∀ (n : Nat) {e : Expr}, Expr.fvarsBelow p e → Expr.shiftFromN p n e = e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    show Expr.shiftFrom p (Expr.shiftFromN p n e) = e
    rw [shiftFromN_eq_self n h, Expr.shiftFrom_eq_self h]

/-- **A well-scoped term's reading, deeper**: the reading lifted at
the cut `0`. -/
theorem denoteMeta_deepen {m : EnvModel V env} {ψ : Name → Nat} {D : Nat} {e : Expr}
    {ea : AnnotTerm} (hw : Expr.WScoped D e)
    (h : denoteMeta m.acval env ψ D e = some ea) (δ : Nat) :
    denoteMeta m.acval env ψ (D + δ) e = some (ea.liftN δ 0) := by
  have hs := denoteMeta_shiftFromN (acval := m.acval) (env := env) (φ := ψ) m.acval_closed
    (p := D) δ (Nat.le_refl D) hw
  rw [shiftFromN_eq_self δ hw.fvarsBelow, h, Nat.sub_self, Option.map_some] at hs
  exact hs

/-- **The `ih` opener's stored type, read at the walk's frame.**  At
`δ` binders below the opener's own position the tower is the one at
`ih` position `d + δ` — `denoteMeta_blockIhOpenerTy` composed with the
depth's lift and `mkPisAV_ihTeleAtR_shift`. -/
theorem denoteMeta_blockIhOpenerTy_deep {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o d i : Nat} {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {as1 : List Expr} (h1 : FvarList (nP + o + nF + d) as1)
    {concl : Expr} {conclA : AnnotTerm}
    (hws : Expr.WScoped (nP + o + nF + d)
      ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw
        (ConLeche.structFieldTeleOf cty nP nF i)) concl).instantiateList as1 0))
    (hconcl : denoteMeta m.acval env ψ
        (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (concl.instantiateList
          ((openFvars (nP + o + nF + d)
            (ConLeche.structFieldTeleOf cty nP nF i).length).reverse ++ as1) 0)
      = some conclA) (δ : Nat) :
    denoteMeta m.acval env ψ (nP + o + nF + d + δ)
        ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw (ConLeche.structFieldTeleOf cty nP nF i))
          concl).instantiateList as1 0)
      = some (mkPisAV (ihTeleAtR nF o i (d + δ) (rebit (pwBit ψ pw) tl))
          (conclA.liftN δ tl.length)) := by
  rw [denoteMeta_deepen hws
      (denoteMeta_blockIhOpenerTy hop0 hCf hCb hstripC hi hfr h1 hconcl) δ,
    ← rebit_length (pwBit ψ pw) tl, mkPisAV_ihTeleAtR_shift]

/-! ## The consumer's shape, and the two indices it asks about

The rule lane's composition (`M5M-data-REPORT.md` §S16.6) wants the
existential form — the conclusion's reading is whatever
`denoteMeta_instPisAtLift_peel` hands it off the run's
`Expr.instPisAtLift … (recTyOf c') = some concl` — and it asks this
file to FIX two indices.  Both are fixed here:

* **the `ih` level `l` is the opener's own position `r`**, not `0`:
  `blockIhPis` generates the binder for the `r`-th key at `l = r`, and
  the reading is only correct at a frame whose tail has exactly `r`
  entries (`instSeq_structIdxAtM` couples the two — the second lift's
  cut `nF + l + j` is where the frame's `o` extras sit).  So the
  consumer does pay an `l`-shift to reach the design's `l = 0` tower;
  `ihTeleAtR_shiftAt` above is that shift for the whole telescope, in
  the form `liftN_mkPisAV` states a lifted tower in.
* **the depth is the opener's own**, `fr.rP + fr.nF + r`, and it
  lifts: reading the same (fvar-carrying) term `δ` deeper moves the
  tower to `l = r + δ` (`denoteMeta_blockIhOpenerTy_deep`).  At the
  walk's depth `F + fr.nR + d` the level is therefore `fr.nR + d`, NOT
  `r` — the two are the same statement, and a consumer that reads at
  the walk's frame should take the `_deep` form and skip the lift. -/

/-- **§S16.6's statement**: the `ih` opener's stored type reads to a
`mkPisAV` tower over field `i`'s telescope at the opener's own `ih`
level, whatever its conclusion reads to. -/
theorem denoteMeta_blockIhOpenerTy_exists {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o d i : Nat} {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {as1 : List Expr} (h1 : FvarList (nP + o + nF + d) as1) {concl : Expr}
    (hconcl : ∃ conclA, denoteMeta m.acval env ψ
        (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (concl.instantiateList
          ((openFvars (nP + o + nF + d)
            (ConLeche.structFieldTeleOf cty nP nF i).length).reverse ++ as1) 0)
      = some conclA) :
    ∃ B : AnnotTerm, denoteMeta m.acval env ψ (nP + o + nF + d)
        ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw (ConLeche.structFieldTeleOf cty nP nF i))
          concl).instantiateList as1 0)
      = some (mkPisAV (ihTeleAtR nF o i d (rebit (pwBit ψ pw) tl)) B) :=
  hconcl.imp fun _ h => denoteMeta_blockIhOpenerTy hop0 hCf hCb hstripC hi hfr h1 h

/-- **§S16.6's statement at the WALK's depth**: `δ` binders below the
opener, the same tower at `ih` level `d + δ`. -/
theorem denoteMeta_blockIhOpenerTy_deep_exists {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o d i : Nat} {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {as1 : List Expr} (h1 : FvarList (nP + o + nF + d) as1) {concl : Expr}
    (hws : Expr.WScoped (nP + o + nF + d)
      ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw
        (ConLeche.structFieldTeleOf cty nP nF i)) concl).instantiateList as1 0))
    (hconcl : ∃ conclA, denoteMeta m.acval env ψ
        (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (concl.instantiateList
          ((openFvars (nP + o + nF + d)
            (ConLeche.structFieldTeleOf cty nP nF i).length).reverse ++ as1) 0)
      = some conclA) (δ : Nat) :
    ∃ B : AnnotTerm, denoteMeta m.acval env ψ (nP + o + nF + d + δ)
        ((Expr.mkPisOf (ConLeche.structTeleAt nF o i d pw (ConLeche.structFieldTeleOf cty nP nF i))
          concl).instantiateList as1 0)
      = some (mkPisAV (ihTeleAtR nF o i (d + δ) (rebit (pwBit ψ pw) tl)) B) :=
  hconcl.elim fun _ h =>
    ⟨_, denoteMeta_blockIhOpenerTy_deep hop0 hCf hCb hstripC hi hfr h1 hws h δ⟩

/-! ## `hop` — the run's identification of the opener's stored type

`denoteMeta_blockIhOpenerTy` takes the opener's stored type in the
shape `(Expr.mkPisOf (structTeleAt …) concl).instantiateList as1 0`;
what the RUN leaves is `checkBlockRule`'s third opening,
`openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse) (rP + nF)`.
The two meet through four facts, all of them now in the tree:

* `openPisAtFvars_fvarTypeD` (`FixRecReadDefs.lean`) — the `r`-th
  opener's stored type IS the `r`-th stripped binder domain with the
  `r` earlier openers `instSeq`'d;
* `stripPis_blockIhPis` (`BlockRecRegimes.lean`) — that binder is the
  key's own domain at `ih` level `r`;
* `stripPis_instantiateList` — the frame's opening reaches it at cut
  `r`;
* `instantiateList_split` — the `instSeq` and the cut-`r` opening
  COMPOSE into the single opening list
  `(fvsIh.take r).reverse ++ (fvsPref ++ fvsF).reverse`, which is a
  `FvarList (rP + nF + r)` — the battery's `as1`. -/

/-- **The opener list, extended by the openers standing before it**,
is a frame opening: `openPisAtFvars` puts opener `k` at index
`rP + nF + k`, so the first `r` of them REVERSED head the opening
list, exactly as `FvarList`'s descending index wants. -/
theorem FvarList.openerExtend {E r : Nat} {L fvs : List Expr} (hL : FvarList E L)
    (hidx : ∀ (j : Nat) (x : Expr), fvs[j]? = some x → ∃ ty, x = Expr.fvar (E + j) ty)
    (hwsty : ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
      Expr.WScoped (E + j) (Expr.fvarTypeD x))
    (hlen : r ≤ fvs.length) :
    FvarList (E + r) ((fvs.take r).reverse ++ L) := by
  have htl : (fvs.take r).length = r := by rw [List.length_take]; omega
  refine ⟨by rw [List.length_append, List.length_reverse, htl, hL.1]; omega,
    fun j hj => ?_, fun x hx => ?_⟩
  · by_cases hjr : j < r
    · have hlt : r - 1 - j < (fvs.take r).length := by rw [htl]; omega
      obtain ⟨y, hy⟩ : ∃ y, (fvs.take r)[r - 1 - j]? = some y :=
        ⟨(fvs.take r)[r - 1 - j], List.getElem?_eq_getElem hlt⟩
      obtain ⟨ty, hty⟩ := hidx (r - 1 - j) y (by
        rw [← hy, List.getElem?_take_of_lt (show r - 1 - j < r from by omega)])
      refine ⟨ty, ?_⟩
      rw [List.getElem?_append_left (by rw [List.length_reverse, htl]; omega),
        List.getElem?_reverse (by rw [htl]; omega), htl, hy, hty]
      congr 2
      omega
    · obtain ⟨ty, hty⟩ := hL.2.1 (j - r) (by omega)
      refine ⟨ty, ?_⟩
      rw [List.getElem?_append_right (by rw [List.length_reverse, htl]; omega),
        List.length_reverse, htl, hty]
      congr 2
      omega
  · rcases List.mem_append.mp hx with hx' | hx'
    · rw [List.mem_reverse] at hx'
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
      have hqr : q < r := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [htl] at this; exact this
      have hq' : fvs[q]? = some x := by
        rw [← hq, List.getElem?_take_of_lt hqr]
      obtain ⟨ty, rfl⟩ := hidx q x hq'
      have := hwsty q _ hq'
      simp only [Expr.WScoped]
      exact ⟨by omega, this⟩
    · exact Expr.WScoped.mono (by omega) (hL.2.2 x hx')

set_option maxHeartbeats 800000 in
/-- **`hop`, at the run.**  The `r`-th `ih` opener's STORED type is the
generated Π-tower over field `i`'s telescope at `ih` level `r`, over
the callee's conclusion, opened at the frame the check built. -/
theorem blockIhOpener_stored
    {nP rP nF : Nat} {pw : PropWhen} {recTyOf : Nat → Expr}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    {is : List (Nat × Nat)} {body ihTele : Expr} {L fvsIh : List Expr} {bodyO : Expr}
    (hpis : ConLeche.blockIhPis nP rP nF pw recTyOf teleOf idxOf is 0 body = some ihTele)
    (hL : FvarList (rP + nF) L) (hfv : ihTele.hasFvar = false)
    (hopen : ConLeche.openPisAtFvars is.length (ihTele.instantiateList L) (rP + nF)
      = some (fvsIh, bodyO))
    {r i c : Nat} (hkey : is[r]? = some (i, c)) {x : Expr} (hx : fvsIh[r]? = some x) :
    ∃ concl : Expr,
      Expr.instPisAtLift
          (ConLeche.blockRulePrefixVars rP nF (r + (teleOf i).length) ++
            (idxOf i).map (ConLeche.structIdxAt nF (rP - nP) i r (teleOf i).length) ++
            [Expr.mkAppN (.bvar (nF - 1 - i + r + (teleOf i).length))
              (ConLeche.structTeleVars (teleOf i).length)])
          (recTyOf c) = some concl ∧
      x.fvarTypeD
        = (Expr.mkPisOf (ConLeche.structTeleAt nF (rP - nP) i r pw (teleOf i))
            concl).instantiateList ((fvsIh.take r).reverse ++ L) 0 ∧
      FvarList (rP + nF + r) ((fvsIh.take r).reverse ++ L) := by
  -- the generator's binder list, and the frame's opening of it
  obtain ⟨bs, hst, hbslen, hbidx⟩ := stripPis_blockIhPis is 0 body ihTele hpis
  obtain ⟨bs', hst', hbs'len, hbs'idx⟩ := stripPis_instantiateList L is.length 0 hst
  obtain ⟨concl, hconcl, hbr⟩ := hbidx r i c hkey
  rw [Nat.zero_add] at hconcl hbr
  have hbr' := hbs'idx r _ hbr
  rw [Nat.zero_add] at hbr'
  -- the opener's stored type is that binder, with the earlier openers substituted
  have hfvT := openPisAtFvars_fvarTypeD is.length hopen hst' r _ x hbr' hx
  -- the two substitutions compose
  have hrlt : r < fvsIh.length := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    exact this
  have htl : (fvsIh.take r).length = r := by rw [List.length_take]; omega
  have hseq : ∀ Y : Expr, Expr.instSeq (fvsIh.take r) (r - 1) Y
      = Y.instantiateList (fvsIh.take r).reverse 0 := by
    intro Y
    cases r with
    | zero => rw [List.take_zero, List.reverse_nil, Expr.instantiateList_nil]; rfl
    | succ r' =>
      rw [← Expr.instSpine_eq_instSeq]
      exact Expr.instSpine_eq_instantiateList (fvsIh.take (r' + 1)) r' Y
        (by rw [htl])
  refine ⟨concl, hconcl, ?_, ?_⟩
  · have hsplit := instantiateList_split (fvsIh.take r).reverse L
      (Expr.mkPisOf (ConLeche.structTeleAt nF (rP - nP) i r pw (teleOf i)) concl) 0
    rw [Nat.zero_add, List.length_reverse, htl] at hsplit
    rw [hfvT, hseq]
    exact hsplit
  · exact FvarList.openerExtend hL
      (fun j y hy => openPisAtFvars_index is.length _ (rP + nF) hopen j y hy)
      (fun j y hy => openPisAtFvars_typeWScoped is.length hopen
        (wscoped_instantiateList hL ihTele hfv 0) j y hy)
      (by omega)

/-! ## `hopener` — `hop` and the reading, at the consumer's spelling

`blockRuleHfit_of` (`BlockRecData.lean`) takes the opener's two facts
as ONE premise, stated the way the fold reaches them: through the
RESIDUE frame's opening list `as2`, whose suffix is the check's own
`(fvsPref ++ fvsF ++ fvsIh).reverse`.  Getting from there to
`fvsIh[r]` is the frame's index arithmetic, and the rest is
`blockIhOpener_stored` and the reading battery. -/

/-- A found position is the key at that index. -/
theorem pairIdxOf?_getElem? {ps : List (Nat × Nat)} {p : Nat × Nat} {r : Nat}
    (h : ConLeche.pairIdxOf? ps p = some r) : ps[r]? = some p := by
  have hr : r < ps.length := pairIdxOf?_lt h
  have hp : ps.getD r (0, 0) = p := by
    have := List.find?_some h; simpa using this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at hp
  rw [List.getElem?_eq_getElem hr, hp]

/-- A suffix is read at the shifted index. -/
theorem suffix_getElem? {xs ys : List Expr} (h : ys <:+ xs) {n : Nat}
    (hn : xs.length = n + ys.length) (k : Nat) : ys[k]? = xs[n + k]? := by
  obtain ⟨pre, rfl⟩ := h
  have hpre : pre.length = n := by
    rw [List.length_append] at hn; omega
  rw [List.getElem?_append_right (by omega), hpre]
  congr 1
  omega

set_option maxHeartbeats 1600000 in
/-- **`hopener`, from the run**: the `ih` opener's stored type has the
call's Π-count and reads to the design's telescope at the walk's
frame.  Its `hconcl` premise is the CALLEE's conclusion reading, which
is what `denoteMeta_instPisAtLift_peel` gives off the run's own
`Expr.instPisAtLift … (recTyOf c') = some concl`. -/
theorem blockRuleHopener_of {envT : Env} {mT : EnvModel V envT} {ψ : Name → Nat}
    {fr : ConLeche.BlockRuleFrame} {F o : Nat}
    {cty : Expr} {fvs0 : List Expr} {crest : Expr}
    {tlF : Nat → List (Nat × Nat × AnnotTerm)} {EisF : Nat → List AnnotTerm}
    {recTyOf : Nat → Expr} {body ihTele bodyO : Expr}
    {fvsPref fvsF fvsIh : List Expr} {as2₀ : List Expr}
    (hF : fr.nP + o + fr.nF = F) (ho : fr.rP - fr.nP = o) (hrP : fr.nP + o = fr.rP)
    (hop0 : ConLeche.openPisAtFvars (fr.nP + fr.nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (fr.nP + fr.nF)).isSome = true)
    (htele : fr.teleOf = ConLeche.structFieldTeleOf cty fr.nP fr.nF)
    (hfld : ∀ i c' r : Nat, ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      i < fr.nF ∧ FieldReadAt mT ψ fr.nP fr.nF i cty fvs0 (tlF i) (EisF i))
    (hpis : ConLeche.blockIhPis fr.nP fr.rP fr.nF fr.pw recTyOf fr.teleOf fr.idxOf
      fr.ihKeys 0 body = some ihTele)
    (hihfv : ihTele.hasFvar = false)
    (hLpf : FvarList (fr.rP + fr.nF) (fvsPref ++ fvsF).reverse)
    (hopen : ConLeche.openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse)
      (fr.rP + fr.nF) = some (fvsIh, bodyO))
    (has2 : as2₀ = (fvsPref ++ fvsF ++ fvsIh).reverse)
    (hpflen : (fvsPref ++ fvsF).length = fr.rP + fr.nF)
    (hconcl : ∀ (i c' r : Nat) (concl : Expr) (as1 : List Expr),
      ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      Expr.instPisAtLift
          (ConLeche.blockRulePrefixVars fr.rP fr.nF (r + (fr.teleOf i).length) ++
            (fr.idxOf i).map (ConLeche.structIdxAt fr.nF o i r (fr.teleOf i).length) ++
            [Expr.mkAppN (.bvar (fr.nF - 1 - i + r + (fr.teleOf i).length))
              (ConLeche.structTeleVars (fr.teleOf i).length)])
          (recTyOf c') = some concl →
      FvarList (fr.nP + o + fr.nF + r) as1 →
      ∃ conclA, denoteMeta mT.acval envT ψ
          (fr.nP + o + fr.nF + r + (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)
          (concl.instantiateList ((openFvars (fr.nP + o + fr.nF + r)
            (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length).reverse ++ as1) 0)
        = some conclA) :
    ∀ (d i c' r : Nat) (as2 : List Expr) (tyOp : Expr),
      ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      as2₀ <:+ as2 → FvarList (F + fr.nR + d) as2 →
      (Expr.bvar (d + fr.nR - 1 - r)).instantiateList as2 0 = .fvar (F + r) tyOp →
      (tyOp.stripPis (fr.teleOf i).length).isSome = true ∧
      ∃ B : AnnotTerm, denoteMeta mT.acval envT ψ (F + fr.nR + d) tyOp
        = some (mkPisAV (ihTeleAtR fr.nF o i (fr.nR + d)
            (rebit (pwBit ψ fr.pw) (tlF i))) B) := by
  intro d i c' r as2 tyOp hrpos hsx h2 hhead
  obtain ⟨hiF, hfr⟩ := hfld i c' r hrpos
  have hr : r < fr.nR := pairIdxOf?_lt hrpos
  have hIhlen : fvsIh.length = fr.nR := openPisAtFvars_length fr.nR hopen
  -- (1) the opener the head names IS `fvsIh[r]`
  have hj : d + fr.nR - 1 - r < F + fr.nR + d := by omega
  obtain ⟨ty0, hty0⟩ := h2.2.1 (d + fr.nR - 1 - r) hj
  rw [show F + fr.nR + d - 1 - (d + fr.nR - 1 - r) = F + r from by omega] at hty0
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hty0
  have hinst : (Expr.bvar (d + fr.nR - 1 - r)).instantiateList as2 0 = Expr.fvar (F + r) ty0 := by
    rw [Expr.instantiateList, if_neg (by omega), dif_pos (by omega)]
    simp only [Nat.sub_zero]
    rw [show as2[d + fr.nR - 1 - r] = Expr.fvar (F + r) ty0 from hget0, Expr.instantiateList]
  have hEq : ty0 = tyOp := by
    have h := hinst.symm.trans hhead
    injection h
  rw [hEq] at hty0
  -- the suffix, and the ascending frame's index
  have hcat : (fvsPref ++ fvsF ++ fvsIh).length = fr.rP + fr.nF + fr.nR := by
    rw [List.length_append, hpflen, hIhlen]
  have has2len : as2₀.length = F + fr.nR := by
    rw [has2, List.length_reverse, hcat]; omega
  have hsufk := suffix_getElem? hsx (n := d) (by rw [h2.1, has2len]; omega) (fr.nR - 1 - r)
  rw [show d + (fr.nR - 1 - r) = d + fr.nR - 1 - r from by omega] at hsufk
  have hIhr : fvsIh[r]? = some (Expr.fvar (F + r) tyOp) := by
    have h1' := hsufk.trans hty0
    rw [has2, List.getElem?_reverse (by rw [hcat]; omega), hcat,
      show fr.rP + fr.nF + fr.nR - 1 - (fr.nR - 1 - r) = (fvsPref ++ fvsF).length + r from by
        rw [hpflen]; omega,
      List.getElem?_append_right (by omega)] at h1'
    rw [← h1']
    congr 1
    omega
  -- (2) `hop`
  obtain ⟨concl, hconclRun, hstored, hFv1⟩ :=
    blockIhOpener_stored hpis hLpf hihfv hopen (pairIdxOf?_getElem? hrpos) hIhr
  rw [show (Expr.fvar (F + r) tyOp).fvarTypeD = tyOp from rfl, ho] at hstored
  rw [ho] at hconclRun
  rw [show fr.rP + fr.nF + r = fr.nP + o + fr.nF + r from by omega] at hFv1
  refine ⟨?_, ?_⟩
  -- (3) the Π-count
  · rw [hstored]
    obtain ⟨bs, hbs⟩ : ∃ p, (Expr.mkPisOf (ConLeche.structTeleAt fr.nF o i r fr.pw
        (fr.teleOf i)) concl).stripPis (fr.teleOf i).length = some p :=
      Option.isSome_iff_exists.mp (stripPis_isSome_mkPisOf _ _ _
        (by rw [structTeleAt_length]; omega))
    obtain ⟨bs', hbs', -, -⟩ := stripPis_instantiateList
      ((fvsIh.take r).reverse ++ (fvsPref ++ fvsF).reverse) (fr.teleOf i).length 0 hbs
    rw [hbs']
    rfl
  -- (4) the reading, at the walk's frame
  · have hwsOp : Expr.WScoped (fr.nP + o + fr.nF + r)
        ((Expr.mkPisOf (ConLeche.structTeleAt fr.nF o i r fr.pw
          (ConLeche.structFieldTeleOf cty fr.nP fr.nF i)) concl).instantiateList
          ((fvsIh.take r).reverse ++ (fvsPref ++ fvsF).reverse) 0) := by
      have hw := h2.2.2 _ (List.mem_of_getElem? hty0)
      simp only [Expr.WScoped] at hw
      rw [hF, ← htele, ← hstored]
      exact hw.2
    obtain ⟨B, hB⟩ := denoteMeta_blockIhOpenerTy_deep_exists hop0 hCf hCb hstripC hiF hfr
      hFv1 hwsOp (hconcl i c' r concl _ hrpos hconclRun hFv1) (fr.nR + d - r)
    refine ⟨B, ?_⟩
    rw [show fr.nP + o + fr.nF + r + (fr.nR + d - r) = F + fr.nR + d from by omega,
      show r + (fr.nR + d - r) = fr.nR + d from by omega] at hB
    rw [hstored, htele]
    exact hB

end ConLeche.Model
