module

public import ConLeche.Model.Inductives.BlockRecRule

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

end ConLeche.Model
