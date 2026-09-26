module

public import ConLeche.Model.Inductives.BlockRecRule

public section

/-!
# The `ih` OPENER's stored type, read

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

The rule's `hfit` needs that type's READING, and needs it as a
`mkPisAV` tower: `spineFit_of_teleFitPA`
(`BlockRecLaw.lean`) is stated at one, and `TeleFitPA` at an arbitrary
`Ta` says nothing about the domains the certified spine has to fit.

## The readings

`denoteMeta_ihSpineAt` (`Model/Inductives/FixRecRead.lean`) reads a
`structTeleAt` tower only with the CONCLUSION spelled (a head applied
to leading arguments, the field's index expressions and the field at
its own telescope variables).  The opener's conclusion is not of that
shape (it is a callee's stored TYPE instantiated at that spine), so the
reading is cut one level lower:

* `denoteMeta_structTeleAtPis` — the tower over `structTeleAt` with an
  ARBITRARY conclusion, whose reading is a premise.  The whole content
  is the telescope, binderwise (`denoteMeta_ihIdxAtM` at each binder),
  and it lands at `ihTeleAtR`, which is what the consumer needs.
* `denoteMeta_blockIhOpenerTy` — the same statement at the CHECK's own
  opening list (`FvarList`, `instantiateList`), which is the shape the
  rule's premises are spelled in; the twin of
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

/-! ## The opener's stored type, at the CHECK's own opening list

The rule's premises spell its frames as `FvarList E as1` and opens with
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

/-! ## The `ih` position's shift

The opener at `ih` position `r` is generated at `l = r` and reads at
the frame whose tail has `r` entries; a consumer standing `δ` binders
deeper reads the same data at `l = r + δ`.  `ihIdxAtM_shift`
(`BlockRecRule.lean`) is the elementwise `0 → d` case of the move;
these three are the whole telescope's, in the `liftDoms` form
`liftN_mkPisAV` (`StructRecKit.lean`) states a lifted Π-tower in —
so a consumer transports between the two readings with ONE `liftN`,
the same way `ihSpineFold_blockRec` transports the guarded call's. -/

/-! ## The same reading, at a deeper frame

The consumer of the `ih` opener's type is the rule body's WALK, which
stands `δ` binders below the opener's own position — and reading the
SAME (opened, hence `fvar`-carrying) term at a deeper frame is
reading it at the shallow one and lifting, because `denoteMeta` reads
`fvar k` at depth `D` as `bvar (D - 1 - k)`
(`denoteMeta_shiftFromN` at the cut `p = D`).  Composed with the ih
position's shift, that is the statement at the walk's frame with no
work left for the consumer. -/

/-! ## The consumer's shape, and the two indices it asks about

The rule's composition wants the existential form — the conclusion's
reading is whatever `denoteMeta_instPisAtLift_peel` hands it off the
run's `Expr.instPisAtLift … (recTyOf c') = some concl` — at two fixed
indices:

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

/-! ## `hop` — the run's identification of the opener's stored type

`denoteMeta_blockIhOpenerTy` takes the opener's stored type in the
shape `(Expr.mkPisOf (structTeleAt …) concl).instantiateList as1 0`;
what the RUN leaves is `checkBlockRule`'s third opening,
`openPisAtFvars fr.nR (ihTele.instantiateList (fvsPref ++ fvsF).reverse) (rP + nF)`.
The two meet through four facts:

* `openPisAtFvars_fvarTypeD` (`FixKit.lean`) — the `r`-th
  opener's stored type IS the `r`-th stripped binder domain with the
  `r` earlier openers `instSeq`'d;
* `stripPis_blockIhPis` (`BlockCallCerts.lean`) — that binder is the
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

/-! ## The opener's CONCLUSION, read — `hconcl`

`blockRuleHopener_of` below reduces the fit's opener premise to ONE
input: the CALLEE's stored type, peeled at the generated call's spine
(`blockIhPis`' own `instPisAtLift`) and opened at the rule frame's
variables, HAS a reading.  This section produces it, and it is the
`blockIhSpinePis` recipe one level down — the SAME spine, peeling a
callee's `∀`-telescope instead of applying a constant:

* the spine's elements are bounded at the frame and carry no free
  variable (`blockIhSpine_closed`), so the check's capture-avoiding
  peel commutes with the frame's opening (`instPisAtLift_instSeq`,
  `BlockRecRule.lean`);
* the opened spine READS — the prefix variables' bvars,
  `denoteMetaSpine_ihIdx` and the applied field, which are
  `denoteMeta_blockIhSpinePis`' own three segments
  (`denoteMetaSpine_blockIhSpine`);
* the callee's stored type is CLOSED, so the frame's opening leaves it
  alone and its reading at depth `0` is its reading at the frame
  (`denoteMeta_deepen`).

`denoteMeta_instPisAtLift_peel` (`BlockRecRead.lean`) then reads the
peel itself, and the conclusion's reading is whatever it hands back —
which is all `denoteMeta_blockIhOpenerTy_deep_exists` asks for. -/


/-! ## `hopener` — `hop` and the reading, at the consumer's spelling

`blockRuleHfit_of` (`BlockRecData.lean`) takes the opener's two facts
as ONE premise, stated the way the fold reaches them: through the
RESIDUE frame's opening list `as2`, whose suffix is the check's own
`(fvsPref ++ fvsF ++ fvsIh).reverse`.  Getting from there to
`fvsIh[r]` is the frame's index arithmetic, and the rest is
`blockIhOpener_stored` and the reading battery. -/

end ConLeche.Model
