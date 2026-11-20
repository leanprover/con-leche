module

public import ConLeche.Model.Modular.IsModel
public import ConLeche.Verify.Driver.SeesCtx
import ConLeche.Verify.Driver.SeesOwn
import ConLeche.Model.OfEnvModelM

public section

/-!
# The modular theorem over what each module sees (task #618)

An accepted run over a closure (`Driver.Compose.Run`, every module read through the search path,
no import added) has a family of models, one per module, such that

* each module's model is a model of the module's own constants (`moduleConstants`, over the
  input: its private part's);
* a name a module sees as another module's (`Sees`: its header loads a part of that module
  holding a constant of that name) has the value that module's model gives it.

**The construction.**  The development of the run has the compatible family of the modular
theorem (`modular_posModels`: each module's model read positionally through its own environment,
a context name valued as the module it is read from values it, and as every earlier module that
agrees on it).  Module `M`'s model is that family's member at `M`'s rank on every name `M`'s own
environment stores; a name it does not store but sees is valued as the one module it sees it
from (`Run.sees_unique`: a name seen from two modules is a clash, so stored in the context);
any other name as the member at `M`'s rank.

* **The model holds** (`isModel_of_agree`): it agrees with the member on every stored name, the
  module's constants are stored by its own records (`Run.own_covers`), and `Eq` reads as equality
  at whichever member gives its value.
* **The seen names agree**: a seen name is stored by the module it is seen from
  (`Run.part_own`).  Where `M` stores it, it is a context name (`Run.sees_ctx`: no own name of
  `M` is loaded), agreeing with the seen module's copy (`Run.sees_agree`), so the family values
  it alike; where `M` does not, `M`'s model takes that module's value.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean SetTheory

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}

/-- **The compatible family, read positionally**: for every module up to `i`, a model of its own
environment, read through the stored constants' level parameters (`posModel`); a context name has
the value of the module it is read from, and of every earlier module that agrees on it and stores
it. -/
theorem modular_posModels (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Module) (i : Nat)
    (hok : ∀ j ≤ i, LocalOk .verified pins maxNatSize dev j) :
    ∃ base : Nat → Name → List Nat → V,
      (∀ j ≤ i, ∃ mp : EnvModelM V (dev j).own, base j = posModel (cvalOf mp.base2.acval) (dev j).own) ∧
      (∀ j ≤ i, ∀ n, ((dev j).context.find? n).isSome = true →
        (dev j).src n ≤ i ∧ base j n = base ((dev j).src n) n) ∧
      (∀ j ≤ i, ∀ b < j, ∀ n, ((dev j).context.find? n).isSome = true → Agree dev j b n →
        ((dev b).own.find? n).isSome = true → base j n = base b n) := by
  classical
  obtain ⟨mm, hc⟩ := modularModels (V := V) (pins := pins) hok
  have hex : ∀ j (hj : j ≤ i), ∃ mp : EnvModelM V (dev j).own,
      ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = (mm j (by omega)).1 n :=
    fun j hj => (mm j (by omega)).2.2.2.2.elim fun mp h => ⟨mp, h.2.2⟩
  let mp : ∀ j, j ≤ i → EnvModelM V (dev j).own := fun j hj => Classical.choose (hex j hj)
  let base : Nat → Name → List Nat → V := fun j =>
    if hj : j ≤ i then posModel (cvalOf (mp j hj).base2.acval) (dev j).own else fun _ _ => empty
  have hbase : ∀ j (hj : j ≤ i),
      base j = posModel (cvalOf (mp j hj).base2.acval) (dev j).own := by
    intro j hj; simp only [base, hj, ↓reduceDIte]
  -- two stored copies of one name, with one statement and one value in the family, read alike
  have hsame : ∀ j (hj : j ≤ i) b (hb : b ≤ i) n {cj cb : ConstantInfo},
      (dev j).own.find? n = some cj → (dev b).own.find? n = some cb →
      cj.toConstantVal = cb.toConstantVal → (mm j (by omega)).1 n = (mm b (by omega)).1 n →
      base j n = base b n := by
    intro j hj b hb n cj cb hJ hB hcv he
    have hcval : cvalOf (V := V) (mp j hj).base2.acval n = cvalOf (mp b hb).base2.acval n := by
      apply cvalOf_congr
      rw [Classical.choose_spec (hex j hj) n (by rw [hJ]; rfl),
        Classical.choose_spec (hex b hb) n (by rw [hB]; rfl)]
      exact he
    rw [hbase j hj, hbase b hb]
    funext vals
    rw [posModel_of_find hJ, posModel_of_find hB, hcv, hcval]
  refine ⟨base, fun j hj => ⟨mp j hj, hbase j hj⟩, fun j hj n hn => ?_,
    fun j hj b hbj n hn hag hbn => ?_⟩
  · obtain ⟨hs, he, -⟩ := hc j (by omega) n ⟨hn, trivial⟩
    have hs' : (dev j).src n < i + 1 := hs
    have hsi : (dev j).src n ≤ i := by omega
    refine ⟨hsi, ?_⟩
    obtain ⟨ciC, hC⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ciB, hB, hal, -⟩ := agree_alike hok (Agree.same rfl) hj hsi hC
    have hJ : (dev j).own.find? n = some ciC :=
      own_find?_of_context (ImportOk.chain (hok j hj).importOk).1 hC
    have hcv : ciC.toConstantVal = ciB.toConstantVal := by
      rcases hal with rfl | ⟨h, -⟩
      · rfl
      · exact h
    exact hsame j hj _ hsi n hJ hB hcv he
  · have hbi : b ≤ i := by omega
    obtain ⟨hs, he, hsrcs⟩ := hc j (by omega) n ⟨hn, trivial⟩
    have hy : (b, viewOf dev j b) ∈ (toDev V pins maxNatSize dev).sources j :=
      List.mem_map.2 ⟨b, List.mem_range.2 hbj, rfl⟩
    have hb' := hsrcs _ hy (by omega) ⟨hbn, hn, hag⟩
    obtain ⟨ciC, hC⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ciB, hB, hal, -⟩ := agree_alike hok hag hj hbi hC
    have hJ : (dev j).own.find? n = some ciC :=
      own_find?_of_context (ImportOk.chain (hok j hj).importOk).1 hC
    have hcv : ciC.toConstantVal = ciB.toConstantVal := by
      rcases hal with rfl | ⟨h, -⟩
      · rfl
      · exact h
    exact hsame j hj b hbi n hJ hB hcv (he.trans hb'.symm)

/-- `EqReads` asks only `Eq`'s value. -/
theorem EqReads.congr {model model' : Name → List Nat → V} (h : model eqName = model' eqName)
    (hm : EqReads model') : EqReads model := by
  intro k T L R hT hL hR
  rw [h]; exact hm k T L R hT hL hR

theorem le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | _ :: l, _, .tail _ h => by have := le_sum_of_mem (l := l) h; simp; omega

end ConLeche.Model.Modular

namespace ConLeche.Driver.Compose.Run

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean SetTheory
  ConLeche.Model ConLeche.Model.Modular

universe w

variable {V : Type w} [SetTheory V] {sp : Roots} {fs : FS} {maxNatSize : Nat}

/-- **The modular theorem over what each module sees**, at an accepted run (see the module
docstring). -/
theorem sees_isModel (V : Type w) [SetTheory V] (R : Run sp fs maxNatSize)
    (hl : ∀ M, R.look M = sp) (hx : ∀ M, R.x M = #[]) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ M ∈ R.names, IsModel V (model M) (moduleConstants sp fs M)) ∧
      (∀ M ∈ R.names, ∀ n m', Sees sp fs M n m' → model M n = model m' n) := by
  classical
  let i := (R.names.map R.rk).sum
  have hle : ∀ M ∈ R.names, R.rk M ≤ i := fun M hM =>
    le_sum_of_mem (List.mem_map_of_mem hM)
  have hok : ∀ j ≤ i, LocalOk .verified natOpPinSets maxNatSize R.dev j := fun j _ => R.localOk j
  obtain ⟨base, hmp, hctx, hagr⟩ := modular_posModels V natOpPinSets maxNatSize R.dev i hok
  let own : Name → Env := fun M => (R.dev (R.rk M)).own
  let model : Name → Name → List Nat → V := fun M n =>
    if ((own M).find? n).isSome then base (R.rk M) n
    else if h : ∃ m', Sees sp fs M n m' then base (R.rk h.choose) n
    else base (R.rk M) n
  have hpart : ∀ {M n m'}, Sees sp fs M n m' → m' ∈ R.names →
      ((own m').find? n).isSome = true := by
    rintro M n m' ⟨p, c, -, hc, rfl⟩ hm'
    have := R.part_own hm' (hx m') (p := p) (by rw [hl]; exact hc)
    exact this
  have hmodel_own : ∀ {M n}, ((own M).find? n).isSome = true → model M n = base (R.rk M) n := by
    intro M n h; simp only [model, h, ↓reduceIte]
  refine ⟨model, fun M hM => ?_, fun M hM n m' hs => ?_⟩
  · obtain ⟨mp, hmpe⟩ := hmp (R.rk M) (hle M hM)
    -- the module's constants are stored in its own environment
    have hrec : RecordsStored (moduleConstants sp fs M) (own M) :=
      (own_recordsStored (hok _ (hle M hM)).importOk).mono fun c hc => by
        have := R.own_covers hM (hx M) (c := c) (by rw [hl]; exact hc)
        obtain ⟨c', hc', hst⟩ := this
        exact ⟨c', hc', hst⟩
    refine isModel_of_agree mp hrec (fun n ci hf => ?_) ?_
    · rw [hmodel_own (by rw [hf]; rfl), hmpe]
    · -- `Eq`'s value is a member's that stores it, or `M`'s own
      by_cases h1 : ((own M).find? eqName).isSome = true
      · exact EqReads.congr (by rw [hmodel_own h1, hmpe]) (eqReads_envModelM mp)
      · by_cases h2 : ∃ m', Sees sp fs M eqName m'
        · have hm₀ := (R.sees_rank hl hx hM h2.choose_spec).1
          obtain ⟨mp₀, hmp₀⟩ := hmp (R.rk h2.choose) (hle _ hm₀)
          refine EqReads.congr (model' := base (R.rk h2.choose)) ?_ (by
            rw [hmp₀]; exact eqReads_envModelM mp₀)
          funext vals
          simp only [model, h1, h2, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
        · refine EqReads.congr (model' := base (R.rk M)) ?_ (by
            rw [hmpe]; exact eqReads_envModelM mp)
          funext vals
          simp only [model, h1, h2, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hm', hlt⟩ := R.sees_rank hl hx hM hs
    rw [hmodel_own (hpart hs hm')]
    by_cases h1 : ((own M).find? n).isSome = true
    · rw [hmodel_own h1]
      have hc := R.sees_ctx hl hx hM hs h1
      exact hagr _ (hle M hM) _ hlt n hc (R.sees_agree hl hx hM hs hc) (hpart hs hm')
    · have hc : ((R.dev (R.rk M)).context.find? n).isSome = false := by
        cases h : ((R.dev (R.rk M)).context.find? n).isSome
        · rfl
        · exact absurd (own_stored_of_context hok (hle M hM) h) h1
      have hex : ∃ m', Sees sp fs M n m' := ⟨m', hs⟩
      have hu := R.sees_unique hl hx hM hex.choose_spec hs hc
      simp only [model, h1, hex, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      rw [hu]

end ConLeche.Driver.Compose.Run
