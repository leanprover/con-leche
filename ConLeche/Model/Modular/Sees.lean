module

public import ConLeche.Model.Modular.IsModel
public import ConLeche.Verify.Driver.SeesCtx
import ConLeche.Verify.Driver.SeesOwn
import ConLeche.Model.OfEnvModelM
import ConLeche.Model.IsModelRename
import ConLeche.Verify.Driver.Reach

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

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet}

/-- **The compatible family, read positionally**: for every module up to `i`, a model of its own
environment, read through the stored constants' level parameters (`posModel`); a context name has
the value of the module it is read from, and of every earlier module that agrees on it and stores
it. -/
theorem modular_posModels (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat)
    (hok : ∀ j ≤ i, LocalOk pins dev j) :
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
    have hy : (b, viewOf dev j b) ∈ (toDev V pins dev).sources j :=
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

variable {V : Type w} [SetTheory V] {sp : Roots} {fs : FS}

/-- **The modular theorem over what each module sees**, at an accepted run read through one
lookup (see the module docstring), with imports added at some modules (a compared challenge's
solution, task #619): what a module sees with them (`SeesX`) is valued as its seen module values
it. -/
theorem sees_isModel (V : Type w) [SetTheory V] (R : Run sp fs)
    (hl : ∀ M, R.look M = sp) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ M ∈ R.names, IsModel V (model M) (moduleConstants sp fs M)) ∧
      (∀ M ∈ R.names, ∀ n m', SeesX sp fs (R.x M) M n m' → model M n = model m' n) := by
  classical
  let i := (R.names.map R.rk).sum
  have hle : ∀ M ∈ R.names, R.rk M ≤ i := fun M hM =>
    le_sum_of_mem (List.mem_map_of_mem hM)
  have hok : ∀ j ≤ i, LocalOk natOpPinSets R.dev j := fun j _ => R.localOk j
  obtain ⟨base, hmp, hctx, hagr⟩ := modular_posModels V natOpPinSets R.dev i hok
  let own : Name → Env := fun M => (R.dev (R.rk M)).own
  let model : Name → Name → List Nat → V := fun M n =>
    if ((own M).find? n).isSome then base (R.rk M) n
    else if h : ∃ m', SeesX sp fs (R.x M) M n m' then base (R.rk h.choose) n
    else base (R.rk M) n
  have hpart : ∀ {M n m'}, M ∈ R.names → SeesX sp fs (R.x M) M n m' →
      ((own m').find? n).isSome = true := by
    rintro M n m' hM hs
    obtain ⟨hm', -, hxm'⟩ := R.sees_rank hl hM hs
    obtain ⟨p, c, -, hc, rfl⟩ := hs
    have := R.part_own hm' hxm' (p := p) (by rw [hl]; exact hc)
    exact this
  have hmodel_own : ∀ {M n}, ((own M).find? n).isSome = true → model M n = base (R.rk M) n := by
    intro M n h; simp only [model, h, ↓reduceIte]
  refine ⟨model, fun M hM => ?_, fun M hM n m' hs => ?_⟩
  · obtain ⟨mp, hmpe⟩ := hmp (R.rk M) (hle M hM)
    have hnd := (ImportOk.chain (hok _ (hle M hM)).importOk).1
    -- every constant of the module is stored, as itself or renamed
    have hcov : ∀ c, moduleConstants sp fs M c → ∃ ci, (own M).find? c.name = some ci ∧
        ((StoredAs ci c ∧ ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
            RecReads (own M).find? ci ∨ ∃ k cv, ci = quotAt k cv) ∨ RenamedAs ci c) := by
      intro c hc
      rcases R.own_covers_x hM (c := c) (by rw [hl]; exact hc) with ⟨c', hc', hst⟩ |
        ⟨ci, hci, hn, hst⟩
      · obtain ⟨ci, hf, hst', hrd⟩ := own_recordsStored (hok _ (hle M hM)).importOk c' hc'
        have hn : c'.name = c.name := by
          show c'.toConstantVal.name = c.toConstantVal.name
          rw [hst.1]
        refine ⟨ci, hn ▸ hf, .inl ⟨hst'.trans hst, fun cv mI rP isK rules hc1 => ?_⟩⟩
        obtain ⟨isK', rules', h', -⟩ := hst.2.2.1 cv mI rP isK rules hc1
        exact hrd cv mI rP isK' rules' h'
      · have hctx : ∀ c', c' ∈ (streamEnv (R.w M).reach.ctx.toList).consts → c' ∈ (own M).consts :=
          fun c' hc' => by
            show c' ∈ (R.dev (R.rk M)).own.consts
            rw [R.dev_rk hM]
            exact (ConLeche.Driver.mem_streamEnv_consts _ _).2 (.inr hc')
        refine ⟨ci, hn ▸ Driver.find?_of_nodup hnd (hctx ci hci), ?_⟩
        rcases hst with ⟨hst, f, hf, hrd⟩ | hren
        · refine .inl ⟨hst, fun cv mI rP isK rules hc1 => .inl ?_⟩
          refine RecReads.mono (fun n c' h => ?_) (hrd cv mI rP isK rules hc1)
          obtain ⟨hm, rfl⟩ := hf n c' h
          exact Driver.find?_of_nodup hnd (hctx c' hm)
        · exact .inr hren
    have hag : AgreesOn (model M) (cvalOf mp.base2.acval) (own M) := fun n ci hf => by
      rw [hmodel_own (by rw [hf]; rfl), hmpe]
    let Rs : ConstantInfo → Prop := fun c => moduleConstants sp fs M c ∧
      ∃ ci, (own M).find? c.name = some ci ∧ StoredAs ci c ∧
        ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
          RecReads (own M).find? ci ∨ ∃ k cv, ci = quotAt k cv
    have hRs : RecordsStored Rs (own M) := fun c ⟨_, ci, hf, hst, hrd⟩ => ⟨ci, hf, hst, hrd⟩
    have heq : EqReads (model M) := by
      -- `Eq`'s value is a member's that stores it, or `M`'s own
      by_cases h1 : ((own M).find? eqName).isSome = true
      · exact EqReads.congr (by rw [hmodel_own h1, hmpe]) (eqReads_envModelM mp)
      · by_cases h2 : ∃ m', SeesX sp fs (R.x M) M eqName m'
        · have hm₀ := (R.sees_rank hl hM h2.choose_spec).1
          obtain ⟨mp₀, hmp₀⟩ := hmp (R.rk h2.choose) (hle _ hm₀)
          refine EqReads.congr (model' := base (R.rk h2.choose)) ?_ (by
            rw [hmp₀]; exact eqReads_envModelM mp₀)
          funext vals
          simp only [model, h1, h2, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
        · refine EqReads.congr (model' := base (R.rk M)) ?_ (by
            rw [hmpe]; exact eqReads_envModelM mp)
          funext vals
          simp only [model, h1, h2, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
    have hRsM := isModel_of_agree mp hRs hag heq
    intro c hc
    obtain ⟨ci, hf, ⟨hst, hrd⟩ | hren⟩ := hcov c hc
    · exact hRsM c ⟨hc, ci, hf, hst, hrd⟩
    · exact modelOf_renamed mp hag hf hren
  · obtain ⟨hm', hlt, -⟩ := R.sees_rank hl hM hs
    rw [hmodel_own (hpart hM hs)]
    by_cases h1 : ((own M).find? n).isSome = true
    · rw [hmodel_own h1]
      have hc := R.sees_ctx hl hM hs h1
      exact hagr _ (hle M hM) _ hlt n hc (R.sees_agree hl hM hs hc) (hpart hM hs)
    · have hc : ((R.dev (R.rk M)).context.find? n).isSome = false := by
        cases h : ((R.dev (R.rk M)).context.find? n).isSome
        · rfl
        · exact absurd (own_stored_of_context hok (hle M hM) h) h1
      have hex : ∃ m', SeesX sp fs (R.x M) M n m' := ⟨m', hs⟩
      have hu := R.sees_unique hl hM hex.choose_spec hs hc
      simp only [model, h1, hex, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      rw [hu]

end ConLeche.Driver.Compose.Run
