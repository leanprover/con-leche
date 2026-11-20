module

public import ConLeche.Model.Modular.Main
public import ConLeche.Model.IsModelBridge
import ConLeche.Model.OfEnvModelM
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.Copies

public section

/-!
# The modular theorem over `IsModel` (task #618)

A development every module of which passes the local checks has, for every module, a model of
its own records (`IsModel`, over the input: `constantsOf (dev j).decls`), and every name a module
reads from another module is interpreted as that module interprets it.

The models are the compatible family's (`modularModels`), each read positionally through its own
environment (`posModel`): a module's own records are stored in its own environment as they say
(`declsRun_recordsStored`: the fold's accepting run from the context), so the bridge
(`isModel_of_envModelM`) applies; a context name is stored alike by the module it is read from
(`agree_alike`: one statement, so one list of level parameters), and the family gives it one value.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Cached SetTheory

universe w

/-- **A module's own records are stored in its own environment**, as they say. -/
theorem own_recordsStored {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {dev : Nat → Module} {j : Nat} (h : ImportOk mode pins maxNatSize dev j) :
    RecordsStored (· ∈ constantsOf (dev j).decls) (dev j).own := by
  obtain ⟨q, hq⟩ := h.accepted
  have hnd := (ImportOk.chain h).1
  have hb := declsRun_blockRead hq
  have hr := declsRun_reads hq (PushChain.refl (dev j).context)
  have henv : q.2.env = (dev j).own := by rw [declsRun_env mode hq]; rfl
  intro c hc
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  obtain ⟨ci, hci, hst⟩ := records_stored (hb d hd) c hc
  have hmem : ci ∈ (dev j).own.consts :=
    (Driver.mem_streamEnv_consts (dev j).decls _).2 (.inl ⟨d, hd, hci⟩)
  have hn : c.name = ci.name := by
    show c.toConstantVal.name = ci.toConstantVal.name
    rw [hst.1]
  refine ⟨ci, hn ▸ Driver.find?_of_nodup hnd hmem, hst, ?_⟩
  have := hr d hd ci hci
  rwa [henv] at this

/-- **The modular theorem, over the input** (see the module docstring). -/
theorem modular_isModel (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Module) (i : Nat)
    (hok : ∀ j ≤ i, LocalOk .verified pins maxNatSize dev j) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j ≤ i, IsModel V (model j) (· ∈ constantsOf (dev j).decls)) ∧
      ∀ j ≤ i, ∀ n, ((dev j).context.find? n).isSome = true →
        (dev j).src n ≤ i ∧ model j n = model ((dev j).src n) n := by
  classical
  obtain ⟨mm, hc⟩ := modularModels (V := V) (pins := pins) hok
  have hex : ∀ j (hj : j ≤ i), ∃ mp : EnvModelM V (dev j).own,
      ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = (mm j (by omega)).1 n :=
    fun j hj => (mm j (by omega)).2.2.2.2.elim fun mp h => ⟨mp, h.2.2⟩
  let mp : ∀ j, j ≤ i → EnvModelM V (dev j).own := fun j hj => Classical.choose (hex j hj)
  let model : Nat → Name → List Nat → V := fun j =>
    if hj : j ≤ i then posModel (cvalOf (mp j hj).base2.acval) (dev j).own else fun _ _ => empty
  have hmodel : ∀ j (hj : j ≤ i),
      model j = posModel (cvalOf (mp j hj).base2.acval) (dev j).own := by
    intro j hj; simp only [model, hj, ↓reduceDIte]
  refine ⟨model, fun j hj => ?_, fun j hj n hn => ?_⟩
  · rw [hmodel j hj]
    exact isModel_of_envModelM (mp j hj) (own_recordsStored (hok j hj).importOk)
  · obtain ⟨hs, he, -⟩ := hc j (by omega) n ⟨hn, trivial⟩
    have hs' : (dev j).src n < i + 1 := hs
    have hsi : (dev j).src n ≤ i := by omega
    refine ⟨hsi, ?_⟩
    rw [hmodel j hj, hmodel _ hsi]
    obtain ⟨ciC, hC⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ciB, hB, hal, -⟩ := agree_alike hok (Agree.same rfl) hj hsi hC
    have hJ : (dev j).own.find? n = some ciC :=
      own_find?_of_context (ImportOk.chain (hok j hj).importOk).1 hC
    have hcv : ciC.toConstantVal = ciB.toConstantVal := by
      rcases hal with rfl | ⟨h, -⟩
      · rfl
      · exact h
    have hcval : cvalOf (V := V) (mp j hj).base2.acval n =
        cvalOf (mp ((dev j).src n) hsi).base2.acval n := by
      apply cvalOf_congr
      rw [Classical.choose_spec (hex j hj) n (by rw [hJ]; rfl),
        Classical.choose_spec (hex _ hsi) n (by rw [hB]; rfl)]
      exact he
    funext vals
    rw [posModel_of_find hJ, posModel_of_find hB, hcv, hcval]

end ConLeche.Model.Modular
