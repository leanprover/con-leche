module

public import ConLeche.Model.IndCons
import ConLeche.Model.NatEqs
import ConLeche.Model.Env.CanonCrest

public section

/-!
# The P step at a projection table's install (task #362)

`declStep_preserves_of_pushTable`: the install kit at a structure's
projection table.  A table is not a constant: its install adds no name
and moves no leaf, so the leaf valuation stays the prefix's, and every
stored name looks up as before.  The only thing it changes is that the
structure's `.proj` nodes now read (`denote`'s `.proj` clause consults
the table); a reading the prefix already had survives
(`denote_pushTable_mono`: the new table is of a structure that had
none), so every environment law transports along the extension
(`ModelExt.pushTable`) exactly as at a fresh constant's install.  The
one row the transports cannot supply — the new table's own
`TowerEntryLaw` at every field — is the install's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ProjEntry
  ProjTable)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The carrier at a table install**: the prefix's, with the table's
well-formedness and head data added. -/
@[expose] def EnvModel.pushTable (m : EnvModel V env) {t : ProjTable}
    (hwf : ConLeche.EnvWF ⟨env.consts, t :: env.tables⟩)
    (hhead : ∀ i, i < t.numFields → ConLeche.TowerHead env (t.entry i)) :
    EnvModel V ⟨env.consts, t :: env.tables⟩ where
  wf := hwf
  acval := m.acval
  cval_closed := m.cval_closed
  basis_pinned := m.basis_pinned
  proj_ok := ProjOkT.pushTable m.proj_ok hhead
  rec_ctors := m.rec_ctors
  acval_params := m.acval_params
  acval_wellDenoted := m.acval_wellDenoted

/-- `NatOps` across a table install: the stored operations, their
guards and their equations' readings are the prefix's. -/
theorem natOps_pushTable (mp : EnvModelM V μ env) {t : ProjTable}
    (hT : env.findTable? t.structName = none)
    {m₂ : EnvModel V ⟨env.consts, t :: env.tables⟩} (hac : m₂.acval = mp.base2.acval)
    (φ : Name → Nat) : NatOps m₂ φ := by
  intro c hcN cv v hint hf
  obtain ⟨hg, hpin, hlaws⟩ := mp.nat_ops φ c hcN cv v hint hf
  obtain ⟨hN, -, -, -, -⟩ := ConLeche.Verify.natOpGuard_stored hg
  obtain ⟨ciN, hfN, -⟩ := ConLeche.Verify.storedNoLevels_exists hN
  refine ⟨hg, hpin, fun eq hq => ?_⟩
  obtain ⟨L, R, hL, hR, hlaw⟩ := hlaws eq hq
  obtain ⟨h1, h2⟩ := natOpEquations_frag_of_guard hg eq hq
  have hf0 : env.find? c = some (.defnInfo cv v hint) := hf
  have hfE : (env.find? c).isSome = true := by rw [hf0]; rfl
  have hfN' : (env.find? ConLeche.natName).isSome = true := by rw [hfN]; rfl
  refine ⟨L, R, ?_, ?_, ?_⟩
  · rw [hac]
    exact denote_pushTable_mono hT φ 2 (constsBound_of_natFragOk hfE hfN' h1) hL
  · rw [hac]
    exact denote_pushTable_mono hT φ 2 (constsBound_of_natFragOk hfE hfN' h2) hR
  · rw [hac]
    exact hlaw

/-- `CapsOk` across a table install: the stored families, their readings
and their leaves are the prefix's. -/
theorem capsOk_pushTable (mp : EnvModelM V μ env) {t : ProjTable}
    (hT : env.findTable? t.structName = none)
    {m₂ : EnvModel V ⟨env.consts, t :: env.tables⟩} (hac : m₂.acval = mp.base2.acval) :
    CapsOk m₂ := by
  constructor
  · intro T cvT caps hf hcape hres hfam φ' us hlen
    obtain ⟨TVa, hTVa, hokTVa, hlaw, hcoh⟩ :=
      mp.caps_ok.1 T cvT caps hf hcape hres hfam φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_, ?_⟩
    · rw [hac]
      exact denote_pushTable_mono hT _ 0
        (constsBound_instType mp.base2.wf (ConLeche.Env.find?_mem hf) us) hTVa
    · rw [hac]
      exact hlaw
    · refine hcoh.transport (fun cvC nPc nFc hf₂ => hf₂)
        (fun cvC nPc nFc TCa hf hTCa => ?_) (by rw [hac]) (fun _ _ _ => rfl)
      rw [hac]
      exact denote_pushTable_mono hT _ 0
        (constsBound_instType mp.base2.wf (ConLeche.Env.find?_mem hf) us) hTCa
  · intro T cvT caps hf hcapu hres φ' us hlen
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ := mp.caps_ok.2 T cvT caps hf hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denote_pushTable_mono hT _ 0
        (constsBound_instType mp.base2.wf (ConLeche.Env.find?_mem hf) us) hTVa
    · rw [hac]
      exact hlaw

/-- **The P step at a projection table's install.**  The structure has
no table yet, the table is well formed and carries its head data at
every field, and the fields' projection laws are supplied.  The leaf
valuation is the prefix's; everything else transports. -/
theorem declStep_preserves_of_pushTable (mp : EnvModelM V μ env) {t : ProjTable}
    (hT : env.findTable? t.structName = none)
    (hwf : ConLeche.EnvWF ⟨env.consts, t :: env.tables⟩)
    (hhead : ∀ i, i < t.numFields → ConLeche.TowerHead env (t.entry i))
    (hlaw : ∀ m₂ : EnvModel V ⟨env.consts, t :: env.tables⟩,
      m₂.acval = mp.base2.acval →
      ∀ (φ : Name → Nat) (i : Nat), i < t.numFields →
        TowerEntryLaw m₂ φ t.structName i (t.entry i)) :
    ∃ mp' : EnvModelM V μ ⟨env.consts, t :: env.tables⟩,
      mp'.base2.acval = mp.base2.acval := by
  let m₂ : EnvModel V ⟨env.consts, t :: env.tables⟩ := mp.base2.pushTable hwf hhead
  have hac : m₂.acval = mp.base2.acval := rfl
  have hx : ModelExt mp ⟨env.consts, t :: env.tables⟩ m₂.acval := ModelExt.pushTable mp hT
  have hbound := envWF_constsBound mp.base2.wf
  -- a stored type's reading at the install is the prefix's
  have hreadT : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : Term),
      denote m₂.acval ⟨env.consts, t :: env.tables⟩ ψ 0 c.toConstantVal.type = some ta →
      denote mp.base2.acval env ψ 0 c.toConstantVal.type = some ta := by
    intro c hc ψ ta hta
    obtain ⟨ta', hta'⟩ := mp.type_reads c hc ψ
    obtain rfl : ta' = ta := Option.some.inj ((hx.denote (hbound _ hc).1 hta').symm.trans hta)
    exact hta'
  refine ⟨{
    base2 := m₂
    type_reads := fun c hc ψ => by
      obtain ⟨ta, hta⟩ := mp.type_reads c hc ψ
      exact ⟨ta, hx.denote (hbound _ hc).1 hta⟩
    type_wellDenotedTy := fun c hc ψ ta hta =>
      mp.type_wellDenotedTy c hc ψ ta (hreadT c hc ψ ta hta)
    mem_type := fun c hc ψ ta hta =>
      mp.mem_type c hc ψ ta (hreadT c hc ψ ta hta)
    defn_reads := fun ψ cv value hmem => by
      obtain ⟨hint, hdt⟩ := hmem
      obtain ⟨t, ht, hlr⟩ := mp.defn_reads ψ cv value ⟨hint, hdt⟩
      exact ⟨t, hx.denote ((hbound _ hdt).2 cv value hint rfl) ht, hlr⟩
    nat_heads := mp.nat_heads
    nat_ops := natOps_pushTable mp hT hac
    div_mod := mp.div_mod
    eq_law := mp.eq_law
    caps_ok := capsOk_pushTable mp hT hac
    rec_rules := fun φ n cv mI rP rules hf rl hmem =>
      recRuleLaw_ext mp hx φ hf hmem
    reduce_ops := mp.reduce_ops
    tower_ok := fun φ T i entry hf => by
      by_cases hh : t.structName = T ∧ (env.find? T).isSome = true
      · obtain ⟨tbl, hft, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
        rw [ConLeche.Env.findTable?_pushTable, ite_eq_left hh] at hft
        obtain rfl := Option.some.inj hft
        rw [← hh.1]
        exact hlaw m₂ hac φ i hi
      · have hP : Env.findProj? ⟨env.consts, t :: env.tables⟩ T i = env.findProj? T i := by
          unfold Env.findProj?
          rw [ConLeche.Env.findTable?_pushTable, ite_eq_right hh]
        rw [hP] at hf
        exact towerEntryLaw_ext mp hx φ hf
    ind_strict := fun I cv caps hf ψ ab n hread hn ρ vs hsp => by
      have hm := ConLeche.Env.find?_mem hf
      exact mp.ind_strict I cv caps hf ψ ab n (hreadT _ hm ψ _ hread) hn ρ vs hsp
    lfpBlocks := mp.lfpBlocks
    lfp_ok := mp.lfp_ok_transport (fun _ _ hf _ => hf) (fun _ _ _ _ => rfl)
      (fun _ _ _ hf ψ _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        hx.denote (hbound _ hm).1 hta)
      (fun _ _ _ _ hf ψ _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        hx.denote (hbound _ hm).1 hta)
      (fun _ _ hf _ _ hA ψ d _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        hx.denote (canonOf_constsBound (hbound _ hm).1 hA) hta) }, rfl⟩

end ConLeche.Model
