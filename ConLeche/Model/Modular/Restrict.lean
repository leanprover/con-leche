module

public import ConLeche.Model.Modular.RestrictNat
public import ConLeche.Model.Modular.RestrictRules
public import ConLeche.Model.Modular.RestrictLfp

public section

/-!
# A context's model, read from its sources' models

The first half of the modular theorem's amalgamation (`ConLeche/Modular.lean`): a context read
from its sources (`CtxRead`), with a covered model of each source whose leaves are the context's
on every name read alike, has a model (`CtxModel`): every law of a context constant is read off
its source's law (`Model/Modular/Restrict{Agree,Base,Nat,Rules,Lfp}.lean`), and the context
records its sources' blocks.

Three facts come as hypotheses beyond `CtxRead` and the sources' models: the context's `Nat`
facts (`hnatC`); that a compiler-trust opaque's name is stored as its source's constant (`hred`:
a definition at such a name presented as its statement would carry no identity law); and, for a
recorded member whose stored type does not show its telescope, that the telescope its block read
is read alike and that its reduction runs at a part of the context (`hdh`; the source's run is at
a part of the source).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term SetTheory

universe w

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-- **The context's model.** -/
noncomputable def model : EnvModelM V C where
  base2 := S.base
  type_reads := S.type_reads
  type_wellDenotedTy := S.type_wellDenotedTy
  mem_type := S.mem_type
  defn_reads := S.defn_reads
  nat_heads := S.nat_heads
  nat_ops := S.nat_ops
  div_mod := S.div_mod
  eq_law := S.eq_law
  caps_ok := S.caps_ok
  rec_rules := S.rec_rules
  reduce_ops := S.reduce_ops
  tower_ok := S.tower_ok
  lfpBlocks := S.lfpList
  lfp_ok := S.lfp_ok

theorem model_acval : S.model.base2.acval = aC := by rfl

/-- **The context's model is covered.** -/
theorem model_cover : LfpCover S.model [] where
  cover := fun n cv caps hf _ hq => by
    obtain ⟨D, hD, mm, hmm, hmn⟩ :=
      (S.cover n).cover n cv caps (S.src_ind hf rfl) List.not_mem_nil hq
    have hmem : n ∈ D.names := hmn ▸ S.member_getD hD hmm
    exact ⟨D, S.lfpList_of hf hD hmem, mm, hmm, hmn⟩
  nodup := fun D hD => by
    obtain ⟨n, -, -, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).nodup D hDn
  len := fun D hD => by
    obtain ⟨n, -, -, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).len D hDn
  all := fun D hD mm hmm cv caps hf => by
    obtain ⟨n, cvn, capsn, hfn, hDn, hmem⟩ := S.mem_lfpList hD
    have hb := (S.blockNames hfn hDn hmem).1 mm hmm
    exact (S.cover n).all D hDn mm hmm cv caps (by rw [← hb.2]; exact hf)
  fresh := fun _ _ _ _ h => List.not_mem_nil h
  own := fun D hD => S.lfpOwn hD
  wid := fun D hD => by
    obtain ⟨n, -, -, -, hDn, -⟩ := S.mem_lfpList hD; exact (S.cover n).wid D hDn

/-- **The context's recorded telescopes were reduced at a part of it.** -/
theorem model_ran : FamilyRan S.model := by
  intro D hD mm f hmm ht cv caps hf hfl
  obtain ⟨n, _, _, hfn, hDn, -⟩ := S.mem_lfpList hD
  exact (S.defh n (isSome_of hfn) D hDn mm f hmm ht cv caps hf hfl).2

end CtxSrc

/-- **THE CONTEXT'S MODEL**: a context read from its sources' covered models has a covered model
at the leaves `aC` (see the module docstring for the three further hypotheses). -/
theorem ctxModel {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
    {aC : Name → (Name → Nat) → Term}
    (hread : CtxRead C E R)
    (m : (n : Name) → EnvModelM V (E n)) (hcov : ∀ n, LfpCover (m n) [])
    (heta : ∀ n, EtaFamiliesClosed (E n)) (hnat : ∀ n, NatFacts (E n))
    (hnatC : NatFacts C)
    (hred : ∀ n ci, C.find? n = some ci → n ∈ reduceOpNames → (E n).find? n = some ci)
    (hdh : ∀ n, (C.find? n).isSome = true → ∀ D ∈ (m n).lfpBlocks, ∀ mm f, mm < D.k →
      D.telescope mm = some f → ∀ cv caps, C.find? (D.member mm) = some (.indInfo cv caps) →
      formerDefHeaded cv = true →
      f.type.constsResolve (R n) = true ∧
      ∃ envB F, EnvExt envB C ∧ cv.type.constsResolve envB = true ∧
        reducedFormer (fueledOps .verified F) envB cv (caps.nparams + caps.nIdx) = .ok f)
    (hleaf : ∀ n, (C.find? n).isSome = true → ∀ d, ((R n).find? d).isSome = true →
      aC d = (m n).base2.acval d)
    (hclosed : ∀ n ψ, Term.Closed (aC n ψ)) (hwd : ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (aC n ψ)) :
    CtxModel V C aC := by
  let S : CtxSrc V C E R aC :=
    ⟨hread, m, hcov, heta, hnat, hnatC, hred, hdh, hleaf, hclosed, hwd⟩
  exact ⟨S.model, S.model_cover, S.model_ran, S.etaClosed, hnatC, fun _ _ => by
    rw [S.model_acval]⟩

end ConLeche.Model.Modular
