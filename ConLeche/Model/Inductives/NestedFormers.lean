module

public import ConLeche.Model.Inductives.DeclNested
import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The formers' model of a nested run (task #279 M-D′ D2, DESIGN §M.44)

The restored block's first stage, `env₁ = consNestedFormers (stored.take
p.k) env`, conses the REAL members' formers exactly as the auxiliary
install stored them (the checked former, the empty capability record).
Its model is the cons chain `stageMembersGoG` — the formers' loop at an
ARBITRARY closed leaf — with each member's leaf the AUXILIARY model's
(`mpAux.acval T`): the leaf is closed, level-parametric, graded and
inhabits the former's reading at `envAux` (the model's own rows), and
the former's reading at the PRE-BLOCK carrier is the datum's
(`AuxBlockAgree`, `declMutualCore`'s widening), so nothing is read
across the scratch environment's later stages.

**What comes out**: a model of `env₁` whose carrier is the auxiliary
one on the block's real formers and the pre-block one — hence, through
`AuxBlockAgree`, the auxiliary one — on every name stored before the
block.  That is the agreement `restoredCopyField_read` is stated to
consume, and the environment at which K.17's `whnf` witness is read.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps MutualBlock AuxStored
  MutualFormerA NestedParts)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The restored formers' conses are the checked formers' -/

omit [SetTheory V] in
/-- `consNestedFormers` at records carrying the checked formers with the
empty capability record IS `consMutualFormers` at those formers. -/
theorem consNestedFormers_eq_consMutualFormers :
    ∀ {as : List AuxStored} {fms : List MutualFormerA} {env : Env},
      as.length = fms.length →
      (∀ (i : Nat) (a : AuxStored) (f : MutualFormerA), as[i]? = some a → fms[i]? = some f →
        a.cvTa = f.cvTa ∧ a.caps = {}) →
      ConLeche.consNestedFormers as env = ConLeche.consMutualFormers fms env
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | a :: as, f :: fms, env, hlen, h => by
    obtain ⟨h1, h2⟩ := h 0 a f rfl rfl
    simp only [ConLeche.consNestedFormers, ConLeche.consMutualFormers, h1, h2]
    exact consNestedFormers_eq_consMutualFormers (by simpa using hlen)
      (fun i a' f' ha hf => h (i + 1) a' f' (by simpa using ha) (by simpa using hf))

/-! ## The formers' model -/

/-- **The model of the environment holding the block's real formers**
(M-D′ D2): from the auxiliary model `mpAux` and its agreement with the
pre-block carrier (`AuxBlockAgree`), a model of
`consNestedFormers (stored.take p.k) env` whose carrier is `mpAux`'s on
every real member and `mp`'s — hence `mpAux`'s — on every name stored
before the block; the η families stay closed (the formers carry no η
bit, K.20). -/
theorem nestedFormersModel {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : NestedParts} {b : MutualBlock} {stored : List AuxStored}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone)
      = true)
    (hkp : p.k ≤ b.k)
    (mpAux : EnvModelM V μ envAux) (d : IndRepData V)
    (hreps : MutualBlockReps mpAux.base2 b d) (hag : AuxBlockAgree F mp mpAux b true d) :
    ∃ mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env),
      ConLeche.EtaFamiliesClosed (ConLeche.consNestedFormers (stored.take p.k) env) ∧
      (∀ t, t < p.k →
        mp₁.base2.acval (d.memberName t) = mpAux.base2.acval (d.memberName t)) ∧
      (∀ n : Name, (env.find? n).isSome = true →
        mp₁.base2.acval n = mp.base2.acval n) := by
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  obtain ⟨fms, hformers, hkF, hposF, hstoredF⟩ := auxFormers_stored hrun hfreshRec
  obtain ⟨hstLen, hstGet⟩ := ConLeche.auxStoredAll_get hstored
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNodup, hlpsAll, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -⟩ := hrun
  obtain ⟨-, hkb, -, -, -, -, hnames, hall⟩ := hreps
  -- the checked members carry the declared names, distinct
  have hnamesF : fms.map (·.cvTa.name) = b.memberNames := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map]
    cases hft : fms[t]? with
    | none =>
      have hn : b.formers[t]? = none := by
        rw [List.getElem?_eq_none_iff] at hft ⊢
        exact (by rw [← hkF]; exact hft : b.k ≤ t)
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hn]
    | some f =>
      obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hl, hff.name]
  have hndF : (fms.map (·.cvTa.name)).Nodup := by
    rw [hnamesF]
    have hNd := hNodup
    unfold ConLeche.MutualBlock.blockNames at hNd
    exact (List.nodup_append.mp (List.nodup_append.mp hNd).1).1
  -- the members' level parameters are the block's
  have hlpsF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → f.cvTa.levelParams = b.lps := by
    intro t f hft
    obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
    have hall' : (b.formers.all fun f => f.1.levelParams == b.lps) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp hlpsAll).1
    have := List.all_eq_true.mp hall' (cv, f.nIdx) (List.mem_of_getElem? hl)
    rw [hff.lps]
    simpa using this
  -- a real member's datum name is its checked former's
  have hmemName : ∀ (t : Nat) (f : MutualFormerA), t < b.k → fms[t]? = some f →
      d.memberName t = f.cvTa.name := by
    intro t f ht hft
    rw [hnames t ht, ← hnamesF, List.getD_eq_getElem?_getD, List.getElem?_map, hft]
    rfl
  -- the stored records of the real members are the checked formers with
  -- the empty capability record
  have hstoredEq : ∀ (i : Nat) (a : AuxStored) (f : MutualFormerA),
      (stored.take p.k)[i]? = some a → (fms.take p.k)[i]? = some f →
      a.cvTa = f.cvTa ∧ a.caps = {} := by
    intro i a f ha hf
    rw [List.getElem?_take] at ha hf
    split at ha
    · next hik =>
      rw [if_pos hik] at hf
      obtain ⟨cv, nIdx, hl, hfind⟩ := ConLeche.auxStored?_inv (hstGet i a ha)
      obtain ⟨cv', bs, hl', hff, -⟩ := hposF i f hf
      obtain rfl : cv' = cv := (Prod.mk.inj (Option.some.inj (hl'.symm.trans hl))).1
      have hst := hstoredF f (List.mem_of_getElem? hf)
      rw [hff.name, hfind] at hst
      exact ConstantInfo.indInfo.inj (Option.some.inj hst)
    · exact nomatch ha
  have hEq : ConLeche.consNestedFormers (stored.take p.k) env
      = ConLeche.consMutualFormers (fms.take p.k) env :=
    consNestedFormers_eq_consMutualFormers
      (by rw [List.length_take, List.length_take, hstLen, hkF]) hstoredEq
  have hE₁ : ConLeche.EtaFamiliesClosed (ConLeche.consNestedFormers (stored.take p.k) env) :=
    EtaFamiliesClosed.ofFreshExt hE (consNestedFormers_freshExt hK20)
  rw [hEq] at hE₁ ⊢
  -- the loop at the auxiliary leaves
  obtain ⟨mp₁, hleaf, hoff⟩ := stageMembersGoG (μ := μ) (nP := b.nP) (resSort := d.resSort)
    (lps := b.lps) (Aof := fun t => mpAux.base2.acval (d.memberName t)) (ppsF := d.ppsM)
    (lvlsF := d.lvlsM) (fms.take p.k) (fun i => i) env mp hE
    (fun f hf => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
      rw [List.getElem?_take] at hi
      split at hi
      · obtain ⟨cv, bs, -, hff, -⟩ := hposF i f hi
        exact MemberConsOk.ofFront hff
      · exact nomatch hi)
    (by rw [List.map_take]; exact hndF.sublist (List.take_sublist _ _))
    (by
      intro i f hfi
      rw [List.getElem?_take] at hfi
      split at hfi
      · next hik =>
        have hib : i < b.k := Nat.lt_of_lt_of_le hik hkp
        have hname := hmemName i f hib hfi
        obtain ⟨s, cvT, cvR, caps, mI, rP, rules, hfindT, -, -, hs, hrep⟩ := hall i hib
        have hcvT : cvT = f.cvTa := by
          have hst := hstoredF f (List.mem_of_getElem? hfi)
          rw [← hname, hfindT] at hst
          exact (ConstantInfo.indInfo.inj (Option.some.inj hst)).1
        subst hcvT
        have hlps := hlpsF i f hfi
        refine ⟨hlps, hag.2 _ _ hformers i f hfi, fun ψ => ?_, fun ψ₁ ψ₂ hφ => ?_,
          fun ψ ρ => ?_, fun ψ ρ => ?_⟩
        · exact mpAux.base2.cval_closedL _ ψ
        · refine mpAux.base2.acval_params _ _ hfindT ψ₁ ψ₂ ?_
          show ∀ q ∈ f.cvTa.levelParams, ψ₁ q = ψ₂ q
          rw [hlps]; exact hφ
        · exact ⟨mpAux.base2.acval_wellDenoted _ ψ ρ, mpAux.acval_validV _ ψ ρ⟩
        · -- the leaf inhabits the former's reading at the scratch environment
          have hread := hrep.former.read ψ
          have hmem := mpAux.mem_type _ (ConLeche.Semantics.Env.find?_mem hfindT) ψ _ hread ρ
          have hsv : s.eval ψ = d.resSort.eval ψ := hs ψ
          change interp V ρ (mpAux.base2.acval f.cvTa.name ψ) ∈ˢ _ at hmem
          rw [hsv, ← hname] at hmem
          exact hmem
      · exact nomatch hfi)
  refine ⟨mp₁, hE₁, fun t ht => ?_, fun n hn => ?_⟩
  · obtain ⟨f, hft⟩ : ∃ f, fms[t]? = some f :=
      ⟨_, List.getElem?_eq_getElem (by rw [hkF]; exact Nat.lt_of_lt_of_le ht hkp)⟩
    have h := hleaf t f (by rw [List.getElem?_take, if_pos ht]; exact hft)
    rw [hmemName t f (Nat.lt_of_lt_of_le ht hkp) hft]
    rw [hmemName t f (Nat.lt_of_lt_of_le ht hkp) hft] at h
    exact h
  · refine hoff n fun i f hfi hh => ?_
    rw [List.getElem?_take] at hfi
    split at hfi
    · obtain ⟨cv, bs, -, hff, -⟩ := hposF i f hfi
      rw [hh, hff.name, hff.fresh] at hn
      exact nomatch hn
    · exact nomatch hfi

end ConLeche.Model
