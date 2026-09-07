import ConLeche.Semantics.Direct.DeclDirectFix
import ConLeche.Semantics.Direct.DeclDirectEta

/-!
# The direct sum declaration keeps the η-families closed (task #175
sum-types, indexed)

Every store the direct sum install performs is a fresh cons
(`checkConstantVal`'s duplicate guard for the former and the recursor;
the constructors are checked at the former's environment and consed
in order under the distinct-names guard), and the one former it
stores carries the sum's capability record (`directSumCaps`, whose
`eta` is `false` — a sum is never structure-like), so
`EtaFamiliesClosed.cons_nonind` applies at every step.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectSumParts fueledOps checkDirectSumInd checkDirectSumCtors
  checkDirectSumRec consSumCtors directSumRules directSumCaps EtaFamiliesClosed)

/-- The constructors' conses keep the η-families closed: each name is
fresh at the environment it is consed onto — fresh at the former's
environment by its run, and distinct from the earlier constructors. -/
theorem consSumCtors_etaClosed {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EtaFamiliesClosed env →
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (ctorsA.map (·.1.name)).Nodup →
      EtaFamiliesClosed (consSumCtors nP ctorsA env)
  | [], _, hE, _, _ => hE
  | c :: cs, env, hE, hfresh, hnd => by
    simp only [consSumCtors]
    have hE' : EtaFamiliesClosed ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩ :=
      EtaFamiliesClosed.cons_nonind hE (hfresh c List.mem_cons_self)
        (fun _ _ heq => nomatch heq)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine consSumCtors_etaClosed hE' ?_ hnd.2
    intro c' hc'
    rw [ConLeche.Env.find?_cons]
    split
    · next heq =>
      exfalso
      apply hnd.1
      rw [List.mem_map]
      exact ⟨c', hc', heq.symm⟩
    · exact hfresh c' (List.mem_cons_of_mem _ hc')

/-- **The direct sum arm keeps the η-families closed.** -/
theorem declDirectSumRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectSumParts} (hE : EtaFamiliesClosed env)
    (h : DeclDirectSumRun μ F env p env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hnd, cvTa, env₁, p', ctorsA, cvRa, rhss, hInd, -, hCtors, hRec, rfl⟩ := h
  obtain ⟨cvT, s, hnameT, -, hcvT, hps, rfl, -⟩ := ConLeche.checkDirectSumInd_shape hInd
  obtain ⟨hfT, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hcvT
  have hE₁ : EtaFamiliesClosed ⟨.indInfo cvTa (directSumCaps p') :: env.consts⟩ :=
    EtaFamiliesClosed.cons_nonind hE (by
      have hn : cvTa.name = cvT.name := by
        obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
          ConLeche.checkConstantVal_inv hcvT
        rw [hTeq]
      show env.find? cvTa.name = none
      rw [hn]; exact hfT)
      (fun cv caps heq he => by
        obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact absurd he Bool.false_ne_true)
  obtain ⟨hlen, hall⟩ := ConLeche.checkDirectSumCtors_inv hCtors
  -- the constructors' names, annotated, are the block's
  have hnames : ctorsA.map (·.1.name) = p'.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p'.ctors.length := by simpa using h2
      obtain ⟨-, hrun⟩ := hall j (p'.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      obtain ⟨hccv, -, -⟩ := ConLeche.checkDirectSumCtor_shape hrun
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hCeq]
  have hE₂ : EtaFamiliesClosed
      (consSumCtors p'.nP ctorsA ⟨.indInfo cvTa (directSumCaps p') :: env.consts⟩) := by
    refine consSumCtors_etaClosed hE₁ ?_ (by rw [hnames, hps]; simpa using hnd)
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p'.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, hrun⟩ := hall j (p'.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hccv, -, -⟩ := ConLeche.checkDirectSumCtor_shape hrun
    obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hn : c.1.name = (p'.ctors[j]).1.name := by rw [hCeq]
    rw [hn]; exact hfC
  obtain ⟨hnR, -, -, -, -⟩ := ConLeche.checkDirectSumRec_facts hRec
  obtain ⟨cvRi, -, -, -, hcvR, -⟩ := ConLeche.checkDirectSumRec_shape hRec
  obtain ⟨hfR, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hcvR
  refine EtaFamiliesClosed.cons_nonind hE₂ ?_ (fun _ _ heq => nomatch heq)
  show (consSumCtors p'.nP ctorsA
    ⟨.indInfo cvTa (directSumCaps p') :: env.consts⟩).find? cvRa.name = none
  rw [hnR]; exact hfR

/-- **The direct recursive arm keeps the η-families closed** (task
#188): the same conses as the sum's, the recursor's from its own
stage. -/
theorem declDirectFixRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : ConLeche.DirectFixParts} (hE : EtaFamiliesClosed env)
    (h : DeclDirectFixRun μ F env p env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨-, -, hnd, cvTa, env₁, p₁, ctorsA, cvRa, rhss, -, -, -, hInd, -, -, -, hCtors, -, hRec,
    rfl⟩ := h
  obtain ⟨cvT, s, hTn, -, hcvT, rfl, rfl, -⟩ := ConLeche.checkDirectSumInd_shape hInd
  obtain ⟨hfT, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hcvT
  have hE₁ : EtaFamiliesClosed
      ⟨.indInfo cvTa (directSumCaps (p.toDirectSumParts.withSort s)) :: env.consts⟩ :=
    EtaFamiliesClosed.cons_nonind hE (by
      have hn : cvTa.name = p.cvT.name := by
        obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
          ConLeche.checkConstantVal_inv hcvT
        rw [hTeq]; exact hTn
      show env.find? cvTa.name = none
      rw [hn, ← hTn]; exact hfT)
      (fun cv caps heq he => by
        obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact absurd he Bool.false_ne_true)
  obtain ⟨hlen, hall⟩ := ConLeche.checkDirectSumCtors_inv hCtors
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      obtain ⟨hccv, -, -⟩ := ConLeche.checkDirectSumCtor_shape hrun
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hCeq]
  have hE₂ : EtaFamiliesClosed
      (consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (directSumCaps (p.toDirectSumParts.withSort s)) :: env.consts⟩) := by
    refine consSumCtors_etaClosed hE₁ ?_ (by rw [hnames]; exact hnd)
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hccv, -, -⟩ := ConLeche.checkDirectSumCtor_shape hrun
    obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hn : c.1.name = (p.ctors[j]).1.name := by rw [hCeq]
    rw [hn]; exact hfC
  obtain ⟨hnR, -, -, -, -⟩ := ConLeche.checkDirectFixRec_facts hRec
  obtain ⟨cvRi, -, -, -, hcvR, -⟩ := ConLeche.checkDirectFixRec_shape hRec
  obtain ⟨hfR, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hcvR
  refine EtaFamiliesClosed.cons_nonind hE₂ ?_ (fun _ _ heq => nomatch heq)
  show (consSumCtors p.nP ctorsA
    ⟨.indInfo cvTa (directSumCaps (p.toDirectSumParts.withSort s)) :: env.consts⟩).find? cvRa.name = none
  rw [hnR]; exact hfR

/-! ## The dispatch -/

/-- The `.indDecl` run dispatch keeps the η-families closed, by the
kernel's own case split. -/
theorem declIndRunDispatchEtaClosed {μ : CheckMode} {F : Nat}
    {env envI : Env} {block : List ConstantInfo}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndRunDispatch μ F env block envI) : EtaFamiliesClosed envI := by
  unfold DeclIndRunDispatch at h
  split at h
  · exact declDirectRun_etaClosed hE h
  · split at h
    · exact declDirectSumRun_etaClosed hE h
    · split at h
      · exact declDirectFixRun_etaClosed hE h
      · exact declIndEtaClosedRun hE h

end ConLeche.Semantics
