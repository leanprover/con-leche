import Lech.SetP.DirectFix.FixRuleKitP
import Lech.SetP.DirectFix.FixRecLawP

/-!
# The rule right-hand side's gradedness (task #188)

A recursive rule's right-hand side `λ p⃗ M m⃗ f⃗. m_j f⃗ ih⃗` mentions the
recursor (in the inductive hypotheses `ih_i = rec p⃗ M m⃗ e⃗_i f_i`), so
the kernel's inference run at the pre-recursor environment cannot
certify it as the sum route's; its `AnnotOkP` is proved from the
model: the minor lies in its ih-extended space (the K-frame package),
the fields fit, each inductive hypothesis is the recursor leaf — in
the recursor type's reading — applied along a spine fitting the
binder data (`FixPre.hspine`), landing in the ih domain
(`recConcAV_at`), and the ih tower folds (`ihSpL_spine`).  The
λ-tower's gradedness is the domain walk (`mkLamsC_ok2`) and its
validity the validity walk (`mkLamsC_validV`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The block split of a rule spine -/

/-- **The block split** of a spine fitting the recursor's binder data
below the indices: the parameters, the motive (in its reading), the
minors (in their ih-extended readings). -/
theorem fixBlock_split {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w b : Nat}
    {pps ips : List (Nat × Nat × AVExpr)} (hlenP : pps.length = nP)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {Fss Ess : List (List AVExpr)} {rss : List (List Bool)} {Eiss : List (List (List AVExpr))}
    (hminor : ∀ ρp : Nat → V, Sat2 V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j cd, cds[j]? = some cd → ∀ (M : V) (ms : List V), ms.length = j →
        interp2 V (consList ms (cons M ρp))
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
              (ihDomsI ρp M rss Eiss (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp [])
    (ρb : Nat → V) (as : List V)
    (hsp : SpineFit ρb ((pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
        (fixMinorsData m ψ nP b cds 1).map (·.2.2)) as) :
    ∃ (ps : List V) (M : V) (ms : List V),
      as = (ps ++ [M]) ++ ms ∧ ps.length = nP ∧ ms.length = n ∧
      Sat2 V ((pps.map (·.2.2)).reverse) (consList ps ρb) ∧
      M ∈ˢ interp2 V (consList ps ρb) (motiveAVI m T ψ nP nIdx elimL ips) ∧
      (∀ j, j < n → ms.getD j pt ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ (concI w (consList ps ρb) M (Ess.getD j []) j fs)
          (ihDomsI (consList ps ρb) M rss Eiss (fun j' => (Fss.getD j' []).length) j fs))
        (Fss.getD j []) (consList ps ρb) []) := by
  have hlenMD : (fixMinorsData m ψ nP b cds 1).length = n := by rw [fixMinorsData_length, hn]
  obtain ⟨c₁, ms, rfl, hsp₂, hspM⟩ := spineFit_append_inv hsp
  obtain ⟨ps, m₁, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₂
  obtain ⟨M, rfl, hM⟩ := spineFit_singleton hspMot
  have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hlenP]
  have hlenMs : ms.length = n := by rw [hspM.length_eq, List.length_map, hlenMD]
  have hρp : Sat2 V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρb) hspP
    rwa [List.append_nil] at this
  have hframe : consList (ps ++ [M]) ρb = cons M (consList ps ρb) := by
    rw [consList_append, consList_cons, consList_nil]
  rw [hframe] at hspM
  refine ⟨ps, M, ms, rfl, hlenPs, hlenMs, hρp, hM, ?_⟩
  intro j hj
  obtain ⟨cd, hcd⟩ : ∃ cd, cds[j]? = some cd := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hmem := FixKI.spineFit_getD_mem' hspM (l := j) (by rw [List.length_map, hlenMD]; exact hj)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsData_getElem?, hcd,
    Option.map_some, Option.getD_some] at hmem
  have hread := hminor (consList ps ρb) hρp j cd hcd M (ms.take j)
    (by rw [List.length_take, hlenMs]; omega)
  rw [hread] at hmem
  exact hmem

/-! ## One inductive hypothesis -/

/-- **An inductive hypothesis' facts** at the rule's leaf frame: the
recursor at the block, the field's index values and the field is
graded, valid, and lies in the ih domain — the motive at the index
values and the field. -/
theorem ihAppAV_facts {ℓ w u s nP nF nIdx n j i : Nat} {rds : List (Nat × Nat × AVExpr)}
    {Fss Ess : List (List AVExpr)} {Ids : List AVExpr} {rss : List (List Bool)}
    {Eiss : List (List (List AVExpr))}
    (h : FixPre V ℓ w u nP Fss Ess Fss Ids rss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx) (hjn : j < n)
    {Fs : List AVExpr} (hFsj : Fss[j]? = some Fs) (hlenFs : Fs.length = nF)
    {R : AVExpr} (hR : R = directFixRecAVI ℓ w nP Fss Ess Ids rss Eiss rds s)
    (hRcl : VExpr.bvarsBelow 0 R.erase)
    {ρ : Nat → V} {as₁ ms as₂ : List V} {M : V}
    (hlen₁ : as₁.length = nP) (hlenm : ms.length = n) (hlen₂ : as₂.length = nF)
    (hRok : AnnotOkP V (consList as₂ (consList ms (cons M (consList as₁ ρ)))) R)
    (hspB : SpineFit ρ ((rds.take (nP + 1 + n)).map (·.2.2)) ((as₁ ++ [M]) ++ ms))
    (hreal : ChainsRealI (fixFamI u w (consList as₁ ρ) Ids nIdx rss Eiss Fss Ess) u
      (consList as₁ ρ) Ids rss Eiss Fss Fss Ess)
    (hEisV : ∀ E ∈ (Eiss.getD j []).getD i [],
      AnnotValidV V (consList (as₂.take i) (consList as₁ ρ)) E)
    (hsp₂ : SpineFit (consList as₁ ρ) Fs as₂)
    (hi : i ∈ recIdx (rss.getD j []) nF) :
    AnnotOk2 V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (ihAppAV R nP n nF i ((Eiss.getD j []).getD i [])) ∧
      AnnotValidV V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (ihAppAV R nP n nF i ((Eiss.getD j []).getD i [])) ∧
      interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          (ihAppAV R nP n nF i ((Eiss.getD j []).getD i []))
        ∈ˢ SetTheory.app
          ((((Eiss.getD j []).getD i []).map (interp2 V (consList (as₂.take i) (consList as₁ ρ)))).foldl
            SetTheory.app M) (as₂.getD i pt) := by
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have hjF : j < Fss.length := by rw [hFss]; exact hjn
  have hFsD : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hlenIds : Ids.length = nIdx := hIds
  -- the real chain at the field
  have hc := chainRealI_at Fs Fs 0 [] as₂ rfl (by rw [← hFsD]; exact hreal.2.2.2.2 j hjF)
    (by simpa using hsp₂) i (by rw [hlenFs]; exact hik) (by rw [Nat.zero_add]; exact hri)
  rw [Nat.zero_add, List.nil_append] at hc
  obtain ⟨hEok, hvsp, heq⟩ := hc
  generalize hvals : ((Eiss.getD j []).getD i []).map (interp2 V (consList (as₂.take i) (consList as₁ ρ)))
    = vals at hvsp heq ⊢
  -- the field lies in the family at the index values
  have hfield : as₂.getD i pt ∈ˢ SetTheory.app
      (fixFamI u w (consList as₁ ρ) Ids nIdx rss Eiss Fss Ess) (tupW u vals) := by
    have := FixKI.spineFit_getD_mem' hsp₂ (by rw [hlenFs]; exact hik)
    rw [heq] at this
    exact this
  -- the spine fits the recursor's binder data
  have hshB : shiftE (Fss.length + 1) 0 (consList ((as₁ ++ [M]) ++ ms) ρ) = consList as₁ ρ := by
    rw [hFss, consList_append, consList_append, consList_cons, consList_nil, shiftE_minors hlenm]
  have hfit : SpineFit ρ (rds.map (·.2.2)) (((as₁ ++ [M]) ++ ms) ++ vals ++ [as₂.getD i pt]) := by
    refine h.hspine ρ ((as₁ ++ [M]) ++ ms) (by rw [hFss]; exact hspB) vals (as₂.getD i pt) ?_ ?_
    · rw [hshB]; exact hvsp
    · rw [hshB, hIds]; exact hfield
  -- the recursor leaf's membership and the chain
  have hRmem : interp2 V ρ R ∈ˢ interp2 V ρ (mkPisAV rds (recConcAV Fss.length Ids.length)) := by
    rw [hR]; exact directFixRecAVI_mem h ρ
  have hchain := appChainOk_of_mkPisAV' h.hz (fun hm as' hsp' => h.hconc0 hm ρ as' hsp') hRmem hfit
  have hval := mkPisAV_fold_mem h.hz (fun hm as' hsp' => h.hconc0 hm ρ as' hsp') hRmem hfit
  -- the argument readings
  have hlenVals : vals.length = nIdx := by rw [hvsp.length_eq, hIds]
  have hargs : ((recPrefixBvars nP n nF ++ ((Eiss.getD j []).getD i []).map (ihIdxAt nF (n + 1) i 0) ++
      [AVExpr.bvar (nF - 1 - i)]).map (interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
      = ((as₁ ++ [M]) ++ ms) ++ vals ++ [as₂.getD i pt] := by
    rw [List.map_append, List.map_append, map_recPrefixBvars_interp hlen₁ hlenm hlen₂, List.map_map]
    simp only [List.map_cons, List.map_nil, interp2_bvar]
    rw [consList_apply_lt' as₂ _ (by omega), show as₂.length - 1 - (nF - 1 - i) = i from by omega]
    congr 2
    rw [← hvals]
    apply List.map_congr_left
    intro E _
    simp only [Function.comp]
    have := interp_ihIdxAt (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms) (by omega)
      (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) E
    rw [consList_nil] at this
    exact this
  have hRi : interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ)))) R = interp2 V ρ R :=
    interp2_closed (V := V) hRcl _ ρ
  have hargsOk : ∀ a ∈ recPrefixBvars nP n nF ++ ((Eiss.getD j []).getD i []).map (ihIdxAt nF (n + 1) i 0) ++
      [AVExpr.bvar (nF - 1 - i)], AnnotOk2 V (consList as₂ (consList ms (cons M (consList as₁ ρ)))) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · unfold recPrefixBvars at ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
          · rw [List.mem_singleton] at ha; subst ha; trivial
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        have := (AnnotOk2_ihIdxAt (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms) (by omega)
          (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) E)
        rw [consList_nil] at this
        exact this.mpr (hEok E hE)
    · rw [List.mem_singleton] at ha; subst ha; trivial
  unfold ihAppAV
  obtain ⟨hok, hv⟩ := mkAppN_ok2_of_chain hRok.1 hargsOk (by rw [hargs, hRi]; exact hchain)
  refine ⟨hok, ?_, ?_⟩
  · -- validity
    refine mkAppN_validV hRok.2 fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · unfold recPrefixBvars at ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
          · rw [List.mem_singleton] at ha; subst ha; trivial
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        have := (AnnotValidV_ihIdxAt (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms)
          (by omega) (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) E)
        rw [consList_nil] at this
        exact this.mpr (hEisV E hE)
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · -- the value: in the conclusion at the spine
    rw [hv, hargs, hRi]
    have hM : consList ((as₁ ++ [M]) ++ ms) ρ n = M := by
      rw [consList_append, consList_append, consList_cons, consList_nil,
        show n = 0 + ms.length from by omega, consList_apply_add]
      rfl
    rw [consList_append, consList_append, consList_cons, consList_nil, hFss, hIds,
      recConcAV_at vals hlenVals, hM] at hval
    exact hval

end Lech.SetP
