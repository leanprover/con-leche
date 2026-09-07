import ConLeche.Verify.Direct.DirectRec
import ConLeche.Kernel.Direct.SumInstall

/-!
# The generated recursor at a constructor list (task #175 sum-types)

`ConLeche/Verify/Direct/DirectRec.lean`'s syntactic kit at one
constructor, generalized to the list the generators fold over
(`directMinorsPis`/`directMinorsLams`): the unfoldings of
`directRecTy`/`directRecRhs`, the minor premise's telescope under any
number of earlier binders (`instSeq_minorBody_at`: the motive is the
first extra, the earlier minors follow), the rule body under the
motive and all minors (`instSeq_ruleBody_at`: minor `j` is extra
`j + 1`), and the `.proj`-freeness of the generated forms.
-/

namespace ConLeche

open Expr

/-! ## The unfoldings -/

theorem directMinorTy_unfold {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} (h : directMinorTy C lps nP nF o pw cty = some mty) :
    ∃ (cbs : List (Expr × BinderMeta)) (crest0 : Expr),
      cty.stripPis nP = some (cbs, crest0) ∧
      Expr.replacePisPw pw nF (crest0.liftLooseBVars o 0)
        (.app (.bvar (nF + o - 1)) (directCtorSpineAt C lps o nP nF)) = some mty := by
  unfold directMinorTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, hmty⟩ := h
  exact ⟨q.1, q.2, hq, hmty⟩

theorem directMinorsPis_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {cs : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr}
    (h : directMinorsPis lps nP pw ((C, nF, cty) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTy C lps nP nF o pw cty = some mty ∧
      directMinorsPis lps nP pw cs (o + 1) body = some rest ∧
      mins = .forallE mty rest ⟨pw⟩ := by
  unfold directMinorsPis at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

theorem directMinorsLams_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {cs : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr}
    (h : directMinorsLams lps nP pw ((C, nF, cty) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTy C lps nP nF o pw cty = some mty ∧
      directMinorsLams lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam mty rest ⟨pw⟩ := by
  unfold directMinorsLams at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

theorem directMinorsPis_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsPis lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsPis, Option.some.injEq] at h
  exact h.symm

theorem directMinorsLams_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsLams lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsLams, Option.some.injEq] at h
  exact h.symm

/-- `directRecTy`, unfolded to the minors' telescope. -/
theorem directRecTy_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr)}
    (h : directRecTy T lps elim large nP tty ctors = some recTy) :
    ∃ minors : Expr,
      directMinorsPis lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1
        (.forallE (directFam T lps nP (ctors.length + 1))
          (.app (.bvar (ctors.length + 1)) (.bvar 0))
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some minors ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.forallE
          (directMotiveTy T lps nP (directElimLevel elim large)) minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some recTy := by
  unfold directRecTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨minors, hminors, hr⟩ := h
  exact ⟨minors, hminors, hr⟩

/-- `directRecRhs` at rule `j`, unfolded. -/
theorem directRecRhs_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr)} {j : Nat}
    (h : directRecRhs T lps elim large nP tty ctors j = some rhs) :
    ∃ (C : Name) (nF : Nat) (cty : Expr) (cbs : List (Expr × BinderMeta))
      (crest0 inner minors : Expr),
      ctors[j]? = some (C, nF, cty) ∧
      cty.stripPis nP = some (cbs, crest0) ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nF
        (crest0.liftLooseBVars (ctors.length + 1) 0)
        (Expr.mkAppN (.bvar (nF + ctors.length - 1 - j))
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k))) = some inner ∧
      directMinorsLams lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1 inner
        = some minors ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.lam
          (directMotiveTy T lps nP (directElimLevel elim large)) minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some rhs := by
  unfold directRecRhs at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    obtain ⟨C, nF, cty⟩ := c
    rw [hj] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, inner, hinner, minors, hminors, hr⟩ := h
    exact ⟨C, nF, cty, q.1, q.2, inner, minors, rfl, hq, hinner, hminors, hr⟩

/-! ## The closed spellings under extras -/

/-- The minor premise's conclusion `motive (C p⃗ f⃗)`, spelled under
`extras.length` binders (the motive first, then the earlier minors),
instantiated at the parameters and the extras and then at the
fields: the motive extra applied to the constructor at the
variables. -/
theorem instSeq_minorBody_at (tfvs extras xFvs : List Expr) {C : Name}
    {lps : List Name} {nP nF : Nat} {mfv : Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true)
    (hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true)
    (hhead : extras[0]? = some mfv) :
    instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
        (.app (.bvar (nF + extras.length - 1)) (directCtorSpineAt C lps extras.length nP nF)))
      = .app mfv (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)) := by
  have hpos : 0 < extras.length := by
    have := (List.getElem?_eq_some_iff.mp hhead).1
    omega
  have hcl : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlen : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
  have hclM : mfv.looseBVarsBounded 0 = true := hclE mfv (List.mem_of_getElem? hhead)
  unfold directCtorSpineAt
  rw [instSeq_app, instSeq_mkAppN, instSeq_app, instSeq_mkAppN,
    List.map_append, List.map_append]
  have hhead' : instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
      (.bvar (nF + extras.length - 1)) = mfv := by
    have := instSeq_bvar (tfvs ++ extras) (nP + extras.length - 1 + nF) (nF + extras.length - 1)
      hcl (by omega) (by rw [hlen]; omega)
    rw [show nP + extras.length - 1 + nF - (nF + extras.length - 1) = nP from by omega,
      List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
    exact (Option.some.inj this).symm
  rw [hhead', instSeq_eq_self _ _ hclM,
    instSeq_eq_self (e := Expr.const C (lps.map .param)) _ _ rfl,
    instSeq_eq_self (e := Expr.const C (lps.map .param)) _ _ rfl,
    show nP + extras.length - 1 + nF = extras.length + nF + nP - 1 from by omega,
    map_instSeq_directPsAt (tfvs ++ extras) (extras.length + nF) nP hcl (by omega),
    List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    show extras.length + nF + nP - 1 = nP + extras.length - 1 + nF from by omega,
    map_instSeq_fieldBvars_above (tfvs ++ extras) (nP + extras.length - 1 + nF) nF
      (by rw [hlen]; omega),
    map_instSeq_fieldBvars xFvs nF hclX hlenX]
  have htfvs : tfvs.map (fun x => instSeq xFvs (nF - 1) x) = tfvs := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map]
    exact instSeq_eq_self _ _ (hclT _ (List.getElem_mem h2))
  rw [htfvs]

/-- The rule's body `minor_j f⃗` (spelled under the motive and all
`n` minors), instantiated at the parameters, the motive and the
minors and then at the fields: extra `j + 1` applied to the field
variables. -/
theorem instSeq_ruleBody_at (tfvs extras xFvs : List Expr) {nP nF j : Nat} {mkfv : Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true)
    (hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true)
    (hj : extras[j + 1]? = some mkfv) :
    instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
        (Expr.mkAppN (.bvar (nF + (extras.length - 1) - 1 - j))
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k))))
      = Expr.mkAppN mkfv xFvs := by
  have hjlt : j + 1 < extras.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  have hcl : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlen : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
  have hclK : mkfv.looseBVarsBounded 0 = true := hclE mkfv (List.mem_of_getElem? hj)
  rw [instSeq_mkAppN, instSeq_mkAppN]
  have hhead : instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
      (.bvar (nF + (extras.length - 1) - 1 - j)) = mkfv := by
    have := instSeq_bvar (tfvs ++ extras) (nP + extras.length - 1 + nF)
      (nF + (extras.length - 1) - 1 - j) hcl (by omega) (by rw [hlen]; omega)
    rw [show nP + extras.length - 1 + nF - (nF + (extras.length - 1) - 1 - j) = nP + (j + 1)
        from by omega,
      List.getElem?_append_right (by omega), hlenT, Nat.add_sub_cancel_left, hj] at this
    exact (Option.some.inj this).symm
  rw [hhead, instSeq_eq_self _ _ hclK,
    map_instSeq_fieldBvars_above (tfvs ++ extras) (nP + extras.length - 1 + nF) nF
      (by rw [hlen]; omega),
    map_instSeq_fieldBvars xFvs nF hclX hlenX]

/-! ## No projection nodes -/

namespace Expr

variable {T : Name} {i : Nat}

theorem NoProjAt.directMinorTy {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} (h : directMinorTy C lps nP nF o pw cty = some mty)
    (hC : NoProjAt T i cty) : NoProjAt T i mty := by
  obtain ⟨cbs, crest0, hs, hm⟩ := directMinorTy_unfold h
  exact NoProjAt.replacePisPw nF hm (NoProjAt.stripPis nP hs hC).liftLooseBVars
    (by rw [noProjAt_app]; exact ⟨by simp, NoProjAt.directCtorSpineAt _ _ _ _ _⟩)

theorem NoProjAt.directMinorsPis {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {ctors : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr},
      directMinorsPis lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, NoProjAt T i c.2.2) → NoProjAt T i body → NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [directMinorsPis_nil h]; exact hb
  | (C, nF, cty) :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := directMinorsPis_cons h
    rw [noProjAt_forallE]
    exact ⟨NoProjAt.directMinorTy hmty (hcs _ List.mem_cons_self),
      NoProjAt.directMinorsPis hrest (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hb⟩

theorem NoProjAt.directMinorsLams {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {ctors : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr},
      directMinorsLams lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, NoProjAt T i c.2.2) → NoProjAt T i body → NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [directMinorsLams_nil h]; exact hb
  | (C, nF, cty) :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := directMinorsLams_cons h
    rw [noProjAt_lam]
    exact ⟨NoProjAt.directMinorTy hmty (hcs _ List.mem_cons_self),
      NoProjAt.directMinorsLams hrest (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hb⟩

/-- **The generated recursor type has no `.proj` node** the type
former's and the constructors' types do not have. -/
theorem NoProjAt.directRecTy_list {T' : Name} {lps : List Name} {elim : Name}
    {large : Bool} {nP : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr)}
    (h : ConLeche.directRecTy T' lps elim large nP tty ctors = some recTy)
    (hT : NoProjAt T i tty) (hC : ∀ c ∈ ctors, NoProjAt T i c.2.2) : NoProjAt T i recTy := by
  obtain ⟨minors, hmin, hr⟩ := directRecTy_unfold h
  have hmot : NoProjAt T i (directMotiveTy T' lps nP (directElimLevel elim large)) := by
    unfold ConLeche.directMotiveTy
    simp only [noProjAt_forallE, noProjAt_sort, and_true]
    exact NoProjAt.directFam _ _ _ _
  refine NoProjAt.replacePisPw nP hr hT ?_
  simp only [noProjAt_forallE]
  refine ⟨hmot, NoProjAt.directMinorsPis hmin hC ?_⟩
  simp only [noProjAt_forallE, noProjAt_app, noProjAt_bvar, and_true]
  exact NoProjAt.directFam _ _ _ _

/-- **The generated rules have no `.proj` node** the type former's and
the constructors' types do not have. -/
theorem NoProjAt.directRecRhs_list {T' : Name} {lps : List Name} {elim : Name}
    {large : Bool} {nP j : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr)}
    (h : ConLeche.directRecRhs T' lps elim large nP tty ctors j = some rhs)
    (hT : NoProjAt T i tty) (hC : ∀ c ∈ ctors, NoProjAt T i c.2.2) : NoProjAt T i rhs := by
  obtain ⟨C, nF, cty, cbs, crest0, inner, minors, hj, hs, hi, hmin, hr⟩ := directRecRhs_unfold h
  have hcrest : NoProjAt T i crest0 :=
    NoProjAt.stripPis nP hs (hC _ (List.mem_of_getElem? hj))
  have hinner : NoProjAt T i inner :=
    NoProjAt.pisToLamsPw nF hi hcrest.liftLooseBVars
      (NoProjAt.mkAppN (by simp) (fun a ha => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        simp))
  have hmot : NoProjAt T i (directMotiveTy T' lps nP (directElimLevel elim large)) := by
    unfold ConLeche.directMotiveTy
    simp only [noProjAt_forallE, noProjAt_sort, and_true]
    exact NoProjAt.directFam _ _ _ _
  refine NoProjAt.pisToLamsPw nP hr hT ?_
  simp only [noProjAt_lam]
  exact ⟨hmot, NoProjAt.directMinorsLams hmin hC hinner⟩

end Expr

end ConLeche

namespace ConLeche

open Expr

/-! ## The elimination restriction's readout -/

/-- `Level.isNeverZero` is sound: such a level evaluates to a nonzero
number at every assignment. -/
theorem Level.isNeverZero_sound (φ : Name → Nat) :
    ∀ l : Level, l.isNeverZero = true → Level.eval φ l ≠ 0
  | .zero, h => by simp [Level.isNeverZero] at h
  | .param _, h => by simp [Level.isNeverZero] at h
  | .succ _, _ => by simp [Level.eval]
  | .max l r, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true] at h
    simp only [Level.eval]
    rcases h with h | h
    · have := Level.isNeverZero_sound φ l h; omega
    · have := Level.isNeverZero_sound φ r h; omega
  | .imax l r, h => by
    simp only [Level.isNeverZero] at h
    have := Level.isNeverZero_sound φ r h
    simp only [Level.eval, if_neg this]
    omega

/-! ## The stored rules, positionally -/

/-- A stored rule is constructor `j`'s rule at right-hand side `j`. -/
theorem directSumRules_getElem? {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ directSumRules nP mI rP recTy ctorsA rhss →
      ∃ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        ctorsA[j]? = some cA ∧ rhss[j]? = some rhs ∧
        r = ⟨cA.1.name, cA.2, nP,
          if Expr.recRulePlain recTy mI rP nP then .plain else .inert, rhs⟩
  | [], _, r, h => by simp [directSumRules] at h
  | _ :: _, [], r, h => by simp [directSumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [directSumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, c, rhs, rfl, rfl, rfl⟩
    · obtain ⟨j, cA, rhs', hc, hr, rfl⟩ := directSumRules_getElem? h
      exact ⟨j + 1, cA, rhs', by simpa using hc, by simpa using hr, rfl⟩

/-! ## The indexed generators, unfolded (task #175 indexed families) -/

theorem directMinorTyI_unfold {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} (h : directMinorTyI C lps nP nF o pw cty = some mty) :
    ∃ (cbs fbs : List (Expr × BinderMeta)) (crest0 res : Expr),
      cty.stripPis nP = some (cbs, crest0) ∧
      crest0.stripPis nF = some (fbs, res) ∧
      Expr.replacePisPw pw nF (crest0.liftLooseBVars o 0)
        (Expr.mkAppN (.bvar (nF + o - 1))
          ((res.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
            [directCtorSpineAt C lps o nP nF])) = some mty := by
  unfold directMinorTyI at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, r, hr, hmty⟩ := h
  exact ⟨q.1, r.1, q.2, r.2, hq, hr, hmty⟩

theorem directMinorsPisI_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {cs : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr}
    (h : directMinorsPisI lps nP pw ((C, nF, cty) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTyI C lps nP nF o pw cty = some mty ∧
      directMinorsPisI lps nP pw cs (o + 1) body = some rest ∧
      mins = .forallE mty rest ⟨pw⟩ := by
  unfold directMinorsPisI at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

theorem directMinorsLamsI_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {cs : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr}
    (h : directMinorsLamsI lps nP pw ((C, nF, cty) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTyI C lps nP nF o pw cty = some mty ∧
      directMinorsLamsI lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam mty rest ⟨pw⟩ := by
  unfold directMinorsLamsI at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

theorem directMinorsPisI_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsPisI lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsPisI, Option.some.injEq] at h
  exact h.symm

theorem directMinorsLamsI_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsLamsI lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsLamsI, Option.some.injEq] at h
  exact h.symm

/-- `directRecTyI`, unfolded to its five steps. -/
theorem directRecTyI_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr)}
    (h : directRecTyI T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ (tbs : List (Expr × BinderMeta)) (itele motiveTy major minors : Expr),
      tty.stripPis nP = some (tbs, itele) ∧
      directMotiveTyI T lps nP nIdx (directElimLevel elim large) itele = some motiveTy ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nIdx
        (itele.liftLooseBVars (ctors.length + 1) 0)
        (.forallE (directFamI T lps nP nIdx (ctors.length + 1) 0)
          (Expr.mkAppN (.bvar (nIdx + ctors.length + 1)) (directPsAt 1 nIdx ++ [.bvar 0]))
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some major ∧
      directMinorsPisI lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1 major
        = some minors ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.forallE motiveTy minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some recTy := by
  unfold directRecTyI at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, motiveTy, hmot, major, hmaj, minors, hmin, hr⟩ := h
  exact ⟨q.1, q.2, motiveTy, major, minors, hq, hmot, hmaj, hmin, hr⟩

/-- `directRecRhsI` at rule `j`, unfolded. -/
theorem directRecRhsI_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr)} {j : Nat}
    (h : directRecRhsI T lps elim large nP nIdx tty ctors j = some rhs) :
    ∃ (C : Name) (nF : Nat) (cty : Expr) (tbs cbs : List (Expr × BinderMeta))
      (itele motiveTy crest0 inner minors : Expr),
      ctors[j]? = some (C, nF, cty) ∧
      tty.stripPis nP = some (tbs, itele) ∧
      directMotiveTyI T lps nP nIdx (directElimLevel elim large) itele = some motiveTy ∧
      cty.stripPis nP = some (cbs, crest0) ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nF
        (crest0.liftLooseBVars (ctors.length + 1) 0)
        (Expr.mkAppN (.bvar (nF + ctors.length - 1 - j))
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k))) = some inner ∧
      directMinorsLamsI lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1 inner
        = some minors ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.lam motiveTy minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some rhs := by
  unfold directRecRhsI at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    obtain ⟨C, nF, cty⟩ := c
    rw [hj] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tq, htq, motiveTy, hmot, q, hq, inner, hinner, minors, hminors, hr⟩ := h
    exact ⟨C, nF, cty, tq.1, q.1, tq.2, motiveTy, q.2, inner, minors, rfl, htq, hmot, hq,
      hinner, hminors, hr⟩

/-! ## Instantiation under a mid-cutoff lift -/

/-- **Lifting above a cutoff and instantiating through the lifted
region**: `q` mentions its `c` innermost binders and the `pre.length`
above them; lifting `rest.length` at cutoff `c` and instantiating the
prefix and the rest above the innermost `c` is instantiating the
prefix alone (`instSeq_liftLooseBVars_prefix` at `c = 0`). -/
theorem instSeq_liftLooseBVars_mid :
    ∀ (pre rest : List Expr) {q : Expr} {c : Nat},
      (∀ a ∈ pre, a.looseBVarsBounded 0 = true) →
      q.looseBVarsBounded (pre.length + c) = true →
      instSeq (pre ++ rest) (pre.length + rest.length + c - 1)
        (q.liftLooseBVars rest.length c) =
      instSeq pre (pre.length + c - 1) q := by
  intro pre
  induction pre with
  | nil =>
    intro rest q c _ hq
    have hq0 : q.looseBVarsBounded c = true := by simpa using hq
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    rw [liftLooseBVars_eq_self hq0]
    show instSeq rest (rest.length + c - 1) q = q
    rcases Nat.eq_zero_or_pos (rest.length + c) with h0 | hpos
    · have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    · exact instSeq_eq_self_of_bounded rest _ hq0 (by omega)
  | cons a pre' ih =>
    intro rest q c hpre hq
    have ha : a.looseBVarsBounded 0 = true := hpre a List.mem_cons_self
    have hq' : (q.instantiate1 a (pre'.length + c)).looseBVarsBounded
        (pre'.length + c) = true :=
      looseBVarsBounded_instantiate1_gen ha (by simpa [Nat.add_right_comm] using hq)
    show instSeq (pre' ++ rest) ((a :: pre').length + rest.length + c - 1 - 1)
        ((q.liftLooseBVars rest.length c).instantiate1 a
          ((a :: pre').length + rest.length + c - 1)) =
      instSeq pre' ((a :: pre').length + c - 1 - 1)
        (q.instantiate1 a ((a :: pre').length + c - 1))
    rw [show (a :: pre').length + rest.length + c - 1 =
        (pre'.length + c) + rest.length from by simp; omega,
      show (a :: pre').length + c - 1 = pre'.length + c from by simp,
      show (pre'.length + c) + rest.length - 1 = pre'.length + rest.length + c - 1 from by omega,
      liftLooseBVars_instantiate1 ha (by omega)]
    exact ih rest (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hq'

/-- The minor premise's conclusion at an indexed family,
`motive e⃗ (C p⃗ f⃗)` spelled under `extras.length` binders, instantiated
at the parameters, the extras and the fields: the motive extra at the
index expressions (instantiated at the parameters and the fields
alone) and the constructor at the variables. -/
theorem instSeq_minorBodyI_at (tfvs extras xFvs : List Expr) {C : Name}
    {lps : List Name} {nP nF : Nat} {mfv : Expr} {es : List Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true)
    (hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true)
    (hhead : extras[0]? = some mfv)
    (hes : ∀ e ∈ es, e.looseBVarsBounded (nP + nF) = true) :
    instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF)
        (Expr.mkAppN (.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++ [directCtorSpineAt C lps extras.length nP nF])))
      = Expr.mkAppN mfv
          (es.map (fun e => instSeq xFvs (nF - 1) (instSeq tfvs (nP + nF - 1) e)) ++
            [Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)]) := by
  have hpos : 0 < extras.length := by
    have := (List.getElem?_eq_some_iff.mp hhead).1
    omega
  have hsp := instSeq_minorBody_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead
    (C := C) (lps := lps)
  simp only [instSeq_app] at hsp
  obtain ⟨hhd, hspine⟩ := Expr.app.inj hsp
  rw [Expr.mkAppN_append_one, Expr.mkAppN_append_one]
  simp only [instSeq_app, instSeq_mkAppN, hhd, hspine, List.map_map]
  congr 2
  apply List.map_congr_left
  intro e he
  simp only [Function.comp]
  congr 1
  have := instSeq_liftLooseBVars_mid tfvs extras (c := nF) hclT (by rw [hlenT]; exact hes e he)
  rw [hlenT, show nP + extras.length + nF - 1 = nP + extras.length - 1 + nF from by omega] at this
  exact this

end ConLeche
