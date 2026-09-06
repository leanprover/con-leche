import Setlec.Verify.Direct.DirectRec

/-!
# The generated recursor at a constructor list (task #175 sum-types)

`Setlec/Verify/Direct/DirectRec.lean`'s syntactic kit at one
constructor, generalized to the list the generators fold over
(`directMinorsPis`/`directMinorsLams`): the unfoldings of
`directRecTy`/`directRecRhs`, the minor premise's telescope under any
number of earlier binders (`instSeq_minorBody_at`: the motive is the
first extra, the earlier minors follow), the rule body under the
motive and all minors (`instSeq_ruleBody_at`: minor `j` is extra
`j + 1`), and the `.proj`-freeness of the generated forms.
-/

namespace Setlec

open Expr

/-! ## The unfoldings -/

theorem directMinorTy_unfold {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} (h : directMinorTy C lps nP nF o pw cty = some mty) :
    ∃ (cbs : List (Name × Expr × BinderMeta)) (crest0 : Expr),
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
      mins = .forallE (Name.lastStr C) mty rest ⟨.default, pw⟩ := by
  unfold directMinorsPis at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

theorem directMinorsLams_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {cs : List (Name × Nat × Expr)} {o : Nat} {body mins : Expr}
    (h : directMinorsLams lps nP pw ((C, nF, cty) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTy C lps nP nF o pw cty = some mty ∧
      directMinorsLams lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam (Name.lastStr C) mty rest ⟨.default, pw⟩ := by
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
        (.forallE (.str .anonymous "t") (directFam T lps nP (ctors.length + 1))
          (.app (.bvar (ctors.length + 1)) (.bvar 0))
          ⟨.default, Level.zeronessOf (directElimLevel elim large)⟩) = some minors ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.forallE (.str .anonymous "motive")
          (directMotiveTy T lps nP (directElimLevel elim large)) minors
          ⟨.default, Level.zeronessOf (directElimLevel elim large)⟩) = some recTy := by
  unfold directRecTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨minors, hminors, hr⟩ := h
  exact ⟨minors, hminors, hr⟩

/-- `directRecRhs` at rule `j`, unfolded. -/
theorem directRecRhs_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr)} {j : Nat}
    (h : directRecRhs T lps elim large nP tty ctors j = some rhs) :
    ∃ (C : Name) (nF : Nat) (cty : Expr) (cbs : List (Name × Expr × BinderMeta))
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
        (.lam (.str .anonymous "motive")
          (directMotiveTy T lps nP (directElimLevel elim large)) minors
          ⟨.default, Level.zeronessOf (directElimLevel elim large)⟩) = some rhs := by
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
    (h : Setlec.directRecTy T' lps elim large nP tty ctors = some recTy)
    (hT : NoProjAt T i tty) (hC : ∀ c ∈ ctors, NoProjAt T i c.2.2) : NoProjAt T i recTy := by
  obtain ⟨minors, hmin, hr⟩ := directRecTy_unfold h
  have hmot : NoProjAt T i (directMotiveTy T' lps nP (directElimLevel elim large)) := by
    unfold Setlec.directMotiveTy
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
    (h : Setlec.directRecRhs T' lps elim large nP tty ctors j = some rhs)
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
    unfold Setlec.directMotiveTy
    simp only [noProjAt_forallE, noProjAt_sort, and_true]
    exact NoProjAt.directFam _ _ _ _
  refine NoProjAt.pisToLamsPw nP hr hT ?_
  simp only [noProjAt_lam]
  exact ⟨hmot, NoProjAt.directMinorsLams hmin hC hinner⟩

end Expr

end Setlec
