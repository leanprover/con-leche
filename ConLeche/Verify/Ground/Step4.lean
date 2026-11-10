module

public import ConLeche.Verify.Ground.Run
import ConLeche.Verify.Ground.Step0

public section

/-!
# Mode 4: pushing a spine's arguments (task #423 soundness, layer (c))

Each argument becomes an argument frame whose cell's origin is the
argument's term under the spine's environment: an environment cell (a
variable), a new value cell (a λ, a `Nat` literal), the neutral cell, a
constant's or a closed term's slot cell, or a new thunk.  When none is left,
the head is evaluated.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-! ## Spines -/

theorem mkAppN_bounded {d : Nat} : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).looseBVarsBounded d = true ↔
      f.looseBVarsBounded d = true ∧ ∀ a ∈ as, a.looseBVarsBounded d = true
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, mkAppN_bounded as]
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩⟩

theorem mkAppN_take_succ (f : Expr) (ss : List Expr) {j : Nat} (hj : j < ss.length) :
    Expr.mkAppN f (ss.take (j + 1)) = .app (Expr.mkAppN f (ss.take j)) ss[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some]
  rw [show ∀ (l : List Expr) (a : Expr), Expr.mkAppN f (l ++ [a]) = .app (Expr.mkAppN f l) a from
    fun l a => by induction l generalizing f <;> simp_all [Expr.mkAppN]]

theorem DenArgs.get {P : G4Prog} : ∀ {o p n : Nat} {ss : List Expr}, DenArgs P o p n ss →
    ∀ j (hj : j < ss.length), ∃ a, P.code[p + j]? = some a ∧ Den P a ss[j]
  | _, _, _, _, .cons h₁ _ hd _, 0, _ => ⟨_, by simpa using h₁, hd⟩
  | _, p, _, _, .cons _ _ _ hr, j + 1, hj => by
    obtain ⟨a, h₁, hd⟩ := DenArgs.get hr j (by simpa using hj)
    exact ⟨a, by rw [show p + (j + 1) = p + 1 + j by omega]; exact h₁, hd⟩

/-- A spine's claim under an agreeing origin assignment, and weakened. -/
theorem SpineAt.mono {P : G4Prog} {ev : Array Nat} {oc oc' : Nat → Expr} {N pc env x : Nat}
    {k k' : Expr → Prop} (h : SpineAt P ev oc pc env x k) (hr : EvRef ev N) (ha : Agree oc oc' N)
    (hk : ∀ u, k u → k' u) : SpineAt P ev oc' pc env x k' := by
  obtain ⟨hd, n, sh, ss, cs, h₀, h₁, h₂, hlt, hh, has, he, hb, hx, hk₀⟩ := h
  refine ⟨hd, n, sh, ss, cs, h₀, h₁, h₂, hlt, hh, has, he, hb, hx, ?_⟩
  rw [← map_agree ha (EnvL.mem_lt hr he)]; exact hk _ hk₀

/-- **The next argument** of a spine: its node, its term, and the claim
one argument further down once a frame for a cell with that origin is
pushed. -/
theorem SpineAt.next {env : Env} {t₀ : Expr} {P : G4Prog} {ev argA : Array Nat} {oc : Nat → Expr}
    {pc e j : Nat} {fl : List Fr} (h : SpineAt P ev oc pc e (j + 1) (K env t₀ P argA oc fl)) :
    ∃ ao sa cs, P.code[pc + 3 + j]? = some ao ∧ Den P ao sa ∧ EnvL ev e cs ∧
      sa.looseBVarsBounded cs.length = true ∧ ∀ c, oc c = sa.instantiateList (cs.map oc) →
      SpineAt P ev oc pc e j (K env t₀ P argA oc (.arg c :: fl)) := by
  obtain ⟨hd, n, sh, ss, cs, h₀, h₁, h₂, hlt, hh, has, he, hb, hx, hk⟩ := h
  have hl := has.length
  obtain ⟨ao, hao, hda⟩ := has.get j (by omega)
  refine ⟨ao, _, cs, hao, hda, he, (mkAppN_bounded ss sh).mp hb |>.2 _ (List.getElem_mem _),
    fun c hc => ⟨hd, n, sh, ss, cs, h₀, h₁, h₂, hlt, hh, has, he, hb, by omega, ?_⟩⟩
  show K env t₀ P argA oc fl (.app _ (oc c))
  rw [mkAppN_take_succ sh ss (by omega)] at hk
  rw [hc]; simpa [Expr.instantiateList] using hk

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- **No argument left**: the head is evaluated. -/
theorem step_args_done (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = 0) :
    MInv env t₀ oc { s with mode := 0, pc := s.P.code[s.pc + 1]!, x := 0 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hd, n, sh, ss, cs, h₀, h₁, h₂, hlt, hh, has, he, hb, -, hk⟩ := hf
  rw [hx] at hk
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  show ∃ u, NodeTerm s.P s.ev oc _ s.env u ∧ _
  rw [get!_of_some h₁]
  exact ⟨_, ⟨sh, cs, hh, he, ((mkAppN_bounded ss sh).mp hb).1, rfl⟩, by simpa [Expr.mkAppN] using hk⟩

/-- **An argument frame pushed** (the common tail of every argument kind):
the store after the step, the frame's cell allocated, its origin the
argument's term. -/
theorem step_args_frame {s' : MS} {oc' : Nat → Expr} {j c : Nat} (h : MInv env t₀ oc s fl)
    (hm : s.mode = 4) (hx : s.x = j + 1) (hst : SInv env oc' s') (ha : Agree oc oc' s.N)
    (hN : s.N ≤ s'.N) (hP : s'.P = s.P) (hev : s'.ev = s.ev) (harg : s'.argA = s.argA)
    (hfs : s'.fs = s.fs.push (g4Tag c 1)) (hm' : s'.mode = 4) (hpc : s'.pc = s.pc)
    (henv : s'.env = s.env) (hx' : s'.x = j) (hc : c < s'.N)
    (horig : ∀ ao sa cs, s.P.code[s.pc + 3 + j]? = some ao → Den s.P ao sa → EnvL s.ev s.env cs →
      sa.looseBVarsBounded cs.length = true → oc' c = sa.instantiateList (cs.map oc')) :
    MInv env t₀ oc' s' (.arg c :: fl) := by
  have hf := h.focus
  simp only [Focus, hm, hx] at hf
  have hf' := hf.mono h.store.evRef ha (fun u hu =>
    K.move h.store.argRef ha (ExtR.refl _) (Pre.refl _) h.frames hu)
  obtain ⟨ao, sa, cs, hao, hda, he, hb, hnext⟩ := hf'.next
  refine ⟨hst, by rw [hfs]; exact FS.pushArg h.stack c, ?_, ?_⟩
  · intro f hf''
    rcases List.mem_cons.mp hf'' with rfl | hf''
    · exact hc
    · rw [hP, harg]; exact (h.frames f hf'').grow (ExtR.refl _) (Pre.refl _) hN
  · show Focus env t₀ oc' s' _
    unfold Focus; rw [hm', hP, hev, hpc, henv, hx', harg]
    exact hnext c (horig ao sa cs hao hda he hb)

/-- The spine's witnesses are unique. -/
theorem spine_wit_unique {P : G4Prog} {ev : Array Nat} {p e ao ao' : Nat} {sa sa' : Expr}
    {cs cs' : List Nat} (h₁ : P.code[p]? = some ao) (h₁' : P.code[p]? = some ao') (h₂ : Den P ao sa)
    (h₂' : Den P ao' sa') (h₃ : EnvL ev e cs) (h₃' : EnvL ev e cs') : sa' = sa ∧ cs' = cs := by
  rw [h₁] at h₁'; obtain rfl := Option.some.inj h₁'
  exact ⟨Den.unique h₂' h₂, EnvL.unique h₃' h₃⟩

/-- **An argument frame for an allocated cell** whose origin is the argument's term. -/
theorem step_args_old {s' : MS} {j c ao : Nat} {sa : Expr} {cs : List Nat} (h : MInv env t₀ oc s fl)
    (hm : s.mode = 4) (hx : s.x = j + 1) (hao : s.P.code[s.pc + 3 + j]? = some ao)
    (hda : Den s.P ao sa) (he : EnvL s.ev s.env cs)
    (hs' : s' = { s with fs := s.fs.push (g4Tag c 1), x := j }) (hc : c < s.N)
    (horig : oc c = sa.instantiateList (cs.map oc)) : MInv env t₀ oc s' (.arg c :: fl) := by
  subst hs'
  refine step_args_frame h hm hx (h.store.same rfl rfl rfl rfl rfl rfl rfl) (Agree.refl _ _)
    (Nat.le_refl _) rfl rfl rfl rfl hm rfl rfl rfl hc (fun ao' sa' cs' hao' hda' he' _ => ?_)
  obtain ⟨rfl, rfl⟩ := spine_wit_unique hao hao' hda hda' he he'
  exact horig

/-- **An argument frame for a new cell** (`[w0, w1, w2, 0]`) whose origin is
the argument's term, the slots unchanged or one slot set to it. -/
theorem step_args_new {s' : MS} {j ao w0 w1 w2 : Nat} {sa : Expr} {cs : List Nat}
    (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]? = some ao) (hda : Den s.P ao sa) (he : EnvL s.ev s.env cs)
    (hb : sa.looseBVarsBounded cs.length = true)
    (hP : s'.P = s.P) (hcel : s'.cel = (((s.cel.push w0).push w1).push w2).push 0)
    (hval : Pre s.val s'.val) (hvs : s'.val.size % 4 = 0) (hev : s'.ev = s.ev) (harg : s'.argA = s.argA)
    (hsl : s'.slots = s.slots ∨ ∃ sl, s'.slots = g4SlotSet s.slots sl (s.P.epBase + s.N) ∧
      Owns s.P sl (sa.instantiateList (cs.map oc)))
    (hmem : s'.mem = s.mem) (hfs : s'.fs = s.fs.push (g4Tag s.N 1)) (hm' : s'.mode = 4)
    (hpc : s'.pc = s.pc) (henv : s'.env = s.env) (hx' : s'.x = j)
    (hok : CellOK env s.P s'.val s.ev s.argA (ocExt oc s.N (sa.instantiateList (cs.map oc))) s'.cel s.N)
    (hv : 2 ≤ w0 → w0 - 2 < s'.val.size / 4) :
    MInv env t₀ (ocExt oc s.N (sa.instantiateList (cs.map oc))) s' (.arg s.N :: fl) := by
  have htc : (sa.instantiateList (cs.map oc)).looseBVarsBounded 0 = true :=
    bounded _ sa 0 (h.store.allClosed he) (by simpa using hb)
  have ha := Agree.ext oc s.N (sa.instantiateList (cs.map oc))
  obtain ⟨hcsz, -, -, -, -⟩ := push4_spec s.cel w0 w1 w2 0 h.store.celSz
  have hN : s'.N = s.N + 1 := by simp only [MS.N]; rw [hcel, hcsz]; have := h.store.celSz; omega
  have hst₀ : SInv env (ocExt oc s.N (sa.instantiateList (cs.map oc))) { s' with slots := s.slots } :=
    h.store.alloc (s' := { s' with slots := s.slots }) hP hcel hval hvs (by rw [hev]; exact Pre.refl _)
      (by rw [hev]; exact h.store.evSz) harg rfl hmem
      (by rw [hev]; exact h.store.evRef.mono (Nat.le_succ _)) htc (by show CellOK env s.P s'.val s'.ev _ _ s'.cel s.N; rw [hev]; exact hok) hv
  have hst : SInv env (ocExt oc s.N (sa.instantiateList (cs.map oc))) s' := by
    rcases hsl with hsl | ⟨sl, hsl, how⟩
    · exact hst₀.same rfl rfl rfl rfl rfl hsl rfl
    · have hep : s.P.epBase + s.N > s.P.epBase := by have := h.store.cell0; omega
      refine (hst₀.withSlots (slots' := s'.slots) (fun sl' hne => ?_)).same rfl rfl rfl rfl rfl rfl rfl
      show _ < s'.N ∧ Owns s'.P sl' _
      rw [hP] at hne ⊢; rw [hsl, slotGet_set] at hne ⊢; rw [hN]
      by_cases hq : sl' = sl
      · subst hq
        rw [ite_eq_left rfl, ite_eq_left hep, Nat.add_sub_cancel_left, ocExt_self]
        exact ⟨Nat.lt_succ_self _, how⟩
      · rw [ite_eq_right hq] at hne ⊢
        obtain ⟨hlt, how'⟩ := h.store.slotsOK sl' hne
        rw [← ha _ hlt]
        exact ⟨Nat.lt_succ_of_lt hlt, how'⟩
  refine step_args_frame h hm hx hst ha (by omega) hP hev harg hfs hm' hpc henv hx' (by omega)
    (fun ao' sa' cs' hao' hda' he' _ => ?_)
  obtain ⟨rfl, rfl⟩ := spine_wit_unique hao hao' hda hda' he he'
  rw [ocExt_self, ← map_agree ha (EnvL.mem_lt h.store.evRef he)]

/-- The next argument's witnesses, its node `ao` read off the code. -/
theorem MInv.argWit {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) :
    ∃ sa cs, s.P.code[s.pc + 3 + j]? = some ao ∧ Den s.P ao sa ∧ EnvL s.ev s.env cs ∧
      sa.looseBVarsBounded cs.length = true := by
  have hf := h.focus
  simp only [Focus, hm, hx] at hf
  obtain ⟨ao', sa, cs, hao', hda, he, hb, -⟩ := hf.next
  rw [get!_of_some hao'] at hao; subst hao
  exact ⟨sa, cs, hao', hda, he, hb⟩

/-- **A variable argument**: its environment cell. -/
theorem step_arg_var {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 0) :
    MInv env t₀ oc { s with
      fs := s.fs.push (g4Tag (g4EnvGet s.ev s.env s.P.code[ao + 1]!) 1), x := j }
      (.arg (g4EnvGet s.ev s.env s.P.code[ao + 1]!) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨i, hi, rfl⟩ := hda.inv0 (by rw [some_of_lt hda.lt_size, ht])
  have hil : i < cs.length := by simpa [Expr.looseBVarsBounded] using hb
  rw [get!_of_some hi, EnvL.get he i hil]
  have hgd : cs.getD i 0 = cs[i] := by simp [List.getElem?_eq_getElem hil]
  have hmem : cs.getD i 0 ∈ cs := by rw [hgd]; exact List.getElem_mem hil
  refine step_args_old h hm hx hao' hda he rfl (EnvL.mem_lt h.store.evRef he _ hmem) ?_
  rw [lookup (h.store.allClosed he) (by simpa using hil)]; simp [List.getElem?_eq_getElem hil]

/-- **A neutral argument**: cell 0. -/
theorem step_arg_neutral {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 8) :
    MInv env t₀ oc { s with fs := s.fs.push 1, x := j } (.arg 0 :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain rfl := hda.inv8 (by rw [some_of_lt hda.lt_size, ht])
  refine step_args_old h hm hx hao' hda he (by rw [show g4Tag 0 1 = 1 by rw [g4Tag_eq]])
    h.store.cell0 ?_
  rw [h.store.oc0, Expr.instantiateList_eq_self (by simp [bot, Expr.looseBVarsBounded])]

/-- **A thunk argument** (a spine, a `let`, a string, a projection): a new
thunk of the argument's node under the spine's environment. -/
theorem step_arg_thunk {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push 0).push ao).push s.env).push 0
      fs := s.fs.push (g4Tag (s.cel.size >>> 2) 1)
      x := j } (.arg (s.cel.size >>> 2) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2]
  obtain ⟨-, hc0, hc1, hc2, -⟩ := push4_spec s.cel 0 ao s.env 0 h.store.celSz
  have ha := Agree.ext oc s.N (sa.instantiateList (cs.map oc))
  refine ⟨_, step_args_new h hm hx hao' hda he hb rfl rfl (Pre.refl _) h.store.valSz rfl rfl (.inl rfl)
    rfl rfl hm rfl rfl rfl ?_ (by omega)⟩
  show CellOK env s.P s.val s.ev s.argA _ _ (s.cel.size / 4)
  unfold CellOK; rw [hc0, hc1, hc2]
  exact ⟨sa, cs, hda, he, hb, by
    rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, ← map_agree ha (EnvL.mem_lt h.store.evRef he)]⟩

/-- **A λ argument**: a new closure value and its value cell. -/
theorem step_arg_lam {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 2) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push ((s.val.size >>> 2) + 2)).push ao).push s.env).push 0
      val := (((s.val.push 0).push ao).push s.env).push 0
      fs := s.fs.push (g4Tag (s.cel.size >>> 2) 1)
      x := j } (.arg (s.cel.size >>> 2) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  have hshr2' : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, hshr2']
  obtain ⟨-, hc0, -, -, -⟩ := push4_spec s.cel (s.val.size / 4 + 2) ao s.env 0 h.store.celSz
  obtain ⟨hvsz, hv0, hv1, hv2, hvp⟩ := push4_spec s.val 0 ao s.env 0 h.store.valSz
  have ha := Agree.ext oc s.N (sa.instantiateList (cs.map oc))
  refine ⟨_, step_args_new h hm hx hao' hda he hb rfl rfl hvp (by rw [hvsz]; have := h.store.valSz; omega)
    rfl rfl (.inl rfl) rfl rfl hm rfl rfl rfl ?_ (fun _ => by rw [hvsz]; omega)⟩
  show CellOK env s.P _ s.ev s.argA _ _ (s.cel.size / 4)
  unfold CellOK; rw [hc0]
  refine ⟨sa.instantiateList (cs.map (ocExt oc s.N (sa.instantiateList (cs.map oc)))), .closure hv0
    (by rw [hv1]; exact ht) ?_, ?_⟩
  · rw [hv1, hv2]; exact ⟨sa, cs, hda, he, hb, rfl⟩
  · rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, ← map_agree ha (EnvL.mem_lt h.store.evRef he)]
    exact .refl

/-- **A `Nat` literal argument**: a new literal value and its value cell. -/
theorem step_arg_nat {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4) (hx : s.x = j + 1)
    (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 5) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push ((s.val.size >>> 2) + 2)).push ao).push 0).push 0
      val := (((s.val.push 2).push s.P.code[ao + 1]!).push 0).push 0
      fs := s.fs.push (g4Tag (s.cel.size >>> 2) 1)
      x := j } (.arg (s.cel.size >>> 2) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨n, hn, rfl⟩ := hda.inv5 (by rw [some_of_lt hda.lt_size, ht])
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  have hshr2' : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, hshr2', get!_of_some hn]
  obtain ⟨-, hc0, -, -, -⟩ := push4_spec s.cel (s.val.size / 4 + 2) ao 0 0 h.store.celSz
  obtain ⟨hvsz, hv0, hv1, -, hvp⟩ := push4_spec s.val 2 n 0 0 h.store.valSz
  refine ⟨_, step_args_new h hm hx hao' hda he hb rfl rfl hvp (by rw [hvsz]; have := h.store.valSz; omega)
    rfl rfl (.inl rfl) rfl rfl hm rfl rfl rfl ?_ (fun _ => by rw [hvsz]; omega)⟩
  show CellOK env s.P _ s.ev s.argA _ _ (s.cel.size / 4)
  unfold CellOK; rw [hc0]
  refine ⟨_, .natLit hv0, ?_⟩
  rw [hv1, show s.cel.size / 4 = s.N from rfl, ocExt_self,
    Expr.instantiateList_eq_self (by simp [Expr.looseBVarsBounded])]
  exact .refl

/-- A constant argument's entry and slot. -/
theorem const_slot {P : G4Prog} {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} (hI : Inv find? findProj? P) {ao : Nat} {sa : Expr} (hda : Den P ao sa)
    (ht : P.code[ao]! = 4) :
    ∃ k info, P.code[ao + 1]? = some k ∧ P.kInfo[k]? = some info ∧ sa = infoTerm info ∧
      P.kSlot[k]? = some P.kSlot[k]! := by
  obtain ⟨k, info, hk, hinfo, rfl⟩ := hda.inv4 (by rw [some_of_lt hda.lt_size, ht])
  have hkl : k < P.kSlot.size := by
    rw [hI.kSlotSize]
    rcases Nat.lt_or_ge k P.kInfo.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hinfo; cases hinfo
  exact ⟨k, info, hk, hinfo, rfl, some_of_lt hkl⟩

/-- **A constant argument, its slot set**: the slot's cell. -/
theorem step_arg_const_hit {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4)
    (hx : s.x = j + 1) (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 4)
    (hc : g4SlotGet s.slots s.P.epBase s.P.kSlot[s.P.code[ao + 1]!]! ≠ 0) :
    MInv env t₀ oc { s with
      fs := s.fs.push (g4Tag (g4SlotGet s.slots s.P.epBase s.P.kSlot[s.P.code[ao + 1]!]!) 1), x := j }
      (.arg (g4SlotGet s.slots s.P.epBase s.P.kSlot[s.P.code[ao + 1]!]!) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨k, info, hk, hinfo, rfl, hsl⟩ := const_slot h.store.prog hda ht
  rw [get!_of_some hk] at hc ⊢
  obtain ⟨hlt, how⟩ := h.store.slotsOK _ hc
  refine step_args_old h hm hx hao' hda he rfl hlt ?_
  rw [Expr.instantiateList_eq_self (infoTerm_closed info)]
  exact h.store.prog.owns_unique how (.inr ⟨k, info, hsl, hinfo, rfl⟩)

/-- **A constant argument, its slot empty**: a thunk of the constant node,
registered in the slot. -/
theorem step_arg_const_miss {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4)
    (hx : s.x = j + 1) (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 4) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push 0).push ao).push 0).push 0
      fs := s.fs.push (g4Tag (s.cel.size >>> 2) 1)
      slots := g4SlotSet s.slots s.P.kSlot[s.P.code[ao + 1]!]! (s.P.epBase + (s.cel.size >>> 2))
      x := j } (.arg (s.cel.size >>> 2) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨k, info, hk, hinfo, rfl, hsl⟩ := const_slot h.store.prog hda ht
  have hcl := infoTerm_closed info
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, get!_of_some hk]
  obtain ⟨-, hc0, hc1, hc2, -⟩ := push4_spec s.cel 0 ao 0 0 h.store.celSz
  refine ⟨_, step_args_new h hm hx hao' hda he hb rfl rfl (Pre.refl _) h.store.valSz rfl rfl
    (.inr ⟨_, rfl, by rw [Expr.instantiateList_eq_self hcl]; exact .inr ⟨k, info, hsl, hinfo, rfl⟩⟩)
    rfl rfl hm rfl rfl rfl ?_ (by omega)⟩
  show CellOK env s.P s.val s.ev s.argA _ _ (s.cel.size / 4)
  unfold CellOK; rw [hc0, hc1, hc2]
  exact ⟨infoTerm info, [], hda, .nil, hcl, by
    rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, Expr.instantiateList_eq_self hcl,
      List.map_nil, Expr.instantiateList_nil]⟩

/-- **A shared argument, its slot set**: the slot's cell. -/
theorem step_arg_shared_hit {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4)
    (hx : s.x = j + 1) (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 9)
    (hc : g4SlotGet s.slots s.P.epBase s.P.code[ao + 1]! ≠ 0) :
    MInv env t₀ oc { s with
      fs := s.fs.push (g4Tag (g4SlotGet s.slots s.P.epBase s.P.code[ao + 1]!) 1), x := j }
      (.arg (g4SlotGet s.slots s.P.epBase s.P.code[ao + 1]!) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨sl, a, h₁, h₂, hdaa, a', hcn⟩ := hda.inv9 (by rw [some_of_lt hda.lt_size, ht])
  rw [get!_of_some h₁] at hc ⊢
  obtain ⟨hlt, how⟩ := h.store.slotsOK sl hc
  have hcl := h.store.prog.shared_closed hcn hda
  refine step_args_old h hm hx hao' hda he rfl hlt ?_
  rw [Expr.instantiateList_eq_self hcl]
  exact h.store.prog.owns_unique how (.inl ⟨a', ao, hcn, h₁, hda⟩)

/-- **A shared argument, its slot empty**: a thunk of the closed term under
the empty environment, registered in the slot. -/
theorem step_arg_shared_miss {j ao : Nat} (h : MInv env t₀ oc s fl) (hm : s.mode = 4)
    (hx : s.x = j + 1) (hao : s.P.code[s.pc + 3 + j]! = ao) (ht : s.P.code[ao]! = 9) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push 0).push s.P.code[ao + 2]!).push 0).push 0
      fs := s.fs.push (g4Tag (s.cel.size >>> 2) 1)
      slots := g4SlotSet s.slots s.P.code[ao + 1]! (s.P.epBase + (s.cel.size >>> 2))
      x := j } (.arg (s.cel.size >>> 2) :: fl) := by
  obtain ⟨sa, cs, hao', hda, he, hb⟩ := h.argWit hm hx hao
  obtain ⟨sl, a, h₁, h₂, hdaa, a', hcn⟩ := hda.inv9 (by rw [some_of_lt hda.lt_size, ht])
  have hcl := h.store.prog.shared_closed hcn hda
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, get!_of_some h₁, get!_of_some h₂]
  obtain ⟨-, hc0, hc1, hc2, -⟩ := push4_spec s.cel 0 a 0 0 h.store.celSz
  refine ⟨_, step_args_new h hm hx hao' hda he hb rfl rfl (Pre.refl _) h.store.valSz rfl rfl
    (.inr ⟨_, rfl, by rw [Expr.instantiateList_eq_self hcl]; exact .inl ⟨a', ao, hcn, h₁, hda⟩⟩)
    rfl rfl hm rfl rfl rfl ?_ (by omega)⟩
  show CellOK env s.P s.val s.ev s.argA _ _ (s.cel.size / 4)
  unfold CellOK; rw [hc0, hc1, hc2]
  exact ⟨sa, [], hdaa, .nil, hcl, by
    rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, Expr.instantiateList_eq_self hcl,
      List.map_nil, Expr.instantiateList_nil]⟩

end

end ConLeche.Verify.Ground
