module

public import ConLeche.Verify.Ground.Run
import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step1
public import ConLeche.Verify.Ground.Step1N
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.StrLitExpr

public section

/-!
# Mode 1: the ι and projection frames (task #423 soundness, layer (c))

The value in focus meets a recursor's ι frame or a projection frame.  A
constructor value fires the rule (`ERed.iota`; after the K step,
`ERed.iotaK`) or selects the field (`ERed.proj`); a literal major is first
turned into its constructor form (`ERed.natLit`, `ERed.strLit`, the string's
form compiled), and a string under a projection likewise.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached ConLeche.Rules

theorem getElem!_of_getElem? {α : Type} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : a[i]! = x := by
  rw [getElem!_def, h]

/-- The constructor's arity bounds its type's Π-telescope at any levels. -/
theorem peelPis_of_g4Pis (ks : List Name) (us : List Level) :
    ∀ (ty : Expr) (acc n : Nat), n + acc ≤ g4Pis ty acc →
      (Expr.peelPis n (ty.instantiateLevelParams ks us)).isSome = true
  | .forallE _ b, acc, n, h => by
    rcases n with _ | n
    · rfl
    · simp only [Expr.instantiateLevelParams, Expr.peelPis, g4Pis] at h ⊢
      exact peelPis_of_g4Pis ks us b (acc + 1) n (by omega)
  | .bvar _, acc, n, h | .fvar _ _, acc, n, h | .sort _, acc, n, h | .const _ _, acc, n, h
  | .app _ _, acc, n, h | .lam _ _, acc, n, h | .letE _ _ _, acc, n, h | .lit _, acc, n, h
  | .proj _ _ _, acc, n, h => by
    have h0 : n = 0 := by simp only [g4Pis] at h; omega
    subst h0; rfl

theorem span_getD {a : Array Nat} {oc : Nat → Expr} {start len j : Nat} (hj : j < len) (d : Expr) :
    ((span a start len).map oc).getD j d = oc a[start + j]! := by
  simp [span, hj]

theorem span_length (a : Array Nat) (start len : Nat) : (span a start len).length = len := by
  simp [span]

theorem FS.top_proj' {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 4) :
    ∃ fl', fl = .proj fs[fs.size - 2]! :: fl' ∧ 2 ≤ fs.size ∧ FS fs (fs.size - 2) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | @proj t' fl' _ h' => exact ⟨fl', by simp, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht
                             rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

theorem FS.pushProj {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (pi : Nat) :
    FS ((fs.push pi).push 4) ((fs.push pi).push 4).size (.proj pi :: fl) := by
  have := FS.proj (fs := (fs.push pi).push 4) (t := fs.size)
    (by rw [show fs.size + 1 = (fs.push pi).size by simp, getElem!_push_eq']; rfl)
    (FS.push _ (by simp) (FS.push _ (Nat.le_refl _) h))
  rw [getElem!_push_lt' (by simp), getElem!_push_eq'] at this
  simpa using this

theorem FS.pop2 {fs : Array Nat} {fl : List Fr} (h : FS fs (fs.size - 2) fl) :
    FS fs.pop.pop fs.pop.pop.size fl := by
  show FS (g4PopN fs 2) (g4PopN fs 2).size fl
  rw [g4PopN_size]; exact FS.popN 2 (Nat.le_refl _) h

/-- A constructor entry's constant. -/
theorem ctorEntry {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    {P : G4Prog} (hI : Inv find? findProj? P) {k : Nat} (hk : k < P.kInfo.size)
    (h1 : P.kTag[k]! = 1) :
    ∃ c us nP nF cv, entryTerm P k = .const c us ∧ find? c = some (.ctorInfo cv nP nF) ∧
      P.kArity[k]! = g4Pis cv.type 0 ∧ (∃ i, P.nids[c]? = some i ∧ P.kB[k]! = i) ∧
      P.kD[k]! = us.length := by
  have h1' : P.kTag[k]? = some 1 := by rw [some_of_lt (by rw [hI.sizes]; exact hk), h1]
  obtain ⟨c, us, nP, nF, hi, ⟨cv, hf, ha⟩, -, ⟨i, hn, hb⟩, hd⟩ := (hI.ents k hk).tag1 hk h1'
  exact ⟨c, us, nP, nF, cv, by unfold entryTerm; rw [hi]; rfl, hf, get!_of_some ha,
    ⟨i, hn, get!_of_some hb⟩, get!_of_some hd⟩

/-! ## The ι frame: the rule's lookup and side conditions -/

/-- A recursor entry's constant and its declaration. -/
theorem recEntry {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    {P : G4Prog} (hI : Inv find? findProj? P) {k : Nat} (hk : k < P.kInfo.size)
    (h2 : P.kTag[k]? = some 2) :
    ∃ c lps us mI rP base nr isK isEta, P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) ∧
      entryTerm P k = .const c us ∧ RecOK find? P k c lps us mI rP base nr isK isEta := by
  obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, hr⟩ := (hI.ents k hk).tag2 hk h2
  exact ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, by unfold entryTerm; rw [hi]; rfl, hr⟩

/-- `g4FindRule` finds the first row of the range whose name id is `c`, or
returns the range's end. -/
theorem findRule_spec (rNid : Array Nat) (c : Nat) : ∀ (n i : Nat),
    (g4FindRule rNid c n i = i + n ∧ ∀ j, j < n → rNid[i + j]! ≠ c) ∨
    (∃ j, j < n ∧ g4FindRule rNid c n i = i + j ∧ rNid[i + j]! = c ∧ ∀ j', j' < j → rNid[i + j']! ≠ c)
  | 0, i => .inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, i => by
    simp only [g4FindRule]
    by_cases h : rNid[i]! = c
    · refine .inr ⟨0, by omega, by simp [h], by simpa using h, fun _ h' => absurd h' (Nat.not_lt_zero _)⟩
    · have hb : (rNid[i]! == c) = false := by simpa using h
      rw [hb]; simp only [Bool.false_eq_true, ite_false]
      rcases findRule_spec rNid c n (i + 1) with ⟨he, hne⟩ | ⟨j, hj, he, hc, hlt⟩
      · refine .inl ⟨by rw [he]; omega, fun j hj => ?_⟩
        rcases j with _ | j
        · simpa using h
        · have := hne j (by omega); rwa [show i + 1 + j = i + (j + 1) by omega] at this
      · refine .inr ⟨j + 1, by omega, by rw [he]; omega,
          by rw [show i + (j + 1) = i + 1 + j by omega]; exact hc, fun j' hj' => ?_⟩
        rcases j' with _ | j'
        · simpa using h
        · have := hlt j' (by omega); rwa [show i + 1 + j' = i + (j' + 1) by omega] at this

/-- **The rule the engine finds is the rule `Red.iota` selects**: with
injective name ids, the first row naming the constructor's id is the first
rule of that constructor. -/
theorem findRule_find {find? : Name → Option ConstantInfo} {P : G4Prog} {isK : Bool}
    {lps : List Name} {us : List Level} {rules : List RecRule} {base : Nat} (hnid : NidOK P)
    (hrows : ∀ i (h : i < rules.length), RowOK find? P (base + i) isK lps us rules[i])
    {cj : Name} {ij : Nat} (hcj : P.nids[cj]? = some ij)
    (hri : g4FindRule P.rNid ij rules.length base ≠ base + rules.length) :
    ∃ j, ∃ hj : j < rules.length, g4FindRule P.rNid ij rules.length base = base + j ∧
      rules.find? (fun r' => r'.ctor == cj) = some rules[j] ∧ rules[j].ctor = cj := by
  have hid : ∀ i (h : i < rules.length), (P.rNid[base + i]! = ij ↔ rules[i].ctor = cj) := by
    intro i h
    obtain ⟨-, -, -, -, ⟨ni, hni, hrn⟩, -⟩ := hrows i h
    rw [get!_of_some hrn]
    constructor
    · rintro rfl; exact hnid.2 _ _ _ hni hcj
    · intro he; rw [he] at hni; rw [hni] at hcj; exact Option.some.inj hcj
  rcases findRule_spec P.rNid ij rules.length base with ⟨he, -⟩ | ⟨j, hj, he, hc, hlt⟩
  · exact absurd he hri
  · refine ⟨j, hj, he, ?_, (hid j hj).mp hc⟩
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using (hid j hj).mp hc, j, hj, rfl, fun j' hj' => ?_⟩
    have := hlt j' hj'
    simpa [← hid j' (by omega)] using this

/-- **Not case 3**: the engine's side condition is `Red.iota`'s case
premise. -/
theorem iotaCase_of_gCase3 {env : Env} {isK : Bool} {cvj : ConstantVal} {us : List Level}
    (h : gCase3 env.find? isK cvj us = false) : IotaCase env isK cvj us false := by
  unfold gCase3 at h
  cases isK with
  | true => exact .k
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i cvT caps hf
      split at h
      · rename_i hl
        split at h
        · rename_i s hs
          exact .never hf (by simpa using hl) (by simpa using h)
        · cases h
      · cases h
    · cases h

/-- **Binding a span** (`g4BindSpan`, from its `j`-th cell): the records
extend the environment by those cells, the last innermost. -/
theorem bindSpan_spec (argA : Array Nat) (start : Nat) : ∀ (k j env : Nat) (ev : Array Nat) (cs : List Nat),
    ev.size % 2 = 0 → env ≤ ev.size / 2 → EnvL ev env cs →
    Pre ev (g4BindSpan argA start ev k j env) ∧ (g4BindSpan argA start ev k j env).size = ev.size + 2 * k ∧
      EnvL (g4BindSpan argA start ev k j env) (if k = 0 then env else (g4BindSpan argA start ev k j env).size / 2)
        ((List.range k).reverse.map (fun i => argA[start + (j + i)]!) ++ cs)
  | 0, _, _, ev, _, _, _, h => ⟨Pre.refl ev, by show ev.size = _; omega,
      by show EnvL ev _ _; simpa using h⟩
  | k + 1, j, env, ev, cs, h2, hle, h => by
    simp only [g4BindSpan]
    have hrec := EnvL.record h2 hle h argA[start + j]!
    have hsz : ((ev.push argA[start + j]!).push env).size = ev.size + 2 := by simp
    have hshr : ev.size >>> 1 = ev.size / 2 := Nat.shiftRight_eq_div_pow _ _
    rw [hshr]
    obtain ⟨hp, hs, he⟩ := bindSpan_spec argA start k (j + 1) (ev.size / 2 + 1) _ _ (by rw [hsz]; omega)
      (by rw [hsz]; omega) hrec
    refine ⟨((Pre.push _ _).trans (Pre.push _ _)).trans hp, by rw [hs, hsz]; omega, ?_⟩
    have hlist : (List.range k).reverse.map (fun i => argA[start + (j + 1 + i)]!) ++ argA[start + j]! :: cs =
        (List.range (k + 1)).reverse.map (fun i => argA[start + (j + i)]!) ++ cs := by
      rw [rev_range_succ (fun i => argA[start + (j + i)]!) k, List.append_assoc]
      simp only [Nat.add_zero, List.singleton_append]
      congr 2
      funext i; congr 2; omega
    rw [← hlist]
    split at he
    · rename_i hk0; subst hk0
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show (g4BindSpan argA start ((ev.push argA[start + j]!).push env) 0 (j + 1)
          (ev.size / 2 + 1)).size / 2 = ev.size / 2 + 1 by simp [g4BindSpan]; omega]
      exact he
    · simpa using he

theorem bindSpan_ref (argA : Array Nat) (start : Nat) {N : Nat} : ∀ (k j env : Nat) (ev : Array Nat),
    EvRef ev N → ev.size % 2 = 0 → env ≤ ev.size / 2 → (∀ i, i < k → argA[start + (j + i)]! < N) →
    EvRef (g4BindSpan argA start ev k j env) N
  | 0, _, _, _, hr, _, _, _ => hr
  | k + 1, j, env, ev, hr, h2, hle, hc => by
    simp only [g4BindSpan]
    have hshr : ev.size >>> 1 = ev.size / 2 := Nat.shiftRight_eq_div_pow _ _
    rw [hshr]
    have hsz : ((ev.push argA[start + j]!).push env).size = ev.size + 2 := by simp
    refine bindSpan_ref argA start k (j + 1) _ _ (hr.push2 h2 (Nat.le_refl _) ?_ hle) (by rw [hsz]; omega)
      (by rw [hsz]; omega) (fun i hi => ?_)
    · have := hc 0 (by omega); simpa using this
    · have := hc (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem span_rev (a : Array Nat) (start k : Nat) :
    (List.range k).reverse.map (fun i => a[start + (0 + i)]!) = (span a start k).reverse := by
  simp [span, List.map_reverse]

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- **A closed term compiled and entered** under frames whose claim holds of
it: the program grows, the focus is the compiled node under the empty
environment. -/
theorem MInv.enterCompiled (h : MInv env t₀ oc s fl) {fs : Array Nat} {fl' : List Fr}
    (hfs : FS fs fs.size fl') (hfl : FlOK s.P s.argA s.N fl') {e : Expr}
    (hc : e.looseBVarsBounded 0 = true) (hK : K env t₀ s.P s.argA oc fl' e) :
    MInv env t₀ oc { s with
      P := (g4Comp env.find? env.findProj? g4CompFuel s.P e).2, fs := fs, mode := 0,
      pc := (g4Comp env.find? env.findProj? g4CompFuel s.P e).1, env := 0, x := 0 } fl' := by
  have hcomp := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P e h.store.prog
  generalize g4Comp env.find? env.findProj? g4CompFuel s.P e = r at hcomp ⊢
  obtain ⟨o, P1⟩ := r
  obtain ⟨hI1, hx1, sb, hd, ha⟩ := hcomp
  dsimp only at hI1 hx1 hd ⊢
  have hx := hx1.toExtR
  refine ⟨(h.store.grow (s' := { s with P := P1 }) hI1 hx hx.epBase (Pre.refl _) h.store.celSz
    (Pre.refl _) h.store.valSz (Pre.refl _) h.store.evSz (Pre.refl _) rfl rfl (Agree.refl _ _)
    h.store.evRef h.store.argRef
    (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega))).same rfl rfl rfl rfl rfl rfl rfl,
    hfs, hfl.grow hx (Pre.refl _) (Nat.le_refl _), ?_⟩
  refine ⟨sb, ⟨sb, [], hd, .nil, Approx.bounded ha hc, by simp [Expr.instantiateList_nil]⟩, ?_⟩
  exact K.grow env t₀ oc hx (Pre.refl _) fl' hfl (K.step env t₀ s.P s.argA oc fl' hK (.forget .refl ha))

/-! ## The projection frame -/

/-- **A constructor at a projection frame**: the field's cell is entered
(`ERed.proj`). -/
theorem step_proj_ctor (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 4) (hpi : s.fs[s.fs.size - 2]! ≠ 0) (h1 : s.val[g4X4 s.x]! = 1)
    (hc1 : s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1)
    (hc2 : s.P.kB[s.val[g4X4 s.x + 1]!]! = s.P.pNid[s.fs[s.fs.size - 2]! - 1]!)
    (hc3 : s.P.pIdx[s.fs[s.fs.size - 2]! - 1]! < s.P.pNF[s.fs[s.fs.size - 2]! - 1]!)
    (hc4 : s.val[g4X4 s.x + 3]! = s.P.pNP[s.fs[s.fs.size - 2]! - 1]! + s.P.pNF[s.fs[s.fs.size - 2]! - 1]!)
    (hc5 : s.val[g4X4 s.x + 3]! ≤ s.P.kArity[s.val[g4X4 s.x + 1]!]!)
    (hc6 : s.P.kD[s.val[g4X4 s.x + 1]!]! = s.P.pNl[s.fs[s.fs.size - 2]! - 1]!) :
    ∃ fl', MInv env t₀ oc { s with
      fs := s.fs.pop.pop, mode := 2, pc := 0, env := 0,
      x := s.argA[s.val[g4X4 s.x + 2]! + s.P.pNP[s.fs[s.fs.size - 2]! - 1]! +
        s.P.pIdx[s.fs[s.fs.size - 2]! - 1]!]! } fl' := by
  rw [g4X4_eq] at h1 hc1 hc2 hc4 hc5 hc6 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨hk, hs, rfl⟩ := hv.inv1 h1
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_proj' h.stack hn ht
  generalize s.fs[s.fs.size - 2]! = pi at hpi hc2 hc3 hc4 hc6 hK h
  obtain ⟨q, rfl⟩ : ∃ q, pi = q + 1 := ⟨pi - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc2 hc3 hc4 hc6 ⊢
  have hq : q < s.P.projs.size := by
    rcases (h.frames _ (List.mem_cons_self ..) : FrOK s.P s.argA s.N (.proj (q + 1))) with h' | h'
    · cases h'
    · simpa using h'
  obtain ⟨sn, i, en, hpj, hfp, ⟨ni, hni, hpn⟩, hpi', hpnp, hpnf, hpnl, -⟩ := h.store.prog.prjs q hq
  rw [get!_of_some hpn] at hc2
  rw [get!_of_some hpi', get!_of_some hpnf] at hc3
  rw [get!_of_some hpnp, get!_of_some hpnf] at hc4
  rw [get!_of_some hpnl] at hc6
  rw [get!_of_some hpnp, get!_of_some hpi']
  simp only [K, hpj] at hK
  generalize s.val[4 * s.x + 1]! = kc at hk hc1 hc2 hc5 hc6 hK
  generalize s.val[4 * s.x + 2]! = st at hs hK ⊢
  generalize s.val[4 * s.x + 3]! = len at hs hc4 hc5 hK
  obtain ⟨c, us, nP, nF, cv, he, hf, har, ⟨i', hci, hkb⟩, hkd⟩ := ctorEntry h.store.prog hk hc1
  have hce : c = en.ctor := h.store.prog.nidOK.2 _ _ _ hci (by rw [hni, ← hc2, hkb])
  subst hce
  rw [he] at hK
  have hlen : (Expr.mkAppN (.const en.ctor us) ((span s.argA st len).map oc)).getAppArgs.length =
      en.numParams + en.numFields := by
    rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs, span_length, hc4]
  have hred := ERed.proj (env := env) (sn := sn) (i := i) hfp
    (by rw [Expr.getAppFn_mkAppN]; rfl) hc3 hlen (by rw [← hkd, hc6]) hf
    (by rw [hlen, ← hc4]; exact peelPis_of_g4Pis _ _ cv.type 0 len (by omega))
  rw [Expr.getAppArgs_mkAppN] at hred
  simp only [Expr.getAppArgs, List.nil_append] at hred
  rw [span_getD (by omega)] at hred
  refine ⟨fl', h.store.same rfl rfl rfl rfl rfl rfl rfl, hfs.pop2,
    fun f hf => h.frames f (List.mem_cons_of_mem _ hf), ?_, ?_⟩
  · exact h.store.argRef _ (by omega)
  · rw [show st + en.numParams + i = st + (en.numParams + i) by omega]
    exact K.step env t₀ s.P s.argA oc fl' hK hred

/-- **A string at a projection frame**: its constructor form is compiled and
evaluated under the frame pushed again (`ERed.strLit`). -/
theorem step_proj_str (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 4) (h3 : s.val[g4X4 s.x]! = 3)
    (hok : s.P.strOk = true) :
    ∃ fl', MInv env t₀ oc { s with
      P := (g4Comp env.find? env.findProj? g4CompFuel s.P
        (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!)).2,
      fs := (s.fs.pop.pop.push s.fs[s.fs.size - 2]!).push 4, mode := 0,
      pc := (g4Comp env.find? env.findProj? g4CompFuel s.P
        (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!)).1, env := 0, x := 0 } fl' := by
  rw [g4X4_eq] at h3 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨str, hstr, rfl⟩ := hv.inv3 h3
  rw [getElem!_of_getElem? hstr]
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_proj' h.stack hn ht
  refine ⟨_, h.enterCompiled (FS.pushProj hfs.pop2 _) (fun f hf => h.frames f hf)
    (strLitToConstructor_looseBVars str 0) ?_⟩
  exact K.step env t₀ s.P s.argA oc _ hK (.strLit (hR.str hok))

end

end ConLeche.Verify.Ground
