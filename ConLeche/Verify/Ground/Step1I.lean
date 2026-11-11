module

import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step1
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Ground.Step3
public import ConLeche.Verify.Ground.Step1N
import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.InstSpine
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

/-- Level instantiation keeps a telescope's syntactic arity. -/
theorem peelPis_inst (ks : List Name) (us : List Level) :
    ∀ (k : Nat) {e : Expr}, (Expr.peelPis k e).isSome = true →
      (Expr.peelPis k (e.instantiateLevelParams ks us)).isSome = true
  | 0, _, _ => rfl
  | k + 1, .forallE _ b, h => by
    simp only [Expr.instantiateLevelParams, Expr.peelPis] at h ⊢
    exact peelPis_inst ks us k h
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => by
    simp [Expr.peelPis] at h

theorem mkAppN_append (f : Expr) : ∀ (l₁ l₂ : List Expr),
    Expr.mkAppN f (l₁ ++ l₂) = Expr.mkAppN (Expr.mkAppN f l₁) l₂
  | [], _ => rfl
  | a :: l₁, l₂ => mkAppN_append (.app f a) l₁ l₂

theorem span_take (a : Array Nat) (start m n : Nat) (h : m ≤ n) : (span a start n).take m = span a start m := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [span_append, List.take_append_of_le_length (by simp [span_length]),
    List.take_of_length_le (by simp [span_length])]

theorem span_drop (a : Array Nat) (start m n : Nat) : (span a start (m + n)).drop m = span a (start + m) n := by
  rw [span_append, List.drop_append_of_le_length (by simp [span_length]),
    List.drop_of_length_le (by simp [span_length]), List.nil_append]

theorem FS.top_iota' {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 3) :
    ∃ fl', fl = .iota fs[fs.size - 4]! fs[fs.size - 3]! fs[fs.size - 2]! :: fl' ∧ 4 ≤ fs.size ∧
      FS fs (fs.size - 4) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | @iota t' fl' _ h' => exact ⟨fl', by simp, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

theorem recFireComparands_fst_eq (rl : RecRule) (cnP : Nat) (lps : List Name) (us : List Level)
    (cl : List Name) (as : List Expr) (rP : Nat) :
    (recFireComparands rl cnP lps us cl as rP).1 = gCmpLevels rl lps us cl := by
  unfold recFireComparands gCmpLevels; split <;> rename_i heq <;> simp [heq]

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

/-! ## The ι frame at a constructor -/

/-- **The rule fires**: at a constructor value whose rule the engine finds
outside case 3, the frames below the ι frame accept the rule's right-hand
side on the recursor's leading arguments and the constructor's fields
(`ERed.iota`; after the K step, `ERed.iotaK`). -/
theorem MInv.iotaFire (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) (h1 : s.val[g4X4 s.x]! = 1)
    {k ri : Nat} (hk : s.fs[s.fs.size - 4]! = k)
    (hkc : s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1)
    (hri : g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[k]! s.P.kC[k]! = ri)
    (hne : ri ≠ s.P.kC[k]! + s.P.kD[k]!)
    (hcl : s.val[g4X4 s.x + 3]! = s.P.rCP[ri]! + s.P.rNF[ri]!) (hc3 : s.P.rC3[ri]! = 0) :
    ∃ fl' c lps us mI rP base nr isK isEta rhs, fl = .iota k s.fs[s.fs.size - 3]! s.fs[s.fs.size - 2]! :: fl' ∧
      FS s.fs (s.fs.size - 4) fl' ∧ FlOK s.P s.argA s.N fl' ∧
      s.P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) ∧ base ≤ ri ∧ ri < base + nr ∧
      (s.P.rules[ri]!).rhs = rhs ∧ s.P.kB[k]! = rP ∧
      s.fs[s.fs.size - 3]! + rP ≤ s.argA.size ∧
      s.val[g4X4 s.x + 2]! + s.P.rCP[ri]! + s.P.rNF[ri]! ≤ s.argA.size ∧
      CodeOK s.P s.P.ruleCode[ri]! (rhs.instantiateLevelParams lps us) ∧
      (rhs.instantiateLevelParams lps us).looseBVarsBounded 0 = true ∧
      K env t₀ s.P s.argA oc fl' (Expr.mkAppN (rhs.instantiateLevelParams lps us)
        ((span s.argA s.fs[s.fs.size - 3]! rP ++
          span s.argA (s.val[g4X4 s.x + 2]! + s.P.rCP[ri]!) s.P.rNF[ri]!).map oc)) := by
  rw [g4X4_eq] at h1 hkc hri hcl ⊢
  obtain ⟨-, u, hv, hK⟩ := h.val1 hm
  obtain ⟨hkcl, hs, rfl⟩ := hv.inv1 h1
  obtain ⟨fl', hfl, -, hfs⟩ := FS.top_iota' h.stack hn ht
  rw [hk] at hfl
  have hfr : FrOK s.P s.argA s.N (.iota k s.fs[s.fs.size - 3]! s.fs[s.fs.size - 2]!) :=
    h.frames _ (by rw [hfl]; exact List.mem_cons_self ..)
  have hflr : FlOK s.P s.argA s.N fl' := fun f hf => h.frames f (by rw [hfl]; exact List.mem_cons_of_mem _ hf)
  rw [hfl] at hK
  have hI := h.store.prog
  have hnid := hI.nidOK
  have hargR := h.store.argRef
  refine ⟨fl', ?_⟩
  generalize s.fs[s.fs.size - 3]! = start at hfr hK hfl ⊢
  generalize s.fs[s.fs.size - 2]! = len at hfr hK hfl ⊢
  generalize s.val[4 * s.x + 1]! = kc at hkcl hkc hri hK
  generalize s.val[4 * s.x + 2]! = ms at hs hK ⊢
  generalize s.val[4 * s.x + 3]! = cl at hs hcl hK
  obtain ⟨hkk, hlen0, hsl, htag, har⟩ := hfr
  obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, he, cv, rules, hfind, hlps, hus, hpeel, hrPmI,
    -, har', hkB, hkC, hkD, hnr, hbr, ⟨kfab, hkE, hkf⟩, hrows⟩ := recEntry hI hkk htag
  rw [har'] at har
  have hlen : len = mI + 1 := by have := Option.some.inj har; omega
  subst hlen hlps hnr
  rw [get!_of_some hkC, get!_of_some hkD] at hri hne
  obtain ⟨cj, usj, nP, nF, cvj, hej, hfj, -, ⟨ij, hij, hkbj⟩, -⟩ := ctorEntry hI hkcl hkc
  rw [hkbj] at hri
  obtain ⟨j, hj, hrij, hfindr, hctor⟩ := findRule_find hnid hrows hij (by rw [hri]; exact hne)
  rw [hri] at hrij; subst hrij
  obtain ⟨hrow1, hnf, hcp, hc3', -, w, hw, hcode⟩ := hrows j hj
  have hcpv : gCtorParams env.find? rules[j].ctor = nP := by rw [hctor]; simp [gCtorParams, hfj]
  rw [get!_of_some hnf, get!_of_some hcp, hcpv] at hcl ⊢
  rw [get!_of_some hc3'] at hc3
  have hcase : ruleCase3 env.find? isK cv.levelParams us rules[j] = false := by
    cases h' : ruleCase3 env.find? isK cv.levelParams us rules[j] <;> simp_all
  have hg : gCase3 env.find? isK cvj (gCmpLevels rules[j] cv.levelParams us cvj.levelParams) = false := by
    unfold ruleCase3 at hcase; rw [hctor, hfj] at hcase; exact hcase
  have hrc : rules[j].rhs.looseBVarsBounded 0 = true :=
    ((hwf.consts _ (Env.find?_mem hfind)).2.2.2.2.2 cv mI rP isK rules rfl rules[j]
      (List.getElem_mem hj)).2.2.2.1
  rw [hej] at hK
  have hargs : (Expr.mkAppN (.const c us) ((span s.argA start (mI + 1)).map oc)).getAppArgs =
      (span s.argA start (mI + 1)).map oc := by
    rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
  have hpe : (Expr.peelPis (Expr.mkAppN (.const c us) ((span s.argA start (mI + 1)).map oc)).getAppArgs.length
      (cv.type.instantiateLevelParams cv.levelParams us)).isSome = true := by
    rw [hargs, List.length_map, span_length]; exact peelPis_inst _ _ _ hpeel
  have htake : ((span s.argA start (mI + 1)).map oc).take rP = (span s.argA start rP).map oc := by
    rw [← List.map_take, span_take _ _ _ _ (by omega)]
  have hred : ERed env (spanTerm s.P s.argA oc k start (mI + 1))
      (Expr.mkAppN (rules[j].rhs.instantiateLevelParams cv.levelParams us)
        ((span s.argA start rP ++ span s.argA (ms + nP) rules[j].nfields).map oc)) := by
    unfold spanTerm; rw [he]
    rcases hK.1 with hmaj | h4
    · have := ERed.iota (env := env) (e := Expr.mkAppN (.const c us) ((span s.argA start (mI + 1)).map oc))
        (major := Expr.mkAppN (.const cj usj) ((span s.argA ms cl).map oc)) (rl := rules[j])
        (by rw [Expr.getAppFn_mkAppN]; rfl) hfind (by rw [hargs, List.length_map, span_length]) hus
        (by rw [hargs, span_getD (by omega)]; simpa using hmaj) (by rw [Expr.getAppFn_mkAppN]; rfl) hfj
        hfindr (by rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs, span_length, hcl])
        (by rw [recFireComparands_fst_eq]; exact iotaCase_of_gCase3 hg) hpe
      rw [hargs, htake, Expr.getAppArgs_mkAppN] at this
      simp only [Expr.getAppArgs, List.nil_append] at this
      rw [hcl, ← List.map_drop, span_drop, ← List.map_append] at this; exact this
    · rw [get!_of_some hkE] at h4
      rcases hkf with rfl | ⟨kc', rl, -, -, -, rfl, rfl, hnf0⟩
      · exfalso; revert h4; split <;> split <;> omega
      · obtain rfl : j = 0 := by simp at hj; omega
        have := ERed.iotaK (env := env) (e := Expr.mkAppN (.const c us) ((span s.argA start (mI + 1)).map oc))
          (by rw [Expr.getAppFn_mkAppN]; rfl) hfind (by rw [hargs, List.length_map, span_length]) hus hpe
        rw [hargs, htake] at this
        simp only [List.getElem_cons_zero] at hnf0 ⊢
        rw [hnf0, span_zero, List.append_nil]; exact this
  refine ⟨c, cv.levelParams, us, mI, rP, base, rules.length, isK, isEta, rules[j].rhs, hfl, hfs, hflr, hi,
    by omega, by omega, ?_, get!_of_some hkB, by omega, by omega, by rw [get!_of_some hw]; exact hcode,
    by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hrc,
    K.step env t₀ s.P s.argA oc fl' hK.2 hred⟩
  rw [getElem!_of_getElem? hrow1]

/-- The value in focus under an extended program. -/
theorem MInv.withProg1 (h : MInv env t₀ oc s fl) (hm : s.mode = 1) {P' : G4Prog}
    (hI : Inv env.find? env.findProj? P') (hx : ExtR s.P P') :
    MInv env t₀ oc { s with P := P' } fl := by
  obtain ⟨hxv, t, hv, hK⟩ := h.val1 hm
  refine ⟨h.store.grow (s' := { s with P := P' }) hI hx hx.epBase (Pre.refl _) h.store.celSz (Pre.refl _)
    h.store.valSz (Pre.refl _) h.store.evSz (Pre.refl _) rfl rfl (Agree.refl _ _) h.store.evRef
    h.store.argRef (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega)), h.stack,
    h.frames.grow hx (Pre.refl _) (Nat.le_refl _), ?_⟩
  simp only [Focus, hm]
  refine ⟨hxv, t, hv.pre hx (Pre.refl _) (Pre.refl _) (Pre.refl _) (by have := h.store.valSz; omega), ?_⟩
  exact K.grow env t₀ oc hx (Pre.refl _) fl h.frames hK

/-- **The rule's right-hand side not yet compiled**: it is compiled and
stored in the rule's row, and the value returned again (a stutter). -/
theorem step_iota_compile (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) (h1 : s.val[g4X4 s.x]! = 1)
    {k ri : Nat} (hk : s.fs[s.fs.size - 4]! = k)
    (hkc : s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1)
    (hri : g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[k]! s.P.kC[k]! = ri)
    (hne : ri ≠ s.P.kC[k]! + s.P.kD[k]!)
    (hcl : s.val[g4X4 s.x + 3]! = s.P.rCP[ri]! + s.P.rNF[ri]!) (hc3 : s.P.rC3[ri]! = 0)
    {c' : Name} {lps : List Name} {us : List Level} {mI' rP' base' nr' : Nat} {isK' isEta' : Bool}
    (hik : s.P.kInfo[k]! = .recr c' lps us mI' rP' base' nr' isK' isEta') :
    MInv env t₀ oc { s with P :=
      { (g4Comp env.find? env.findProj? g4CompFuel s.P ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).2 with
        ruleCode := (g4Comp env.find? env.findProj? g4CompFuel s.P
          ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).2.ruleCode.set! ri
          ((g4Comp env.find? env.findProj? g4CompFuel s.P
            ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).1 + 1) } } fl := by
  obtain ⟨fl', c, lps₀, us₀, mI, rP, base, nr, isK, isEta, rhs, -, -, -, hi, hb₁, hb₂, -⟩ :=
    h.iotaFire hwf hm hn ht h1 hk hkc hri hne hcl hc3
  rw [getElem!_of_getElem? hi] at hik
  simp only [G4Info.recr.injEq] at hik
  obtain ⟨-, rfl, rfl, -, -, -, -, -, -⟩ := hik
  have hcomp := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P
    ((s.P.rules[ri]!).rhs.instantiateLevelParams lps₀ us₀) h.store.prog
  generalize g4Comp env.find? env.findProj? g4CompFuel s.P
    ((s.P.rules[ri]!).rhs.instantiateLevelParams lps₀ us₀) = r at hcomp ⊢
  obtain ⟨o, P1⟩ := r
  obtain ⟨hI1, hx1, sb, hd, ha⟩ := hcomp
  dsimp only at hI1 hx1 hd ⊢
  have hrl : ri < s.P.rules.size := by
    have := h.store.prog.rows_lt (P := s.P) ⟨_, _, _, _, _, _, _, _, _, hi, hb₁, hb₂⟩; omega
  have hrr : (P1.rules[ri]!) = (s.P.rules[ri]!) := by
    simp only [getElem!_def, (rowR_eq (hx1.toExtR.row ri hrl)).1]
  have hI2 := hI1.setRuleCode (hx1.toExtR.kInfo_some hi) hb₁ hb₂ hd (by rw [hrr]; exact ha)
  exact h.withProg1 hm hI2 (hx1.toExtR.trans (ExtR.codes P1 P1.kCode _))

/-- **The rule fires, its right-hand side not a λ of the bound arity**: the
leading arguments and the fields are pushed as argument frames over the
compiled right-hand side. -/
theorem step_iota_frames (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) (h1 : s.val[g4X4 s.x]! = 1)
    {k ri : Nat} (hk : s.fs[s.fs.size - 4]! = k)
    (hkc : s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1)
    (hri : g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[k]! s.P.kC[k]! = ri)
    (hne : ri ≠ s.P.kC[k]! + s.P.kD[k]!)
    (hcl : s.val[g4X4 s.x + 3]! = s.P.rCP[ri]! + s.P.rNF[ri]!) (hc3 : s.P.rC3[ri]! = 0)
    (hrc : s.P.ruleCode[ri]! ≠ 0) :
    ∃ fl', MInv env t₀ oc { s with
      fs := g4PushArgs s.argA s.fs[s.fs.size - 3]!
        (g4PushArgs s.argA (s.val[g4X4 s.x + 2]! + s.P.rCP[ri]!) (g4PopN s.fs 4) s.P.rNF[ri]!) s.P.kB[k]!,
      mode := 0, pc := s.P.ruleCode[ri]! - 1, env := 0, x := 0 } fl' := by
  obtain ⟨fl', c, lps, us, mI, rP, base, nr, isK, isEta, rhs, -, hfs, hfl, -, -, -, -, hkB, hs₁, hs₂, hcode,
    hcl0, hK⟩ := h.iotaFire hwf hm hn ht h1 hk hkc hri hne hcl hc3
  rcases hcode with h0 | ⟨o, sb, ho, hd, ha⟩
  · exact absurd h0 hrc
  rw [ho, Nat.add_sub_cancel, hkB]
  generalize s.fs[s.fs.size - 3]! = start at hs₁ hK ⊢
  generalize s.val[g4X4 s.x + 2]! + s.P.rCP[ri]! = ms at hs₂ hK ⊢
  generalize s.P.rNF[ri]! = nf at hs₂ hK ⊢
  have hcell : ∀ st n, st + n ≤ s.argA.size → ∀ c ∈ span s.argA st n, c < s.N := by
    intro st n hle c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range] at hj
    exact h.store.argRef _ (by omega)
  refine ⟨_, h.store.same rfl rfl rfl rfl rfl rfl rfl,
    FS.pushArgs _ _ _ (FS.pushArgs _ _ _ hfs.popK), ?_, ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf; exact hcell _ _ hs₁ c hc
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf; exact hcell _ _ (by omega) c hc
    · exact hfl f hf
  · refine ⟨sb, ⟨sb, [], hd, .nil, Approx.bounded ha hcl0, by simp [Expr.instantiateList_nil]⟩, ?_⟩
    rw [K.args, K.args, ← mkAppN_append, ← List.map_append]
    exact K.step env t₀ s.P s.argA oc fl' hK (.forget .refl (Approx.mkAppN ha (Approx.Args.refl _)))

/-- **The rule fires, its right-hand side a λ of the bound arity**: the
leading arguments and the fields are bound at once, and the λ's body
evaluated (`beta` × the arity). -/
theorem step_iota_bind (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) (h1 : s.val[g4X4 s.x]! = 1)
    {k ri : Nat} (hk : s.fs[s.fs.size - 4]! = k)
    (hkc : s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1)
    (hri : g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[k]! s.P.kC[k]! = ri)
    (hne : ri ≠ s.P.kC[k]! + s.P.kD[k]!)
    (hcl : s.val[g4X4 s.x + 3]! = s.P.rCP[ri]! + s.P.rNF[ri]!) (hc3 : s.P.rC3[ri]! = 0)
    (hrc : s.P.ruleCode[ri]! ≠ 0) (hl2 : s.P.code[s.P.ruleCode[ri]! - 1]! = 2)
    (htn : s.P.code[s.P.ruleCode[ri]! - 1 + 2]! = s.P.kB[k]! + s.P.rNF[ri]!) :
    ∃ fl', MInv env t₀ oc { s with
      ev := g4BindSpan s.argA (s.val[g4X4 s.x + 2]! + s.P.rCP[ri]!)
        (g4BindSpan s.argA s.fs[s.fs.size - 3]! s.ev s.P.kB[k]! 0 0) s.P.rNF[ri]! 0
        (if s.P.kB[k]! == 0 then 0 else (g4BindSpan s.argA s.fs[s.fs.size - 3]! s.ev s.P.kB[k]! 0 0).size >>> 1),
      fs := g4PopN s.fs 4, mode := 0, pc := s.P.code[s.P.ruleCode[ri]! - 1 + 3]!,
      env := if s.P.kB[k]! + s.P.rNF[ri]! == 0 then 0 else
        (g4BindSpan s.argA (s.val[g4X4 s.x + 2]! + s.P.rCP[ri]!)
          (g4BindSpan s.argA s.fs[s.fs.size - 3]! s.ev s.P.kB[k]! 0 0) s.P.rNF[ri]! 0
          (if s.P.kB[k]! == 0 then 0 else
            (g4BindSpan s.argA s.fs[s.fs.size - 3]! s.ev s.P.kB[k]! 0 0).size >>> 1)).size >>> 1,
      x := 0 } fl' := by
  obtain ⟨fl', c, lps, us, mI, rP, base, nr, isK, isEta, rhs, -, hfs, hfl, -, -, -, -, hkB, hs₁, hs₂, hcode,
    hcl0, hK⟩ := h.iotaFire hwf hm hn ht h1 hk hkc hri hne hcl hc3
  rcases hcode with h0 | ⟨o, sb, ho, hd, ha⟩
  · exact absurd h0 hrc
  rw [ho, Nat.add_sub_cancel] at hl2 htn ⊢
  rw [hkB] at htn ⊢
  generalize s.fs[s.fs.size - 3]! = start at hs₁ hK ⊢
  generalize s.val[g4X4 s.x + 2]! + s.P.rCP[ri]! = ms at hs₂ hK ⊢
  generalize s.P.rNF[ri]! = nf at hs₂ hK htn ⊢
  have h2 : s.P.code[o]? = some 2 := by rw [some_of_lt hd.lt_size, hl2]
  have htn' : s.P.code[o + 2]? = some (rP + nf) := by
    obtain ⟨_, _, _, _, -, h', -⟩ := hd.lam_inv h2; rw [h', ← htn, get!_of_some h']
  have htn1 : 1 ≤ rP + nf := by
    obtain ⟨_, tn'', _, _, -, h', -, -, -, htel⟩ := hd.lam_inv h2
    rw [htn'] at h'; cases h'
    rcases htel with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> omega
  obtain ⟨sb', hdb, rfl, hin⟩ := Den.lamWalk (rP + nf) hd h2 htn' (Nat.le_refl _)
  rw [get!_of_some (hin rfl)]
  have hev := h.store.evSz
  obtain ⟨p1, sz1, el1⟩ := bindSpan_spec s.argA start rP 0 0 s.ev [] hev (Nat.zero_le _) .nil
  generalize hE1 : g4BindSpan s.argA start s.ev rP 0 0 = EV1 at p1 sz1 el1 ⊢
  have he1 : (if rP == 0 then 0 else EV1.size >>> 1) = (if rP = 0 then 0 else EV1.size / 2) := by
    by_cases hr : rP = 0 <;> simp [hr, Nat.shiftRight_eq_div_pow]
  rw [he1]
  have hle1 : (if rP = 0 then 0 else EV1.size / 2) ≤ EV1.size / 2 := by split <;> omega
  obtain ⟨p2, sz2, el2⟩ := bindSpan_spec s.argA ms nf 0 (if rP = 0 then 0 else EV1.size / 2) EV1 _
    (by rw [sz1]; omega) hle1 el1
  have hcell : ∀ st n, st + n ≤ s.argA.size → ∀ i, i < n → s.argA[st + (0 + i)]! < s.N :=
    fun st n hle i hi => h.store.argRef _ (by omega)
  have hr1 := bindSpan_ref s.argA start rP 0 0 s.ev h.store.evRef hev (Nat.zero_le _) (hcell _ _ hs₁)
  rw [hE1] at hr1
  have hr2 := bindSpan_ref s.argA ms nf 0 _ EV1 hr1 (by rw [sz1]; omega) hle1 (hcell _ _ (by omega))
  have he2 : (if rP + nf == 0 then 0 else (g4BindSpan s.argA ms EV1 nf 0 (if rP = 0 then 0 else EV1.size / 2)).size >>> 1) =
      (if nf = 0 then (if rP = 0 then 0 else EV1.size / 2) else
        (g4BindSpan s.argA ms EV1 nf 0 (if rP = 0 then 0 else EV1.size / 2)).size / 2) := by
    rw [show (rP + nf == 0) = false by simp; omega]
    by_cases hnf : nf = 0
    · subst hnf
      have hr : rP ≠ 0 := by omega
      simp [g4BindSpan, hr, Nat.shiftRight_eq_div_pow]
    · simp [hnf, Nat.shiftRight_eq_div_pow]
  rw [he2]
  generalize g4BindSpan s.argA ms EV1 nf 0 (if rP = 0 then 0 else EV1.size / 2) = EV2 at p2 sz2 el2 hr2 ⊢
  rw [span_rev, span_rev, List.append_nil, ← List.reverse_append] at el2
  refine ⟨fl', (h.store.withEv (p1.trans p2) (by rw [sz2, sz1]; omega) hr2).same rfl rfl rfl rfl rfl rfl rfl,
    hfs.popK, hfl, ?_⟩
  refine ⟨_, ⟨sb', _, hdb, el2, ?_, rfl⟩, ?_⟩
  · have := Approx.bounded ha hcl0
    rw [lams_bounded] at this
    simpa [span_length, Nat.add_comm] using this
  · have hβ := betaN_env env ((span s.argA start rP ++ span s.argA ms nf).map oc) sb' []
    rw [List.length_map, List.length_append, span_length, span_length, Expr.instantiateList_nil,
      List.append_nil] at hβ
    have h₁ := K.step env t₀ s.P s.argA oc fl' hK (.forget .refl (Approx.mkAppN ha (Approx.Args.refl _)))
    have h₂ := K.step env t₀ s.P s.argA oc fl' h₁ hβ
    rwa [← List.map_reverse] at h₂

/-! ## The ι frame at a literal major -/

/-- **A string major**: its constructor form is compiled and evaluated under
the ι frame (`ERed.strLit`). -/
theorem step_iota_str (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (h3 : s.val[g4X4 s.x]! = 3) (hok : s.P.strOk = true) :
    MInv env t₀ oc { s with
      P := (g4Comp env.find? env.findProj? g4CompFuel s.P
        (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!)).2, mode := 0,
      pc := (g4Comp env.find? env.findProj? g4CompFuel s.P
        (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!)).1, env := 0, x := 0 } fl := by
  rw [g4X4_eq] at h3 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨str, hstr, rfl⟩ := hv.inv3 h3
  rw [getElem!_of_getElem? hstr]
  exact h.enterCompiled h.stack h.frames (strLitToConstructor_looseBVars str 0)
    (K.step env t₀ s.P s.argA oc fl hK (.strLit (hR.str hok)))

/-- **The literal `0` as a major**: `Nat.zero` (`ERed.natLit`). -/
theorem step_iota_zero (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (h2 : s.val[g4X4 s.x]! = 2) (hok : s.P.natOk = true) (h0 : s.val[g4X4 s.x + 1]! = 0) :
    MInv env t₀ oc { s with
      val := (((s.val.push 1).push s.P.kZero).push 0).push 0, mode := 1, pc := 0, env := 0,
      x := s.val.size >>> 2 } fl := by
  rw [g4X4_eq] at h2 h0
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain rfl := hv.inv2 h2
  rw [h0] at hK
  have := h.pushCtor0 h.stack h.frames hR.zero.1 (by
    rw [hR.zero.2]; exact K.step env t₀ s.P s.argA oc fl hK (.natLit (n := 0) (hR.nat hok)))
  exact this

/-- **The literal `m + 1` as a major**: `Nat.succ` on a new value cell
holding the literal `m` (`ERed.natLit`). -/
theorem step_iota_succ (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (h2 : s.val[g4X4 s.x]! = 2) (hok : s.P.natOk = true) {m : Nat} (hm1 : s.val[g4X4 s.x + 1]! = m + 1) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push ((s.val.size >>> 2) + 2)).push 0).push 0).push 0,
      val := (((((((s.val.push 2).push m).push 0).push 0).push 1).push s.P.kSucc).push s.argA.size).push 1,
      argA := s.argA.push (s.cel.size >>> 2), mode := 1, pc := 0, env := 0,
      x := (s.val.size >>> 2) + 1 } fl := by
  rw [g4X4_eq] at h2 hm1
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain rfl := hv.inv2 h2
  rw [hm1] at hK
  have hK' := K.step env t₀ s.P s.argA oc fl hK (.natLit (n := m + 1) (hR.nat hok))
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  have hshc : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr, hshc]
  have hvs := h.store.valSz
  obtain ⟨vz1, v0, v1, -, vp1⟩ := push4_spec s.val 2 m 0 0 hvs
  generalize hV1 : (((s.val.push 2).push m).push 0).push 0 = V1 at vz1 v0 v1 vp1
  obtain ⟨vz2, w0, w1, w2, vp2⟩ := push4_spec V1 1 s.P.kSucc s.argA.size 1 (by rw [vz1]; omega)
  have w3 := push4_get3 V1 1 s.P.kSucc s.argA.size 1 (by rw [vz1]; omega)
  have hV1u : V1.size / 4 = s.val.size / 4 + 1 := by rw [vz1]; omega
  rw [hV1u] at w0 w1 w2 w3
  generalize hV2 : (((V1.push 1).push s.P.kSucc).push s.argA.size).push 1 = V2 at vz2 w0 w1 w2 w3 vp2
  have u0 : V2[4 * (s.val.size / 4)]! = 2 := by rw [vp2.2 _ (by rw [vz1]; omega)]; exact v0
  have u1 : V2[4 * (s.val.size / 4) + 1]! = m := by rw [vp2.2 _ (by rw [vz1]; omega)]; exact v1
  refine ⟨ocExt oc s.N (.lit (.natVal m)), ?_⟩
  have hS1 := h.store.alloc (s' := { s with
      cel := (((s.cel.push (s.val.size / 4 + 2)).push 0).push 0).push 0, val := V2 }) (w0 := s.val.size / 4 + 2) (w1 := 0) (w2 := 0) (t := .lit (.natVal m)) rfl rfl
    (vp1.trans vp2) (by rw [vz2, vz1]; omega) (Pre.refl _) h.store.evSz rfl rfl rfl
    (h.store.evRef.mono (Nat.le_succ _)) rfl ?_ (fun _ => by rw [vz2, vz1]; omega)
  · have hN1 : ({ s with cel := (((s.cel.push (s.val.size / 4 + 2)).push 0).push 0).push 0, val := V2 } : MS).N =
        s.N + 1 := by
      simp only [MS.N, Array.size_push]; have := h.store.celSz; omega
    have hS2 := hS1.withValArg (val' := V2) (argA' := s.argA.push s.N) (Pre.refl _) (by rw [vz2, vz1]; omega)
      (Pre.push _ _) (by
        rw [hN1]; exact (h.store.argRef.mono (Nat.le_succ _)).push (Nat.lt_succ_self _))
    refine ⟨hS2.same rfl rfl rfl rfl rfl rfl rfl, h.stack, ?_, ?_⟩
    · exact h.frames.grow (ExtR.refl _) (Pre.push _ _) (by simp only [MS.N, Array.size_push]; omega)
    · show _ < _ ∧ ∃ t, ValDen s.P V2 s.ev (s.argA.push s.N) _ _ t ∧ _
      refine ⟨show s.val.size / 4 + 1 < V2.size / 4 by rw [vz2, vz1]; omega, _, .ctor w0 (by rw [w1]; exact hR.succ.1)
        (by rw [w2, w3]; simp), ?_⟩
      rw [w1, w2, w3, span_one, getElem!_push_eq', List.map_cons, List.map_nil, ocExt_self]
      change K env t₀ s.P _ _ fl (.app (entryTerm s.P s.P.kSucc) _)
      rw [hR.succ.2]
      exact K.move h.store.argRef (Agree.ext oc s.N _) (ExtR.refl _) (Pre.push _ _) h.frames hK'
  · unfold CellOK
    rw [show 4 * s.N = 4 * (s.cel.size / 4) from rfl]
    obtain ⟨-, c0, -, -, -⟩ := push4_spec s.cel (s.val.size / 4 + 2) 0 0 0 h.store.celSz
    rw [c0]
    refine ⟨_, .natLit u0, ?_⟩
    rw [u1, ocExt_self]; exact .refl

end

end ConLeche.Verify.Ground
