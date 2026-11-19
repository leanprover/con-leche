module

public import ConLeche.OleanInput
public import ConLeche.Verify.IsModelRecords
public import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads

/-!
# The reader's records cover the input

`InputRecords` (`ConLeche/OleanInput.lean`) is the `.olean` input as a set of records, read off
the closure's views.  The reader (`readOleansAt`) loads the closure's modules in an order,
merges their constants by Lean's rule, emits the merged constants in lean4export's order and
builds the stream reader's records from them.  `readOleansAt_covers`: every record of the
closure is stored, as `StoredAs` says, by a record of a declaration the reader read — where that
declaration passes the reserved names' check (a theorem stored for the axiom `Quot.sound` would
not, and an accepted stream has none).

* `readOleansAt_entry`: a constant of a view of a module of the closure has its merged copy
  under its name, the constant itself, or a theorem standing for it (`EntryStands`: Lean's rule
  keeps one of two proofs of one statement, and a theorem for an axiom);
* `covers_of_stored`: a merged constant's records are among the emitted declarations', a block
  member's in its block's record (`home_group`), with the recursors' rules firing against the
  block's type formers, which are the recursor's `all`.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## A view's constant, merged -/

/-- **The merged copy `e'` stands for the view's constant `c`**: it is `c`, or a theorem of
`c`'s statement standing for a theorem or for an axiom of a proposition. -/
@[expose] def EntryStands (e' : CEntry) (c : CEntryF Name Expr) : Prop :=
  e'.toCEntryF = c ∨
    (e'.toCEntryF.cv = c.cv ∧ e'.kind.tag = 2 ∧ (c.kind.tag = 2 ∨ c.kind = .ax false))

/-- **A view's constant is `lazyEntry`'s read of its skeleton**, but for a theorem's value. -/
theorem lazyEntry_eq_of_spec {r : Region} {i : Nat} {s : CEntryF UInt64 UInt64}
    {c e : CEntryF Name Expr} (hc : s.mapM (nameP r) (exprP r) = some c)
    (he : lazyEntry (nameP r) (exprP r) r i s = some e) (hk : c.kind.tag ≠ 2) : e = c := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all' =>
    have := (CEntryF.mapM_parts hc).2.2.2.1
    simp only [CKindF.tag] at this
    exact absurd this.symm hk
  | _ =>
    simp only [lazyEntry] at he
    rw [hc] at he
    cases he
    rfl

/-- What a successful read's merge is. -/
structure MergeFacts (mg : Merged) (ds : Array Declaration) : Prop where
  names : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n
  order : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true
  nodup : mg.order.toList.Nodup
  blocks : blocksOk mg = .ok ()
  decls : declsOf (emitAll mg mg.order) = .ok ds

/-- **A constant of a view of a module of the closure has its merged copy.** -/
theorem readOleansAt_entry {sp : Roots} (hsp : sp.bare = sp) {roots : Array Name} {jobs : Nat}
    {pace : Pace} {lenient homes : Bool} {fs : FS} {rd : OleanRead} {hs hs' : HS}
    (h : (readOleansAt sp roots none jobs pace lenient homes : ModelIO _) fs hs (.ok (.ok rd)) hs') :
    ∃ mg, MergeFacts mg rd.decls ∧ ∀ {m : Name} {d : ModDecoded} {c : CEntryF Name Expr},
      InClosure sp fs roots m → ViewOf sp fs m d → c ∈ d.constants →
      ∃ e', mg.map[c.name]? = some e' ∧ EntryStands e' c := by
  obtain ⟨order, ls, mg, rs, -, h1, h2, hco, hcr, hstand, hm, hb, hr, hds, -, -⟩ :=
    readOleansAt_ok hsp h
  have hrs : rs = mg.order := by
    simp only [Option.map_none, ite_self, rootConstants] at hr
    cases hr
    rfl
  subst hrs
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mergeAll_ok hm
  refine ⟨mg, ⟨fun n x hx => (hk2 n x hx).1, hk3, hk4, hb, hds⟩, ?_⟩
  intro m d c hcl hv hc
  have hmo := hcl.mem_order hco hcr
  have : m ∈ ls.map (·.name) := by
    rw [h1]
    simpa using hmo
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp this
  obtain ⟨i, f, -, hf, hload⟩ := h2 l hl
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := readFiles_unique hf hf'
  obtain ⟨r, a, sk, skels, hreg, -, hsk, hskels, -, -, hlazy⟩ := loadAt_spec hload
  obtain ⟨sk', hsk', hspec⟩ := view_parts hreg hview
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := mapM_mem_inv hspec (by simpa using hc)
  obtain ⟨s, hs1, hs2⟩ := constSpec_parts hcs
  obtain ⟨s', hs'mem, hs'⟩ := mapM_mem hskels hloc
  rw [hs1] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  obtain ⟨hn, hlp, hty, hth⟩ := lazyEntry_of_spec hs2 hent
  obtain ⟨c', hc', hst⟩ := hstand l hl e (by simpa using he)
  rw [hn] at hc'
  refine ⟨c', hc', ?_⟩
  have hecv : e.toCEntryF.cv = c.cv := by
    simp only [CEntryF.cv, hn, hlp, hty]
  by_cases h2c : c.kind.tag = 2
  · -- a theorem: the loaded entry is a theorem, and so is what stands for it
    cases hck : c.kind with
    | thm v all =>
      obtain ⟨-, g, -, -, hek, -, -⟩ := hth v all hck
      refine .inr ⟨?_, ?_, .inl (by rw [hck]; rfl)⟩
      · rcases hst with he' | ⟨n1, t1, l1, -⟩
        · rw [he']; exact hecv
        · simp only [CEntryF.cv] at hecv ⊢
          rw [n1, t1, l1]; exact hecv
      · rcases hst with he' | ⟨-, -, -, k1⟩
        · rw [he', hek]; rfl
        · rw [hek] at k1
          cases hk' : c'.kind <;> rw [hk'] at k1 <;> first | rfl | exact k1.elim
    | _ => rw [hck] at h2c; simp [CKindF.tag] at h2c
  · have hec : e.toCEntryF = c := lazyEntry_eq_of_spec hs2 hent h2c
    rcases hst with rfl | ⟨n1, t1, l1, k1⟩
    · exact .inl hec
    · have hkc : e.kind = c.kind := by rw [← hec]
      rw [hkc] at k1
      cases hck : c.kind with
      | ax u =>
        rw [hck] at k1
        cases hk' : c'.kind with
        | thm v a =>
          rw [hk'] at k1
          obtain ⟨-, rfl⟩ := k1
          refine .inr ⟨?_, by rw [hk']; rfl, .inr hck⟩
          simp only [CEntryF.cv] at hecv ⊢
          rw [n1, t1, l1]; exact hecv
        | ax u' =>
          rw [hk'] at k1
          obtain rfl : u' = u := k1
          refine .inl ?_
          rw [← hec]
          rcases c' with ⟨⟨cn, cl, ct, ck⟩, cu⟩
          rcases e with ⟨⟨en, el, et, ek⟩, eu⟩
          simp only at n1 t1 l1 hk' hkc hck ⊢
          rw [n1, t1, l1, hk', hkc, hck]
        | _ => rw [hk'] at k1; exact k1.elim
      | thm v a => rw [hck] at h2c; exact absurd rfl h2c
      | _ => rw [hck] at k1; cases hk' : c'.kind <;> rw [hk'] at k1 <;> exact k1.elim

/-! ## A block's record -/

theorem mapM_ok_forall₂ {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → Forall₂ (fun x y => f x = .ok y) xs ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok zs =>
        rw [hxs] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons hx (mapM_ok_forall₂ hxs)

theorem mapM_ok_mem {ε α β : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = .ok y := by
  obtain ⟨y, hy, h⟩ := Forall₂.mem_left (mapM_ok_forall₂ h) x hx
  exact ⟨y, hy, h⟩

theorem mapM_ok_mem_inv {ε α β : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨x, hx, h⟩ := Forall₂.mem_right (mapM_ok_forall₂ h) y hy
  exact ⟨x, hx, h⟩

/-- Two maps of one list, zipped, hold the pair of each element's values. -/
theorem mapM_ok_zip {ε α β γ : Type} {f : α → Except ε β} {g : α → Except ε γ}
    {xs : List α} {a : List β} {b : List γ} (hf : xs.mapM f = .ok a) (hg : xs.mapM g = .ok b)
    {x : α} (hx : x ∈ xs) {fx : β} {gx : γ} (hfx : f x = .ok fx) (hgx : g x = .ok gx) :
    (fx, gx) ∈ a.zip b := by
  have h1 := mapM_ok_forall₂ hf
  have h2 := mapM_ok_forall₂ hg
  clear hf hg
  induction h1 generalizing b with
  | nil => cases hx
  | @cons x' y' xs' ys' hxy t ih =>
    cases h2 with
    | cons hxz t2 =>
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hfx] at hxy; rw [hgx] at hxz
        cases hxy; cases hxz
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx t2)

/-- The constructor index map: a listed name maps to a position holding it. -/
theorem ctorIx_notMem (n : Name) : ∀ (ns : List Name) (m : Std.HashMap Name Nat) (j : Nat),
    n ∉ ns → (ns.foldl (fun (mi : Std.HashMap Name Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1))
      (m, j)).1[n]? = m[n]?
  | [], _, _, _ => rfl
  | a :: ns, m, j, h => by
    simp only [List.foldl_cons]
    rw [ctorIx_notMem n ns _ _ (fun h' => h (List.mem_cons_of_mem _ h')),
      Std.HashMap.getElem?_insert]
    have : (a == n) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => h (he ▸ List.mem_cons_self)
    rw [this]; rfl

theorem ctorIx_mem (n : Name) : ∀ (ns : List Name) (m : Std.HashMap Name Nat) (j : Nat),
    n ∈ ns → ∃ k, (ns.foldl (fun (mi : Std.HashMap Name Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1))
      (m, j)).1[n]? = some k ∧ j ≤ k ∧ ns[k - j]? = some n
  | [], _, _, h => by cases h
  | a :: ns, m, j, h => by
    simp only [List.foldl_cons]
    by_cases hn : n ∈ ns
    · obtain ⟨k, h1, h2, h3⟩ := ctorIx_mem n ns _ (j + 1) hn
      refine ⟨k, h1, by omega, ?_⟩
      have : k - j = (k - (j + 1)) + 1 := by omega
      rw [this]
      simpa using h3
    · have ha : a = n := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h hn
      subst ha
      refine ⟨j, ?_, Nat.le_refl _, by simp⟩
      rw [ctorIx_notMem a ns _ _ hn, Std.HashMap.getElem?_insert_self]

/-- `ctorAt` finds a listed constructor record by its name. -/
theorem ctorAt_of_mem {nm : Nat → M Name} {ex : Nat → M Expr} {cts : List IndCtorRec}
    {L2 : List (CEntryF Name Expr)} (hc : Forall₂ (CtorRes nm ex) cts L2) {cn : List Name}
    (hcn : cts.mapM (fun c => nm c.cv.name) = .ok cn) {n : Name} (hn : n ∈ cn) :
    ∃ ct y, ctorAt cn cts n = some ct ∧ y ∈ L2 ∧ CtorRes nm ex ct y ∧ y.name = n := by
  have hcn' : cn = L2.map (·.name) := by
    rw [mapM_res (F := fun (c : IndCtorRec) => nm c.cv.name) (G := CEntryF.name)
      (fun t c (h : CtorRes nm ex t c) => h.1.1) hc] at hcn
    cases hcn; rfl
  obtain ⟨k, hk, -, hkn⟩ := ctorIx_mem n cn {} 0 hn
  simp only [Nat.sub_zero] at hkn
  rcases getElem?_forall₂ hc k with ⟨-, h2⟩ | ⟨ct, y, h1, h2, hr⟩
  · rw [hcn', List.getElem?_map, h2] at hkn; cases hkn
  · refine ⟨ct, y, ?_, List.mem_of_getElem? h2, hr, ?_⟩
    · simp only [ctorAt, hk, Option.bind_some, List.getElem?_toArray, h1]
    · rw [hcn', List.getElem?_map, h2] at hkn
      exact Option.some.inj hkn

/-- The type formers of a block: a block's former records' names. -/
theorem blockFormerNames_append (a b : List ConstantInfo) :
    blockFormerNames (a ++ b) = blockFormerNames a ++ blockFormerNames b := by
  simp [blockFormerNames, List.filterMap_append]

/-- **What a block's record holds**: each type former's record; each recursor's, its rules
firing `.plain` until `blockRecords` reads them; a constructor record for each constructor a
type lists; and the formers' names are the types'. -/
theorem declOfF_ind_records {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr}
    {ts : List IndTypeRec} {cts : List IndCtorRec} {rs : List IndRecRec}
    {L1 L2 L3 : List (CEntryF Name Expr)} {p : Declaration}
    (hd : declOfF nm lv ex (.ind ts cts rs) = .ok (.inl p))
    (ht : Forall₂ (TyRes nm ex) ts L1) (hc : Forall₂ (CtorRes nm ex) cts L2)
    (hr : Forall₂ (RecRes nm ex) rs L3) :
    ∃ block nP, p = .indDecl block nP ∧
      (∀ x ∈ L1, ConstantInfo.indInfo x.cv {} ∈ block) ∧
      blockFormerNames block = L1.map (·.name) ∧
      (∀ x ∈ L3, ∀ all np ni nmo nmi rules k iu,
        x.kind = .recur all np ni nmo nmi rules k iu →
        ConstantInfo.recInfo x.cv (np + nmo + nmi + ni) (np + nmo + nmi) k
          (rules.map fun r => ⟨r.1, r.2.1, .plain, r.2.2⟩) ∈ block) ∧
      (∀ x ∈ L1, ∀ np ni all cs nn ir iu irf, x.kind = .induct np ni all cs nn ir iu irf →
        ∀ n ∈ cs, n ∈ L2.map (·.name) → ∃ y ∈ L2, y.name = n ∧
          ∃ ind cidx np' nf iu', y.kind = .ctor ind cidx np' nf iu' ∧
            ∃ T, ConstantInfo.ctorInfo y.cv np' nf T ∈ block) := by
  simp only [declOfF, bind, Except.bind] at hd
  cases hv : validateIndF nm lv ex ts cts rs with
  | error e => rw [hv] at hd; cases hd
  | ok v =>
  rw [hv] at hd
  rcases v with v | ⟨cts1, nPd⟩
  · simp [pure, Except.pure] at hd
  simp only at hd
  obtain ⟨-, -, tyN, listed, cn, htn, hl, hcn, rfl⟩ := validateIndF_inr hv
  cases hb : indBlockOfF nm lv ex ts (ctorsListed cn cts tyN listed) rs nPd with
  | error e => rw [hb] at hd; cases hd
  | ok b =>
  rw [hb] at hd
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd
  subst hd
  unfold indBlockOfF at hb
  obtain ⟨types, h1, hb⟩ := bind_ok_inv hb
  obtain ⟨ctors, h2, hb⟩ := bind_ok_inv hb
  obtain ⟨recs, h3, hb⟩ := bind_ok_inv hb
  simp only [pure, Except.pure, Except.ok.injEq] at hb
  subst hb
  have hty : types = L1.map fun x => ConstantInfo.indInfo x.cv {} := by
    rw [mapM_res (G := fun x : CEntryF Name Expr => ConstantInfo.indInfo x.cv {})
      (fun t c (h : TyRes nm ex t c) => by
        simp [cvOfF_res h.1, CEntryF.cv, bind, Except.bind, pure, Except.pure]) ht] at h1
    cases h1; rfl
  have hrecs : recs = L3.map fun x => match x.kind with
      | .recur _ np ni nmo nmi rules k _ =>
        ConstantInfo.recInfo x.cv (np + nmo + nmi + ni) (np + nmo + nmi) k
          (rules.map fun r => ⟨r.1, r.2.1, .plain, r.2.2⟩)
      | _ => default := by
    rw [mapM_res (G := fun x : CEntryF Name Expr => match x.kind with
      | .recur _ np ni nmo nmi rules k _ =>
        ConstantInfo.recInfo x.cv (np + nmo + nmi + ni) (np + nmo + nmi) k
          (rules.map fun r => ⟨r.1, r.2.1, .plain, r.2.2⟩)
      | _ => default)
      (fun t c (h : RecRes nm ex t c) => by
        obtain ⟨g, all, rules, hk, hru⟩ := h
        rw [mapM_res (G := fun r : Name × Nat × Expr => (⟨r.1, r.2.1, .plain, r.2.2⟩ : RecRule))
          (fun ru x ⟨a1, a2, a3⟩ => by simp [ruleOfF, a1, a2, a3, bind, Except.bind, pure,
            Except.pure]) hru]
        simp [hk, cvOfF_res g, CEntryF.cv, bind, Except.bind, pure, Except.pure]) hr] at h3
    cases h3; rfl
  have hctors : ∀ y ∈ ctors, ∃ cv nP nF T, y = ConstantInfo.ctorInfo cv nP nF T := by
    intro y hy
    obtain ⟨⟨c, T⟩, -, hf⟩ := mapM_ok_mem_inv h2 hy
    obtain ⟨cv, -, hf⟩ := bind_ok_inv hf
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    exact ⟨_, _, _, _, hf.symm⟩
  refine ⟨_, nPd, rfl, fun x hx => ?_, ?_, fun x hx all np ni nmo nmi rules k iu hk => ?_, ?_⟩
  · rw [hty]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))
  · rw [blockFormerNames_append, blockFormerNames_append, hty, hrecs]
    have e1 : ∀ L : List (CEntryF Name Expr),
        blockFormerNames (L.map fun x => ConstantInfo.indInfo x.cv {}) = L.map (·.name) := by
      intro L
      induction L with
      | nil => rfl
      | cons x l ih =>
        simp only [blockFormerNames, List.map_cons, List.filterMap_cons] at ih ⊢
        rw [ih]; rfl
    have e2 : blockFormerNames ctors = [] := by
      simp only [blockFormerNames, List.filterMap_eq_nil_iff]
      intro y hy
      obtain ⟨cv, nP, nF, T, rfl⟩ := hctors y hy
      rfl
    have e3 : ∀ L : List (CEntryF Name Expr), blockFormerNames (L.map fun x => match x.kind with
        | .recur _ np ni nmo nmi rules k _ =>
          ConstantInfo.recInfo x.cv (np + nmo + nmi + ni) (np + nmo + nmi) k
            (rules.map fun r => ⟨r.1, r.2.1, .plain, r.2.2⟩)
        | _ => default) = [] := by
      intro L
      simp only [blockFormerNames, List.filterMap_eq_nil_iff, List.mem_map]
      rintro y ⟨x, -, rfl⟩
      rcases x with ⟨n, l, t, k⟩
      cases k <;> rfl
    rw [e1, e2, e3]; simp
  · rw [hrecs]
    refine List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, ?_⟩)
    simp only [hk]
  · intro x hx np ni all cs nn ir iu irf hk n hn hnL
    obtain ⟨τ, hτ, hτx⟩ := Forall₂.mem_right ht x hx
    obtain ⟨g, ni', all', cs', nn', ir', irf', hk', hcs⟩ := hτx
    rw [hk] at hk'
    obtain ⟨-, -, -, rfl, -⟩ := CKindF.induct.inj hk'
    have hcn' : cn = L2.map (·.name) := by
      rw [mapM_res (F := fun (c : IndCtorRec) => nm c.cv.name) (G := CEntryF.name)
        (fun t c (h : CtorRes nm ex t c) => h.1.1) hc] at hcn
      cases hcn; rfl
    obtain ⟨ct, y, hat, hy, hry, hyn⟩ := ctorAt_of_mem hc hcn (hcn' ▸ hnL)
    have hzip : (x.name, cs) ∈ tyN.zip listed := mapM_ok_zip htn hl hτ g.1 hcs
    have hmem : (ct, x.name) ∈ ctorsListed cn cts tyN listed := by
      unfold ctorsListed
      exact List.mem_flatMap.mpr ⟨_, hzip, List.mem_map.mpr ⟨ct, List.mem_filterMap.mpr ⟨n, hn, hat⟩, rfl⟩⟩
    obtain ⟨z, hz, hfz⟩ := mapM_ok_mem h2 hmem
    obtain ⟨cv, hcv, hfz⟩ := bind_ok_inv hfz
    simp only [pure, Except.pure, Except.ok.injEq] at hfz
    obtain ⟨g2, ind, cidx, iu', hky⟩ := hry
    rw [cvOfF_res g2] at hcv
    cases hcv
    refine ⟨y, hy, hyn, ind, cidx, ct.numParams, ct.numFields, iu', hky, x.name, ?_⟩
    have hfz' : ConstantInfo.ctorInfo y.cv ct.numParams ct.numFields x.name = z := hfz
    rw [hfz']
    exact List.mem_append_left _ (List.mem_append_right _ hz)

end ConLeche.Frontend.Olean
