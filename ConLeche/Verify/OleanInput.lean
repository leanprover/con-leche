module

public import ConLeche.OleanInput
public import ConLeche.Frontend.Prepare
public import ConLeche.Verify.IsModelRecords
public import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Driver.Provenance
public import ConLeche.Verify.Cached.Fill

/-!
# The reader's records cover the input

`closureConstants` (`ConLeche/OleanInput.lean`) is the `.olean` input as a set of records, read off
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

/-- **What a block's record holds**: each type former's record; each recursor's, its rules
firing `.plain` until `blockConstants` reads them; a constructor record for each constructor a
type lists. -/
theorem declOfF_ind_records {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr}
    {ts : List IndTypeRec} {cts : List IndCtorRec} {rs : List IndRecRec}
    {L1 L2 L3 : List (CEntryF Name Expr)} {p : Declaration}
    (hd : declOfF nm lv ex (.ind ts cts rs) = .ok (.inl p))
    (ht : Forall₂ (TyRes nm ex) ts L1) (hc : Forall₂ (CtorRes nm ex) cts L2)
    (hr : Forall₂ (RecRes nm ex) rs L3) :
    ∃ block nP, p = .indDecl block nP ∧
      (∀ x ∈ L1, ConstantInfo.indInfo x.cv {} ∈ block) ∧
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
  refine ⟨_, nPd, rfl, fun x hx => ?_, fun x hx all np ni nmo nmi rules k iu hk => ?_, ?_⟩
  · rw [hty]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))
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

/-! ## A merged constant's records among the declarations -/

/-- **`r` is stored by a record of a declaration of `ds`** (`StoredAs`), where that declaration
passes the reserved names' check. -/
@[expose] def CoveredBy (ds : Array Declaration) (r : ConstantInfo) : Prop :=
  ∃ d ∈ ds, basisNamesOk d = true → ∃ c' ∈ d.constants, StoredAs c' r

/-- A constant that is no part of a block has its declaration's records. -/
theorem entryRecords_low {c : CEntryF Name Expr} (ht : c.kind.tag < 5) :
    entryConstants c = ((declOfEntry c).map Declaration.constants).getD [] := by
  rcases c with ⟨n, l, t, k⟩
  cases k <;> first | rfl | (simp [CKindF.tag] at ht)

/-- A constant with a declaration is safe. -/
theorem declOfEntry_safe {c : CEntryF Name Expr} {d : Declaration} (h : declOfEntry c = some d) :
    c.kind.skipped = false := by
  unfold declOfEntry at h
  split at h <;> simp_all [CKindF.skipped]

/-- The emitted declaration of a safe constant is its declaration. -/
theorem entryDecl_safe {c : CEntry} (hsk : c.skipped = false) :
    entryDecl c = declOfEntry c.toCEntryF := by
  rcases c with ⟨⟨n, l, t, k⟩, u⟩
  unfold CEntry.skipped at hsk
  cases k with
  | ax b => cases b <;> simp_all [entryDecl, declOfEntry, CKindF.skipped, CEntryF.cv]
  | opaq v b => cases b <;> simp_all [entryDecl, declOfEntry, CKindF.skipped, CEntryF.cv]
  | defn v h s =>
    simp only [CKindF.skipped, bne_eq_false_iff_eq] at hsk
    subst hsk
    cases h <;> rfl
  | quot q =>
    simp only [entryDecl, declOfEntry, CEntryF.cv]
    split <;> simp_all
  | _ => rfl

/-- A statement record is stored by a theorem of its statement. -/
theorem stmt_storedAs {cv : ConstantVal} {r : ConstantInfo}
    (h : r = .thmInfo cv ∨ r = .axiomInfo cv) : StoredAs (.thmInfo cv) r := by
  unfold StoredAs
  rcases h with rfl | rfl <;> refine ⟨rfl, ?_, ?_, ?_⟩ <;> intros <;> contradiction

/-- **A constant that is no part of a block has its records among the declarations'**, the
merged copy's: the constant's own, or a theorem's of its statement. -/
theorem covers_entry {mg : Merged} {ds : Array Declaration} (F : MergeFacts mg ds) {e' : CEntry}
    {c : CEntryF Name Expr} (he : mg.map[c.name]? = some e') (hst : EntryStands e' c)
    (ht : c.kind.tag < 5) {r : ConstantInfo} (hr : r ∈ entryConstants c) : CoveredBy ds r := by
  rw [entryRecords_low ht] at hr
  cases hdc : declOfEntry c with
  | none => rw [hdc] at hr; cases hr
  | some dc =>
  rw [hdc] at hr
  simp only [Option.map_some, Option.getD_some] at hr
  have hsafe := declOfEntry_safe hdc
  have hmo : c.name ∈ mg.order := (F.order _).2 (contains_of_getElem he)
  rcases hst with hec | ⟨hcv, he2, hc2⟩
  · have hsk : e'.skipped = false := by
      unfold CEntry.skipped; rw [hec]; exact hsafe
    have ht' : e'.kind.tag < 5 := by
      have : e'.kind = c.kind := by rw [← hec]
      rw [this]; exact ht
    obtain ⟨p, hp, hpd⟩ := Driver.declsOf_entry F.names F.order F.decls F.blocks hmo he hsk ht'
    rw [entryDecl_safe hsk, hec, hdc] at hp
    cases hp
    exact ⟨dc, hpd, fun _ => ⟨r, hr, StoredAs.refl r⟩⟩
  · cases hk : e'.kind with
    | thm v a =>
      have hsk : e'.skipped = false := by
        unfold CEntry.skipped; rw [hk]; rfl
      obtain ⟨p, hp, hpd⟩ := Driver.declsOf_entry F.names F.order F.decls F.blocks hmo he hsk
        (by rw [hk]; simp [CKindF.tag])
      rw [entryDecl_safe hsk] at hp
      have hp' : declOfEntry e'.toCEntryF = some (.thmDecl e'.toCEntryF.cv v) := by
        simp only [declOfEntry, hk]
      rw [hp'] at hp
      cases hp
      refine ⟨_, hpd, fun hb => ⟨.thmInfo e'.toCEntryF.cv, List.mem_singleton_self _, ?_⟩⟩
      rw [hcv]
      apply stmt_storedAs
      rcases c with ⟨n, l, t, k⟩
      simp only at hc2
      rcases hc2 with hc2 | rfl
      · cases k with
        | thm v' a' =>
          simp only [declOfEntry, Option.some.injEq] at hdc
          subst hdc
          simp only [Declaration.constants, List.mem_singleton] at hr
          exact .inl hr
        | _ => simp [CKindF.tag] at hc2
      · simp only [declOfEntry, Option.some.injEq] at hdc
        subst hdc
        simp only [basisNamesOk, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.contains_eq_mem, decide_eq_false_iff_not] at hb
        have hn : n = e'.toCEntryF.cv.name := by
          rw [hcv]; rfl
        simp only [Declaration.constants, CEntryF.cv] at hr
        by_cases hq : n = quotSoundName
        · exfalso; apply hb
          rw [← hn, hq]
          simp [reservedBasisNames]
        · by_cases hs : n = sorryAxName
          · exfalso
            rw [hs] at hr
            simp only [show sorryAxName ≠ quotSoundName by decide, ↓reduceIte,
              List.not_mem_nil] at hr
          · simp only [hq, hs, ↓reduceIte, List.mem_singleton] at hr
            exact .inr hr
    | _ => rw [hk] at he2; simp [CKindF.tag] at he2

/-- A constructor the merge's blocks take is stored under its name. -/
theorem mem_blockCtors_stored {mg : Merged} (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    {tys : List CEntry} {z : CEntry} (hz : z ∈ blockCtors mg tys) : mg.map[z.name]? = some z := by
  obtain ⟨t, -, hz⟩ := List.mem_flatMap.mp hz
  split at hz
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hz
    rw [hN w z hw]; exact hw
  · cases hz

/-- The type formers a block's names list are those names. -/
theorem blockTys_names {mg : Merged} (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n) :
    ∀ {l : List Name}, (∀ x ∈ l, ∃ m, mg.map[x]? = some m ∧ m.kind.tag = 5) →
      (((l.filterMap (mg.map[·]?)).filter (·.kind.tag == 5)).map (·.toCEntryF)).map (·.name) = l
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨m, hm, ht⟩ := h x List.mem_cons_self
    simp only [List.filterMap_cons, hm, List.filter_cons, ht, beq_self_eq_true, ↓reduceIte,
      List.map_cons]
    rw [blockTys_names hN (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rw [show m.toCEntryF.name = x from hN x m hm]

/-- **A block member's record is in its block's record**: a type former as `indInfo`, a
constructor at its parameter count, a recursor with its rules firing against the block's type
formers, which are its `all`. -/
theorem covers_block {mg : Merged} {ds : Array Declaration} (F : MergeFacts mg ds) {e' : CEntry}
    (he : mg.map[e'.name]? = some e') (ht : 5 ≤ e'.kind.tag) {r : ConstantInfo}
    (hr : r ∈ entryConstants e'.toCEntryF) : ∃ d ∈ ds, ∃ c' ∈ d.constants, StoredAs c' r := by
  have hG := blocksOk_good F.blocks F.order
  -- a member of a block's record has its record in the block's records
  have inRecs : ∀ {block nP c}, c ∈ block → (∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules) →
      c ∈ (Declaration.indDecl block nP).constants := fun hc _ => hc
  have tysMem : ∀ {all : List Name} {x : Name} {m : CEntry}, x ∈ all → mg.map[x]? = some m →
      m.kind.tag = 5 → m.toCEntryF ∈ ((blockTys mg all).filter (·.kind.tag == 5)).map (·.toCEntryF) :=
    fun hx hm ht5 => List.mem_map_of_mem (List.mem_filter.mpr
      ⟨List.mem_filterMap.mpr ⟨_, hx, hm⟩, by simp [ht5]⟩)
  cases hk : e'.kind with
  | induct np ni all cs nn ir iu irf =>
    cases iu
    rotate_left
    · simp [entryConstants, hk, declOfEntry] at hr
    have hsk : e'.skipped = false := by unfold CEntry.skipped; rw [hk]; rfl
    have hI : IsInd e' all cs := ⟨np, ni, nn, ir, false, irf, hk⟩
    obtain ⟨p, hp, ts, cts, rs, hdp, h1, h2, h3⟩ :=
      home_group hG F.names F.order F.nodup F.decls he hI hsk
    obtain ⟨block, nP, rfl, hT, -, -⟩ :=
      declOfF_ind_records hdp (tys_res h1) (ctors_res h2) (recs_res h3)
    have hr' : r = .indInfo e'.toCEntryF.cv {} := by
      simpa [entryConstants, hk] using hr
    subst hr'
    refine ⟨_, hp, _, inRecs (hT _ (tysMem (hG.ind he hI).1 he (by rw [hk]; rfl)))
      (fun _ _ _ _ _ h => nomatch h), StoredAs.refl _⟩
  | ctor ind cidx np nf iu =>
    cases iu
    rotate_left
    · simp [entryConstants, hk, declOfEntry] at hr
    have hr' : r = .ctorInfo e'.toCEntryF.cv np nf ind := by
      simpa [entryConstants, hk] using hr
    subst hr'
    obtain ⟨m, all, cs, hm, hmI, hncs⟩ := hG.ctor he ⟨cidx, np, nf, false, hk⟩
    obtain ⟨hind, -, hcsm⟩ := hG.ind hm hmI
    obtain ⟨m', hm', -, hsm⟩ := hcsm _ hncs
    rw [he] at hm'; cases hm'
    have hsk : m.skipped = false := by
      rw [← hsm]; unfold CEntry.skipped; rw [hk]; rfl
    obtain ⟨p, hp, ts, cts, rs, hdp, h1, h2, h3⟩ :=
      home_group hG F.names F.order F.nodup F.decls hm hmI hsk
    obtain ⟨block, nP, rfl, -, -, hC⟩ :=
      declOfF_ind_records hdp (tys_res h1) (ctors_res h2) (recs_res h3)
    obtain ⟨mnp, mni, mnn, mir, miu, mirf, hmk⟩ := hmI
    have hmT : m.toCEntryF ∈ ((blockTys mg all).filter (·.kind.tag == 5)).map (·.toCEntryF) :=
      tysMem hind hm (by rw [hmk]; rfl)
    have heC : e' ∈ blockCtors mg (blockTys mg all) := by
      refine List.mem_flatMap.mpr ⟨m, List.mem_filterMap.mpr ⟨_, hind, hm⟩, ?_⟩
      simp only [hmk]
      exact List.mem_filterMap.mpr ⟨_, hncs, he⟩
    have heL : e'.name ∈ (((blockCtors mg (blockTys mg all)).filter (·.kind.tag == 6)).map
        (·.toCEntryF)).map (·.name) :=
      List.mem_map.mpr ⟨e'.toCEntryF, List.mem_map_of_mem (List.mem_filter.mpr
        ⟨heC, by simp [hk, CKindF.tag]⟩), rfl⟩
    obtain ⟨y, hy, hyn, ind', cidx', np', nf', iu', hyk, T, hyb⟩ :=
      hC _ hmT mnp mni all cs mnn mir miu mirf hmk e'.name hncs heL
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hzs := mem_blockCtors_stored F.names (List.mem_filter.mp hz).1
    have hzn : z.name = e'.name := hyn
    rw [hzn, he] at hzs
    cases hzs
    rw [hk] at hyk
    obtain ⟨-, -, rfl, rfl, -⟩ := CKindF.ctor.inj hyk
    refine ⟨_, hp, _, inRecs hyb (fun _ _ _ _ _ h => nomatch h), ?_⟩
    unfold StoredAs
    refine ⟨rfl, ?_, ?_, fun cvj cnP nF T' h => by cases h; exact ⟨_, _, rfl⟩⟩ <;> intros <;>
      contradiction
  | recur all np ni nmo nmi rules k iu =>
    cases iu
    rotate_left
    · simp [entryConstants, hk, declOfEntry] at hr
    obtain ⟨t, rest, m, cs, hall, hm, hmI, hsm⟩ := hG.recur he ⟨np, ni, nmo, nmi, rules, k, false, hk⟩
    have hsk : m.skipped = false := by
      rw [hsm]; unfold CEntry.skipped; rw [hk]; rfl
    obtain ⟨p, hp, ts, cts, rs, hdp, h1, h2, h3⟩ :=
      home_group hG F.names F.order F.nodup F.decls hm hmI hsk
    obtain ⟨block, nP, rfl, -, hR, -⟩ :=
      declOfF_ind_records hdp (tys_res h1) (ctors_res h2) (recs_res h3)
    have heR : e' ∈ blockRecs mg (recMapOf mg) t := by
      rw [blockRecs_order mg F.nodup t]
      refine List.mem_filterMap.mpr ⟨e'.name, List.mem_filter.mpr ⟨?_, ?_⟩, he⟩
      · exact Array.mem_toList_iff.mpr ((F.order _).2 (contains_of_getElem he))
      · simp [he, recUnder, hk, hall]
    have hrb := hR e'.toCEntryF (List.mem_map_of_mem (List.mem_filter.mpr
      ⟨heR, by simp [hk, CKindF.tag]⟩)) all np ni nmo nmi rules k false hk
    refine ⟨_, hp, _, hrb, ?_⟩
    have hr' : r = .recInfo e'.toCEntryF.cv (np + nmo + nmi + ni) (np + nmo + nmi) k
        (rules.map fun (cn, nf, rhs) => { ctor := cn, nfields := nf, fire := .plain, rhs }) := by
      simpa [entryConstants, hk] using hr
    subst hr'
    have hrules : (rules.map fun r => (⟨r.1, r.2.1, .plain, r.2.2⟩ : RecRule)) =
        rules.map fun (cn, nf, rhs) => { ctor := cn, nfields := nf, fire := .plain, rhs } := by
      apply List.map_congr_left
      rintro ⟨cn, nf, rhs⟩ -
      rfl
    rw [← hrules]
    exact StoredAs.refl _
  | _ => rw [hk] at ht; simp [CKindF.tag] at ht

/-! ## The closure's records -/

/-- **Every record of the closure is stored by a record the reader read** (where that record
passes the reserved names' check). -/
theorem readOleansAt_covers {sp : Roots} (hsp : sp.bare = sp) {roots : Array Name} {jobs : Nat}
    {pace : Pace} {lenient homes : Bool} {fs : FS} {rd : OleanRead} {hs hs' : HS}
    (h : (readOleansAt sp roots none jobs pace lenient homes : ModelIO _) fs hs (.ok (.ok rd)) hs')
    {r : ConstantInfo} (hr : closureConstants sp fs roots r) : CoveredBy rd.decls r := by
  obtain ⟨mg, F, hentry⟩ := readOleansAt_entry hsp h
  obtain ⟨m, hcl, f, d, c, hf, hd, hc, hrc⟩ := hr
  obtain ⟨e', he, hst⟩ := hentry hcl ⟨f, hf, hd⟩ hc
  by_cases ht : c.kind.tag < 5
  · exact covers_entry F he hst ht hrc
  · have hec : e'.toCEntryF = c := by
      rcases hst with hec | ⟨-, -, hc2⟩
      · exact hec
      · exfalso; apply ht
        rcases hc2 with hc2 | hc2 <;> rw [hc2] <;> decide
    subst hec
    obtain ⟨d', hd', c', hc', hst'⟩ := covers_block F he (by omega) hrc
    exact ⟨d', hd', fun _ => ⟨c', hc', hst'⟩⟩

/-- **An accepted read of a closure stores its input**: the fold accepted the reader's records,
prepared with a prelude and with the theorems' values in place, so every record of every
constant of the closure's views is stored as `StoredAs` says. -/
theorem checkDecls_inputStored {sp : Roots} (hsp : sp.bare = sp) {roots : Array Name}
    {jobs : Nat} {pace : Pace} {lenient homes : Bool} {fs : FS} {rd : OleanRead} {hs hs' : HS}
    (h : (readOleansAt sp roots none jobs pace lenient homes : ModelIO _) fs hs (.ok (.ok rd)) hs')
    {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat} {pre : PreludeIx}
    {used : Declaration → Array Name} {F : Expr → Expr} {env : Env}
    (hc : Cached.checkDecls mode pins maxNatSize
      ((prepareD pre rd.decls used).decls.map (Cached.fillDecl F)) = .ok env) :
    RecordsStored (closureConstants sp fs roots) env := by
  have hst := Cached.checkDecls_recordsStored hc
  obtain ⟨n, fe, run, -⟩ := Cached.checkDecls_run mode hc
  have hb := Cached.declsRun_basisNamesOk run
  have hrec : ∀ d, (Cached.fillDecl F d).constants = d.constants := by intro d; cases d <;> rfl
  have hbn : ∀ d, basisNamesOk (Cached.fillDecl F d) = basisNamesOk d := by
    intro d; cases d <;> rfl
  have hmem : ∀ {d}, d ∈ (prepareD pre rd.decls used).decls →
      Cached.fillDecl F d ∈ ((prepareD pre rd.decls used).decls.map (Cached.fillDecl F)).toList :=
    fun hd => Array.mem_toList_iff.mpr (Array.mem_map_of_mem hd)
  refine hst.mono fun r hr => ?_
  obtain ⟨d, hd, hcov⟩ := readOleansAt_covers hsp h hr
  have hd' := hmem (Frontend.mem_prepareD (used := used) (pre := pre) hd)
  obtain ⟨c', hc', hs⟩ := hcov (hbn d ▸ hb _ hd')
  exact ⟨c', mem_constantsOf.2 ⟨_, hd', (hrec d).symm ▸ hc'⟩, hs⟩
end ConLeche.Frontend.Olean
