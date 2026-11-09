module

public import ConLeche.Verify.FastOps
public import ConLeche.Verify.ProjTele
import ConLeche.Kernel.Inductives.StructParts
import ConLeche.Verify.Cached.Erase
public import ConLeche.Verify.Level
import ConLeche.Kernel.Inductives.SumInstall

public section

/-!
# Generated projection bodies and recursors, opened

The projection bodies opened; the generated recursor opened, at one
constructor, at a constructor list, and with recursive fields.
-/

namespace ConLeche

/-!
## The projection bodies, opened

The direct install's table stores `bodies[i] = F_i[p⃗ ↦ bvars, f_j ↦
.proj T j (bvar 0)]` (`structProjBodies`: the raw domain of field `i`
instantiated in one walk at the loose parameter variables and the
earlier projections of the subject — `structProjBodies_spec`).  The
reading side opens a body at fresh variables (`projTele`'s reading),
and what it needs is the syntactic identity between that opened body
and the constructor telescope peeled at the **variables** themselves:

    instSpine (fvsD nP ++ [tfvD nP]) nP bodies[i]
      = the domain of `instPisAt (fvsD nP ++ projArgsD T i nP) cty`

(`structProjBody_open`).  It is `instSeq_instSeqLift` — the collapse
of a capture-avoiding instantiation at open arguments followed by a
closed instantiation of the ambient variables into the plain
instantiation at the already-instantiated arguments — applied to the
raw binder domain, with `instSeqLift_eq_instantiateLift` reading the
one walk as the binder-by-binder fold and `instPisAt_head` identifying
the variable peel's head domain.
-/


open Expr

/-! ## The plain peel's head (the `instantiate1` twin of
`instPisAtLift_head`) -/

theorem stripPis_instantiate1_full {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs : List Expr}
      {body : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.instantiate1 v j).stripPis k =
          some (bs', body.instantiate1 v (j + k)) ∧
        ∀ (i : Nat) (b : Expr), bs[i]? = some b →
          bs'[i]? = some (b.instantiate1 v (j + i)) := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [stripPis], fun i b hb => by simp at hb⟩
  | succ k ih =>
    intro e bs body j h
    match e, h with
    | .forallE d bo, h =>
      simp only [stripPis] at h
      cases hs : bo.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : d :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨bs', h1, h2⟩ := ih (j + 1) (by rw [hs])
        refine ⟨d.instantiate1 v j :: bs', ?_, ?_⟩
        · simp only [instantiate1, stripPis, h1,
            show j + 1 + k = j + (k + 1) from by omega, Option.map_some]
        · intro i b hbi
          rw [← hb] at hbi
          cases i with
          | zero =>
            obtain rfl : d = b := by simpa using hbi
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hbi ⊢
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h2 i b hbi

/-- The head binder of a partial plain `∀`-instantiation walk,
characterized by the raw telescope's binder list. -/
theorem instPisAt_head :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr} {mrem : Nat}
      {bs : List Expr} {body : Expr}
      {b : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      e.stripPis (args.length + (mrem + 1)) = some (bs, body) →
      bs[args.length]? = some b →
      ∃ bodyR, rest = .forallE
        (instSeq args (args.length - 1) b) bodyR := by
  intro args
  induction args with
  | nil =>
    intro e ds rest mrem bs body b h hstrip hb
    simp only [instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [show [].length + (mrem + 1) = mrem + 1 from by simp] at hstrip
    match e, hstrip with
    | .forallE d bo, hstrip =>
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis mrem with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some p =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : d :: p.1 = bs ∧ p.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        obtain rfl : d = b := by simpa using hb
        exact ⟨bo, rfl⟩
  | cons a as ih =>
    intro e ds rest mrem bs body b h hstrip hb
    match e, h with
    | .forallE d bo, h =>
      simp only [instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', rest'⟩, h', heq⟩ := h
      obtain ⟨-, rfl⟩ : d :: ds' = ds ∧ rest' = rest := by simpa using heq
      rw [show (a :: as).length + (mrem + 1) =
        (as.length + (mrem + 1)) + 1 from by simp; omega] at hstrip
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis (as.length + (mrem + 1)) with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some q =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : d :: q.1 = bs ∧ q.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        simp only [List.length_cons, List.getElem?_cons_succ] at hb
        obtain ⟨bs', hstrip', hpos⟩ :=
          stripPis_instantiate1_full (v := a) (as.length + (mrem + 1)) 0 hs
        obtain ⟨bodyR, hhead⟩ := ih (b := b.instantiate1 a as.length)
          h' hstrip'
          (by rw [hpos as.length b hb]; simp)
        exact ⟨bodyR, by rw [hhead]; rfl⟩

/-! ## Instantiation sequences at bounded cuts -/

/-- An instantiation sequence whose every cut is at or above the
subject's loose-variable bound is the identity. -/
theorem instSeq_eq_self_of_bounded :
    ∀ (args : List Expr) (t : Nat) {e : Expr} {k : Nat},
      e.looseBVarsBounded k = true → k + args.length ≤ t + 1 →
      instSeq args t e = e := by
  intro args
  induction args with
  | nil => intro t e k _ _; rfl
  | cons a as ih =>
    intro t e k hb hle
    show instSeq as (t - 1) (e.instantiate1 a t) = e
    rw [instantiate1_eq_self (looseBVarsBounded_mono
      (by simp only [List.length_cons] at hle; omega) hb)]
    exact ih (t - 1) hb (by simp only [List.length_cons] at hle; omega)

theorem instSeq_proj :
    ∀ (args : List Expr) (t : Nat) (s : Name) (j : Nat) (e : Expr),
      instSeq args t (.proj s j e) = .proj s j (instSeq args t e)
  | [], _, _, _, _ => rfl
  | a :: as, t, s, j, e => by
    show instSeq as (t - 1) (.proj s j (e.instantiate1 a t)) = _
    rw [instSeq_proj as]
    rfl

/-- A stripped telescope's binder domains are bounded at their own
depth. -/
theorem stripPis_binder_bounded :
    ∀ (k : Nat) {e : Expr} {bs : List Expr}
      {body : Expr} {j : Nat},
      e.stripPis k = some (bs, body) → e.looseBVarsBounded j = true →
      ∀ (i : Nat) (b : Expr), bs[i]? = some b →
        b.looseBVarsBounded (j + i) = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h _ i b hb
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hb
    simp at hb
  | succ k ih =>
    intro e bs body j h hb i b hbi
    match e, h with
    | .forallE ty bo, h =>
      simp only [stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hbstrip, heq⟩ := h
      obtain ⟨rfl, -⟩ : ty :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      cases i with
      | zero =>
        obtain rfl : ty = b := by simpa using hbi
        simpa using hb.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbi
        have := ih hbstrip hb.2 i b hbi
        rw [show j + 1 + i = j + (i + 1) from by omega] at this
        exact this

/-! ## The generator -/

/-- Two peels in a row are one. -/
theorem stripPis_append : ∀ (n : Nat) {e r : Expr} {ps : List Expr},
    e.stripPis n = some (ps, r) → ∀ {m : Nat} {ds : List Expr} {body : Expr},
      r.stripPis m = some (ds, body) → e.stripPis (n + m) = some (ps ++ ds, body)
  | 0, e, r, ps, h, m, ds, body, hr => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hr
  | n + 1, e, r, ps, h, m, ds, body, hr => by
    match e, h with
    | .forallE d bo, h =>
      simp only [Expr.stripPis] at h
      cases hs : bo.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ : d :: q.1 = ps ∧ q.2 = r := by cases h; exact ⟨rfl, rfl⟩
        rw [show n + 1 + m = (n + m) + 1 from by omega]
        simp only [Expr.stripPis, stripPis_append n (e := bo) (ps := q.1) (by rw [hs]) hr,
          Option.map_some, List.cons_append]

theorem structProjBodiesGo_spec (T : Name) :
    ∀ (k i : Nat) (vs : List Expr) (r : Expr) (bs : List Expr),
      structProjBodiesGo T vs k i r = some bs →
      bs.length = k ∧
      ∀ j, j < k → ∃ (ds : List Expr) (body b : Expr),
        r.stripPis (j + 1) = some (ds, body) ∧ ds[j]? = some b ∧
        bs.getD j default = b.instantiateLift
          (((List.range j).map fun jj => structProjArgP T (i + jj)).reverse ++ vs)
  | 0, i, vs, r, bs, h => by
    simp only [structProjBodiesGo, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1, i, vs, r, bs, h => by
    match r, h with
    | .forallE fdom body, h =>
      simp only [structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs', hrec, rfl⟩ := h
      obtain ⟨hlen, hrest⟩ := structProjBodiesGo_spec T k (i + 1) _ _ bs' hrec
      refine ⟨by simp [hlen], fun j hj => ?_⟩
      cases j with
      | zero => exact ⟨[fdom], body, fdom, rfl, rfl, by simp⟩
      | succ j =>
        obtain ⟨ds, body', b, hs, hb, hbj⟩ := hrest j (by omega)
        refine ⟨fdom :: ds, body', b, ?_, by simpa using hb, ?_⟩
        · simp only [Expr.stripPis, hs, Option.map_some]
        · rw [List.getD_cons_succ, hbj, List.range_succ_eq_map, List.map_cons, List.map_map,
            List.reverse_cons, List.append_assoc, Nat.add_zero, List.singleton_append]
          congr 3
          apply List.map_congr_left
          intro jj _
          simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 jj]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      exact nomatch h

/-- **The bodies are the substituted raw domains**: body `i` is the
constructor telescope's binder `nP + i`, instantiated in one walk at
the loose parameters and the first `i` subject projections, innermost
first; there is one per field. -/
theorem structProjBodies_spec {T : Name} {nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (h : structProjBodies T nP nF cty = some bodies) :
    bodies.size = nF ∧
    ∀ i, i < nF → ∃ (ds : List Expr) (body b : Expr),
      cty.stripPis (nP + i + 1) = some (ds, body) ∧ ds[nP + i]? = some b ∧
      bodies.getD i default = b.instantiateLift
        (structProjPs nP ++ (List.range i).map (structProjArgP T)).reverse := by
  unfold structProjBodies at h
  cases hr : cty.stripPis nP with
  | none => rw [hr] at h; exact nomatch h
  | some pr =>
    obtain ⟨ps, r⟩ := pr
    rw [hr] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨bs, hgo, rfl⟩ := h
    obtain ⟨hlen, hspec⟩ := structProjBodiesGo_spec T nF 0 _ r bs hgo
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    obtain ⟨ds, body, b, hs, hb, hbi⟩ := hspec i hi
    have hpsLen : ps.length = nP := stripPis_length _ hr
    refine ⟨ps ++ ds, body, b, ?_, ?_, ?_⟩
    · rw [Nat.add_assoc]; exact stripPis_append nP hr hs
    · rw [List.getElem?_append_right (by omega), hpsLen, Nat.add_sub_cancel_left]; exact hb
    · have hgetD : bs.toArray.getD i default = bs.getD i default := by
        simp [Array.getD, List.getD_eq_getElem?_getD]
        split <;> simp_all
      rw [hgetD, hbi, List.reverse_append]
      simp only [Nat.zero_add]

/-! ## The opened body -/

/-- The parameter variables, dummy-annotated (the reading ignores
annotations). -/
@[expose] def fvsD (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.fvar k (.sort .zero)

/-- The subject variable. -/
@[expose] def tfvD (nP : Nat) : Expr := Expr.fvar nP (.sort .zero)

/-- The earlier projections of the subject variable. -/
@[expose] def projArgsD (T : Name) (i nP : Nat) : List Expr :=
  (List.range i).map fun j => Expr.proj T j (tfvD nP)

theorem fvsD_length (nP : Nat) : (fvsD nP).length = nP := by simp [fvsD]

theorem projArgsD_length (T : Name) (i nP : Nat) : (projArgsD T i nP).length = i := by
  simp [projArgsD]

theorem fvsD_closed (nP : Nat) : ∀ a ∈ fvsD nP ++ [tfvD nP], a.looseBVarsBounded 0 = true := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; rfl
  · rw [List.mem_singleton] at ha; subst ha; rfl

theorem fvsD_getElem? (nP k : Nat) (hk : k < nP) :
    (fvsD nP)[k]? = some (Expr.fvar k (.sort .zero)) := by
  simp [fvsD, List.getElem?_map, List.getElem?_range hk]

/-- The loose parameter variables and projection substitutes are
bounded at the parameters and the subject. -/
theorem structProjArgs_bounded (T : Name) (nP i : Nat) :
    ∀ a ∈ structProjPs nP ++ (List.range i).map (structProjArgP T),
      a.looseBVarsBounded (nP + 1) = true := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    have := List.mem_range.mp hk
    simp only [looseBVarsBounded, decide_eq_true_eq]
    omega
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    rfl

/-- Instantiating the loose parameter variables and projection
substitutes at the variables gives the variables and their
projections. -/
theorem structProjArgs_instSeq (T : Name) (nP i : Nat) :
    (structProjPs nP ++ (List.range i).map (structProjArgP T)).map
        (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = fvsD nP ++ projArgsD T i nP := by
  have hclosed := fvsD_closed nP
  have hlen : (fvsD nP ++ [tfvD nP]).length = nP + 1 := by simp [fvsD_length]
  -- the variable at each slot
  have hget : ∀ k, k < nP + 1 →
      (fvsD nP ++ [tfvD nP])[k]? = some (Expr.fvar k (.sort .zero)) := by
    intro k hk
    rcases Nat.lt_or_ge k nP with hk' | hk'
    · rw [List.getElem?_append_left (by rw [fvsD_length]; exact hk')]
      exact fvsD_getElem? nP k hk'
    · obtain rfl : k = nP := by omega
      rw [List.getElem?_append_right (by rw [fvsD_length]; exact Nat.le_refl _),
        fvsD_length, Nat.sub_self]
      rfl
  have hbvar : ∀ j, j ≤ nP →
      instSeq (fvsD nP ++ [tfvD nP]) nP (.bvar j)
        = Expr.fvar (nP - j) (.sort .zero) := by
    intro j hj
    have := instSeq_bvar (fvsD nP ++ [tfvD nP]) nP j hclosed hj (by rw [hlen]; omega)
    rw [hget (nP - j) (by omega)] at this
    exact (Option.some.inj this).symm
  rw [List.map_append]
  congr 1
  · show (structProjPs nP).map (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = (List.range nP).map (fun k => Expr.fvar k (.sort .zero))
    unfold structProjPs
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    show instSeq (fvsD nP ++ [tfvD nP]) nP (.bvar (nP - k)) = _
    rw [hbvar (nP - k) (by omega), show nP - (nP - k) = k from by omega]
  · show ((List.range i).map (structProjArgP T)).map (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = (List.range i).map (fun j => Expr.proj T j (tfvD nP))
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    show instSeq (fvsD nP ++ [tfvD nP]) nP (.proj T j (.bvar 0)) = _
    rw [instSeq_proj, hbvar 0 (Nat.zero_le _), Nat.sub_zero]
    rfl

/-- **The body, opened at the variables, is the variable peel's
domain** (task #175 S1): instantiating body `i` at the parameter and
subject variables (the reading's opening of `projTele`) is the head
domain of the constructor telescope instantiated at the variables and
the subject's earlier projections — the fvar-side peel the readings
already know how to read. -/
theorem structProjBody_open {T : Name} {nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (h : structProjBodies T nP nF cty = some bodies)
    (hstrip : (cty.stripPis (nP + nF)).isSome = true)
    (hcl : cty.looseBVarsBounded 0 = true) {i : Nat} (hi : i < nF) :
    ∃ (cds : List Expr) (bodyC : Expr),
      Expr.instPisAt (fvsD nP ++ projArgsD T i nP) cty
        = some (cds, .forallE
            (Expr.instSpine (fvsD nP ++ [tfvD nP]) nP (bodies.getD i default)) bodyC) := by
  obtain ⟨-, hspec⟩ := structProjBodies_spec h
  obtain ⟨bs, body0, b, hs, hb, hbody⟩ := hspec i hi
  rw [← instSeqLift_eq_instantiateLift] at hbody
  have hlenB : (structProjPs nP ++ (List.range i).map (structProjArgP T)).length = nP + i := by
    simp [structProjPs]
  have hlenF : (fvsD nP ++ projArgsD T i nP).length = nP + i := by
    simp [fvsD_length, projArgsD_length]
  -- the fvar peel exists, and its head is the domain's plain sequence
  obtain ⟨⟨cds, rest⟩, hpa⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvsD nP ++ projArgsD T i nP)
      (by rw [hlenF]; exact stripPis_isSome_of_le (by omega) hstrip))
  obtain ⟨bodyC, hheadF⟩ := instPisAt_head _ (mrem := 0) hpa
    (by rw [hlenF]; exact hs) (by rw [hlenF]; exact hb)
  refine ⟨cds, bodyC, ?_⟩
  rw [hpa, hheadF, hbody, Expr.instSpine_eq_instSeq]
  -- the collapse
  have hdomB : b.looseBVarsBounded (nP + i) = true := by
    have := stripPis_binder_bounded (nP + i + 1) hs hcl (nP + i) b hb
    simpa using this
  have hcol := instSeq_instSeqLift (fvsD nP ++ [tfvD nP]) nP (fvsD_closed nP)
    (by simp [fvsD_length]) _ (structProjArgs_bounded T nP i) b
  rw [hlenB, structProjArgs_instSeq,
    instSeq_eq_self_of_bounded _ _ hdomB (by simp [fvsD_length]; omega)] at hcol
  rw [hlenB, hlenF, hcol]

/-!
## The recursor, opened

The reading side (`Model/Inductives/StructRecKit.lean`) opens a
structure recursor's telescope binder by binder as `denote` does;
the constructor telescope's residual is the `instPisAt` peel's
(`instPisAt_of_stripPis`).
-/


/-! ## The binder walks -/

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
    simp only [Level.eval, ite_eq_right this]
    omega

/-! ## The stored rules, positionally -/

/-- A stored rule is constructor `j`'s rule at right-hand side `j`. -/
theorem sumRules_getElem? :
    ∀ {ctorList : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules ctorList rhss →
      ∃ (j : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
        ctorList[j]? = some ctor ∧ rhss[j]? = some rhs ∧
        r = { ctor := ctor.1.name, nfields := ctor.2, fire := .plain, rhs := rhs }
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, c, rhs, rfl, rfl, rfl⟩
    · obtain ⟨j, ctor, rhs', hc, hr, rfl⟩ := sumRules_getElem? h
      exact ⟨j + 1, ctor, rhs', by simpa using hc, by simpa using hr, rfl⟩


/-! ## Iterated variable shifts

`Expr.shiftFromN` (`Expr.shiftFrom`, iterated): the reading of a
recursive field's index expressions moves from the constructor's own
opening to the recursor's frame by inserting the `o` extra slots just
after the parameters, which is exactly that shift. -/

/-- `Expr.shiftFrom p`, iterated `n` times: insert `n` fresh variable
slots at index `p`. -/
@[expose] def Expr.shiftFromN (p : Nat) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.shiftFrom p (Expr.shiftFromN p n e)

/-- A shift bumps a free variable at or above the cut by one. -/
theorem Expr.shiftFromN_fvar (p : Nat) :
    ∀ (n idx : Nat) (ty : Expr),
      ∃ (ty' : Expr),
        Expr.shiftFromN p n (Expr.fvar idx ty)
          = Expr.fvar (if idx < p then idx else idx + n) ty'
  | 0, idx, ty => ⟨ty, by
      show Expr.fvar idx ty = _
      by_cases h : idx < p
      · rw [ite_eq_left h]
      · rw [ite_eq_right h, Nat.add_zero]⟩
  | n + 1, idx, ty => by
    obtain ⟨ty', hn⟩ := Expr.shiftFromN_fvar p n idx ty
    by_cases h : idx < p
    · refine ⟨ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, ite_eq_left h, ite_eq_left h]
      simp only [Expr.shiftFrom, ite_eq_right (show ¬ idx ≥ p from by omega)]
    · refine ⟨Expr.shiftFrom p ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, ite_eq_right h, ite_eq_right h,
        show idx + (n + 1) = idx + n + 1 from by omega]
      simp only [Expr.shiftFrom, ite_eq_left (show idx + n ≥ p from by omega)]


end ConLeche
