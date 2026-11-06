module

public import ConLeche.Model.Modular.Read

public section

/-!
# A context and its sources: what they read alike

The first part of `ctxModel` (`Model/Modular/Restrict.lean`).  `CtxSrc` bundles a context read
from its sources (`CtxRead`) with the sources' models and the context's leaves `aC`, which are the
sources' leaves on every name read alike.  This file proves what the two sides agree on: a name
read alike is stored on both sides, with the same level parameters, and an inductive kind is
stored identically; its table and projections are the same; the literal guards agree where their
names are read alike; and so (`CtxSrc.denote_eq`) a term all of whose names are read alike
(`constsResolve` at `R n`) reads alike, at the context's leaves and at its source's.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term

universe w

/-! ## Alike copies and the literal guards -/

theorem Alike.lps {a b : ConstantInfo} (h : Alike a b) :
    a.toConstantVal.levelParams = b.toConstantVal.levelParams := by rw [h.cv]

theorem Alike.natIndOk {a b : ConstantInfo} (h : Alike a b) :
    natIndOk (some a) = natIndOk (some b) := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · rfl
  · cases a <;> cases b <;> simp_all [ConstantInfo.isStmtKind, ConLeche.natIndOk]

theorem Alike.natZeroOk {a b : ConstantInfo} (h : Alike a b) :
    natZeroOk (some a) = natZeroOk (some b) := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · rfl
  · cases a <;> cases b <;> simp_all [ConstantInfo.isStmtKind, ConLeche.natZeroOk]

theorem Alike.natSuccOk {a b : ConstantInfo} (h : Alike a b) :
    natSuccOk (some a) = natSuccOk (some b) := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · rfl
  · cases a <;> cases b <;> simp_all [ConstantInfo.isStmtKind, ConLeche.natSuccOk]

/-- **Two lookups with alike copies**, the shape every guard reads. -/
@[expose] def LookAlike (f g : Option ConstantInfo) : Prop :=
  ∃ a b, f = some a ∧ g = some b ∧ Alike a b

theorem LookAlike.cv {f g : Option ConstantInfo} (h : LookAlike f g) :
    f.map (·.toConstantVal) = g.map (·.toConstantVal) := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  simp [h.cv]

/-- A guard that reads only the copy's constant value agrees on alike lookups. -/
theorem LookAlike.of_cv {f g : Option ConstantInfo} (h : LookAlike f g)
    (ok : Option ConstantInfo → Bool)
    (hok : ∀ a b : ConstantInfo, a.toConstantVal = b.toConstantVal → ok (some a) = ok (some b)) :
    ok f = ok g := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  exact hok a b h.cv

theorem natLitSupported_alike {C E : Env}
    (hN : LookAlike (C.find? natName) (E.find? natName))
    (hZ : LookAlike (C.find? natZeroName) (E.find? natZeroName))
    (hS : LookAlike (C.find? natSuccName) (E.find? natSuccName)) :
    natLitSupported C = natLitSupported E := by
  obtain ⟨a1, b1, e1, f1, h1⟩ := hN
  obtain ⟨a2, b2, e2, f2, h2⟩ := hZ
  obtain ⟨a3, b3, e3, f3, h3⟩ := hS
  unfold natLitSupported
  rw [e1, e2, e3, f1, f2, f3, h1.natIndOk, h2.natZeroOk, h3.natSuccOk]

theorem strLitSupported_alike {C E : Env}
    (hN : LookAlike (C.find? natName) (E.find? natName))
    (hZ : LookAlike (C.find? natZeroName) (E.find? natZeroName))
    (hS : LookAlike (C.find? natSuccName) (E.find? natSuccName))
    (h1 : LookAlike (C.find? stringName) (E.find? stringName))
    (h2 : LookAlike (C.find? stringOfListName) (E.find? stringOfListName))
    (h3 : LookAlike (C.find? listName) (E.find? listName))
    (h4 : LookAlike (C.find? listNilName) (E.find? listNilName))
    (h5 : LookAlike (C.find? listConsName) (E.find? listConsName))
    (h6 : LookAlike (C.find? charName) (E.find? charName))
    (h7 : LookAlike (C.find? charOfNatName) (E.find? charOfNatName)) :
    strLitSupported C = strLitSupported E := by
  unfold strLitSupported
  rw [natLitSupported_alike hN hZ hS,
    h1.of_cv stringTyOk (fun a b h => by simp only [stringTyOk, h]),
    h2.of_cv stringOfListTyOk (fun a b h => by simp only [stringOfListTyOk, h]),
    h3.of_cv listTyOk (fun a b h => by simp only [listTyOk, h]),
    h4.of_cv listNilTyOk (fun a b h => by simp only [listNilTyOk, h]),
    h5.of_cv listConsTyOk (fun a b h => by simp only [listConsTyOk, h]),
    h6.of_cv charTyOk (fun a b h => by simp only [charTyOk, h]),
    h7.of_cv charOfNatTyOk (fun a b h => by simp only [charOfNatTyOk, h])]

theorem levelParamsAt_alike {C E : Env} {x : Name} (h : LookAlike (C.find? x) (E.find? x)) :
    levelParamsAt C x = levelParamsAt E x := by
  obtain ⟨a, b, e, f, h⟩ := h
  unfold levelParamsAt
  rw [e, f]
  exact h.lps

theorem isSome_of {C : Env} {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    (C.find? n).isSome = true := by rw [hf]; rfl

/-! ## The bundle -/

/-- **A context, read from its sources' models** (see the module docstring). -/
structure CtxSrc (V : Type w) [SetTheory V] (C : Env) (E R : Name → Env)
    (aC : Name → (Name → Nat) → Term) where
  read : CtxRead C E R
  /-- each source's model -/
  m : (n : Name) → EnvModelM V (E n)
  cover : ∀ n, LfpCover (m n) []
  eta : ∀ n, EtaFamiliesClosed (E n)
  nat : ∀ n, NatFacts (E n)
  /-- the sources' recorded telescopes were reduced at a part of them -/
  ran : ∀ n, FamilyRan (m n)
  /-- **a former read alike whose stored type does not show its telescope reduces at the
  context as at its source**, and the reduct is read alike.  Explicit: the refinement
  monotonicity of reduction (task #469) is to discharge it -/
  defh : ∀ n T cv caps, (C.find? n).isSome = true → ((R n).find? T).isSome = true →
    C.find? T = some (.indInfo cv caps) → formerDefHeaded cv = true →
    ∀ F f, reducedFormer (fueledOps .verified F) (E n) cv (caps.nparams + caps.nIdx) = .ok f →
      f.type.constsResolve (R n) = true ∧
      ∃ F', reducedFormer (fueledOps .verified F') C cv (caps.nparams + caps.nIdx) = .ok f
  /-- the context's leaf at a name read alike is its source's -/
  leaf : ∀ n, (C.find? n).isSome = true → ∀ d, ((R n).find? d).isSome = true →
    aC d = (m n).base2.acval d
  closed : ∀ n ψ, Term.Closed (aC n ψ)
  wd : ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (aC n ψ)

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-! ## Lookups -/

theorem storedC {n d : Name} (h : ((R n).find? d).isSome = true) :
    (C.find? d).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  exact (S.read.R_sub n d ci hci).2

theorem storedE {n d : Name} (h : ((R n).find? d).isSome = true) :
    ((E n).find? d).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  rw [(S.read.R_sub n d ci hci).1]; rfl

/-- A stored name is read alike from its own source. -/
theorem selfR {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ((R n).find? n).isSome = true := S.read.self n (isSome_of hf)

/-- A name read alike has alike copies. -/
theorem look {n d : Name} (hn : (C.find? n).isSome = true) (hd : ((R n).find? d).isSome = true) :
    LookAlike (C.find? d) ((E n).find? d) := by
  obtain ⟨a, b, h1, h2, h3⟩ := S.read.alike n d hn hd
  exact ⟨a, b, h1, h2, h3⟩

/-- **An inductive kind read alike is the source's**, from the context's side. -/
theorem findE {n d : Name} (hn : (C.find? n).isSome = true) (hd : ((R n).find? d).isSome = true)
    {ci : ConstantInfo} (hf : C.find? d = some ci) (hk : ci.isIndKind = true) :
    (E n).find? d = some ci := by
  obtain ⟨a, b, h1, h2, h3⟩ := S.read.alike n d hn hd
  rw [hf] at h1
  obtain rfl := Option.some.inj h1
  rw [h2, h3.eq_of_indKind (.inl hk)]

/-- ... and from the source's side. -/
theorem findC {n d : Name} (hn : (C.find? n).isSome = true) (hd : ((R n).find? d).isSome = true)
    {ci : ConstantInfo} (hf : (E n).find? d = some ci) (hk : ci.isIndKind = true) :
    C.find? d = some ci := by
  obtain ⟨a, b, h1, h2, h3⟩ := S.read.alike n d hn hd
  rw [hf] at h2
  obtain rfl := Option.some.inj h2
  rw [h1, h3.eq_of_indKind (.inr hk)]

/-- The context's copy of a stored name and its source's. -/
theorem src {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ∃ ci', (E n).find? n = some ci' ∧ Refines ci ci' := S.read.entry n ci hf

/-- **A stored constant of a kind never presented as a statement is its source's.** -/
theorem src_eq {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci)
    (hk : ∀ cv, ci ≠ .axiomInfo cv) : (E n).find? n = some ci := by
  obtain ⟨ci', hf', h | ⟨h, -⟩⟩ := S.src hf
  · rw [hf', h]
  · exact absurd h (hk _)

theorem src_ind {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci)
    (hk : ci.isIndKind = true) : (E n).find? n = some ci :=
  S.src_eq hf fun cv h => by subst h; simp [ConstantInfo.isIndKind] at hk

/-- A table of a name read alike is its source's. -/
theorem table_eq {n d : Name} (hn : (C.find? n).isSome = true)
    (hd : ((R n).find? d).isSome = true) : C.findTable? d = (E n).findTable? d :=
  S.read.table n d hn hd

theorem findProj_eq {n d : Name} (hn : (C.find? n).isSome = true)
    (hd : ((R n).find? d).isSome = true) (i : Nat) :
    C.findProj? d i = (E n).findProj? d i := by
  unfold Env.findProj?
  rw [S.table_eq hn hd]

/-! ## The agreement of readings -/

/-- **A term read alike reads alike** (see the module docstring). -/
theorem denote_eq {n : Name} (hn : (C.find? n).isSome = true) (ψ : Name → Nat) :
    ∀ (d : Nat) (e : Expr), e.constsResolve (R n) = true →
      denote aC C ψ d e = denote (S.m n).base2.acval (E n) ψ d e := by
  have hl := S.leaf n hn
  intro d e
  induction d, e using denote.induct (env := C) with
  | case1 d u => intro _; rw [denote, denote]
  | case2 d idx ty => intro _; rw [denote, denote]
  | case3 d x us ci hf hlen =>
    intro hc
    simp only [Expr.constsResolve] at hc
    obtain ⟨a, b, h1, h2, h3⟩ := S.look hn hc
    rw [hf] at h1
    obtain rfl := Option.some.inj h1
    rw [denote, hf, denote, h2]
    dsimp only
    rw [ite_eq_left hlen, ite_eq_left (h3.lps ▸ hlen), h3.lps, hl x hc]
  | case4 d x us ci hf hlen =>
    intro hc
    simp only [Expr.constsResolve] at hc
    obtain ⟨a, b, h1, h2, h3⟩ := S.look hn hc
    rw [hf] at h1
    obtain rfl := Option.some.inj h1
    rw [denote, hf, denote, h2]
    dsimp only
    rw [ite_eq_right hlen, ite_eq_right (fun h => hlen (h3.lps ▸ h))]
  | case5 d x us hf =>
    intro hc
    simp only [Expr.constsResolve] at hc
    have := S.storedC hc
    rw [hf] at this
    exact nomatch this
  | case6 d ty body ihty ihbody =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    rw [denote, denote, ihty hc.1, ihbody (Expr.constsResolve_instantiate1 hc.1 0 hc.2)]
  | case7 d ty body ihty ihbody =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    rw [denote, denote, ihty hc.1, ihbody (Expr.constsResolve_instantiate1 hc.1 0 hc.2)]
  | case8 d f a ihf iha =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    rw [denote, denote, ihf hc.1, iha hc.2]
  | case9 d ty val body ihty ihv ihbody =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    rw [denote, denote, ihty hc.1.1, ihv hc.1.2,
      ihbody (Expr.constsResolve_instantiate1 hc.1.1 0 hc.2)]
  | case10 d sn i e ihe =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    rw [denote, denote, ihe hc.2, S.findProj_eq hn hc.1 i]
  | case11 d k hsup =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hg := natLitSupported_alike (S.look hn hc.1.1) (S.look hn hc.1.2) (S.look hn hc.2)
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hg ▸ hsup), hl _ hc.1.2, hl _ hc.2]
  | case12 d k hsup =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hg := natLitSupported_alike (S.look hn hc.1.1) (S.look hn hc.1.2) (S.look hn hc.2)
    rw [denote, ite_eq_right hsup, denote, ite_eq_right (fun h => hsup (hg.trans h))]
  | case13 d s hsup =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hZ⟩, hS⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    have hg := strLitSupported_alike (S.look hn hN) (S.look hn hZ) (S.look hn hS)
      (S.look hn h1) (S.look hn h2) (S.look hn h3) (S.look hn h4) (S.look hn h5)
      (S.look hn h6) (S.look hn h7)
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hg ▸ hsup),
      levelParamsAt_alike (S.look hn h4), levelParamsAt_alike (S.look hn h5),
      hl _ h2, hl _ h4, hl _ h5, hl _ h6, hl _ h7, hl _ hZ, hl _ hS]
  | case14 d s hsup =>
    intro hc
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hZ⟩, hS⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    have hg := strLitSupported_alike (S.look hn hN) (S.look hn hZ) (S.look hn hS)
      (S.look hn h1) (S.look hn h2) (S.look hn h3) (S.look hn h4) (S.look hn h5)
      (S.look hn h6) (S.look hn h7)
    rw [denote, ite_eq_right hsup, denote, ite_eq_right (fun h => hsup (hg.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end CtxSrc

end ConLeche.Model.Modular
