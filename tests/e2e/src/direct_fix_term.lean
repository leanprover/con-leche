--#export Term'.elim_var Term'.elim_func Term'.size_func CofixA'.elim_continue CofixA'.elim_intro CofixA'.head_intro Lam'.elim_read Lam'.elim_write Lam'.elim_halt

/-! Task #202 Stage B: `Type`-valued REFLEXIVE blocks with several
constructors — the first-order-term-shaped `Term' F α` (a data field
`n` whose value is the DOMAIN of the reflexive field's telescope, `Fin n
→ Term' F α`, beside an ordinary constructor), the `PFunctor.Approx.
CofixA`-shaped INDEXED family `CofixA' A B n` (a reflexive field at
the predecessor index) and the `Turing.PartrecToTM2.Λ'`-shaped `Lam'`
(reflexive and finitary fields mixed across constructors).  Consumers
eliminate into `Type` and fire iota by `rfl`. -/

inductive Term' (F : Nat → Type) (α : Type) : Type where
  | var (a : α) : Term' F α
  | func (n : Nat) (f : F n) (ts : Fin n → Term' F α) : Term' F α

noncomputable def Term'.elim {F : Nat → Type} {α : Type} {C : Term' F α → Type}
    (hv : ∀ a, C (Term'.var a)) (hf : ∀ n f ts, (∀ i, C (ts i)) → C (Term'.func n f ts))
    (t : Term' F α) : C t :=
  Term'.rec (motive := fun t => C t) hv (fun n f ts ih => hf n f ts ih) t

theorem Term'.elim_var {F : Nat → Type} {α : Type} {C : Term' F α → Type}
    (hv : ∀ a, C (Term'.var a)) (hf : ∀ n f ts, (∀ i, C (ts i)) → C (Term'.func n f ts)) (a : α) :
    Term'.elim hv hf (Term'.var a) = hv a := rfl

theorem Term'.elim_func {F : Nat → Type} {α : Type} {C : Term' F α → Type}
    (hv : ∀ a, C (Term'.var a)) (hf : ∀ n f ts, (∀ i, C (ts i)) → C (Term'.func n f ts))
    (n : Nat) (f : F n) (ts : Fin n → Term' F α) :
    Term'.elim hv hf (Term'.func n f ts) = hf n f ts (fun i => Term'.elim hv hf (ts i)) := rfl

/-- The number of function symbols along the first argument. -/
noncomputable def Term'.size {F : Nat → Type} {α : Type} (t : Term' F α) : Nat :=
  Term'.rec (motive := fun _ => Nat) (fun _ => 0)
    (fun n _ _ ih => match n with
      | 0 => 1
      | m + 1 => Nat.succ (ih ⟨0, Nat.zero_lt_succ m⟩)) t

theorem Term'.size_func {F : Nat → Type} {α : Type} (m : Nat) (f : F (m + 1))
    (ts : Fin (m + 1) → Term' F α) :
    Term'.size (Term'.func (m + 1) f ts) = Nat.succ (Term'.size (ts ⟨0, Nat.zero_lt_succ m⟩)) := rfl

inductive CofixA' (A : Type) (B : A → Type) : Nat → Type where
  | continue : CofixA' A B 0
  | intro (n : Nat) (a : A) (f : B a → CofixA' A B n) : CofixA' A B (n + 1)

noncomputable def CofixA'.elim {A : Type} {B : A → Type} {C : ∀ n, CofixA' A B n → Type}
    (hc : C 0 CofixA'.continue)
    (hi : ∀ n a f, (∀ b, C n (f b)) → C (n + 1) (CofixA'.intro n a f))
    {n : Nat} (x : CofixA' A B n) : C n x :=
  CofixA'.rec (motive := fun n x => C n x) hc (fun n a f ih => hi n a f ih) x

theorem CofixA'.elim_continue {A : Type} {B : A → Type} {C : ∀ n, CofixA' A B n → Type}
    (hc : C 0 CofixA'.continue)
    (hi : ∀ n a f, (∀ b, C n (f b)) → C (n + 1) (CofixA'.intro n a f)) :
    CofixA'.elim hc hi CofixA'.continue = hc := rfl

theorem CofixA'.elim_intro {A : Type} {B : A → Type} {C : ∀ n, CofixA' A B n → Type}
    (hc : C 0 CofixA'.continue)
    (hi : ∀ n a f, (∀ b, C n (f b)) → C (n + 1) (CofixA'.intro n a f))
    (n : Nat) (a : A) (f : B a → CofixA' A B n) :
    CofixA'.elim hc hi (CofixA'.intro n a f) = hi n a f (fun b => CofixA'.elim hc hi (f b)) := rfl

/-- The root's label at a positive index (a constant motive over the index). -/
noncomputable def CofixA'.head {A : Type} {B : A → Type} {n : Nat} (x : CofixA' A B (n + 1)) : A :=
  CofixA'.rec (motive := fun n _ => match n with | 0 => Unit | _ + 1 => A) () (fun _ a _ _ => a) x

theorem CofixA'.head_intro {A : Type} {B : A → Type} (n : Nat) (a : A) (f : B a → CofixA' A B n) :
    CofixA'.head (CofixA'.intro n a f) = a := rfl

inductive Lam' : Type where
  | halt : Lam'
  | write (b : Bool) (k : Lam') : Lam'
  | read (f : Bool → Lam') : Lam'
  | branch (b : Bool) (l : Lam') (r : Lam') : Lam'
  | loop (f : Nat → Lam') (k : Lam') : Lam'

noncomputable def Lam'.elim {C : Lam' → Type} (hh : C Lam'.halt)
    (hw : ∀ b k, C k → C (Lam'.write b k)) (hr : ∀ f, (∀ b, C (f b)) → C (Lam'.read f))
    (hb : ∀ b l r, C l → C r → C (Lam'.branch b l r))
    (hl : ∀ f k, (∀ n, C (f n)) → C k → C (Lam'.loop f k)) (x : Lam') : C x :=
  Lam'.rec (motive := fun x => C x) hh (fun b k ih => hw b k ih) (fun f ih => hr f ih)
    (fun b l r ihl ihr => hb b l r ihl ihr) (fun f k ihf ihk => hl f k ihf ihk) x

theorem Lam'.elim_read {C : Lam' → Type} (hh : C Lam'.halt)
    (hw : ∀ b k, C k → C (Lam'.write b k)) (hr : ∀ f, (∀ b, C (f b)) → C (Lam'.read f))
    (hb : ∀ b l r, C l → C r → C (Lam'.branch b l r))
    (hl : ∀ f k, (∀ n, C (f n)) → C k → C (Lam'.loop f k)) (f : Bool → Lam') :
    Lam'.elim hh hw hr hb hl (Lam'.read f) = hr f (fun b => Lam'.elim hh hw hr hb hl (f b)) := rfl

theorem Lam'.elim_write {C : Lam' → Type} (hh : C Lam'.halt)
    (hw : ∀ b k, C k → C (Lam'.write b k)) (hr : ∀ f, (∀ b, C (f b)) → C (Lam'.read f))
    (hb : ∀ b l r, C l → C r → C (Lam'.branch b l r))
    (hl : ∀ f k, (∀ n, C (f n)) → C k → C (Lam'.loop f k)) (b : Bool) (k : Lam') :
    Lam'.elim hh hw hr hb hl (Lam'.write b k) = hw b k (Lam'.elim hh hw hr hb hl k) := rfl

theorem Lam'.elim_halt {C : Lam' → Type} (hh : C Lam'.halt)
    (hw : ∀ b k, C k → C (Lam'.write b k)) (hr : ∀ f, (∀ b, C (f b)) → C (Lam'.read f))
    (hb : ∀ b l r, C l → C r → C (Lam'.branch b l r))
    (hl : ∀ f k, (∀ n, C (f n)) → C k → C (Lam'.loop f k)) :
    Lam'.elim hh hw hr hb hl Lam'.halt = hh := rfl
