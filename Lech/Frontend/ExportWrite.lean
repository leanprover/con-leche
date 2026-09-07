import Lech.Cached.ParsedC

/-!
# Writing parsed declarations back as lean4export NDJSON (task #200)

The in-process modeller's **debug dump** (`LECH_INMODEL_DUMP`): the
records it generates for a block are serialized in the lean4export
3.x record format and spliced into a copy of the raw input ahead of
the block, so that the result can be handed to `lech-preprocess` and
the *tool* models the generated auxiliary family — the gate for the
generator while the direct fixpoint route (task #188) is not yet at
indices.  Nothing here is on the checking path.

Interning: names, levels and expressions are written once each and
referenced by index; the indices start above the input's own maximum
(`ExportWriter.init base`), and the tool's parser keeps a sparse table
beside its dense one, so a splice never collides with the input's
entries.
-/

namespace Lech.Frontend

open Lech
open Lech.Cached (DeclC)

/-- The writer's interning state and its output lines. -/
structure ExportWriter where
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  exprs : Std.HashMap Expr Nat := {}
  next : Nat
  out : Array String := #[]

namespace ExportWriter

/-- A writer whose first fresh index is `base`. -/
def init (base : Nat) : ExportWriter := { next := base }

private def fresh (w : ExportWriter) : Nat × ExportWriter :=
  (w.next, { w with next := w.next + 1 })

private def emit (w : ExportWriter) (line : String) : ExportWriter :=
  { w with out := w.out.push line }

private def jstr (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
      else if c == '\n' then "\\n" else if c == '\t' then "\\t"
      else if c.toNat < 32 then s!"\\u{String.ofList (Nat.toDigits 16 c.toNat)}" else c.toString)) "") ++ "\""

private def jlist (xs : List Nat) : String :=
  "[" ++ ",".intercalate (xs.map toString) ++ "]"

partial def name (w : ExportWriter) : Name → Nat × ExportWriter
  | .anonymous => (0, w)
  | n@(.str p s) =>
    match w.names[n]? with
    | some i => (i, w)
    | none =>
      let (pi, w) := w.name p
      let (i, w) := w.fresh
      let w := { w with names := w.names.insert n i }
      (i, w.emit s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{jstr s}}}")
  | n@(.num p k) =>
    match w.names[n]? with
    | some i => (i, w)
    | none =>
      let (pi, w) := w.name p
      let (i, w) := w.fresh
      let w := { w with names := w.names.insert n i }
      (i, w.emit s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}")

partial def level (w : ExportWriter) : Level → Nat × ExportWriter
  | .zero => (0, w)
  | l =>
    match w.levels[l]? with
    | some i => (i, w)
    | none =>
      let (body, w) : String × ExportWriter :=
        match l with
        | .succ u => let (a, w) := w.level u; (s!"\"succ\":{a}", w)
        | .max u v => let (a, w) := w.level u; let (b, w) := w.level v; (s!"\"max\":[{a},{b}]", w)
        | .imax u v => let (a, w) := w.level u; let (b, w) := w.level v; (s!"\"imax\":[{a},{b}]", w)
        | .param n => let (a, w) := w.name n; (s!"\"param\":{a}", w)
        | .zero => ("", w)
      let (i, w) := w.fresh
      let w := { w with levels := w.levels.insert l i }
      (i, w.emit s!"\{\"il\":{i},{body}}")

private def levelIds (w : ExportWriter) (ls : List Level) : List Nat × ExportWriter :=
  ls.foldl (fun (acc, w) l => let (i, w) := w.level l; (acc ++ [i], w)) ([], w)

private def binfo : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def expr (w : ExportWriter) (e : Expr) : Nat × ExportWriter :=
  match w.exprs[e]? with
  | some i => (i, w)
  | none =>
    let (body, w) : String × ExportWriter :=
      match e with
      | .bvar k => (s!"\"bvar\":{k}", w)
      | .sort u => let (a, w) := w.level u; (s!"\"sort\":{a}", w)
      | .const n us =>
        let (a, w) := w.name n; let (ls, w) := w.levelIds us
        (s!"\"const\":\{\"name\":{a},\"us\":{jlist ls}}", w)
      | .app f a =>
        let (fi, w) := w.expr f; let (ai, w) := w.expr a
        (s!"\"app\":\{\"arg\":{ai},\"fn\":{fi}}", w)
      | .lam n ty b m =>
        let (ni, w) := w.name n; let (ti, w) := w.expr ty; let (bi, w) := w.expr b
        (s!"\"lam\":\{\"binderInfo\":\"{binfo m.bi}\",\"body\":{bi},\"name\":{ni},\"type\":{ti}}", w)
      | .forallE n ty b m =>
        let (ni, w) := w.name n; let (ti, w) := w.expr ty; let (bi, w) := w.expr b
        (s!"\"forallE\":\{\"binderInfo\":\"{binfo m.bi}\",\"body\":{bi},\"name\":{ni},\"type\":{ti}}", w)
      | .letE n ty v b =>
        let (ni, w) := w.name n; let (ti, w) := w.expr ty; let (vi, w) := w.expr v
        let (bi, w) := w.expr b
        (s!"\"letE\":\{\"body\":{bi},\"name\":{ni},\"nondep\":false,\"type\":{ti},\"value\":{vi}}", w)
      | .lit (.natVal k) => (s!"\"natVal\":\"{k}\"", w)
      | .lit (.strVal s) => (s!"\"strVal\":{jstr s}", w)
      | .proj s k x =>
        let (si, w) := w.name s; let (xi, w) := w.expr x
        (s!"\"proj\":\{\"idx\":{k},\"struct\":{xi},\"typeName\":{si}}", w)
      | .fvar _ _ _ => ("\"bvar\":0", w)
    let (i, w) := w.fresh
    let w := { w with exprs := w.exprs.insert e i }
    (i, w.emit s!"\{\"ie\":{i},{body}}")

private def nameIds (w : ExportWriter) (ns : List Name) : List Nat × ExportWriter :=
  ns.foldl (fun (acc, w) n => let (i, w) := w.name n; (acc ++ [i], w)) ([], w)

private def hints : ReducibilityHint → String
  | .abbrev => "\"abbrev\""
  | .opaque => "\"opaque\""
  | .regular n => s!"\{\"regular\":{n}}"

/-- Does the constant occur in the expression? -/
private def mentions (n : Name) : Expr → Bool
  | .const m _ => m == n
  | .app f a => mentions n f || mentions n a
  | .lam _ t b _ | .forallE _ t b _ => mentions n t || mentions n b
  | .letE _ t v b => mentions n t || mentions n v || mentions n b
  | .proj _ _ e => mentions n e
  | .fvar _ _ t => mentions n t
  | _ => false

/-- One declaration record.  Inductive blocks are written with the
shape data derived from the stored constants (`numIndices` off the
recursor's `majorIdx - rulePrefix`, `numParams` off a constructor,
`isRec` syntactically); only the modeller's own generated blocks are
ever written, so `numNested = 0`, `isReflexive = false`, one motive. -/
def decl (w : ExportWriter) : DeclC → ExportWriter
  | .defnDecl cv v h =>
    let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
    let (ti, w) := w.expr cv.type; let (vi, w) := w.expr v
    w.emit s!"\{\"def\":\{\"all\":[{ni}],\"hints\":{hints h},\"levelParams\":{jlist ls},\"name\":{ni},\"safety\":\"safe\",\"type\":{ti},\"value\":{vi}}}"
  | .thmDecl cv v =>
    let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
    let (ti, w) := w.expr cv.type; let (vi, w) := w.expr v
    w.emit s!"\{\"thm\":\{\"all\":[{ni}],\"levelParams\":{jlist ls},\"name\":{ni},\"type\":{ti},\"value\":{vi}}}"
  | .opaqueDecl cv v =>
    let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
    let (ti, w) := w.expr cv.type; let (vi, w) := w.expr v
    w.emit s!"\{\"opaque\":\{\"all\":[{ni}],\"isUnsafe\":false,\"levelParams\":{jlist ls},\"name\":{ni},\"type\":{ti},\"value\":{vi}}}"
  | .axiomDecl cv =>
    let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
    let (ti, w) := w.expr cv.type
    w.emit s!"\{\"axiom\":\{\"isUnsafe\":false,\"levelParams\":{jlist ls},\"name\":{ni},\"type\":{ti}}}"
  | .basisDecl _ => w
  | .indDecl block =>
    let types := block.filterMap fun ci => match ci with
      | .indInfo cv _ => some cv | _ => none
    let ctors := block.filterMap fun ci => match ci with
      | .ctorInfo cv nP nF => some (cv, nP, nF) | _ => none
    let recs := block.filterMap fun ci => match ci with
      | .recInfo cv mI rP rules => some (cv, mI, rP, rules) | _ => none
    match types.head? with
    | none => w
    | some tcv =>
    let T := tcv.name
    let nP := (ctors.head?.map (·.2.1)).getD 0
    let nIdx := (recs.head?.map fun r => r.2.1 - r.2.2.1).getD 0
    let isRec := ctors.any fun c => mentions T c.1.type
    let (ti, w) := w.name T
    -- types
    let (tys, w) := types.foldl (fun (acc, w) cv =>
      let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
      let (tyi, w) := w.expr cv.type
      let (cs, w) := w.nameIds (ctors.map (·.1.name))
      (acc ++ [s!"\{\"all\":[{ti}],\"ctors\":{jlist cs},\"isRec\":{isRec},\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":{jlist ls},\"name\":{ni},\"numIndices\":{nIdx},\"numNested\":0,\"numParams\":{nP},\"type\":{tyi}}"], w))
      ([], w)
    let (cts, w) := (ctors.zip (List.range ctors.length)).foldl (fun (acc, w) ((cv, cnP, nF), j) =>
      let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
      let (tyi, w) := w.expr cv.type
      (acc ++ [s!"\{\"cidx\":{j},\"induct\":{ti},\"isUnsafe\":false,\"levelParams\":{jlist ls},\"name\":{ni},\"numFields\":{nF},\"numParams\":{cnP},\"type\":{tyi}}"], w))
      ([], w)
    let (rcs, w) := recs.foldl (fun (acc, w) (cv, mI, rP, rules) =>
      let (ni, w) := w.name cv.name; let (ls, w) := w.nameIds cv.levelParams
      let (tyi, w) := w.expr cv.type
      let nm := ctors.length
      let (rls, w) := rules.foldl (fun (acc, w) r =>
        let (ci, w) := w.name r.ctor; let (ri, w) := w.expr r.rhs
        (acc ++ [s!"\{\"ctor\":{ci},\"nfields\":{r.nfields},\"rhs\":{ri}}"], w)) ([], w)
      (acc ++ [s!"\{\"all\":[{ti}],\"isUnsafe\":false,\"k\":false,\"levelParams\":{jlist ls},\"name\":{ni},\"numIndices\":{mI - rP},\"numMinors\":{nm},\"numMotives\":1,\"numParams\":{rP - 1 - nm},\"rules\":[{",".intercalate rls}],\"type\":{tyi}}"], w))
      ([], w)
    w.emit s!"\{\"inductive\":\{\"ctors\":[{",".intercalate cts}],\"recs\":[{",".intercalate rcs}],\"types\":[{",".intercalate tys}]}}"

end ExportWriter

end Lech.Frontend
