/- `scripts/nested-pin-probe.lean` — THE NESTED ELIMINATION'S PIN TABLE,
   READ OFF A STREAM (task #315 R2).

       lake env lean --run scripts/nested-pin-probe.lean STREAM.ndjson BLOCKNAME

   Parses the stream, folds the declarations BEFORE the named inductive
   block with the real cached driver, recognises the block
   (`nestedParts?`), runs the annotation and `elimNested`, and prints,
   per pin: its mimic name, its container, its expression and its
   components; then K.59's REWRITTEN components
   (`nestedPinCompRewrites`), and the edge classification's own test —
   `stripDomPis … |>.getAppFn` on each container field domain, with the
   `declPos` of the pin's container and of the head, which is what
   `nestedPinOrderAt` (K.57) compares.

   An instrument, not a gate: it is what to run when a model-side claim
   about the pins, their components or an edge's head has to be checked
   against the elimination rather than against a reading of the code.
   Fixture scale only — it folds in process, serially (DESIGN, lane
   L-E's probe note).  `tests/e2e/ind_nest_straddle.ndjson` is the
   stream the R2 pricing read with it. -/
import ConLeche
import ConLeche.Frontend.ExportC
import ConLeche.Cached.Installed

open ConLeche

partial def pp : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar i _ => s!"f{i}"
  | .sort u => s!"Sort {repr u}"
  | .const n _ => toString n
  | .app f a => s!"({pp f} {pp a})"
  | .lam ty b _ => s!"(fun : {pp ty} => {pp b})"
  | .forallE ty b _ => s!"(∀ : {pp ty}, {pp b})"
  | .letE ty v b => s!"(let : {pp ty} := {pp v}; {pp b})"
  | .proj s i e => s!"({pp e}.{s}.{i})"
  | .lit _ => "lit"

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "tests/e2e/ind_nest_straddle.ndjson"
  let target := args.getD 1 "Straddle"
  let r ← ConLeche.Frontend.parseExportStreamD path false false
  match r with
  | .error (e, n) => IO.println s!"parse error at {n}: {repr e}"
  | .ok pr =>
    let ds := pr.decls
    let mut idx := 0
    let mut found := false
    for i in [0:ds.size] do
      match ds[i]! with
      | .indDecl block _ =>
        if (block.head?.map (·.name)).getD .anonymous == ConLeche.Name.str ConLeche.Name.anonymous target then
          if !found then idx := i; found := true
      | _ => pure ()
    if !found then IO.println "block not found" else
    let prefixDs := ds.extract 0 idx
    match ConLeche.Cached.checkDecls .verified ConLeche.natOpPinSets prefixDs with
    | .error (e, n) => IO.println s!"prefix rejected at {n}: {repr e}"
    | .ok env =>
      match ds[idx]! with
      | .indDecl block nP =>
        match ConLeche.nestedParts? nP block with
        | none => IO.println "not recognised as nested"
        | some p =>
          let ops := ConLeche.fueledOps (mode := CheckMode.verified) (F := 1000000)
          match ConLeche.nestedAnnotFormers ops env p.nP p.formers with
          | Except.error e => IO.println s!"annotFormers: {repr e}"
          | Except.ok fmsA =>
            match ConLeche.nestedAnnotCtors ops (ConLeche.nestedFormerEnv fmsA env) p.ctors with
            | Except.error e => IO.println s!"annotCtors: {repr e}"
            | Except.ok ctorsA =>
              match ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) with
              | Except.error e => IO.println s!"elim: {repr e}"
              | Except.ok st =>
                IO.println s!"p.k = {p.k}, pins = {st.pins.length}, types = {st.types.length}"
                for (q, i) in st.pins.zipIdx do
                  IO.println s!"pin {i}: aux={q.aux} container={q.container} grpBase={q.grpBase}"
                  IO.println s!"   pin  = {pp q.pin}"
                  for (c, j) in q.pin.getAppArgs.zipIdx do
                    IO.println s!"   comp[{j}] = {pp c}"
                -- the edge classification's OWN test (nestedPinOrderAt), at each pin
                for (q, i) in st.pins.zipIdx do
                  match ConLeche.containerInfo? env q.container with
                  | none => IO.println s!"pin {i}: no containerInfo?"
                  | some ci =>
                    IO.println s!"pin {i}: container={q.container} nP={ci.nP} declPos={repr (ConLeche.declPos env q.container)}"
                    match ci.members[i - q.grpBase]? with
                    | none => IO.println "   no member"
                    | some J =>
                      for (cJ, j) in J.ctors.zipIdx do
                        match cJ.type.stripPis (ci.nP + cJ.nFields) with
                        | none => IO.println s!"   ctor {j}: no stripPis"
                        | some (jbs, _) =>
                          for l in [0:cJ.nFields] do
                            match jbs[ci.nP + l]? with
                            | none => pure ()
                            | some domJ =>
                              let hd := (ConLeche.stripDomPis domJ.1).getAppFn
                              IO.println s!"   ctor {j} field {l}: dom={pp domJ.1} head={pp hd} declPos(head)={repr (match hd with | .const n _ => ConLeche.declPos env n | _ => none)}"
                match ConLeche.nestedRewriteData p st with
                | none => IO.println "no rewrite data"
                | some (params, pbs₀) =>
                  IO.println s!"params = {params.map pp}"
                  match ConLeche.nestedPinCompRewrites env p st params pbs₀ with
                  | none => IO.println "K.59: nestedPinCompRewrites = none (WOULD FIRE)"
                  | some comps =>
                    for (cs, i) in comps.zipIdx do
                      for (c, j) in cs.zipIdx do
                        IO.println s!"rewritten comp[{i}][{j}] = {pp c}"
      | _ => IO.println "not an indDecl"
