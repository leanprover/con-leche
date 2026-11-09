module
-- Guards task #409: `Census.Suz.NExc0`: `import all` of HiInhT (inheriting
-- its grant of `hiL`), and HiInhD stored, at a module the importer cannot
-- certify HiInhL loads.  Lean accepts; declined (task #409, interim; target:
-- accept, once the hole design is revisited).
public import HiInhD
import all HiInhT
public theorem hiM : hiD = hiD := rfl
