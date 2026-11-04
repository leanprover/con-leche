module
-- Guards task #409: HiInhM with its imports in the other order.  The
-- isolated mode declines as at HiInhM; a worker (`--worker=HiInhM2`)
-- numbers HiInhD after HiInhL (it does not load HiInhX) and rejects by
-- the rule X (a name capture), where Lean accepts (target: accept).
import all HiInhT
public import HiInhD
public theorem hiM2 : hiD = hiD := rfl
