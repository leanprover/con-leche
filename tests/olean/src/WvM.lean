module
prelude

public import WvB

public section

-- `wv_x` and `wv_y` unfold to the same private-only `wv_secret`: Lean
-- accepts (it unfolds `wv_p` and `wv_q` to the constant it does not
-- have), the modular check presents `wv_p` and `wv_q` as assumptions
-- (their values read a constant WvM's context lacks) and rejects, unless
-- `--import-all WvM=WvA` puts WvA's private part in the context
theorem wvm : Eq wv_x wv_y := rfl

end
