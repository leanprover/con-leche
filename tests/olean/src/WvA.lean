module
prelude

public import Init.Prelude

public section

-- Mathlib's WittVector case (task #396, `comm_ring_aux₁/₂` of
-- `Mathlib.RingTheory.WittVector.Basic`): two private constants exported
-- with their values (`privateInPublic`) read a private-only one, and
-- exposed public definitions read them
private def wv_secret : Nat := 7

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def wv_p : Nat := wv_secret

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def wv_q : Nat := wv_secret

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def wv_x : Nat := wv_p

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def wv_y : Nat := wv_q

end
