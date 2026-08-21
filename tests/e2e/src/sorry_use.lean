/- End-to-end test: a proof that uses `sorry` exports as a `sorryAx`
   application.  The frontend skips the `sorryAx` declaration (it has
   no set-theoretic model) and must positively decline any use. -/

--#export usesSorry

set_option warn.sorry false in
theorem usesSorry : ∀ (p : Prop), p → p := sorry
