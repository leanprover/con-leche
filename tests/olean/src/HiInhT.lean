module
-- Guards task #409: `Suz.Text2306`, which loads HiInhL at the exported
-- level only (its grant of `hiL` takes `hiD` as a hole).
public import HiInhL
public section
theorem hiT : hiLx = hiLx := rfl
end
