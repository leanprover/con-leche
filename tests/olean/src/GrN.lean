module
-- Guards task #464 (one group's record): a nested type (with auxiliary recursors) and a
-- mutual pair.
public section
inductive Tr | node : List Tr → Tr
mutual
inductive Ev | z | s : Od → Ev
inductive Od | s : Ev → Od
end
end
