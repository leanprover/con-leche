--#export MA.rec MB.rec MA.rec_1
/- Corner case (the MEMBER-MENTION check on outside recursor majors): in a mutual block
   the auxiliary major `List MB` mentions the SECOND member only.
   Official's `is_nested` looks for every type of the declaration
   (`m_new_types`, inductive.cpp v4.34.0 :1040–1044), so it generates
   `MA.rec_1` on `List MB`; the check reads every member name.
   Official 0. -/
mutual
inductive MA where
  | leaf : MA
  | mk : List MB → MA
inductive MB where
  | mk : MA → MB
end
