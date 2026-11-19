-- Task #608: a "solution" that imports its challenge CmpChal: the modular run's graph, with the
-- challenge's added import of its solution, has the cycle CmpChal → CmpImpS → CmpChal (exit 1);
-- the merged comparison checks the challenge's sorry in the solution's closure (exit 2).
module
prelude
public import CmpChal
