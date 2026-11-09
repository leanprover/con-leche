module

public import ConLeche.Driver.ScheduleIO
public import ConLeche.Frontend.Olean.Files
/- `#guard` evaluates at elaboration time: the definitions it runs come in by a `meta import`. -/
meta import ConLeche.Driver.ScheduleIO
meta import ConLeche.Frontend.Olean.Files

public section

/-!
# The scheduler's pure parts on examples

`surpriseOf` (the planning budget's surprise leaves the worker furthest above its reservation
out) and `parseLog` with `etaMs` on a log mixing the three verdict-line formats (`<verdict>
<module>`, the five fields of the ms/rss/at format, the eleven of the statistics and threads
format) and `killed` lines.
-/

namespace ConLecheTests.ScheduleTests

open ConLeche.Driver.Schedule

-- one giant 30 GiB above its reservation, two workers 1 GiB above, one 1 GiB below (KiB)
#guard surpriseOf [(32 * 1048576, 2 * 1048576), (3 * 1048576, 2 * 1048576),
  (3 * 1048576, 2 * 1048576), (1048576, 2 * 1048576)] = 1048576
-- a lone worker's growth is no surprise
#guard surpriseOf [(35 * 1048576, 2 * 1048576)] = 0
#guard surpriseOf [] = 0
-- two equal giants: the second one counts
#guard surpriseOf [(20, 5), (20, 5)] = 15

/-- Two runs, the first in two old formats, the second in the newest one, with kills. -/
def mixedLog : String :=
  "0\t«A»\n" ++
  "0\t«B»\t10000\t400000\t10000\n" ++
  "killed\t«C»\t5000000\t9000000\n" ++
  "0\t«D»\t20000\t400000\t20000\n" ++
  "0\t«E»\t30000\t400000\t5000\t16\t600\t0\t43\t10\t1\n" ++
  "killed\t«F»\t70000\t1000000\n" ++
  "1\t«G»\t40000\t≥500000\t20000\t-\t-\t-\t-\t-\t2\n"

#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).verdicts.size = 5
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).msN = 4
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).msSum = 100000
-- the runs' spans 20 s and 20 s: 100 s of module time in 40 s, 2.5 workers
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).workers = 2500

-- the estimate: 1000 remaining modules at the logged mean of 25 s over the logged 2.5 workers in
-- the first minute; after an hour at 4 workers with 8 finishes of 1000 s each, the mean over all
-- 12 known times over this run's 4 workers
#guard etaMs 1000 100000 4 0 0 2500 16 = some 10000000
#guard etaMs 1000 (100000 + 8000000) (4 + 8) (4 * 3600000) 3600000 2500 16 =
  some (1000 * 8100000 / 12 / 4)

-- previous runs that averaged fewer than one worker: their average, not the jobs
#guard etaMs 1000 100000 4 0 0 500 16 = some 50000000

end ConLecheTests.ScheduleTests
