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

/-- The module `s` of a test log. -/
def nm (s : String) : ConLeche.Name := (ConLeche.Frontend.Olean.parseModName s).get!

/-- Two runs, the first in two old formats, the second in the newest one, with kills. -/
def mixedLog : String :=
  "0\t«A»\n" ++
  "0\t«B»\t10000\t400000\t10000\n" ++
  "killed\t«C»\t5000000\t9000000\n" ++
  "0\t«D»\t20000\t400000\t20000\n" ++
  "0\t«E»\t30000\t400000\t5000\t16\t600\t0\t43\t10\t1\n" ++
  "killed\t«F»\t70000\t1000000\t4\n" ++
  "killed\t«C»\t80000\t12000000\t1\n" ++
  "1\t«G»\t40000\t≥500000\t20000\t-\t-\t-\t-\t-\t2\n"

#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).verdicts.size = 5
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).msN = 4
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).msSum = 100000
-- the runs' spans 20 s and 20 s: 100 s of module time in 40 s, 2.5 workers
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).workers = 2500

-- the seeded state: the exact peaks in log order (the `≥` one left out), the largest set of each
-- module's kills, the latest kill first, the module that ran with threads
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).peaks = #[400000, 400000, 400000]
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.toList.length = 2
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.get? (nm "C")) = some 12000000
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.get? (nm "F")) = some 1000000
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killOrder = [nm "C", nm "F"]
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killMulti.contains (nm "F")
-- C's old four-field line and its one-thread line: not multi-threaded
#guard !(parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killMulti.contains (nm "C")

-- the window keeps the last 200 peaks; the median holds from 20 of them, else the start value
#guard (parseLog ConLeche.Frontend.Olean.parseModName
  (String.join ((List.range 250).map fun i => s!"0\tm{i}\t1\t{i}\t1\n"))).peaks
    = (Array.range 250).extract 50 250
#guard seedPeaks ((Array.range 19).map (· + 1)) 777 = ((Array.range 19).map (· + 1), 777)
#guard seedPeaks ((Array.range 20).map (· + 1)) 777 = ((Array.range 20).map (· + 1), 11)
#guard seedPeaks #[] 777 = (#[], 777)
-- the first finish after a 19-peak seed makes 20: the median applies
#guard (pushPeak ((Array.range 19).map (· + 1)) 777 20).2 = 11

-- the estimate: 1000 remaining modules at the logged mean of 25 s over the logged 2.5 workers in
-- the first minute; after an hour at 4 workers with 8 finishes of 1000 s each, the mean over all
-- 12 known times over this run's 4 workers
#guard etaMs 1000 100000 4 0 0 2500 16 = some 10000000
#guard etaMs 1000 (100000 + 8000000) (4 + 8) (4 * 3600000) 3600000 2500 16 =
  some (1000 * 8100000 / 12 / 4)

-- previous runs that averaged fewer than one worker: their average, not the jobs
#guard etaMs 1000 100000 4 0 0 500 16 = some 50000000

end ConLecheTests.ScheduleTests
