module

public import ConLeche.Driver.Schedule.Status
public import ConLeche.Frontend.Olean.Files
/- `#guard` evaluates at elaboration time: the definitions it runs come in by a `meta import`. -/
meta import ConLeche.Driver.Schedule.Status
meta import ConLeche.Frontend.Olean.Files

public section

/-!
# The scheduler's pure parts on examples

`surpriseOf` (the planning budget's surprise leaves the worker furthest above its reservation
out), the windowed peak (`pushMinute`, `windowPeak`), the fixed queue and its head slot (`nextHead`, `nextFit`, `insertAt`, `victims`) and `parseLog` with `etaMs` on a log mixing the three verdict-line formats (`<verdict>
<module>`, the five fields of the ms/rss/at format, the eleven of the statistics and threads
format) and `killed` lines; the new verdicts (`stack`, `oom-kill`, `signal N (NAME)`, DESIGN #569)
with `exitVerdict` and `parseLog`'s retry rule for `stack`; the seeded state of a resumed run
(`Logged.seed`); the commands `--schedule-commands` prints (`commandLines`, `shellQuote`); the
workers' stack size (`stackEnv`, `stackUsed`, `stackHint`), the sizes (`parseSize`), a failed
start (`spawnFailAct`, `requeueFailed`, `startsHeld`), what held the starts back (`heldBy`), and
the status part's reservation (`statusText`, `statsLines`).
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

-- the windowed peak (`peakWindow` = 5): a sawtooth worker, 13 GiB in minute 0, 1 GiB in minutes
-- 1-6; its peak leaves the window in minute 6, a later sample in the same minute keeps the larger
#guard peakWindow = 5
#guard windowPeak ((#[] : Array (Nat × Nat)) |> (pushMinute · 0 13) |> (pushMinute · 0 2)) = 13
#guard windowPeak ((List.range 6).foldl (fun r i => pushMinute r (i + 1) 1) (pushMinute #[] 0 13))
  = 1
#guard windowPeak ((List.range 5).foldl (fun r i => pushMinute r (i + 1) 1) (pushMinute #[] 0 13))
  = 13
#guard (pushMinute (pushMinute #[(0, 4)] 0 7) 3 1) = #[(0, 7), (3, 1)]
-- a gap of more than the window drops every older minute
#guard (pushMinute #[(0, 4), (2, 9)] 9 1) = #[(9, 1)]
#guard windowPeak #[] = 0

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
-- module's kills, the module that ran with threads
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).peaks = #[400000, 400000, 400000]
#guard (parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.toList.length = 2
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.get? (nm "C")) = some 12000000
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).killSize.get? (nm "F")) = some 1000000
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

-- the verdicts of a signalled worker (`Child.tryWait`: 128 + the signal)
#guard exitVerdict 0 "" false = "0"
#guard exitVerdict 3 "" false = "3"
#guard exitVerdict 134 "x\nStack overflow detected. Aborting.\n" false = "stack"
#guard exitVerdict 134 "some other abort" false = "signal 6 (SIGABRT)"
#guard exitVerdict 137 "" true = "oom-kill"
#guard exitVerdict 137 "" false = "signal 9 (SIGKILL)"
#guard exitVerdict 139 "" false = "signal 11 (SIGSEGV)"
#guard exitVerdict 143 "" false = "signal 15 (SIGTERM)"
#guard exitVerdict 168 "" false = "signal 40"
-- an overflow message does not make another signal a stack overflow; a rise only counts for SIGKILL
#guard exitVerdict 139 "Stack overflow detected" true = "signal 11 (SIGSEGV)"
#guard exitVerdict 134 "" true = "signal 6 (SIGABRT)"
#guard exitVerdict 7 "" false = "exit 7"

/-- A log with the new verdicts: `stack` at 1 GiB (unset: `-`) and at 8 GiB, and the others. -/
def sigLog : String :=
  "stack\t«S1»\t1000\t400000\t1000\t-\t-\t-\t-\t-\t1\t-\n" ++
  "stack\t«S2»\t1000\t400000\t2000\t-\t-\t-\t-\t-\t1\t8388608\n" ++
  "stack\t«S3»\t1000\t400000\t3000\t-\t-\t-\t-\t-\t1\n" ++
  "signal 9 (SIGKILL)\t«K1»\t1000\t400000\t4000\t-\t-\t-\t-\t-\t1\t-\n" ++
  "oom-kill\t«K2»\t1000\t400000\t5000\t-\t-\t-\t-\t-\t1\t-\n"

-- the signal and OOM verdicts are verdicts (the module is done), whatever the stack size
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog).verdicts.get? (nm "K1"))
  = some "signal 9 (SIGKILL)"
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog "8388608").verdicts.get? (nm "K2"))
  = some "oom-kill"
-- `stack` holds for the logged size only; a line without the field never holds
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog).verdicts.get? (nm "S1")) = some "stack"
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog).verdicts.get? (nm "S2")) = none
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog "8388608").verdicts.get? (nm "S1")) = none
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog "8388608").verdicts.get? (nm "S2")) = some "stack"
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog).verdicts.get? (nm "S3")) = none
-- the retried module's peak still counts for the typical peak
#guard (parseLog ConLeche.Frontend.Olean.parseModName sigLog).peaks.size = 5

/-- The queue of the head-slot examples: A B C D E F at positions 0 to 5. -/
def q : List ConLeche.Name := ["A", "B", "C", "D", "E", "F"].map nm

/-- A module's position in `q`. -/
def qpos (m : ConLeche.Name) : Nat := (q.findIdx? (· == m)).getD 99

/-- Known sizes: B (killed) 10, D (killed) 3. -/
def qsize (m : ConLeche.Name) : Nat := if m == nm "B" then 10 else if m == nm "D" then 3 else 0

-- the head slot: the lowest unstarted position, fitting or not (B killed, unstarted again before
-- the never started E F; then a never started C before the killed D)
#guard nextHead qpos [nm "B", nm "D"] [nm "E", nm "F"] = some (nm "B")
#guard nextHead qpos [nm "D"] [nm "C", nm "E"] = some (nm "C")
#guard nextHead qpos [] [] = none
-- another slot: the lowest position that fits; B (10) does not fit a room of 5, D (3, typical 2)
-- does and is before E
#guard nextFit qpos qsize 2 5 [nm "B", nm "D"] [nm "E", nm "F"] = some (nm "D")
-- a never started module before the fitting killed one
#guard nextFit qpos qsize 2 5 [nm "D"] [nm "C"] = some (nm "C")
-- the typical peak does not fit: only killed modules that fit (none here)
#guard nextFit qpos qsize 4 3 [nm "B"] [nm "C"] = none
-- D at the typical peak 4 (above its known 3) fits a room of 4
#guard nextFit qpos qsize 4 4 [nm "B", nm "D"] [nm "E"] = some (nm "D")
-- a killed module back at its own position
#guard insertAt qpos (nm "C") [nm "B", nm "E"] = [nm "B", nm "C", nm "E"]
#guard insertAt qpos (nm "F") [nm "B"] = [nm "B", nm "F"]
#guard insertAt qpos (nm "A") [] = [nm "A"]

-- the victims: the youngest by start first, the head slot's never; (module, start, set), 30 of a
-- limit of 20: E (started at 9) goes, 22 left, then C (started at 5), 17
#guard victims [(nm "A", 1, 10), (nm "C", 5, 5), (nm "E", 9, 8), (nm "B", 3, 7)] (some (nm "A"))
  30 20 = [nm "E", nm "C"]
-- the head is the youngest: still never killed
#guard victims [(nm "A", 9, 25), (nm "C", 5, 5)] (some (nm "A")) 30 20 = [nm "C"]
-- only the head left: nobody (alone over the limit it is the verdict `memory`)
#guard victims [(nm "A", 1, 25)] (some (nm "A")) 25 20 = []
-- a tie in start time: the later in the list first
#guard victims [(nm "C", 5, 5), (nm "D", 5, 5)] none 12 10 = [nm "D"]
-- within the limit: nobody
#guard victims [(nm "C", 5, 5)] none 5 10 = []


-- DESIGN #571: the term that sets a reservation, the over-reserved rows, the `reserve` log lines
#guard resTerm 100 200 50 150 = "window peak"
#guard resTerm 100 200 50 300 = "learned"
#guard resTerm 10 20 50 30 = "typical"
#guard resTerm 10 20 50 0 = "typical"
#guard resTerm 10 50 50 50 = "window peak"
def G : Nat := 1048576
#guard overRows [("a", 0, 2 * G, 2 * G + G * 2 / 5, "typical")] = []
#guard (overRows [("a", 0, 2 * G, 3 * G, "typical")]).length = 1
-- 25 % and 256 MiB
#guard (overRows [("a", 0, G, G + G / 3, "typical")]).length = 1
#guard overRows [("a", 0, G / 10, G / 10 + 1000, "typical")] = []
#guard (overRows [("a", 0, G, 2 * G, "x"), ("b", 0, G, 5 * G, "y")]).map (·.1) = ["b", "a"]
#guard overText [("a", 0, 2 * G, 2 * G, "typical")] = ""
#guard overText [("Fi24Br.Seed", 35340000, 2202010, 18 * G, "learned")]
  = "over-reserved: Fi24Br.Seed 18.0G for 2.1G (learned, 9h49m)"
#guard overText ((List.range 5).map fun i => (s!"m{i}", 1000, G, (i + 2) * G, "learned"))
  = "over-reserved: m4 6.0G for 1.0G (learned, 1s), m3 5.0G for 1.0G (learned, 1s), \
     m2 4.0G for 1.0G (learned, 1s) +2 more"
#guard reserveLine ("A", 5000, 7, 9, "typical") = "reserve\tA\t5000\t7\t9\ttypical"
-- a `reserve` line is no verdict and no run time
#guard (parseLog ConLeche.Frontend.Olean.parseModName (mixedLog ++
  "reserve\t«A»\t5000\t7\t9\ttypical\nreserve\t«Z»\t5000\t7\t9\tlearned\n")).verdicts.size = 5
#guard (parseLog ConLeche.Frontend.Olean.parseModName (mixedLog ++
  "reserve\t«Z»\t5000\t7\t9\tlearned\n")).peaks = #[400000, 400000, 400000]

-- DESIGN #595: a worker alone over the limit is killed and queued again at one thread where it
-- ran several; the verdict `memory` only for one thread
#guard aloneAct 1 = .memory
#guard aloneAct 0 = .memory
#guard aloneAct 5 = .requeueSingle

/-- `memory` verdicts: M at 5 threads, N at one, O in an old line, P at 3 (an earlier `0` line of
P is dropped by the later one), and a `stack` line, which the rule does not touch. -/
def memLog : String :=
  "memory\t«M»\t10000\t≥900000\t10000\t16\t600\t0\t43\t10\t5\t-\n" ++
  "memory\t«N»\t10000\t900000\t10000\t16\t600\t0\t43\t10\t1\t-\n" ++
  "memory\t«O»\n" ++
  "0\t«P»\t10000\t400000\t10000\t16\t600\t0\t43\t10\t1\t-\n" ++
  "memory\t«P»\t20000\t900000\t20000\t16\t600\t0\t43\t10\t3\t-\n"

#guard !((parseLog ConLeche.Frontend.Olean.parseModName memLog).verdicts.contains (nm "M"))
#guard (parseLog ConLeche.Frontend.Olean.parseModName memLog).verdicts.get? (nm "N") = some "memory"
#guard (parseLog ConLeche.Frontend.Olean.parseModName memLog).verdicts.get? (nm "O") = some "memory"
#guard !((parseLog ConLeche.Frontend.Olean.parseModName memLog).verdicts.contains (nm "P"))
-- the module runs again at one thread, at a known size
#guard (parseLog ConLeche.Frontend.Olean.parseModName memLog).killMulti.contains (nm "M")
#guard !((parseLog ConLeche.Frontend.Olean.parseModName memLog).killMulti.contains (nm "N"))
#guard (parseLog ConLeche.Frontend.Olean.parseModName memLog).killSize.get? (nm "P") = some 900000

-- the seeded state: C and F were killed and still have to run, at their known sizes (at least
-- the typical start value 500000), F at one thread; the order of the queue kept
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed
  (["C", "X", "F", "Y"].map nm) 500000).again = ["C", "F"].map nm
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed
  (["C", "X", "F", "Y"].map nm) 500000).pending = ["X", "Y"].map nm
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed
  (["C", "X", "F", "Y"].map nm) 500000).sizes.get? (nm "F") = some 1000000
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed
  (["C", "X", "F", "Y"].map nm) 2000000).sizes.get? (nm "F") = some 2000000
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed
  (["C", "X", "F", "Y"].map nm) 500000).single.toList = [nm "F"]
-- three peaks: fewer than `typMin`, the start value stays
#guard ((parseLog ConLeche.Frontend.Olean.parseModName mixedLog).seed [] 777).typ = 777

-- the log's lines
#guard killLine (nm "A.B") 5000 7 2 = "killed\t«A».«B»\t5000\t7\t2"
#guard verdictLine "0" (nm "A") 10 "≥5" 20 { decls := some 3 } 1 "-"
  = "0\t«A»\t10\t≥5\t20\t3\t-\t-\t-\t-\t1\t-"

-- shell quoting: plain words as they are, everything else in single quotes, a quote as '\''
#guard shellQuote "--search-path=/a/b:/c" = "--search-path=/a/b:/c"
#guard shellQuote "" = "''"
#guard shellQuote "«Mathlib».«Data»" = "'«Mathlib».«Data»'"
#guard shellQuote "a b" = "'a b'"
#guard shellQuote "it's" = "'it'\\''s'"
#guard shellQuote "$HOME" = "'$HOME'"

-- the commands: the graph check first, then a worker per module, in the order given
#guard commandLines "/bin/con-leche" "/l:/i" (nm "R") [nm "B", nm "R"]
    (workerArgs .verified 99 "/l:/i" none) =
  ["/bin/con-leche --check-graph --search-path=/l:/i -- '«R»'",
   "/bin/con-leche --olean --module --verified --max-nat-size=99 --search-path=/l:/i -- '«B»'",
   "/bin/con-leche --olean --module --verified --max-nat-size=99 --search-path=/l:/i -- '«R»'"]
-- `--jobs=N` only where given; the scheduler's own workers get their share
#guard workerArgs .trusted 7 "d" (some 4) (nm "M") =
  #["--olean", "--module", "--jobs=4", "--trusted", "--max-nat-size=7", "--search-path=d", "--",
    "«M»"]

-- the workers' stack size (`--worker-stack-size`, DESIGN #620): set in the worker's environment
-- where given, nothing otherwise (the worker inherits the scheduler's environment)
#guard stackEnv (some 8388608) = #[("LEAN_STACK_SIZE_KB", some "8388608")]
#guard stackEnv none = #[]
-- the size the log records and the `stack` retry rule compares: the flag's, else the inherited
#guard stackUsed (some 8388608) (some "1024") = "8388608"
#guard stackUsed none (some "1024") = "1024"
#guard stackUsed none none = "-"
-- a `stack` verdict logged at the flag's size holds at that size only
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog (stackUsed (some 8388608) none)).verdicts.get?
  (nm "S2")) = some "stack"
#guard ((parseLog ConLeche.Frontend.Olean.parseModName sigLog (stackUsed (some 4194304) none)).verdicts.get?
  (nm "S2")) = none
-- the hint names the flag and the size the worker ran at
#guard (stackHint (nm "M") "8388608").contains "--worker-stack-size (now 8388608 KiB;"
#guard (stackHint (nm "M") "-").contains "(now Lean's default;"
-- the commands: with the flag every worker's line starts with the setting, the graph check's not
#guard commandLines "/bin/con-leche" "/l" (nm "R") [nm "B"] (workerArgs .verified 99 "/l" none)
    (some 8388608) =
  ["/bin/con-leche --check-graph --search-path=/l -- '«R»'",
   "LEAN_STACK_SIZE_KB=8388608 /bin/con-leche --olean --module --verified --max-nat-size=99 \
     --search-path=/l -- '«B»'"]

-- the sizes (`parseSize`, shared by `--schedule-memory` and `--worker-stack-size`): a unit is
-- required
#guard parseSize "8G" = some 8388608
#guard parseSize "512m" = some 524288
#guard parseSize "1T" = some 1073741824
#guard parseSize "8388608" = none
#guard parseSize "G" = none
#guard parseSize "8GB" = none

-- a failed start: requeued while others run, verdict 3 with none running
#guard spawnFailAct 3 == .requeue
#guard spawnFailAct 0 == .stop
-- requeued at its own position: back at the head of the never started ones, or among the killed
#guard requeueFailed (fun (n : Nat) => n) 2 false [5] [3, 4] = ([5], [2, 3, 4])
#guard requeueFailed (fun (n : Nat) => n) 4 true [1, 5] [2] = ([1, 4, 5], [2])
-- the starts are held until fewer workers run than at the failure
#guard startsHeld (some 3) 3
#guard !startsHeld (some 3) 2
#guard !startsHeld none 7
-- what held the starts back after a tick
#guard heldBy false false false 2 8 == none
#guard heldBy true false true 2 8 == none
#guard heldBy true true false 2 8 == some .spawn
#guard heldBy true false false 8 8 == some .jobs
#guard heldBy true false false 5 8 == some .memory

-- the status part: with a limit, the reservation of the planning budget; fixed widths
#guard statusText 75627 59773 49 (some 957000) 80 55 (some (19818100, 1258300, 36490500)) 41943040
    37748736 =
  "[59773 ( 79.0%)  49 wrkr  55 thds  RSS  18.9G tot   1.2G biggest   34.8G of  36.0G rsvd   \
    15m57s eta]"
-- without a limit no reservation
#guard statusText 10 3 1 none 4 1 (some (1048576, 1048576, 5 * 1048576)) 0 =
  "[ 3 ( 30.0%)  1 wrkr  1 thds  RSS   1.0G tot   1.0G biggest        ? eta]"

-- the statistics' held-back line
#guard (statsLines { heldMemMs := 3000, heldJobsMs := 1000 } 10000 4 0 0 0 0 none)[2]? =
  some "  starts held back: by memory 3.0s (30.0 %), by --jobs 1.0s (10.0 %) of the wall time"
#guard (statsLines { heldSpawnMs := 500, spawnFails := 2 } 10000 4 0 0 0 0 none)[2]? =
  some "  starts held back: by memory 0.0s (0.0 %), by --jobs 0.0s (0.0 %), by 2 failed starts \
    0.5s (5.0 %) of the wall time"

end ConLecheTests.ScheduleTests
