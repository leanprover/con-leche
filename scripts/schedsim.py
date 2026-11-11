#!/usr/bin/env python3
"""schedsim.py -- replay a `--schedule-log` offline under a scheduling policy (DESIGN #518, #540).

The input is a scheduler log (`<verdict>\\t<module>\\t<ms>\\t<rss KiB>\\t<at>\\t<decls>\\t<parse>\\t
<check>\\t<busy>\\t<slowest>\\t<threads>`, `ConLeche/Driver/ScheduleIO.lean`; older logs lack the
last fields) of a real run, each module's wall time and peak, taken as its time and peak at one
thread (a module the log ran at more threads is replayed as if one had taken that long).  `killed` lines and repeated modules are skipped (the last verdict
counts).  Optional memory profiles (`--profiles DIR`, files `<module>.tsv` of `ms<TAB>VmRSS KiB`
lines sampled from a lone worker) give a module's memory shape over its run; a module without one
ramps linearly to its peak (`--shape ramp`, the default) or follows the mean profiled shape
(`--shape mean`).

The policy replayed is the scheduler's of `ScheduleIO.run`, at a fixed tick (`--tick`, s):
at most `--jobs` workers; `--budget` the hard limit, admission planning against a lower planning
budget: the limit minus a margin, the margin the larger of `--margin-init` (0.10) x the limit and
the `--margin-stat` (p99; `max`, `pNN`) of the last `--margin-window` (200; 0 all) nonzero
surprises, the plan at least `--margin-floor` (0.5) x the limit; a surprise is the largest, over
the ticks between two starts, of the running workers' current sets minus what admission reserved
for them at the earlier start, the worker furthest above its own reservation left out
(`--margin-excl largest`, DESIGN #545; `none` the rule of #540, `protected`, `largest-pos`).  Admission by size (the planning budget minus the running workers
counted at max(peak so far, typical peak, known size); killed modules first by known size, then
the queue in order at the typical peak, every module that fits in one tick, each taking its
reservation off the room; nothing running: the first always starts); the typical peak the
`--typ-q` quantile (0.5, the median) of the last 200 finished peaks from 20 finishes on, limit /
jobs before; when the current sets exceed the hard limit the largest worker protected (sticky),
the youngest others killed until the current sets fit, each requeued at the front with known size
max(set at the kill, typical, 2 x previous); the protected worker alone over the limit gets the
verdict `memory`; the growth gate (`--growth`, s, 0 off) holds starts while the protected
worker's peak rose within that long.

`--old` replays the policy before #540 (the one of #518's runs): admission against the limit
itself (no planning budget), at most one start per tick and starts at least 200 ms apart (the
stagger, since removed from the scheduler).

Threads (DESIGN #544, the scheduler's rule; the single replay's default, `--threads-d 0` for one
thread per worker, `--old` always one): `--jobs` is the thread budget; a worker starts with
max(1, min(cap, decls // D)) threads, D = `--threads-d` (30), cap the free threads less those
memory could still fill with workers (min(free - 1, room after this start // typical peak,
queued modules) of them; `--threads-greedy`: cap = all free threads); a module killed while
running with more than one thread runs with one from then on.  Its time and peak as below
(`--install-serial`, `--thread-mem`).  `--calibrate` prints DESIGN #544's table (`--calibrate-d`,
`-caps`, `-spare`, `-drain`, `-cases`; data sets `real`, `heavy`, `heavy30`, `mcl`: the log plus
10 McLEnumA-like modules (`MCL`: 87 748 declarations, 554 s, 1.41 GiB; `--mcl N` adds N to a
single replay), `mclheavy30`: both).

Variants: `--order graph|shuffled` (graph needs `--graph-order FILE`, one module per line, the
order of `Graph.graphOf`); `--threads-d D --threads-cap C --thread-budget B`: a worker starts at
threads as above, at most C, its time install + max(slowest, busy / t)
(install = wall - busy at one thread, scaled by s + (1 - s) / t, s = `--install-serial`,
1 by default, 0.56 measured) and its peak scaled by 1 + `--thread-mem` x (t - 1);
`--read-cap R`: a start only while fewer than R workers are in their read
phase; `--reserve now|60`: a killed module
waits at the head of the queue and the scheduler drains for it (no other start until it fits;
`60`: only once it has waited 60 s); `--heavy F --heavy-time X --heavy-mem Y --seed S`: a
random fraction F of the modules made X times longer and Y times
larger (a CFSG-like tail).

The single replay's kill rule is the shipped one of DESIGN #548 (`--kill-by head --gate none
--requeue position`: a fixed queue, a head slot, the youngest others killed); the comparison
tables pass their rules explicitly (`simulate`'s defaults are the rule of #512 with #560's gate,
so that the tables of #518-#546 replay as they were).

Output (one line, or `--json`): the makespan, the mean running workers, the mean memory in use,
the kills and the worker time they lost, the time the growth gate held starts, the `memory`
verdicts.  `--grid` runs the variant table of DESIGN #518 (on the old policy, with its stagger
variants); `--compare` the table of DESIGN #540 (the old policy at 0.85 x and 1 x the limit, the
new one at the limit, at `--compare-cases`, `data:limit GiB:jobs`, data `real`, `heavy`: 1 % at
100x time and 10x memory, `heavy30`: the same at 30x memory).  `--resume-compare` the table of DESIGN #546 (a resumed run: the restart data of #545 without
seeding, with the typical peak seeded from the log's recorded peaks, and with the giants' kill
sizes seeded: `seed_peaks`, `seed_sizes` of `simulate`; `--kill-frac`).  `--margin-compare` the table of DESIGN #545 (the
margin rules at `--margin-cases`; besides the log's data sets `cfsg`: the modules of a CFSG log
(`--cfsg-log`) in `--cfsg-reps` copies, and `restart`: the same after `--giants` synthetic giants,
peaks 10-35 GiB, times 30 min-5 h, at the head of the queue).  `--rank-compare` the table of
DESIGN #548 (`RANK_RULES`, `--rank-rules`, `--rank-cases`; data as for `--margin-compare` and
`starve`: the giants spread over the middle half of the queue): the kill rule (`kill_by` of
`simulate`: sticky protection with the youngest by start, or no protection with the latest queue
position or the latest start first, or `head`: one slot, the head, starts the first module of the
queue whether it fits or not, ungated, and is never killed for memory; the others admit as usual,
and an overflow kills the youngest non-head workers), the growth gate (`gate`: the protected worker's, any worker's
above its reservation, the same only while the current sets exceed the plan, or none) and the
drain for the head of the killed modules (`drain`, s); besides the columns above the waits of the
killed giants (at least 1/8 of the limit) from their kill to their restart.
`--size-compare` the table of DESIGN #566 (`SIZE_RULES`, `--size-rules`, `--size-cases`; the
known size after a kill, `size_rule` of `simulate`, under the shipped head slot and fixed queue;
the mean reservation split into its terms; a CFSG-like data set with `-saw`, e.g. `starve-saw`,
puts every module on a synthetic sawtooth, `saw_shape`).  `--window-compare` the table of
DESIGN #567 (`WINDOW_RULES`, `--window-rules`, the cases of `--size-cases`): a running worker
counted at its peak over the last W minutes in place of its all-time peak (`peak_window`).
"""
import argparse, bisect, json, os, random

FNV_OFF, FNV_PRIME = 14695981039346656037, 1099511628211


def spell(m):
    return ".".join("«" + c + "»" for c in m.split("."))


def fnv1a(s):
    h = FNV_OFF
    for b in s.encode("utf-8"):
        h = ((h ^ b) * FNV_PRIME) & 0xFFFFFFFFFFFFFFFF
    return h


def unspell(s):
    return s.replace("«", "").replace("»", "")


def num(x):
    return None if x in (None, "", "-") else int(x.lstrip("≥"))


def read_log(path):
    """module -> dict(ms, pk, decls, parse, check, busy, slowest, verdict); also the kills.
    The verdict is the line's first field as it stands: an exit code, `timeout`, `memory`, or
    (DESIGN #569) `stack`, `oom-kill`, `signal N (NAME)`; the optional twelfth field `stack` is
    the `LEAN_STACK_SIZE_KB` of the run.  Every spelling is a finished module, as in the
    scheduler (a `stack` one only counts for resume at the same stack size, which a replay
    does not model)."""
    mods, kills = {}, []
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 2:
            continue
        if f[0] == "killed":
            kills.append((unspell(f[1]), num(f[2]) if len(f) > 2 else None))
            continue
        if len(f) < 4:
            continue
        g = f + ["-"] * (11 - len(f))
        mods[unspell(f[1])] = dict(verdict=f[0], ms=num(g[2]), pk=num(g[3]), at=num(g[4]),
                                   decls=num(g[5]), parse=num(g[6]), check=num(g[7]),
                                   busy=num(g[8]), slowest=num(g[9]),
                                   threads=num(g[10]) or 1,
                                   stack=g[11] if len(f) > 11 else None)
    return mods, kills


def log_peaks(path, last=200):
    """The log's recorded peaks (DESIGN #546): the exact rss of the verdict lines (not `≥`), the
    last `last` of them in log order."""
    xs = []
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 4 and f[0] != "killed" and f[3].isdigit():
            xs.append(int(f[3]))
    return xs[-last:]


def read_profiles(d):
    """module -> normalised shape: a list of (fraction of the run, fraction of the peak)."""
    out = {}
    if not d:
        return out
    for fn in os.listdir(d):
        if not fn.endswith(".tsv"):
            continue
        pts = []
        for l in open(os.path.join(d, fn)):
            a = l.split()
            if len(a) >= 2 and a[0].isdigit() and a[1].isdigit():
                pts.append((int(a[0]), int(a[1])))
        if len(pts) < 3:
            continue
        t1 = pts[-1][0] or 1
        p = max(r for _, r in pts) or 1
        out[fn[:-4]] = [(t / t1, r / p) for t, r in pts]
    return out


def mean_shape(profiles, n=50):
    if not profiles:
        return None
    grid = [i / n for i in range(n + 1)]
    acc = [0.0] * (n + 1)
    for sh in profiles.values():
        xs = [x for x, _ in sh]
        for i, g in enumerate(grid):
            j = min(len(sh) - 1, bisect.bisect_left(xs, g))
            acc[i] += sh[j][1]
    return [(g, a / len(profiles)) for g, a in zip(grid, acc)]


class Shape:
    def __init__(self, pts):
        self.xs = [x for x, _ in pts]
        self.ys = [y for _, y in pts]

    def at(self, f):
        if f <= 0:
            return self.ys[0]
        if f >= 1:
            return self.ys[-1]
        j = bisect.bisect_right(self.xs, f)
        x0, x1 = self.xs[j - 1], self.xs[min(j, len(self.xs) - 1)]
        y0, y1 = self.ys[j - 1], self.ys[min(j, len(self.ys) - 1)]
        return y0 if x1 == x0 else y0 + (y1 - y0) * (f - x0) / (x1 - x0)


RAMP = None  # linear ramp: f itself


class Mod:
    __slots__ = ("m", "ms", "pk", "decls", "busy", "slowest", "shape")


# the McLEnumA class (CFSG, DESIGN #544): 87 748 declarations, 554 s at one thread, nearly all of
# it checking (busy 553.9 s), the slowest check 13.5 s, peak 1.41 GiB, parse 2.8 s
MCL = dict(verdict="0", ms=554000, pk=int(1.41 * 2 ** 20), at=0, decls=87748, parse=2800,
           check=553900, busy=553931, slowest=13489)


def build_mods(log, profiles, shape_default, heavy, heavy_time, heavy_mem, seed, mcl=0):
    rng = random.Random(seed)
    names = sorted(log)
    heavy_set = set(rng.sample(names, int(round(heavy * len(names))))) if heavy > 0 else set()
    if mcl:  # after the heavy draw, which stays that of the log alone
        log = dict(log, **{f"Synthetic.McL{i}": dict(MCL) for i in range(mcl)})
        names = sorted(log)
    out = {}
    for n in names:
        r = log[n]
        if r["ms"] is None or r["pk"] is None:
            continue
        x = Mod()
        x.m = n
        tf, mf = (heavy_time, heavy_mem) if n in heavy_set else (1, 1)
        x.ms = max(1, r["ms"]) * tf
        x.pk = max(1, r["pk"]) * mf
        x.decls = r["decls"] or 0
        busy = r["busy"] if r["busy"] is not None else 0
        x.busy = min(busy, r["ms"]) * tf
        x.slowest = min(r["slowest"] or 0, busy) * tf
        sp = profiles.get(n)
        x.shape = Shape(sp) if sp else shape_default
        out[n] = x
    return out, heavy_set


def quantile(sorted_xs, q):
    return sorted_xs[min(len(sorted_xs) - 1, int(len(sorted_xs) * q))]


class W:
    __slots__ = ("mod", "start", "dur", "pk", "hwm", "cur", "threads", "read_end", "resv", "rank",
                 "rose", "ring", "wpk")


def simulate(mods, order, budget_kib, jobs, tick=0.1, growth=10, typ_q=0.5,
             threads_d=0, threads_cap=0, thread_budget=0, thread_mem=0.0, reserve=None,
             install_serial=1.0, read_cap=0, max_time=10 ** 10, plan=True,
             margin_init=0.10, margin_floor=0.5, margin_stat="p99", margin_window=200,
             margin_nonzero=True, stagger=0, burst=0, threads_spare=False,
             threads_drain=0, drain_d=0, margin_excl="largest", seed_peaks=None,
             seed_sizes=None, seed_single=(), kill_by="sticky", gate="prot", drain=None,
             giant_kib=None, front_fifo=False, front_pos=False, size_rule="double",
             peak_window=None):
    """Returns the statistics of one replay.  Times in ms internally.  `budget_kib` is the hard
    limit (kills only above it); with `plan` admission plans against `hard - margin` (DESIGN
    #540): margin = max(margin_init x hard, the `margin_stat` of the last `margin_window`
    surprises), the plan at least `margin_floor` x hard.  A surprise is a stretch's largest
    max(0, the running workers' sets - what admission reserved for them when it last started
    one); a stretch ends at a start.  `margin_excl` (DESIGN #545) leaves one worker's excess out of
    a surprise: `largest` (the shipped rule) the largest single excess over its reservation,
    `protected` the protected worker's, `none` nobody's (#540); `largest-pos` sums only the
    other workers' positive excesses.  `stagger` (ms) and `burst` (starts per tick, 0: all that
    fit) only for the old policy (`OLD`).  A resumed run (DESIGN #546): `seed_peaks`, the log's
    recorded peaks, start the typical peak's window (the median holds at once from 20 of them);
    `seed_sizes`, module -> the largest set at its logged kills, puts those modules at the front in
    that order with the known size max(that, typical peak); `seed_single` modules run with one
    thread.  The kill rule (DESIGN #548): `kill_by="sticky"` the rule of #512 (the largest worker
    protected, sticky, the youngest others killed by start time), `"rank"` no protection, the
    workers of the latest queue position (`rank`, a requeued module keeps its own) killed first,
    `"start"` no protection, the latest started first, `"head"` the head slot: one worker starts
    the first module of the queue (the killed ones first) whenever it has none, fitting or not and
    whatever the gate, and is never killed for memory (alone over the limit: `memory`); the other
    slots admit as usual, and an overflow kills the youngest of them by start time (the head counts
    against the jobs; when it finishes it takes the next module before the other slots do); the
    `head_*` statistics: the time the head holds a giant, the part of it in which a slot and a
    queued module were free and the gate open but nothing fit, the head's starts into a room too
    small for its reservation (`head_forced`), and the kills and overflows while such a start
    runs; `gate="prot"` the growth gate of #560 (the
    protected worker's peak), `"local"` any running worker above its reservation (max(typical,
    known size)) whose peak rose within `growth` s, `"local-tight"` the same only while the current
    sets exceed the plan (for the head slot: the gate holds the other slots only), `"none"`; `drain` (s, None: none) the head of the killed
    modules, waiting that long and not fitting, holds every other start until it fits or nothing
    runs.  `front_pos` (the shipped rule of DESIGN #548): the queue is fixed, a killed module is
    unstarted again at its own position (the head takes the lowest unstarted position, the other
    slots the lowest that fits).  `front_fifo`: a killed module goes behind the killed ones already waiting (the order
    of the kills), not before them.  `giant_kib`: the waits (kill to restart) of modules at least that large are reported
    apart (`giant_wait_*`).  `size_rule` (DESIGN #566), a killed module's known size: `"double"`
    the rule of #512, max(set at the kill, typical peak, 2 x previous known size); `"max"` the
    largest set at any of its kills (admission takes it at least at the typical peak); `"relief"`
    as `"max"`, and a running worker counts at max(peak so far, typical peak), its known size left
    out, once it has run longer than at the kill that set the known size without reaching it;
    `"hwm"` as `"max"`, and a running worker never counts at its known size (only the start
    does).  The `res_*` statistics split the mean reservation into the current sets, the peaks
    above them, the typical peak above the peaks, the known sizes above both, and the part of
    the latter that only the doubling gives (`res_double_gib`).  `peak_window` (DESIGN #567,
    minutes, None: the all-time peak): a running worker counts at its windowed peak in place of
    its peak so far, the largest of its per-minute sample maxima over the current minute of its
    run and the `peak_window` before it (a ring of per-minute maxima, as the scheduler keeps it);
    the split's peak term is then that windowed peak above the current set.  `cascades`: the
    overflows that kill two or more workers, `kill_max` the most one overflow kills,
    `kills_young` the kills of workers younger than 10 minutes."""
    dt = int(tick * 1000)
    rank_of = {m: i for i, m in enumerate(order)}
    wait_by = {}
    surprises, ep_max, surprise_n = [], 0, 0
    hard = budget_kib

    def margin_of():
        base = int(margin_init * hard)
        xs = surprises[-margin_window:] if margin_window else surprises
        if not xs:
            return base
        v = sorted(xs)
        st = max(xs) if margin_stat == "max" else quantile(v, float(margin_stat[1:]) / 100)
        return max(base, st)

    def plan_of():
        if not plan or not hard:
            return budget_kib
        return max(int(margin_floor * hard), hard - margin_of())
    pending = [m for m in order if m in mods]
    pending.reverse()  # pop() from the end = the head
    front = []  # killed modules, head first
    sizes, kills_by = {}, {}
    # the largest set at any kill of each module, and the age of the run that reached it
    maxkill, kill_age = {}, {}
    waited_since = {}
    running = []
    peaks, typ = [], (budget_kib // jobs if budget_kib else 0)
    if seed_peaks:
        peaks = list(seed_peaks[-200:])
        if len(peaks) >= 20:
            typ = quantile(sorted(peaks), typ_q)
    if seed_sizes:
        again = [m for m in seed_sizes if m in mods]
        front = again
        pending = [m for m in pending if m not in seed_sizes]
        sizes = {m: max(typ, seed_sizes[m]) for m in again}
        maxkill = {m: seed_sizes[m] for m in again}
        if size_rule != "double":
            sizes = dict(maxkill)
    prot, prot_track = None, None
    # the head slot (`kill_by="head"`): its worker, whether it started into a room too small for
    # its reservation, and the statistics of DESIGN #548's head-slot question
    head, head_forced = None, False
    hs = dict(head_giant_ms=0, head_giant_starved_ms=0, head_starts=0, head_forced=0,
              head_forced_giants=0, kills_forced=0, overflows_forced=0, overflows=0)
    now, last_start = 0, -10 ** 9
    run_ms = mem_ms = res_ms = gate_ms = 0
    thr_ms = starved_ms = 0
    # the reservation split up (time-weighted KiB x ms): current sets, peaks above them, the
    # typical peak above the peaks, the known sizes above both, the doubling's part of those
    rs_cur = rs_hwm = rs_typ = rs_known = rs_double = 0
    kill_n = kill_ms = work_ms = prot_n = mem_verdicts = 0
    cascades = kill_max = kills_young = 0
    done = 0
    tb = thread_budget or jobs
    threads_used = 0

    drain_since, drain_ms_box = {}, [0]
    single = set(seed_single)  # killed while running with more than one thread: one thread from now on
    thread_starts = thread_sum = 0

    def threads_for(m, room_after):
        if threads_d <= 0 or m.m in single:
            return 1
        free = tb - threads_used
        if threads_spare:
            # leave the cores that memory could still fill with workers (at the typical peak,
            # as many as are queued): threads only from the cores memory cannot fill
            fit = (room_after // typ) if typ else free
            free = max(1, free - 1 - min(free - 1, fit, len(pending) + len(front)))
        t = min(free, m.decls // threads_d)
        if threads_cap:
            t = min(t, threads_cap)
        return max(1, t)

    def dur_pk(m, t):
        if t <= 1:
            return m.ms, m.pk
        install = (m.ms - m.busy) * (install_serial + (1 - install_serial) / t)
        return int(install + max(m.slowest, m.busy / t)), int(m.pk * (1 + thread_mem * (t - 1)))

    def rss(w, at):
        f = (at - w.start) / w.dur if w.dur else 1.0
        s = f if w.mod.shape is None else w.mod.shape.at(f)
        return int(w.pk * min(1.0, max(0.0, s)))

    def eff(w):
        k = sizes.get(w.mod.m, 0)
        if size_rule == "hwm" or (size_rule == "relief" and w.hwm < k
                                  and now - w.start > kill_age.get(w.mod.m, 0)):
            k = 0
        return max(w.wpk, typ, k)

    def sample_peak(w):
        # the windowed peak (DESIGN #567): per-minute maxima of the run in a ring
        if w.cur > w.hwm:
            w.hwm, w.rose = w.cur, now
        if peak_window is None:
            w.wpk = w.hwm
            return
        mi = (now - w.start) // 60000
        r = w.ring
        if r and r[-1][0] == mi:
            if w.cur > r[-1][1]:
                r[-1][1] = w.cur
        else:
            r.append([mi, w.cur])
        while r[0][0] < mi - peak_window:
            r.pop(0)
        w.wpk = max(x[1] for x in r)

    def kill(v):
        nonlocal threads_used, kill_n, kill_ms, work_ms, kills_young
        if now - v.start < 600000:
            kills_young += 1
        if head_forced and head in running:
            hs["kills_forced"] += 1
        running.remove(v)
        threads_used -= v.threads
        kill_n += 1
        kill_ms += now - v.start
        work_ms += now - v.start
        kills_by[v.mod.m] = kills_by.get(v.mod.m, 0) + 1
        if v.threads > 1:
            single.add(v.mod.m)
        if v.cur >= maxkill.get(v.mod.m, 0):
            maxkill[v.mod.m], kill_age[v.mod.m] = v.cur, now - v.start
        if size_rule == "double":
            sizes[v.mod.m] = max(v.cur, typ, 2 * sizes.get(v.mod.m, 0))
        else:
            sizes[v.mod.m] = maxkill[v.mod.m]
        if v.mod.m in front:
            front.remove(v.mod.m)
        if front_pos:
            # the fixed queue: unstarted again at its own position
            bisect.insort(front, v.mod.m, key=lambda m: rank_of.get(m, len(rank_of)))
        elif front_fifo:
            front.append(v.mod.m)  # the killed modules in the order of their kills
        else:
            front.insert(0, v.mod.m)
        waited_since[v.mod.m] = now

    total = len(pending)
    while (pending or front or running) and now < max_time:
        now += dt
        # sample, then the finished ones
        still = []
        for w in running:
            if now - w.start >= w.dur:
                pk = w.pk
                work_ms += w.dur
                done += 1
                threads_used -= w.threads
                peaks.append(pk)
                if len(peaks) > 200:
                    peaks.pop(0)
                if len(peaks) >= 20:
                    typ = quantile(sorted(peaks), typ_q)
            else:
                w.cur = rss(w, now)
                sample_peak(w)
                still.append(w)
        running = still
        if prot is not None and not any(w.mod.m == prot for w in running):
            prot = None
        cur_total = sum(w.cur for w in running)
        reserved = sum(eff(w) for w in running)
        if plan and running:
            exc = [w.cur - w.resv for w in running]
            top = max(0, max(exc))
            if margin_excl == "largest":
                ep = sum(exc) - top
            elif margin_excl == "largest-pos":
                ep = sum(e for e in exc if e > 0) - top
            elif margin_excl == "protected":
                ep = sum(exc) - max(0, next((w.cur - w.resv for w in running
                                             if w.mod.m == prot), 0))
            else:
                ep = sum(exc)
            ep_max = max(ep_max, ep)
        run_ms += len(running) * dt
        mem_ms += cur_total * dt
        res_ms += reserved * dt
        thr_ms += threads_used * dt
        for w in running:
            e = eff(w)
            ht = max(w.wpk, typ)
            rs_cur += w.cur * dt
            rs_hwm += (w.wpk - w.cur) * dt
            rs_typ += (ht - w.wpk) * dt
            rs_known += (e - ht) * dt
            rs_double += max(0, e - max(ht, maxkill.get(w.mod.m, 0))) * dt
        # the overflow
        if budget_kib and running and cur_total > budget_kib and kill_by != "sticky":
            if len(running) == 1:
                big = running[0]
                running = []
                threads_used -= big.threads
                work_ms += now - big.start
                mem_verdicts += 1
                done += 1
            else:
                key = (lambda w: w.rank) if kill_by == "rank" else (lambda w: (w.start, w.rank))
                hs["overflows"] += 1
                if head_forced and head in running:
                    hs["overflows_forced"] += 1
                left = cur_total
                n0 = kill_n
                while left > budget_kib and len(running) > 1:
                    # the head slot's worker is never killed for memory; alone it gets `memory`
                    cands = [w for w in running if w is not head]
                    if not cands:
                        break
                    v = max(cands, key=key)
                    left -= v.cur
                    kill(v)
                cascades += kill_n - n0 >= 2
                kill_max = max(kill_max, kill_n - n0)
        elif budget_kib and running and cur_total > budget_kib:
            if prot is None or not any(w.mod.m == prot for w in running):
                big = max(running, key=lambda w: (w.cur, w.hwm))
            else:
                big = next(w for w in running if w.mod.m == prot)
            if len(running) == 1:
                running = []
                threads_used -= big.threads
                work_ms += now - big.start
                mem_verdicts += 1
                done += 1
                prot = None
            else:
                if prot is None:
                    prot_n += 1
                prot = big.mod.m
                left = cur_total
                while left > budget_kib:
                    others = [w for w in running if w is not big]
                    if not others:
                        break
                    v = max(others, key=lambda w: w.start)
                    left -= v.cur
                    kill(v)
        # the growth gate
        growing = False
        if gate == "none":
            pass
        elif gate in ("local", "local-tight"):
            growing = growth > 0 and (gate == "local" or cur_total > plan_of()) and any(
                w.hwm > max(typ, sizes.get(w.mod.m, 0)) and now - w.rose < growth * 1000
                for w in running)
        elif prot is not None:
            hw = next((w.hwm for w in running if w.mod.m == prot), 0)
            if prot_track and prot_track[0] == prot:
                t = now if hw > prot_track[1] else prot_track[2]
                prot_track = (prot, max(hw, prot_track[1]), t)
                growing = growth > 0 and now - t < growth * 1000
            else:
                prot_track = (prot, hw, now)
                growing = growth > 0
        else:
            prot_track = None
        if growing and len(running) < jobs and (front or pending):
            gate_ms += dt
        started = False
        budget_plan = plan_of()

        def launch(pick, room):
            nonlocal threads_used, thread_starts, thread_sum, last_start
            mod = mods[pick]
            t = threads_for(mod, room - (sizes.get(pick, 0) or typ))
            w = W()
            w.mod, w.start, w.threads = mod, now, t
            w.dur, w.pk = dur_pk(mod, t)
            w.dur = max(w.dur, 1)
            w.read_end = now + int((mod.ms - mod.busy) * w.dur / max(1, mod.ms))
            w.hwm = w.cur = w.wpk = 0
            w.ring = []
            w.resv = 0
            w.rank = rank_of.get(pick, len(rank_of))
            w.rose = now
            if pick in waited_since:
                wait_by[pick] = wait_by.get(pick, 0) + now - waited_since.pop(pick)
            threads_used += t
            if t > 1:
                thread_starts += 1
            thread_sum += t
            running.append(w)
            last_start = now
            return w

        if kill_by == "head":
            if head is not None and head not in running:
                head, head_forced = None, False
            # the head slot: the first module of the queue, fitting or not, gate or not
            if head is None and (front or pending) and len(running) < jobs and threads_used < tb:
                room = (budget_plan - min(budget_plan, sum(eff(w) for w in running))) \
                    if budget_kib else 1 << 60
                if front_pos and front and pending and \
                        rank_of.get(pending[-1], 0) < rank_of.get(front[0], 0):
                    pick = pending.pop()
                else:
                    pick = front.pop(0) if front else pending.pop()
                need = max(typ, sizes.get(pick, 0))
                head_forced = bool(running) and need > room
                head = launch(pick, room)
                hs["head_starts"] += 1
                if head_forced:
                    hs["head_forced"] += 1
                    if giant_kib and mods[pick].pk >= giant_kib:
                        hs["head_forced_giants"] += 1
                started = True
        for _ in range(0 if growing else (burst or 10 ** 9)):
            if now - last_start < stagger or len(running) >= jobs or threads_used >= tb:
                break
            if started and stagger > 0:
                break
            # the read gate: at most `read_cap` workers in their read (install) phase at once
            if read_cap and sum(1 for w in running if now < w.read_end) >= read_cap:
                break
            room = (budget_plan - min(budget_plan, sum(eff(w) for w in running))) \
                if budget_kib else 1 << 60
            pick = None
            if drain is not None and front and running:
                h = front[0]
                if sizes.get(h, 0) > room and now - waited_since.get(h, now) >= drain * 1000:
                    # the drain: no other start until the head of the killed modules fits
                    drain_ms_box[0] += dt
                    break
            for m in front:
                if not running or sizes.get(m, 0) <= room:
                    pick = m
                    break
            if front_pos and pick is not None and pending and (not running or typ <= room) \
                    and rank_of.get(pending[-1], 0) < rank_of.get(pick, 0):
                pick = pending.pop()  # the fixed queue: the lowest position that fits
            elif pick is not None:
                front.remove(pick)
            elif front and reserve is not None and running and \
                    (reserve == 0 or now - waited_since.get(front[0], now) >= reserve * 1000):
                pass  # drain for the head of the killed modules
            elif pending and (not running or typ <= room):
                h = pending[-1]
                if threads_drain and threads_d and running and h not in single and \
                        mods[h].decls // (drain_d or threads_d) >= tb and tb - threads_used < tb:
                    # a module that could use every core: no other start until they are free,
                    # for at most `threads_drain` s
                    since = drain_since.setdefault(h, now)
                    if now - since < threads_drain * 1000:
                        drain_ms_box[0] += dt
                        break
                pick = pending.pop()
            if pick is None:
                break
            launch(pick, room)
            started = True
        if not started and (front or pending) and len(running) < jobs and threads_used < tb:
            starved_ms += dt  # a slot free, a module queued, and nothing started
        if kill_by == "head" and head is not None and head in running and giant_kib \
                and head.mod.pk >= giant_kib:
            hs["head_giant_ms"] += dt
            # memory-starved: a slot and a queued module, the gate open, and still no start fits
            if (front or pending) and len(running) < jobs and threads_used < tb and not growing:
                hs["head_giant_starved_ms"] += dt
        if started and plan:
            # the episode ends: its surprise recorded, the reservations as admission saw them
            if ep_max > 0 or not margin_nonzero:
                surprises.append(max(0, ep_max))
                surprise_n += 1
                if len(surprises) > 10000:
                    surprises.pop(0)
            ep_max = 0
            for w in running:
                w.resv = eff(w)
    for m, t in waited_since.items():  # still waiting at the end (`max_time`)
        wait_by[m] = wait_by.get(m, 0) + now - t
    gw = [t for m, t in wait_by.items() if giant_kib and mods[m].pk >= giant_kib]
    span = max(1, now)
    # a lower bound at one thread per worker: the work over the jobs, the memory-time over the
    # budget (each module at the mean of its shape), the longest module
    ms = [mods[m] for m in order if m in mods]
    area = sum(x.pk * x.ms * (0.5 if x.shape is None else sum(x.shape.ys) / len(x.shape.ys))
               for x in ms)
    lb = max(sum(x.ms for x in ms) / jobs, area / budget_kib if budget_kib else 0,
             max(x.ms for x in ms))
    return dict(plan_end_gib=plan_of() / 2 ** 20,
                surprises=surprise_n,
                surprise_max_gib=(max(surprises) if surprises else 0) / 2 ** 20,
                makespan_s=now / 1000, lower_bound_s=lb / 1000, modules=total, done=done,
                running=run_ms / span, mem_gib=mem_ms / span / 2 ** 20,
                reserved_gib=res_ms / span / 2 ** 20, kills=kill_n, kill_modules=len(kills_by),
                lost_s=kill_ms / 1000, lost_pct=100 * kill_ms / max(1, work_ms),
                gate_s=gate_ms / 1000, protections=prot_n, memory_verdicts=mem_verdicts,
                thread_starts=thread_starts, single=len(single),
                threads_mean=thread_sum / max(1, total), drain_s=drain_ms_box[0] / 1000,
                wait_max_s=max(wait_by.values(), default=0) / 1000,
                wait_sum_s=sum(wait_by.values()) / 1000,
                giant_waited=len(gw), giant_wait_max_s=max(gw, default=0) / 1000,
                giant_wait_sum_s=sum(gw) / 1000,
                threads_running=thr_ms / span, starved_s=starved_ms / 1000,
                res_cur_gib=rs_cur / span / 2 ** 20, res_hwm_gib=rs_hwm / span / 2 ** 20,
                res_typ_gib=rs_typ / span / 2 ** 20, res_known_gib=rs_known / span / 2 ** 20,
                res_double_gib=rs_double / span / 2 ** 20,
                cascades=cascades, kill_max=kill_max, kills_young=kills_young,
                **{k: (v / 1000 if k.endswith("_ms") else v) for k, v in hs.items()})


def make_order(mods, how, graph_file):
    if how == "graph":
        g = [l.strip() for l in open(graph_file) if l.strip()]
        seen = set(g)
        return g + sorted(m for m in mods if m not in seen)
    return [m for _, _, m in sorted((fnv1a(spell(m)), spell(m), m) for m in mods)]


def hms(s):
    s = int(s)
    return f"{s // 3600}h{s % 3600 // 60:02d}m{s % 60:02d}s"


def fmt(r):
    return (f"makespan {hms(r['makespan_s'])} (bound {hms(r['lower_bound_s'])})  "
            f"running {r['running']:5.2f}  "
            f"mem {r['mem_gib']:5.1f} GiB (res {r['reserved_gib']:5.1f})  kills {r['kills']:5d} "
            f"({r['kill_modules']} mods, lost {hms(r['lost_s'])} = {r['lost_pct']:4.1f} %)  "
            f"gate {hms(r['gate_s'])}  memory {r['memory_verdicts']}  "
            f"threaded starts {r['thread_starts']}")


# the policy before #540: no planning budget, one start per tick, 200 ms apart
OLD = dict(plan=False, stagger=200, burst=1, threads_d=0)

VARIANTS = [
    ("a current", OLD),
    ("b threads k=10 cap=4", dict(OLD, threads_d=10, threads_cap=4)),
    ("b threads k=30 cap=4", dict(OLD, threads_d=30, threads_cap=4)),
    ("b threads k=30 cap=8", dict(OLD, threads_d=30, threads_cap=8)),
    ("b threads k=100 cap=8", dict(OLD, threads_d=100, threads_cap=8)),
    ("b threads k=30 cap=4, stagger 0, all starts",
     dict(OLD, threads_d=30, threads_cap=4, stagger=0, burst=64)),
    ("c graph order", dict(OLD, order="graph")),
    ("d reserve now", dict(OLD, reserve=0)),
    ("d reserve 60s", dict(OLD, reserve=60)),
    ("e typical p75", dict(OLD, typ_q=0.75)),
    ("f growth gate off", dict(OLD, growth=0)),
    ("g stagger 50ms", dict(OLD, stagger=50)),
    ("g stagger 10ms", dict(OLD, stagger=10)),
    ("g stagger 0", dict(OLD, stagger=0)),
    ("h stagger 0, all starts per tick", dict(OLD, stagger=0, burst=64)),
    ("i stagger 0, at most 2 reading", dict(OLD, stagger=0, burst=64, read_cap=2)),
    ("i stagger 0, at most 4 reading", dict(OLD, stagger=0, burst=64, read_cap=4)),
]

_G = {}


def _one(job):
    data, budget, jobs, name, kw = job
    mods, orders, base = _G[data]
    kw = dict(base, **kw)
    order = orders[kw.pop("order", "shuffled")]
    scale = kw.pop("scale", 1.0)
    r = simulate(mods, order, int(budget * scale * 2 ** 20), jobs, **kw)
    return (data, budget, jobs, name, r)


# DESIGN #540's comparison: the old policy at 0.85 x the limit (the maintainer's 40 of 47 GiB) and
# at the limit, the new one at the limit (and margin statistics)
COMPARE = [
    ("old at 0.85 x limit", dict(OLD, scale=0.85)),
    ("old at the limit", dict(OLD)),
    ("no stagger, plan = limit", dict(plan=False)),
    ("new, margin p95", dict(margin_stat="p95")),
    ("new, margin p99 (shipped)", dict()),
    ("new, margin max", dict(margin_stat="max")),
]


def compare(a, log, prof, default, base):
    import multiprocessing
    cases = [c.split(":") for c in a.compare_cases.split(",")]
    for name, h, hm in [("real", 0.0, 1), ("heavy", 0.01, 10), ("heavy30", 0.01, 30)]:
        if any(c[0] == name for c in cases):
            mods, _ = build_mods(log, prof, default, h, a.heavy_time, hm, a.seed)
            _G[name] = (mods, {"shuffled": make_order(mods, "shuffled", None)}, base)
    jobs = [(d, float(b), int(j), n, kw) for d, b, j in cases for n, kw in COMPARE]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    print("| data | limit | jobs | policy | makespan | running | kills (modules) | lost | "
          "plan at the end |")
    print("|---|---|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        pl = f"{r['plan_end_gib']:.1f}" if not n.startswith("old") else ""
        print(f"| {d} | {b:g} | {j} | {n} | {hms(r['makespan_s'])} | {r['running']:.2f} | "
              f"{r['kills']} ({r['kill_modules']}) | {hms(r['lost_s'])} = {r['lost_pct']:.1f} % | "
              f"{pl} |")


# DESIGN #544's data sets: name -> (heavy fraction, heavy memory factor, McLEnumA-like modules)
DATASETS = {"real": (0.0, 1, 0), "heavy": (0.01, 10, 0), "heavy30": (0.01, 30, 0),
            "mcl": (0.0, 1, 10), "mclheavy30": (0.01, 30, 10)}


def saw_shape(name):
    """DESIGN #566's synthetic sawtooth: 2-6 teeth over the run (by the module's name), each
    rising from 8 % of the peak to its level over 85 % of its stretch and falling back to 8 %
    (the last one ends at its level); one tooth reaches the peak, the others 0.5-1.0 of it (the
    CFSG workers seen going 13.5 -> 1.1 -> 11.4 GiB)."""
    rng = random.Random(fnv1a(name))
    k = rng.randint(2, 6)
    lv = [rng.uniform(0.5, 1.0) for _ in range(k)]
    lv[rng.randrange(k)] = 1.0
    pts = [(0.0, 0.0)]
    for i, l in enumerate(lv):
        a = i / k
        if i:
            pts.append((a, 0.08))
        pts.append((a + 0.85 / k, l))
        if i < k - 1:
            pts.append((a + 0.95 / k, 0.08))
    pts.append((1.0, lv[-1]))
    return Shape(pts)


def restart_mods(cfsg_log, reps, giants, seed, prof, default, mid=False, saw=False):
    """DESIGN #545's CFSG-like data: the modules of a real CFSG log (`cfsg_log`), `reps` copies of
    each (names suffixed), in the shuffled order; with `giants` > 0 the queue begins with that many
    synthetic giants (peaks uniform in 10-35 GiB, times log-uniform in 30 min-5 h, seed `seed`),
    as after a restart whose interrupted runs were the long ones; with `mid` (DESIGN #548's
    `starve`) the giants are spread evenly over the middle half of the queue instead, so that they
    meet, are killed and come back while the stream of the others runs."""
    import math
    log, _ = read_log(cfsg_log)
    big = {}
    for r in range(reps):
        for n, v in log.items():
            big[n if r == 0 else f"{n}.Rep{r}"] = v
    mods, _ = build_mods(big, prof, default, 0.0, 1, 1, seed)
    if saw:
        for x in mods.values():
            x.shape = saw_shape(x.m)
    order = make_order(mods, "shuffled", None)
    rng = random.Random(seed)
    head = []
    for i in range(giants):
        x = Mod()
        x.m = f"Synthetic.Giant{i}"
        x.ms = int(1000 * 60 * math.exp(rng.uniform(math.log(30), math.log(300))))
        x.pk = int(rng.uniform(10, 35) * 2 ** 20)
        x.decls, x.busy, x.slowest, x.shape = 16, int(x.ms * 0.98), int(x.ms * 0.2), None
        if saw:
            x.shape = saw_shape(x.m)
        mods[x.m] = x
        head.append(x.m)
    if mid and giants:
        n = len(order)
        out = list(order)
        for i, g in reversed(list(enumerate(head))):
            out.insert(n // 4 + i * (n // 2) // giants, g)
        return mods, out
    return mods, head + order


# DESIGN #548's kill rules: (name, kill_by, gate, drain s)
RANK_RULES = [("today: sticky protection, youngest by start", "sticky", "prot", None),
              ("A: rank, local gate", "rank", "local", None),
              ("B: rank, local gate, drain T=0", "rank", "local", 0),
              ("B: rank, local gate, drain T=2min", "rank", "local", 120),
              ("B: rank, local gate, drain T=10min", "rank", "local", 600),
              ("start, local gate, drain T=0", "start", "local", 0),
              ("start, local gate, drain T=2min", "start", "local", 120),
              ("start, local gate, drain T=10min", "start", "local", 600),
              ("A0: rank, no gate", "rank", "none", None),
              ("B0: rank, no gate, drain T=0", "rank", "none", 0),
              ("B0: rank, no gate, drain T=2min", "rank", "none", 120),
              ("B0: rank, no gate, drain T=10min", "rank", "none", 600),
              ("start, no gate, drain T=0", "start", "none", 0),
              ("At: rank, local gate while over the plan", "rank", "local-tight", None),
              ("Bt: rank, local gate while over the plan, drain T=0", "rank", "local-tight", 0),
              ("Bt: rank, local gate while over the plan, drain T=2min", "rank", "local-tight", 120),
              ("Bt: rank, local gate while over the plan, drain T=10min", "rank", "local-tight",
               600),
              ("start, local gate while over the plan, drain T=0", "start", "local-tight", 0),
              ("today, gate off", "sticky", "none", None),
              ("H: head slot, local gate while over the plan", "head", "local-tight", None),
              ("H0: head slot, no gate", "head", "none", None),
              ("Hf: head slot, tight gate, killed in kill order", "head", "local-tight", None,
               dict(front_fifo=True)),
              ("Hf0: head slot, no gate, killed in kill order", "head", "none", None,
               dict(front_fifo=True)),
              ("Hp0: head slot, no gate, fixed queue", "head", "none", None,
               dict(front_pos=True))]


def rank_compare(a, log, prof, default, base):
    """DESIGN #548's table: each case `data:limit GiB:jobs` (data as in `margin_compare`, and
    `starve`: the CFSG log's modules with `--giants` giants spread over the middle half of the
    queue) under each rule of `RANK_RULES`; the CFSG-like data at a tick of 100 ms."""
    import multiprocessing
    cases = [c.split(":") for c in a.rank_cases.split(",")]
    for name in {c[0] for c in cases}:
        kw = {}
        if name in ("cfsg", "restart", "starve"):
            mods, order = restart_mods(a.cfsg_log, a.cfsg_reps,
                                       0 if name == "cfsg" else a.giants, a.seed, prof, default,
                                       mid=name == "starve")
            kw = dict(tick=max(a.tick, 0.1))
        else:
            h, hm, mcl = DATASETS[name]
            mods, _ = build_mods(log, prof, default, h, a.heavy_time, hm, a.seed, mcl)
            order = make_order(mods, "shuffled", None)
        _G[name] = (mods, {"shuffled": order}, dict(base, **kw))
    jobs = [(d, float(b), int(j), n, dict(kill_by=k, gate=g, drain=t, threads_d=a.threads_d,
                                          threads_spare=True,
                                          giant_kib=int(float(b) * 2 ** 20 / 8), **x))
            for d, b, j in cases for i, (n, k, g, t, *xs) in enumerate(RANK_RULES)
            for x in [xs[0] if xs else {}]
            if not a.rank_rules or str(i) in a.rank_rules.split(",")]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    if a.json:
        json.dump([dict(data=d, budget=b, jobs=j, variant=n, **r) for d, b, j, n, r in res],
                  open(a.json_out or "/dev/stdout", "w"))
        return
    print("| case | rule | makespan | running | kills (modules) | lost | gate | drain | "
          "giants waited | giant wait max | giant wait sum | wait max (all) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        print(f"| {d} {b:g}G j{j} | {n} | {hms(r['makespan_s'])} | {r['running']:.2f} | "
              f"{r['kills']} ({r['kill_modules']}) | {hms(r['lost_s'])} = {r['lost_pct']:.1f} % | "
              f"{hms(r['gate_s'])} | {hms(r['drain_s'])} | {r['giant_waited']} | "
              f"{hms(r['giant_wait_max_s'])} | {hms(r['giant_wait_sum_s'])} | "
              f"{hms(r['wait_max_s'])} |")


# DESIGN #566's known-size rules, all under the head slot with the fixed queue (DESIGN #548)
SIZE_RULES = [("(a) doubled (#512)", "double"), ("(b) largest kill set", "max"),
              ("(c) largest kill set, relief", "relief"),
              ("(d) largest kill set, starts only", "hwm")]


# DESIGN #567's peak windows (minutes; None: the all-time peak), with the doubled known size
WINDOW_RULES = [("today: all-time peak", None), ("W = 2 min", 2), ("W = 5 min", 5),
                ("W = 10 min", 10), ("W = 30 min", 30)]


def size_compare(a, log, prof, default, base, window=False):
    """DESIGN #566's table: each case `data:limit GiB:jobs` (data as in `rank_compare`; a
    CFSG-like set with `-saw` has every module on a sawtooth, `saw_shape`, in place of the ramp)
    under each known-size rule of `SIZE_RULES`, with the shipped head slot and fixed
    queue.  With `window` DESIGN #567's: the same cases under each peak window of
    `WINDOW_RULES` (`--window-rules`), the known size doubled as shipped."""
    import multiprocessing
    cases = [c.split(":") for c in a.size_cases.split(",")]
    for name in {c[0] for c in cases}:
        kw = {}
        base_name, saw = (name[:-4], True) if name.endswith("-saw") else (name, False)
        if base_name in ("cfsg", "restart", "starve"):
            mods, order = restart_mods(a.cfsg_log, a.cfsg_reps,
                                       0 if base_name == "cfsg" else a.giants, a.seed, prof,
                                       default, mid=base_name == "starve", saw=saw)
            kw = dict(tick=max(a.tick, 0.1))
        else:
            h, hm, mcl = DATASETS[name]
            mods, _ = build_mods(log, prof, default, h, a.heavy_time, hm, a.seed, mcl)
            order = make_order(mods, "shuffled", None)
        _G[name] = (mods, {"shuffled": order}, dict(base, **kw))
    rules, pick = ([(n, dict(peak_window=w)) for n, w in WINDOW_RULES], a.window_rules) \
        if window else ([(n, dict(size_rule=r)) for n, r in SIZE_RULES], a.size_rules)
    jobs = [(d, float(b), int(j), n, dict(kill_by="head", gate="none", front_pos=True,
                                          threads_d=a.threads_d, threads_spare=True,
                                          giant_kib=int(float(b) * 2 ** 20 / 8), **kw))
            for d, b, j in cases for i, (n, kw) in enumerate(rules)
            if not pick or str(i) in pick.split(",")]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    if a.json:
        json.dump([dict(data=d, budget=b, jobs=j, variant=n, **r) for d, b, j, n, r in res],
                  open(a.json_out or "/dev/stdout", "w"))
        return
    print("| case | rule | makespan | workers | threads | kills (modules) | lost | "
          "giant wait max | reserved = cur + peak + typical + known (doubling) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        print(f"| {d} {b:g}G j{j} | {n} | {hms(r['makespan_s'])} | {r['running']:.2f} | "
              f"{r['threads_running']:.2f} | {r['kills']} ({r['kill_modules']}) | "
              f"{hms(r['lost_s'])} = {r['lost_pct']:.1f} % | {hms(r['giant_wait_max_s'])} | "
              f"{r['reserved_gib']:.1f} = {r['res_cur_gib']:.1f} + {r['res_hwm_gib']:.1f} + "
              f"{r['res_typ_gib']:.1f} + {r['res_known_gib']:.1f} ({r['res_double_gib']:.1f}) |")


# DESIGN #545's margin rules: whose excess a surprise leaves out
MARGIN_RULES = [("#540: nobody", "none"), ("largest", "largest"),
                ("largest, positive parts", "largest-pos"), ("protected", "protected")]


def resume_compare(a, log, prof, default, base):
    """DESIGN #546's table: the restart scenario of #545 (`restart` data: the CFSG log's modules
    after `--giants` synthetic giants at the head of the queue) without seeding, with the typical
    peak seeded from the log's recorded peaks, and with the giants' kill sizes seeded too (the
    set at the kill `--kill-frac` of the peak; they go to the front)."""
    import multiprocessing
    cases = [c.split(":") for c in a.margin_cases.split(",")]
    mods, order = restart_mods(a.cfsg_log, a.cfsg_reps, a.giants, a.seed, prof, default)
    peaks = log_peaks(a.cfsg_log)
    giants = {m: int(a.kill_frac * mods[m].pk) for m in order if m.startswith("Synthetic.Giant")}
    _G["restart"] = (mods, {"shuffled": order}, base)
    variants = [("unseeded", {}), ("typical peak seeded", dict(seed_peaks=peaks)),
                ("typical peak and kill sizes seeded", dict(seed_peaks=peaks, seed_sizes=giants))]
    jobs = [("restart", float(b), int(j), n, dict(margin_excl="largest", threads_d=a.threads_d,
                                                  threads_spare=True, **kw))
            for d, b, j in cases for n, kw in variants]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    print("| case | seeding | makespan | running | kills (modules) | lost | memory verdicts |")
    print("|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        print(f"| {d} {b:g}G j{j} | {n} | {hms(r['makespan_s'])} | {r['running']:.2f} | "
              f"{r['kills']} ({r['kill_modules']}) | {hms(r['lost_s'])} = {r['lost_pct']:.1f} % | "
              f"{r['memory_verdicts']} |")


def margin_compare(a, log, prof, default, base):
    """DESIGN #545's table: each case `data:limit GiB:jobs` (data `real`, `heavy`, `heavy30` from
    the log; `cfsg`, `restart` from `--cfsg-log`) under each rule of `MARGIN_RULES`."""
    import multiprocessing
    cases = [c.split(":") for c in a.margin_cases.split(",")]
    for name in {c[0] for c in cases}:
        if name in ("cfsg", "restart"):
            mods, order = restart_mods(a.cfsg_log, a.cfsg_reps,
                                       a.giants if name == "restart" else 0, a.seed, prof, default)
        else:
            h, hm, mcl = DATASETS[name]
            mods, _ = build_mods(log, prof, default, h, a.heavy_time, hm, a.seed, mcl)
            order = make_order(mods, "shuffled", None)
        _G[name] = (mods, {"shuffled": order}, base)
    jobs = [(d, float(b), int(j), n, dict(margin_excl=k, threads_d=a.threads_d,
                                          threads_spare=True))
            for d, b, j in cases for n, k in MARGIN_RULES]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    if a.json:
        json.dump([dict(data=d, budget=b, jobs=j, variant=n, **r) for d, b, j, n, r in res],
                  open(a.json_out or "/dev/stdout", "w"))
        return
    print("| case | rule | makespan | running | kills (modules) | lost | plan at the end | "
          "largest surprise |")
    print("|---|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        print(f"| {d} {b:g}G j{j} | {n} | {hms(r['makespan_s'])} | {r['running']:.2f} | "
              f"{r['kills']} ({r['kill_modules']}) | {hms(r['lost_s'])} = {r['lost_pct']:.1f} % | "
              f"{r['plan_end_gib']:.1f} | {r['surprise_max_gib']:.1f} |")


def calibrate(a, log, prof, default, base):
    """The thread rule's divisor d against one thread (d = 0) on each case `data:limit GiB:jobs`;
    `jobs` is the thread budget.  One row per case, a cell per d: makespan, kills."""
    import multiprocessing
    cases = [c.split(":") for c in a.calibrate_cases.split(",")]
    ds = [int(x) for x in a.calibrate_d.split(",")]
    caps = [int(x) for x in (a.calibrate_caps or "0").split(",")]
    for name in {c[0] for c in cases}:
        h, hm, mcl = DATASETS[name]
        mods, _ = build_mods(log, prof, default, h, a.heavy_time, hm, a.seed, mcl)
        _G[name] = (mods, {"shuffled": make_order(mods, "shuffled", None)}, base)
    spares = {"both": [False, True], "only": [True]}.get(a.calibrate_spare, [False])
    drains = [int(x) for x in (a.calibrate_drain or "0").split(",")]
    variants = [(f"d={d}" + (f" cap={c}" if c else "") + (" spare" if sp else "")
                 + (f" drain {dr}s" if dr else ""),
                 dict(threads_d=d, threads_cap=c, threads_spare=sp, threads_drain=dr,
                      drain_d=a.calibrate_drain_d))
                for d in ds for c in (caps if d else [0]) for sp in (spares if d else [False])
                for dr in (drains if d else [0])]
    jobs = [(d, float(b), int(j), n, kw) for d, b, j in cases for n, kw in variants]
    with multiprocessing.get_context("fork").Pool(a.procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    if a.json:
        json.dump([dict(data=d, budget=b, jobs=j, variant=n, **r) for d, b, j, n, r in res],
                  open(a.json_out or "/dev/stdout", "w"))
        return
    print("| case | bound | " + " | ".join(n for n, _ in variants) + " |")
    print("|---|---|" + "---|" * len(variants))
    by = {}
    for d, b, j, n, r in res:
        by.setdefault((d, b, j), []).append(r)
    for (d, b, j), rs in by.items():
        cells = [f"{r['makespan_s'] / 60:.1f} ({r['kills']}, {r['thread_starts']})" for r in rs]
        print(f"| {d} {b:g}G j{j} | {rs[0]['lower_bound_s'] / 60:.1f} | " + " | ".join(cells)
              + " |")


def grid(a, datasets, budgets, jobss, variants, procs):
    import multiprocessing
    jobs = [(d, b, j, n, kw) for d in datasets for b in budgets for j in jobss
            for n, kw in variants]
    with multiprocessing.get_context("fork").Pool(procs) as pool:
        res = pool.map(_one, jobs, chunksize=1)
    print("| data | budget | jobs | variant | makespan | bound | running | mem GiB | kills (mods) "
          "| lost | gate | memory |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for d, b, j, n, r in res:
        print(f"| {d} | {b:g} | {j} | {n} | {hms(r['makespan_s'])} | {hms(r['lower_bound_s'])} | "
              f"{r['running']:.2f} | "
              f"{r['mem_gib']:.1f} | {r['kills']} ({r['kill_modules']}) | {r['lost_pct']:.1f} % | "
              f"{hms(r['gate_s'])} | {r['memory_verdicts']} |")
    if a.json:
        json.dump([dict(data=d, budget=b, jobs=j, variant=n, **r) for d, b, j, n, r in res],
                  open(a.json_out or "/dev/stdout", "w"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("log")
    ap.add_argument("--profiles")
    ap.add_argument("--shape", choices=["ramp", "mean"], default="ramp")
    ap.add_argument("--budget", type=float, default=16, help="GiB, 0 for none")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--tick", type=float, default=0.1)
    ap.add_argument("--old", action="store_true",
                    help="the policy before #540: no planning budget, starts 200 ms apart")
    ap.add_argument("--margin-init", type=float, default=0.10)
    ap.add_argument("--margin-floor", type=float, default=0.5)
    ap.add_argument("--margin-stat", default="p99", help="max or pNN")
    ap.add_argument("--margin-window", type=int, default=200)
    ap.add_argument("--growth", type=int, default=10)
    ap.add_argument("--read-cap", type=int, default=0,
                    help="at most this many workers in their read phase (0: no such gate)")
    ap.add_argument("--typ-q", type=float, default=0.5)
    ap.add_argument("--order", choices=["shuffled", "graph"], default="shuffled")
    ap.add_argument("--graph-order")
    ap.add_argument("--threads-d", type=int, default=30,
                    help="threads per worker max(1, min(cap, decls / D)) (0: one thread)")
    ap.add_argument("--threads-greedy", action="store_true",
                    help="cap = all free threads, not only those memory cannot fill")
    ap.add_argument("--threads-cap", type=int, default=0, help="0: none")
    ap.add_argument("--mcl", type=int, default=0,
                    help="add this many McLEnumA-like modules (DESIGN #544)")
    ap.add_argument("--calibrate", action="store_true", help="the table of DESIGN #544")
    ap.add_argument("--calibrate-cases",
                    default="real:16:8,real:16:32,real:1.5:8,real:3:16,heavy:8:16,heavy:16:32,"
                            "heavy30:24:16,heavy30:47:32,mcl:16:8,mcl:16:32,mcl:47:32,"
                            "mclheavy30:47:32")
    ap.add_argument("--calibrate-d", default="0,10,30,100,300")
    ap.add_argument("--calibrate-caps", default="0", help="comma-separated, 0: none")
    ap.add_argument("--calibrate-drain", default="0",
                    help="comma-separated seconds a module that could use every core may hold "
                         "other starts (0: none)")
    ap.add_argument("--calibrate-drain-d", type=int, default=0,
                    help="the drain only for decls / this >= the thread budget (0: d)")
    ap.add_argument("--calibrate-spare", default="", choices=["", "both", "only"],
                    help="also the variant that leaves the cores memory could fill to workers")
    ap.add_argument("--thread-budget", type=int, default=0)
    ap.add_argument("--thread-mem", type=float, default=0.0)
    ap.add_argument("--install-serial", type=float, default=1.0,
                    help="the install phase's serial fraction at more threads (1: not parallel)")
    ap.add_argument("--reserve", type=int, default=None, help="seconds; 0 drains at once")
    ap.add_argument("--heavy", type=float, default=0.0)
    ap.add_argument("--heavy-time", type=float, default=100)
    ap.add_argument("--heavy-mem", type=float, default=10)
    ap.add_argument("--seed", type=int, default=518)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--json-out")
    ap.add_argument("--grid", action="store_true", help="the variant table: real and heavy data")
    ap.add_argument("--grid-budgets", default="8,16,32")
    ap.add_argument("--grid-jobs", default="8,16,32")
    ap.add_argument("--grid-variants", default="", help="comma-separated prefixes, empty for all")
    ap.add_argument("--compare", action="store_true", help="the comparison of DESIGN #540")
    ap.add_argument("--compare-cases",
                    default="real:1.5:8,real:3:16,heavy:8:16,heavy:16:32,heavy30:24:16,"
                            "heavy30:47:16,heavy30:47:32")
    ap.add_argument("--margin-excl", default="largest",
                    choices=["largest", "largest-pos", "protected", "none"],
                    help="whose excess a surprise leaves out (DESIGN #545; none: #540)")
    ap.add_argument("--margin-compare", action="store_true", help="the table of DESIGN #545")
    ap.add_argument("--margin-cases",
                    default="real:1.5:8,real:3:16,heavy:8:16,heavy:16:32,heavy30:24:16,"
                            "heavy30:47:32,cfsg:45:32,restart:45:32,restart:45:16")
    ap.add_argument("--cfsg-log", help="a CFSG scheduler log for the cases cfsg and restart")
    ap.add_argument("--cfsg-reps", type=int, default=5, help="copies of the CFSG log's modules")
    ap.add_argument("--giants", type=int, default=20, help="giants at the head of `restart`")
    ap.add_argument("--resume-compare", action="store_true", help="the table of DESIGN #546")
    ap.add_argument("--kill-frac", type=float, default=0.6,
                    help="the giants' set at their logged kill, as a fraction of their peak")
    ap.add_argument("--kill-by", default="head", choices=["head", "sticky", "rank", "start"],
                    help="the single replay's kill rule (DESIGN #548; head: the shipped one)")
    ap.add_argument("--gate", default="none", choices=["none", "prot", "local", "local-tight"],
                    help="the single replay's growth gate (none: the shipped rule)")
    ap.add_argument("--requeue", default="position", choices=["position", "front", "kills"],
                    help="where a killed module waits: its own position (shipped), the front "
                         "(newest kill first), or behind the killed ones (kill order)")
    ap.add_argument("--rank-compare", action="store_true", help="the table of DESIGN #548")
    ap.add_argument("--rank-rules", default="", help="comma-separated indices of RANK_RULES")
    ap.add_argument("--rank-cases",
                    default="real:1.5:8,real:3:16,heavy:8:16,heavy:16:32,heavy30:24:16,"
                            "heavy30:47:32,cfsg:45:32,restart:45:32,restart:45:16,"
                            "starve:45:32,starve:45:16")
    ap.add_argument("--size-compare", action="store_true", help="the table of DESIGN #566")
    ap.add_argument("--size-rules", default="", help="comma-separated indices of SIZE_RULES")
    ap.add_argument("--size-cases",
                    default="real:1.5:8,real:3:16,heavy:8:16,heavy:16:32,heavy30:24:16,"
                            "heavy30:47:32,cfsg:45:32,restart:45:32,restart:45:16,"
                            "starve:45:32,starve:45:16")
    ap.add_argument("--window-compare", action="store_true", help="the table of DESIGN #567")
    ap.add_argument("--window-rules", default="", help="comma-separated indices of WINDOW_RULES")
    ap.add_argument("--procs", type=int, default=8)
    a = ap.parse_args()
    log, _ = read_log(a.log)
    prof = read_profiles(a.profiles)
    default = Shape(mean_shape(prof)) if a.shape == "mean" and prof else None
    base = dict(tick=a.tick, growth=a.growth, typ_q=a.typ_q,
                thread_mem=a.thread_mem, install_serial=a.install_serial)
    if a.compare:
        compare(a, log, prof, default, base)
        return
    if a.grid:
        sets = [("real", 0.0)] + ([("heavy", a.heavy or 0.01)])
        for name, h in sets:
            mods, _ = build_mods(log, prof, default, h, a.heavy_time, a.heavy_mem, a.seed)
            orders = {"shuffled": make_order(mods, "shuffled", None)}
            if a.graph_order:
                orders["graph"] = make_order(mods, "graph", a.graph_order)
            _G[name] = (mods, orders, base)
        pre = [p for p in a.grid_variants.split(",") if p]
        vs = [(n, kw) for n, kw in VARIANTS if (not pre or any(n.startswith(p) for p in pre))
              and (a.graph_order or kw.get("order") != "graph")]
        grid(a, [n for n, _ in sets], [float(x) for x in a.grid_budgets.split(",")],
             [int(x) for x in a.grid_jobs.split(",")], vs, a.procs)
        return
    if a.calibrate:
        calibrate(a, log, prof, default, base)
        return
    if a.resume_compare:
        resume_compare(a, log, prof, default, base)
        return
    if a.margin_compare:
        margin_compare(a, log, prof, default, base)
        return
    if a.rank_compare:
        rank_compare(a, log, prof, default, base)
        return
    if a.size_compare or a.window_compare:
        size_compare(a, log, prof, default, base, window=a.window_compare)
        return
    mods, _ = build_mods(log, prof, default, a.heavy, a.heavy_time, a.heavy_mem, a.seed, a.mcl)
    order = make_order(mods, a.order, a.graph_order)
    kw = dict(OLD) if a.old else dict(margin_init=a.margin_init, margin_floor=a.margin_floor,
                                       margin_stat=a.margin_stat, margin_window=a.margin_window,
                                       threads_spare=not a.threads_greedy,
                                       margin_excl=a.margin_excl, kill_by=a.kill_by,
                                       gate=a.gate, front_pos=a.requeue == "position",
                                       front_fifo=a.requeue == "kills")
    kw.pop("threads_d", None)
    r = simulate(mods, order, int(a.budget * 2 ** 20), a.jobs, a.tick, a.growth,
                 a.typ_q, 0 if a.old else a.threads_d, a.threads_cap, a.thread_budget, a.thread_mem, a.reserve,
                 a.install_serial, a.read_cap, **kw)
    print(json.dumps(r) if a.json else fmt(r))


if __name__ == "__main__":
    main()
