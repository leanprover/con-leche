# Generator of tests/e2e/dag_beta_tower.ndjson.gz (task #589).
# Usage: python3 scripts/mk_dag_beta_tower.py tests/e2e/dag_tower_unfold.ndjson.gz OUT.ndjson
#
# Adversarial fixture: dag_tower_unfold's prelude, then a definition whose
# value is fun x => t26 with t0 = add x x, t(k+1) = add tk tk (2^27 tree
# nodes, 28 DAG nodes, every one with a loose bvar), twice, and
# dagF 0 = dagF2 0 := rfl (delta + beta on both sides).
import gzip, json, sys
src, out = sys.argv[1], sys.argv[2]
lines = gzip.open(src, 'rt').read().split('\n')
keep = []
for l in lines:
    if '"ie": 10284' in l: break
    keep.append(l)
o = keep[:]
ie = 20000
def emit(d):
    global ie
    d = dict(d); d['ie'] = ie; o.append(json.dumps(d)); ie += 1; return ie - 1
x = emit({'bvar': 0})
t = x
for k in range(27):
    a = emit({'app': {'fn': 10282, 'arg': t}})
    t = emit({'app': {'fn': a, 'arg': t}})
val = emit({'lam': {'binderInfo': 'default', 'body': t, 'name': 43, 'type': 10283}})
ty = emit({'forallE': {'binderInfo': 'default', 'body': 10283, 'name': 43, 'type': 10283}})
o.append(json.dumps({'in': 78, 'str': {'pre': 0, 'str': 'dagF'}}))
o.append(json.dumps({'def': {'all': [78], 'hints': {'regular': 1}, 'levelParams': [], 'name': 78, 'safety': 'safe', 'type': ty, 'value': val}}))
o.append(json.dumps({'in': 900, 'str': {'pre': 0, 'str': 'dagF2'}}))
o.append(json.dumps({'def': {'all': [900], 'hints': {'regular': 1}, 'levelParams': [], 'name': 900, 'safety': 'safe', 'type': ty, 'value': val}}))
o.append(json.dumps({'in': 901, 'str': {'pre': 0, 'str': 'dagFEq'}}))
c1 = emit({'const': {'name': 78, 'us': []}})
c2 = emit({'const': {'name': 900, 'us': []}})
a1 = emit({'app': {'fn': c1, 'arg': 10281}})
a2 = emit({'app': {'fn': c2, 'arg': 10281}})
eq = emit({'const': {'name': 1, 'us': [3]}})
e1 = emit({'app': {'fn': eq, 'arg': 10283}})
e2 = emit({'app': {'fn': e1, 'arg': a1}})
e3 = emit({'app': {'fn': e2, 'arg': a2}})
rf = emit({'const': {'name': 9, 'us': [3]}})
r1 = emit({'app': {'fn': rf, 'arg': 10283}})
r2 = emit({'app': {'fn': r1, 'arg': a1}})
o.append(json.dumps({'thm': {'all': [901], 'levelParams': [], 'name': 901, 'type': e3, 'value': r2}}))
open(out, 'w').write('\n'.join(l for l in o if l) + '\n')
