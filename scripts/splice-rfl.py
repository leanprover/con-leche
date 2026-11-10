#!/usr/bin/env python3
"""splice-rfl.py STREAM THEOREM — replace a theorem's value by `rfl`.

For the hand-patched e2e fixtures (task #552; `k_rescue_stuck` is the
older, manual instance): the source proves a theorem
`∀ xs, @Eq.{u} T lhs rhs` by `sorry` because the elaborator rejects
`rfl`, and the committed stream carries the value
`fun xs => @Eq.refl.{u} T rhs` instead.  The binders are copied from
the statement's ∀-telescope, so `T` and `rhs` keep their de Bruijn
indices.  The stream is rewritten in place; the new records go just
before the theorem's own record.  The old value's nodes stay
(unreferenced).
"""
import json
import sys


def main():
    path, thm = sys.argv[1], sys.argv[2]
    recs = [json.loads(line) for line in open(path)]
    names = {0: ''}
    exprs = {}
    for r in recs:
        if 'in' in r:
            if 'str' in r:
                pre = names[r['str']['pre']]
                names[r['in']] = (pre + '.' if pre else '') + r['str']['str']
            else:
                pre = names[r['num']['pre']]
                names[r['in']] = (pre + '.' if pre else '') + str(r['num']['i'])
        elif 'ie' in r:
            exprs[r['ie']] = r
    nid = {v: k for k, v in names.items()}
    ti = next(i for i, r in enumerate(recs)
              if 'thm' in r and names[r['thm']['name']] == thm)
    t = recs[ti]['thm']
    # peel the ∀-telescope
    binders = []
    e = exprs[t['type']]
    while 'forallE' in e:
        binders.append(e['forallE'])
        e = exprs[e['forallE']['body']]
    # @Eq.{u} T lhs rhs
    rhs = e['app']['arg']
    e1 = exprs[e['app']['fn']]
    e2 = exprs[e1['app']['fn']]
    ty = e2['app']['arg']
    eqc = exprs[e2['app']['fn']]['const']
    assert names[eqc['name']] == 'Eq', names[eqc['name']]
    new = []
    nxt_e = max(exprs) + 1
    if 'Eq.refl' not in nid:
        nn = max(names) + 1
        new.append({'in': nn, 'str': {'pre': nid['Eq'], 'str': 'refl'}})
        nid['Eq.refl'] = nn

    def mk(node):
        nonlocal nxt_e
        node['ie'] = nxt_e
        nxt_e += 1
        new.append(node)
        return node['ie']

    c = mk({'const': {'name': nid['Eq.refl'], 'us': eqc['us']}})
    a = mk({'app': {'arg': ty, 'fn': c}})
    v = mk({'app': {'arg': rhs, 'fn': a}})
    for b in reversed(binders):
        v = mk({'lam': {'binderInfo': b['binderInfo'], 'body': v,
                        'name': b['name'], 'type': b['type']}})
    t['value'] = v
    recs[ti:ti] = new
    with open(path, 'w') as f:
        for r in recs:
            f.write(json.dumps(r, separators=(',', ':'), ensure_ascii=False) + '\n')


if __name__ == '__main__':
    main()
