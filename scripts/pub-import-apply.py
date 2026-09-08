#!/usr/bin/env python3
"""Apply the plan to the given path prefixes."""
import json, re, sys, subprocess
plan=json.load(open('_tmp/m3/plan.json'))
prefixes=tuple(sys.argv[1:])
files=[f for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split()
       if f.startswith(prefixes)]
n=chg=0
for f in files:
    m=f[:-5].replace('/','.')
    if m not in plan: continue
    keep=set(plan[m])
    ls=open(f).read().split('\n'); hit=False
    for i,l in enumerate(ls):
        mm=re.match(r'^public import (?!all\b)([A-Za-z0-9_.]+)\s*$', l)
        if not mm: continue
        t=mm.group(1)
        if t.startswith(('Std','Lean','Init')): continue
        if t not in keep:
            ls[i]='import '+t; n+=1; hit=True
    if hit: open(f,'w').write('\n'.join(ls)); chg+=1
print(f'narrowed {n} imports in {chg} files')
