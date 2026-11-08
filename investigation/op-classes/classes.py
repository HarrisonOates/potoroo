#!/usr/bin/env python3
"""Achiever-class diagnostic for operator-class steps.

usage: classes.py [--min N] [--top K] TASK.sas...

For each fact that some operator or the goal requires, the achievers are the
operators with an effect setting it (from a different value, or unconditionally).
Reported per high-branching fact (more than N achievers):

  n         achievers (the children ordinary POCL creates for a new step)
  pre       distinct precondition maps (prevail + effect pre) among them
  full      distinct (precondition map, effect set) signatures
  must      preconditions shared by every achiever
  disagree  variables on which achievers differ (missing counts as a value)
  split     fewest/most classes from splitting on one disagreeing variable
  tie       achievers whose precondition ADD (from init) is minimal / within 1
  sch, arg  schemas among achievers; worst schema's fewest classes from fixing
            one argument position
"""
import argparse
import os
import statistics
from collections import defaultdict


def parse(path):
    lines = [l.rstrip("\n") for l in open(path)]
    i = 0
    variables, ops, goals, init = [], [], [], []
    while i < len(lines):
        t = lines[i]
        if t == "begin_variable":
            name = lines[i + 1]
            n = int(lines[i + 3])
            values = lines[i + 4 : i + 4 + n]
            variables.append((name, values))
            i += 4 + n
        elif t == "begin_state":
            k = i + 1
            while lines[k] != "end_state":
                init.append(int(lines[k]))
                k += 1
            i = k
        elif t == "begin_goal":
            n = int(lines[i + 1])
            goals = [tuple(map(int, lines[i + 2 + k].split())) for k in range(n)]
            i += 2 + n
        elif t == "begin_operator":
            name = lines[i + 1]
            np_ = int(lines[i + 2])
            pre = {}
            for k in range(np_):
                v, a = map(int, lines[i + 3 + k].split())
                pre[v] = a
            j = i + 3 + np_
            ne = int(lines[j])
            effs = []
            for k in range(ne):
                xs = list(map(int, lines[j + 1 + k].split()))
                nc = xs[0]
                conds = tuple(zip(xs[1 : 1 + 2 * nc : 2], xs[2 : 2 + 2 * nc : 2]))
                v, p, post = xs[1 + 2 * nc :]
                if p != -1 and not conds:
                    pre[v] = p
                effs.append((conds, v, p, post))
            ops.append((name, pre, effs))
            i = j + 1 + ne
        else:
            i += 1
    return variables, ops, goals, init


def hadd(variables, ops, init):
    """Additive costs from the initial state (unit operator costs)."""
    cost = {(v, a): 0 for v, a in enumerate(init)}
    changed = True
    while changed:
        changed = False
        for _, pre, effs in ops:
            if any(f not in cost for f in pre.items()):
                continue
            c = 1 + sum(cost[f] for f in pre.items())
            for conds, v, _, post in effs:
                if all(f in cost for f in conds):
                    cc = c + sum(cost[f] for f in conds)
                    if cc < cost.get((v, post), float("inf")):
                        cost[(v, post)] = cc
                        changed = True
    return cost


def schema_split(names):
    """Group by schema; per schema the fewest classes from fixing one argument."""
    by = defaultdict(list)
    for n in names:
        parts = n.split()
        by[parts[0]].append(parts[1:])
    best = []
    for args in by.values():
        k = len(args[0])
        sizes = [len({a[i] for a in args}) for i in range(k)]
        free = [x for x in sizes if x > 1]
        best.append(min(free) if free else 1)
    return len(by), max(best)


def analyse(path, minimum, top):
    variables, ops, goals, init = parse(path)
    cost = hadd(variables, ops, init)
    required = set(goals)
    for _, pre, effs in ops:
        required.update(pre.items())
        for conds, _, _, _ in effs:
            required.update(conds)
    achievers = defaultdict(list)
    for o, (_, pre, effs) in enumerate(ops):
        for conds, v, p, post in effs:
            if p != post and not conds:
                achievers[(v, post)].append(o)
    rows = []
    for fact in required:
        members = achievers.get(fact, [])
        if len(members) <= minimum:
            continue
        pres = [ops[o][1] for o in members]
        pre_sigs = {frozenset(p.items()) for p in pres}
        full_sigs = {
            (frozenset(ops[o][1].items()), frozenset((v, post) for _, v, _, post in ops[o][2]))
            for o in members
        }
        allvars = set().union(*(p.keys() for p in pres))
        must, disagree, splits = 0, 0, []
        for v in allvars:
            vals = {p.get(v) for p in pres}
            if len(vals) == 1:
                must += 1
            else:
                disagree += 1
                splits.append(len(vals))
        name, values = variables[fact[0]]
        inf = float("inf")
        oc = sorted(
            sum(cost.get(f, inf) for f in ops[o][1].items()) for o in members
        )
        reach = [c for c in oc if c < inf]
        tie0 = sum(1 for c in reach if c == reach[0]) if reach else 0
        tie1 = sum(1 for c in reach if c <= reach[0] + 1) if reach else 0
        schemas, sch_split = schema_split([ops[o][0].strip("()") for o in members])
        rows.append(
            dict(
                fact=f"{name}={values[fact[1]]}",
                n=len(members),
                pre=len(pre_sigs),
                full=len(full_sigs),
                must=must,
                disagree=disagree,
                split=min(splits) if splits else 1,
                maxsplit=max(splits) if splits else 1,
                tie0=tie0,
                tie1=tie1,
                schemas=schemas,
                argsplit=sch_split,
            )
        )
    task = os.path.basename(path)[:-4]
    if not rows:
        print(f"{task}: no fact with more than {minimum} achievers")
        return
    med = lambda k: statistics.median(r[k] for r in rows)
    print(
        f"{task}: {len(rows)} facts >{minimum} achievers | median n {med('n')}"
        f" pre {med('pre')} full {med('full')} must {med('must')}"
        f" disagree {med('disagree')} split {med('split')}"
        f" | ties {med('tie0')}/{med('tie1')} schemas {med('schemas')} argsplit {med('argsplit')}"
    )
    for r in sorted(rows, key=lambda r: -r["n"])[:top]:
        print(
            f"    n={r['n']:4} pre={r['pre']:4} full={r['full']:4} must={r['must']:2}"
            f" disagree={r['disagree']:3} split={r['split']:2}/{r['maxsplit']:2}"
            f" tie={r['tie0']:4}/{r['tie1']:4} sch={r['schemas']} arg={r['argsplit']:3}  {r['fact']}"
        )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--min", type=int, default=20)
    ap.add_argument("--top", type=int, default=3)
    ap.add_argument("tasks", nargs="+")
    a = ap.parse_args()
    for t in a.tasks:
        analyse(t, a.min, a.top)


if __name__ == "__main__":
    main()
