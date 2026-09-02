#!/usr/bin/env python3
"""Generates the larger logistics and gripper instances used for benchmarking.

The committed `examples/logistics-{e,f}.pddl` and `examples/gripper-40.pddl` are
this script's output; regenerate them with `--examples`. `--scaling` emits the
much larger logistics instances used to measure relaxed-planning-graph
construction, which grows fast enough with object count to dominate startup
long before search becomes the bottleneck.

  python3 scripts/gen_instances.py --examples
  python3 scripts/gen_instances.py --scaling --out /tmp
"""
import argparse
import random
import textwrap

CITIES = ["pgh","bos","la","ny","sf","chi","atl","den","sea","mia","dal","phx"]

def wrap(items, opening):
    return textwrap.fill(" ".join(items), width=76,
                         initial_indent=opening,
                         subsequent_indent=" " * len(opening),
                         break_long_words=False, break_on_hyphens=False)

def render(name, domain, objects, init, goal):
    lines = [f"(define (problem {name})", f"  (:domain {domain})",
             wrap(objects, "  (:objects ").rstrip() + ")",
             "  (:init " + ("\n\t " .join(init)) + ")",
             "  (:goal (and " + ("\n\t      ".join(goal)) + ")))"]
    return "\n".join(lines) + "\n"

def logistics(name, n_cities, n_packages, n_planes, seed):
    rng = random.Random(seed)
    cities = CITIES[:n_cities]
    locs = [f"{c}-{k}" for c in cities for k in ("po", "central", "airport")]
    trucks = [f"{c}-truck" for c in cities]
    planes = [f"airplane{i+1}" for i in range(n_planes)]
    packages = [f"package{i+1}" for i in range(n_packages)]

    objects = packages + planes + cities + trucks + locs
    init, goal = [], []
    init += [f"(obj {p})" for p in packages]
    init += [f"(airplane {p})" for p in planes]
    init += [f"(city {c})" for c in cities]
    init += [f"(truck {t})" for t in trucks]
    for l in locs:
        init.append(f"(location {l})")
        if l.endswith("-airport"):
            init.append(f"(airport {l})")
    init += [f"(in-city {l} {l.rsplit('-', 1)[0]})" for l in locs]
    for p in packages:
        start = rng.choice(locs)
        # Goal in a different city, so every package needs at least one flight
        # or truck move; that is what makes the instance non-trivial.
        end = rng.choice([l for l in locs if not l.startswith(start.rsplit("-", 1)[0])])
        init.append(f"(at {p} {start})")
        goal.append(f"(at {p} {end})")
    init += [f"(at {p} {cities[0]}-airport)" for p in planes]
    init += [f"(at {c}-truck {rng.choice([f'{c}-po', f'{c}-central', f'{c}-airport'])})"
             for c in cities]

    return render(name, "logistics-strips", objects, init, goal)

def gripper(name, n_balls):
    balls = [f"ball{i+1}" for i in range(n_balls)]
    objects = ["rooma", "roomb"] + balls + ["left", "right"]
    init = ["(room rooma)", "(room roomb)"]
    init += [f"(ball {b})" for b in balls]
    init += ["(gripper left)", "(gripper right)", "(at-robby rooma)",
             "(free left)", "(free right)"]
    init += [f"(at {b} rooma)" for b in balls]
    goal = [f"(at {b} roomb)" for b in balls]
    return render(name, "gripper-strips", objects, init, goal)


PRESETS = {
    # name:            (cities, packages, planes, seed)
    "logistics-e":     (6, 11, 2, 11),
    "logistics-f":     (8, 14, 3, 22),
    "logistics-g":     (10, 30, 4, 99),
    "logistics-h":     (12, 60, 6, 99),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--examples", action="store_true",
                        help="regenerate the committed example instances")
    parser.add_argument("--scaling", action="store_true",
                        help="emit the large instances used for build-time scaling")
    parser.add_argument("--out", default="examples", help="output directory")
    args = parser.parse_args()
    if not (args.examples or args.scaling):
        parser.error("choose --examples, --scaling, or both")

    names = []
    if args.examples:
        names += ["logistics-e", "logistics-f"]
    if args.scaling:
        names += ["logistics-g", "logistics-h"]
    for name in names:
        cities, packages, planes, seed = PRESETS[name]
        path = f"{args.out}/{name}.pddl"
        with open(path, "w") as out:
            out.write(logistics(name.replace("logistics-", "log-"),
                                cities, packages, planes, seed))
        print(path)
    if args.examples:
        path = f"{args.out}/gripper-40.pddl"
        with open(path, "w") as out:
            out.write(gripper("strips-gripper40", 40))
        print(path)


if __name__ == "__main__":
    main()
