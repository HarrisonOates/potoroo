#!/bin/bash
# Re-run the calibrated port3pea timeouts with at most 7 concurrent jobs on
# this 8-core machine (the cluster pins one physical core per run).
cd "$(dirname "$0")"
while pgrep -f "potoroo-c1 " >/dev/null; do sleep 10; done
export POTOROO_BIN=$PWD/bin/potoroo-c1
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
python3 run.py port3pea-fair calib.jsonl --tasks timeouts.txt --seconds 225 --mem-mb 1024 -j 7 -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -s A --pea
echo DONE
