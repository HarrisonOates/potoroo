#!/bin/bash
# Cluster-ratio protocol: 225 s per GiB, as 1,800 s / 8 GiB on the cluster.
cd "$(dirname "$0")"
while ! grep -q DONE screen3.log; do sleep 15; done
export POTOROO_BIN=$PWD/bin/potoroo-c1
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
A="--tasks panel10.txt --seconds 225 --mem-mb 1024"
python3 run.py add calib.jsonl $A -j 9 -- --fdr-pocl -f ZLIFO -h ADD/LIFO -s A
python3 run.py port3pea calib.jsonl $A -j 9 -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -s A --pea
echo DONE
