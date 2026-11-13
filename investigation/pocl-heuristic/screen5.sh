#!/bin/bash
cd "$(dirname "$0")"
while ! grep -q DONE screen4.log; do sleep 15; done
export POTOROO_BIN=$PWD/bin/potoroo-c2
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 4"
python3 run.py port4pea s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -f "ZLIFO@FFR/LIFO" -s A --pea
echo DONE
