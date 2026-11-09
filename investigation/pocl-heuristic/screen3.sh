#!/bin/bash
cd "$(dirname "$0")"
while ! grep -q DONE screen2.log; do sleep 15; done
export POTOROO_BIN=$PWD/bin/potoroo-s3
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
R="python3 run.py"; A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 8"
$R port3pea s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -s A --pea
$R addpea s1.jsonl $A -- --fdr-pocl -f ZLIFO -h ADD/LIFO -s A --pea
echo DONE
