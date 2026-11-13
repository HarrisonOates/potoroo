#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-s2 POTOROO_HYB=3
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
R="python3 run.py"; A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 8"
POTOROO_BIN=$PWD/bin/potoroo-s1 $R add s1.jsonl $A -- --fdr-pocl -f ZLIFO -h ADD/LIFO -s A
$R port3 s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -s A
$R tadd s1.jsonl $A -- --fdr-pocl -f ZLIFO -h TADD/LIFO -s A
$R port2 s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -s A
echo DONE
