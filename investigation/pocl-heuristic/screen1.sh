#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-s1
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
R="python3 run.py"; A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 5"
$R add s1.jsonl $A -- --fdr-pocl -f ZLIFO -h ADD/LIFO -s A
$R tadd s1.jsonl $A -- --fdr-pocl -f ZLIFO -h TADD/LIFO -s A
POTOROO_HYB=4 $R prune4 s1.jsonl $A -- --fdr-pocl -f ZLIFO -h HYB/LIFO -s A
POTOROO_HYB=3 $R hyb3lc s1.jsonl $A -- --fdr-pocl -f ZLIFO -f "$LC" -h HYB/LIFO -s A
$R taddflowhlc s1.jsonl $A -- --fdr-pocl -f ZLIFO -f "$LC" -h TADD/FLOW_H/LIFO -s A
POTOROO_HYB=4 $R prune4lc s1.jsonl $A -- --fdr-pocl -f ZLIFO -f "$LC" -h HYB/LIFO -s A
echo DONE
