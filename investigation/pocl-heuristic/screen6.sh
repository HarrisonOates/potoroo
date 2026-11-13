#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-c4
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 3"
python3 run.py t2pea s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO*2" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -s A --pea &
python3 run.py p3t3pea s1.jsonl $A -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -f "ZLIFO@TADD/LIFO*3" -s A --pea
wait
echo DONE
