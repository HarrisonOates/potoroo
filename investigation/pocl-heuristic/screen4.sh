#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-c1
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
A="--tasks panel10.txt --seconds 10 --mem-mb 1024 -j 4"
python3 run.py flow s1.jsonl $A -- --fdr-pocl -f ZLIFO -h FLOW/LIFO -s A
python3 run.py lchyb s1.jsonl $A -- --fdr-pocl -f "$LC" -h HYB/LIFO -s A
echo DONE
