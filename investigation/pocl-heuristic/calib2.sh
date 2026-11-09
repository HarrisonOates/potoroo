#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-c2
LC="{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO"
A="--tasks panel10.txt --seconds 225 --mem-mb 1024"
python3 run.py port4pea calib.jsonl $A -j 5 -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "ZLIFO@FLOW/LIFO" -f "$LC@HYB/LIFO" -f "ZLIFO@FFR/LIFO" -s A --pea
echo DONE
