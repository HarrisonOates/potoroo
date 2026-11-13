#!/bin/bash
cd "$(dirname "$0")"
export POTOROO_BIN=$PWD/bin/potoroo-c7
LC20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LC_add/{o}LC_add/{s}LIFO"
Z20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LIFO/{o}LIFO/{s}LIFO"
python3 run.py port3c calib.jsonl --tasks panel10.txt --seconds 225 --mem-mb 1024 -j 7 -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "$Z20@FLOW/LIFO" -f "$LC20@HYB/LIFO" -s A --pea
echo DONE
