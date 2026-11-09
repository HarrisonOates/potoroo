#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "potoroo-c7 " >/dev/null; do sleep 5; done
LC20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LC_add/{o}LC_add/{s}LIFO"
Z20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LIFO/{o}LIFO/{s}LIFO"
POTOROO_BIN=$PWD/bin/potoroo-c7 python3 run.py port3c rest.jsonl --tasks rest.txt --seconds 225 --mem-mb 1024 -j 6 -- --fdr-pocl -f "ZLIFO@TADD/LIFO" -f "$Z20@FLOW/LIFO" -f "$LC20@HYB/LIFO" -s A --pea
echo DONE
