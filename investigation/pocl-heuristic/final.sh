#!/bin/bash
# port3t: port3c with time-shared queues (binary c8), calibrated protocol.
cd "$(dirname "$0")"
LC20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LC_add/{o}LC_add/{s}LIFO"
Z20="{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LIFO/{o}LIFO/{s}LIFO"
F=(--fdr-pocl -f "ZLIFO@TADD/LIFO" -f "$Z20@FLOW/LIFO" -f "$LC20@HYB/LIFO" -s A --pea)
export POTOROO_BIN=$PWD/bin/potoroo-c8
python3 run.py port3t rest.jsonl --tasks rest.txt --seconds 225 --mem-mb 1024 -j 4 -- "${F[@]}" &
python3 run.py port3t calib.jsonl --tasks panel10.txt --seconds 225 --mem-mb 1024 -j 3 -- "${F[@]}"
wait
echo DONE
