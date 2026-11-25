#!/bin/zsh
# Reproduce every search reported in the note. Usage: run_batch.sh PYTHON
# PYTHON needs ortools (9.15) and python-sat. Logs go to ./results-*.log.
# The C8 and C12 rows used 900 s and 120 s limits on a busy MacBook Air; faster
# machines may decide the cases the note lists as undecided.
P=${1:-python3}
{
  for n in 1 2 3 4 5 6 7 8 9 10 11 12; do $P search_cpsat.py C 4 $n --low both --time 1800; done
  for n in 5 6 7 8 9 10 11 12; do $P search_sat.py C 4 $n; done
  for n in 1 2 3 4; do $P search_cpsat.py K2 1 $n --low both --time 60; done
  $P search_sat.py K2 1 3
  for n in 1 2 3 4 5 6 7 8; do $P search_cpsat.py K2 3 $n --low both --time 1800; done
  for n in 7 8; do $P search_sat.py K2 3 $n; done
} > ./results-c4-k2k.log 2>&1
for n in 1 2 3 4 5 6 7 8 9; do $P search_cpsat.py K2 4 $n --time 1200; done > ./results-k24.log 2>&1
{
  for n in 2 4 6 8; do $P search_cpsat.py C 6 $n --time 900; done
  for n in 1 2 3 4 5 6 7 8; do $P search_cpsat.py C 8 $n --time 900; done
} > ./results-cm.log 2>&1
$P search_sat.py C 6 8 > ./results-c6x8-cnf.log 2>&1
for n in 1 2 3 4 5; do $P search_cpsat.py C 12 $n --time 120 --workers 2; done > ./results-c12.log 2>&1
