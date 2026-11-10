#!/usr/bin/env bash
# Post-processes one cell of a sweep (run on the box, repository root): the Summary block, the header, unknowns.py and verdicts-tsv.py of ~/rx/scratch/sweep-p13/CELL.log.
# usage: bash checkct/sweep-post.sh CELL   (CELL = x86_64-nearcore-exact, thumbv7em, ...; the driver binary is in the OUT directory of the run)
set -o pipefail
D=$HOME/rx/scratch/sweep-p13; P=$D/post; mkdir -p $P
c=$1
awk '/^Summary:/{f=1} f' $D/$c.log > $P/$c.summary.txt
awk '/^Summary:/{exit} {print}' $D/$c.log | grep -v '^done \|^ *Compiling\|^ *Downloaded\|^ *Finished' | head -60 > $P/$c.header.txt
case $c in x86_64-*)
  BIN=$D/$c/x86_64-unknown-linux-gnu.driver
  [ -f "$BIN" ] || BIN=$(ls $D/$c/*x86_64*driver* | head -1)
  python3 -I checkct/unknowns.py $BIN $D/$c.log > $P/$c.unknowns.txt 2>$P/$c.unknowns.err
  python3 -I checkct/verdicts-tsv.py $D/$c.log $P/$c.unknowns.txt > $P/$c.verdicts.tsv ;;
*) python3 -I checkct/verdicts-tsv.py $D/$c.log > $P/$c.verdicts.tsv ;;
esac
wc -l $P/$c.verdicts.tsv
