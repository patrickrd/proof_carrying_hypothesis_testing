#!/bin/zsh
# launch.sh -- run all (mode, dataset) jobs, 8 at a time; strep first (validation), SH0ES last.
PY=/private/tmp/claude-501/-Users-prd-Documents-svn-wps-lean-blog/0f5c8167-c0a4-4818-b6d3-3162997a53d3/scratchpad/venv/bin/python
cd "$(dirname "$0")"
ORDER=(strep cars hubble_teach Hubble1929 anorexia Moore GISTEMP Chinchilla CardKrueger Boston_nox Mincer_educ Galton_slope0 Galton_slope1 ReinhartRogoff hubble_creationist Hubble1929_creationist SH0ES)
for nm in $ORDER; do for mode in 0 2; do echo "$mode $nm"; done; done | xargs -P 8 -L 1 sh -c "$PY driver2.py \$0 \$1 36000 > /dev/null 2>&1"
echo ALL_DONE
