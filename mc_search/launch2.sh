#!/bin/zsh
PY=/private/tmp/claude-501/-Users-prd-Documents-svn-wps-lean-blog/0f5c8167-c0a4-4818-b6d3-3162997a53d3/scratchpad/venv/bin/python
cd "$(dirname "$0")"
ORDER=(cars hubble_teach Hubble1929 anorexia strep Moore GISTEMP Chinchilla CardKrueger Boston_nox Mincer_educ Galton_slope0 Galton_slope1 ReinhartRogoff hubble_creationist Hubble1929_creationist)
for nm in $ORDER; do echo "2 $nm"; done | xargs -P 7 -L 1 sh -c "$PY driver2.py \$0 \$1 36000 > /dev/null 2>&1"
echo ALL_DONE2
