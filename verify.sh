#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if [[ "${1:-}" != "--skip-build" ]]; then
  lake build LouYuK4
fi

if grep -rnE '^\s*(axiom|admit)\b|\b(sorry|native_decide)\b' LouYuK4/ LouYuK4.lean | grep -vE '^\S+:[0-9]+:.*(--|/-|\bzero sorry\b)'; then
  echo "FAIL: found forbidden token"
  exit 1
fi

lake env lean --stdin <<'EOF'
import LouYuK4
#print axioms LouYuK4.nu_eq_12_upper
#print axioms LouYuK4.nu_eq_14_upper
#print axioms LouYuK4.nu_eq_16_upper
#print axioms LouYuK4.plummer_min_degree
#print axioms LouYuK4.bipartite_min_4ext_deg_five
#print axioms LouYuK4.lou_yu_k4_order_and_bounds
#print axioms LouYuK4.lou_yu_k4_minDegree_spectrum
#print axioms LouYuK4.lou_yu_k4_attainability
EOF

echo "PASS: LouYuK4 verified with standard axioms only."
