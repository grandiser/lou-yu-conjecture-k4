#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if [[ "${1:-}" != "--skip-build" ]]; then
  lake build LouYuK4
fi

# 1. Static check for metaprogramming / kernel-bypass / unsafe constructs anywhere in source.
if grep -rnE '\b(native_decide|unsafe|implemented_by|extern|skipKernelTC|run_cmd|run_tac|trustCompiler|ofReduceBool)\b|^\s*import\s+Lean\b' LouYuK4/ LouYuK4.lean; then
  echo "FAIL: found forbidden construct in source"
  exit 1
fi

# 2. Independent Lean kernel replay across the full compiled LouYuK4 environment.
lake env leanchecker LouYuK4

# 3. Exhaustive axiom audit over every LouYuK4.* declaration plus explicit main theorem check.
lake env lean --stdin <<'EOF'
import Lean
import LouYuK4

open Lean

#eval show MetaM Unit from do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let required : Array Name := #[
    `LouYuK4.nu_eq_12_upper,
    `LouYuK4.nu_eq_14_upper,
    `LouYuK4.nu_eq_16_upper,
    `LouYuK4.plummer_min_degree,
    `LouYuK4.bipartite_min_4ext_deg_five,
    `LouYuK4.lou_yu_k4_order_and_bounds,
    `LouYuK4.lou_yu_k4_minDegree_spectrum,
    `LouYuK4.lou_yu_k4_attainability
  ]
  for name in required do
    if !env.contains name then
      throwError "missing required declaration: {name}"
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for modIdx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[modIdx]!
    if modName == `LouYuK4 || (`LouYuK4).isPrefixOf modName then
      let constNames := env.header.moduleData[modIdx]!.constNames
      for name in constNames do
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        let extra := axioms.filter (fun ax => !allowed.contains ax)
        if !extra.isEmpty then
          bad := bad.push (name, extra)
  if checked == 0 then
    throwError "no LouYuK4 declarations found in environment"
  if !bad.isEmpty then
    for (name, extra) in bad do
      IO.eprintln s!"FAIL: {name} uses non-standard axioms: {extra.toList}"
    throwError "found {bad.size} declaration(s) with non-standard axioms"
  for name in required do
    let axioms ← Lean.collectAxioms name
    IO.println s!"'{name}' depends on axioms: {axioms.toList}"
  IO.println s!"Audited {checked} LouYuK4 declarations: 0 non-standard axioms."
EOF

echo "PASS: LouYuK4 kernel-checked and verified with standard axioms only."
