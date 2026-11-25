# A Lean 4 proof of the Lou and Yu conjecture for k = 4

This repository contains a human-readable, formally verified Lean 4 proof resolving the Lou and Yu conjecture (2004) for `k = 4`, conditional only on Lou and Yu's published 2004 non-bipartite connectivity theorem passed as an explicit hypothesis rather than an axiom.

Unconditionally in Lean 4 (`LouYuK4.lou_yu_k4_order_and_bounds` and `LouYuK4.lou_yu_k4_attainability`), this library proves the previously open upper bound `delta(G) <= 9` for all orders `v <= 16`, Plummer's 1980 lower bound `delta(G) >= 5`, Lou's 1999 bipartite result `delta(G) = 5` at `k = 4`, the order restrictions `v in {10, 12, 14, 16}`, `delta(G) in {5, 9}` at `v = 10`, `delta(G) != 8` at `v = 12`, and sharp witnesses for all three degrees `5`, `8`, and `9`. Combining these results with Lou and Yu's 2004 non-bipartite lower bound (`hLouYu2004`) yields `delta(G) in {5, 8, 9}` (`LouYuK4.lou_yu_k4_minDegree_spectrum`).

The proof uses no SAT solver, no graph enumeration, no symmetry breaking, and no `native_decide`. Every declaration in `LouYuK4` compiles against Lean 4 (`v4.37.0-rc1`) and Mathlib using only the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`, and passes independent kernel replay via `leanchecker`.

## Problem statement

A connected graph `G` on `v >= 2k + 2` vertices is `k`-extendable if it has a matching of size `k` and every matching of size `k` extends to a perfect matching. A graph `G` is minimally `k`-extendable if `G` is `k`-extendable and deleting any edge destroys `k`-extendability.

Known background results and the conjecture:

- Plummer (1980) proved that every `k`-extendable graph is `(k + 1)`-connected, so `delta(G) >= k + 1`.
- Lou (1999) proved that every bipartite minimally `k`-extendable graph satisfies `delta(G) = k + 1`.
- Lou and Yu (2004) proved that every non-bipartite `k`-extendable graph with `v <= 4k` has connectivity at least `2k`, hence `delta(G) >= 2k`. They conjectured that every connected minimally `k`-extendable graph with `v <= 4k` satisfies:

```text
delta(G) in {k + 1, 2k, 2k + 1}
```

- He, Lu, and Xue (2026) settled the conjecture for `k = 1`.
- Gan and Huang (November 2026, [arXiv:2611.22690](https://arxiv.org/abs/2611.22690)) settled the conjecture for `k = 2` and `k = 3`. The case `k = 4` was open.

The connectedness hypothesis is necessary because the disconnected union `K_8 + K_8` on 16 vertices is minimally 4-extendable with minimum degree 7. In Lean, `LouYuK4/Defs.lean` defines `IsKExtendable` without imposing `v >= 2k + 2`, and `LouYuK4/LowerAndBipartite.lean` proves `v != 8` (`nu_ne_eight_of_connected_min_four`) directly from connectedness and minimal 4-extendability. Because Plummer's theorem makes every connected 4-extendable graph on `v >= 10` vertices 5-connected, deleting any single edge always leaves `G - e` connected, so `IsMinimallyKExtendable` agrees with Plummer's definition.

## Main results

All main theorems are assembled in `LouYuK4/Main.lean`.

### Unconditional theorem (`LouYuK4.lou_yu_k4_order_and_bounds`)

For every connected minimally 4-extendable graph `G` on `v <= 16` vertices:

1. `v` belongs to `{10, 12, 14, 16}`.
2. Every vertex has degree at least 5 (`LouYuK4.plummer_min_degree`, proving Plummer's 1980 connectivity theorem).
3. Some vertex has degree at most 9 (`LouYuK4.nu_eq_12_upper`, `LouYuK4.nu_eq_14_upper`, and `LouYuK4.nu_eq_16_upper`).
4. If `G` is bipartite, then `delta(G) = 5` (`LouYuK4.bipartite_min_4ext_deg_five`).
5. At `v = 10`, `delta(G)` belongs to `{5, 9}` (`LouYuK4.nu_eq_10_ge_six_eq_nine`).
6. At `v = 12`, `delta(G) != 8` (`LouYuK4.nu_eq_12_not_eight`).

### Spectrum theorem (`LouYuK4.lou_yu_k4_minDegree_spectrum`)

Given a connected minimally 4-extendable graph `G` on `v <= 16` vertices and Lou and Yu's 2004 non-bipartite lower bound as an explicit hypothesis:

```lean
hLouYu2004 : ¬ IsBipartite G → ∀ v : V, 8 ≤ G.degree v
```

there exists a minimum-degree vertex `v` of `G` with `G.degree v ∈ {5, 8, 9}`. Passing `hLouYu2004` as a theorem argument keeps the Lean environment free of custom axioms while isolating the one external published theorem used to exclude `delta(G) ∈ {6, 7}` for non-bipartite graphs at orders `12, 14, 16`.

### Sharpness (`LouYuK4.lou_yu_k4_attainability`)

All three values `5`, `8`, and `9` are attained unconditionally by connected regular minimally 4-extendable graphs on at most 16 vertices:

- `delta = 5`: `K_{5,5}` on 10 vertices (`LouYuK4.graphK55`, `LouYuK4.witness_delta_5`).
- `delta = 8`: `G_4 = (K_8 + K_8) + M_8` on 16 vertices (`LouYuK4.graphG4`, `LouYuK4.witness_delta_8`).
- `delta = 9`: `K_10` on 10 vertices (`⊤ : SimpleGraph (Fin 10)`, `LouYuK4.witness_delta_9`).

## Proof overview

Let `G` be a connected minimally 4-extendable graph on `v` vertices and let `F = G^c` be its complement. To prove `delta(G) <= 9`, assume for contradiction that every vertex of `G` has degree at least 10.

1. At `v = 10`, every vertex already has degree at most 9.
2. At `v = 12`, `Delta(F) <= 1`, so `F` is a matching. Deleting any edge of `G` leaves every 4-set with a perfect matching, so `G` cannot be minimally 4-extendable (`LouYuK4.nu_eq_12_upper`).
3. At `v = 14`, `Delta(F) <= 3`. Every 8-set of `G` has a perfect matching by Dirac's bound (`hasPM_eight_of_compl_le_three`). Minimality forces each of the at least 140 ordered edges `(u, v)` of `G` to trigger a 6-vertex Tutte obstruction in `F + uv` (`obstructed_edge_six_cases`), while global charging bounds the total number of obstructed ordered pairs by `42 + 14 + 42 = 98 < 140` (`LouYuK4.nu_eq_14_upper`).
4. At `v = 16`, `Delta(F) <= 5`. The proof splits into two stages.
   - **Closure elimination (`LouYuK4/Order16Closure.lean`).** By Tutte's theorem, an 8-vertex graph `H` whose complement `X` has `Delta(X) <= 5` lacks a perfect matching if and only if `X` contains `K_5`, `K_3 v 3K_1`, or `K_{3,5}` (`not_hasPM_eight_iff_hasBad8`, with necessity proved in `not_hasPM_eight_of_compl_le_five`). We prove a 4-case hitting lemma (`exists_good_eight_of_ten`) showing that every 10-vertex graph with maximum degree at most 5 contains an 8-vertex induced subgraph avoiding all three obstructions. If `F` contains `K_5` or `K_3 v 3K_1`, the complement of the obstruction has 10 or 11 vertices, so it contains a good 8-set whose complementary 8-set lacks a perfect matching, violating 4-extendability. If `F` contains `K_{3,5}` and no smaller obstruction, the same argument forces a disjoint twin `K_{3,5}` on the remaining 8 vertices. Deleting an edge of `G` between the two 3-sides preserves the exact set of good 8-sets, violating minimality. Thus `F` avoids all three obstructions (`nu_eq_16_no_bad_eight`).
   - **Global charging (`LouYuK4/Order16Count.lean`).** Every ordered edge `(u, v)` of `G` must create one of five 8-vertex Tutte obstructions in `F + uv` with `Delta <= 6` (`not_hasPM_eight_of_compl_le_six`): `K_5`, `K_3 v 3K_1` (two subcases), `K_{3,5}`, `K_2 v 5K_1`, or `K_1 v K_{3,3}`. Charging ordered pairs to degree-5 vertices, open twins `O`, and closed twins `C` (which are disjoint, so `|O| + |C| <= 16`) bounds the total number of obstructed ordered edges by `32 + 32 + 4(|O| + |C|) <= 128 < 160` (`nu_eq_16_upper`).

## Module structure

Line counts are measured with `wc -l LouYuK4.lean LouYuK4/*.lean`.

| File | Lines | Contents |
| --- | ---: | --- |
| `LouYuK4/Defs.lean` | 238 | `HasPM`, `IsKExtendable`, `IsMinimallyKExtendable`, and Gan and Huang Lemma 3.3 |
| `LouYuK4/SmallTutte.lean` | 856 | Tutte odd-component wrapper and 4-, 6-, and 8-vertex obstruction classifications |
| `LouYuK4/SmallOrders.lean` | 989 | Order `v = 10` (`delta != 8`), order `v = 12` (`delta != 8` and `delta <= 9`), and order `v = 14` (`delta <= 9`) |
| `LouYuK4/Order16Closure.lean` | 1,318 | 10-vertex hitting lemma (`exists_good_eight_of_ten`) and closure elimination (`nu_eq_16_no_bad_eight`) |
| `LouYuK4/Order16Count.lean` | 1,485 | Local charging lemmas and order `v = 16` bound (`160 <= 128`, `nu_eq_16_upper`) |
| `LouYuK4/LowerAndBipartite.lean` | 1,199 | Plummer's 1980 connectivity theorem (`plummer_min_degree`), `v != 8`, `v = 10` (`delta >= 6 -> delta = 9`), and bipartite minimality (`bipartite_min_4ext_deg_five`) |
| `LouYuK4/Constructions.lean` | 668 | Explicit witnesses `K_{5,5}` (`delta = 5`), `G_4` (`delta = 8`), and `K_10` (`delta = 9`) |
| `LouYuK4/Main.lean` | 116 | Combined theorems `lou_yu_k4_order_and_bounds`, `lou_yu_k4_minDegree_spectrum`, and `lou_yu_k4_attainability` |
| `LouYuK4.lean` | 8 | Root library import |

## How to verify

Install Lean 4 via `elan`, then run the verification script from the repository root:

```sh
./verify.sh
```

The script builds `LouYuK4`, rejects unsafe or kernel-bypass constructs in source files, replays the compiled environment through the independent Lean kernel checker (`lake env leanchecker LouYuK4`), and audits every declaration defined under `LouYuK4` via `Lean.collectAxioms`, failing on any axiom outside `[propext, Classical.choice, Quot.sound]`. GitHub Actions runs the same build together with `leanchecker` and `axiom-audit` in `.github/workflows/verify.yml`.

## How to cite

Machine-readable citation metadata is provided in `CITATION.cff`.

```bibtex
@software{baida2026louyuk4,
  author  = {Baida, Imad},
  title   = {A Lean 4 proof of the Lou and Yu conjecture for k = 4},
  year    = {2026},
  url     = {https://github.com/grandiser/lou-yu-conjecture-k4},
  license = {Apache-2.0}
}
```

## References

- M. D. Plummer, *On n-extendable graphs*, Discrete Mathematics 31 (1980), 201–210.
- D. Lou, *On the structure of minimally n-extendable bipartite graphs*, Discrete Mathematics 202 (1999), 173–181.
- D. Lou and Q. Yu, *Connectivity of k-extendable graphs with large k*, Discrete Applied Mathematics 136 (2004), 55–61.
- X. He, F. Lu, and J. Xue, *Wheel-like bricks and minimal matching covered graphs*, Journal of Graph Theory 111 (2026), 5–16, DOI: [10.1002/jgt.23288](https://doi.org/10.1002/jgt.23288).
- Z. Gan and Y. Huang, *The minimum degree of minimally k-extendable graphs for some k*, [arXiv:2611.22690](https://arxiv.org/abs/2611.22690) (November 2026).
