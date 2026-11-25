# A Lean 4 proof of the Lou and Yu conjecture for k = 4

This repository contains a human-readable, formally verified Lean 4 proof of the Lou and Yu conjecture (2004) for `k = 4`. The proof uses no SAT solver, no graph enumeration, no symmetry breaking, and no `native_decide`. Every theorem compiles against Lean 4 (`v4.37.0-rc1`) and Mathlib using only the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Problem statement

A connected graph `G` on `v` vertices is `k`-extendable if it has a matching of size `k` and every matching of size `k` extends to a perfect matching. It is minimally `k`-extendable if deleting any edge destroys `k`-extendability.

In 2004, Dingjun Lou and Qinglin Yu proved in *Connectivity of k-extendable graphs with large k* (*Discrete Applied Mathematics* 136, 55 to 61) that every non-bipartite `k`-extendable graph with `v <= 4k` has connectivity at least `2k`, while every bipartite minimally `k`-extendable graph has minimum degree `k + 1`. They conjectured that every minimally `k`-extendable graph with `v <= 4k` satisfies:

```
delta(G) in {k + 1, 2k, 2k + 1}
```

The conjecture was settled for `k = 1` by He, Lu, and Xue (*Journal of Graph Theory*, 2026) and for `k = 2` and `k = 3` by Zhiyong Gan and Yi Huang ([arXiv:2611.22690v1](https://arxiv.org/abs/2611.22690), November 2026). The case `k = 4` was open.

## Main result

For every connected minimally 4-extendable graph `G` on `v <= 16` vertices:

1. `v` belongs to `{10, 12, 14, 16}` (`LouYuK4.lou_yu_k4_order_and_bounds`).
2. Every vertex has degree at least 5 (`LouYuK4.plummer_min_degree`, proving Plummer's 1980 connectivity theorem).
3. Some vertex has degree at most 9 (`LouYuK4.nu_eq_12_upper`, `LouYuK4.nu_eq_14_upper`, and `LouYuK4.nu_eq_16_upper`).
4. If `G` is bipartite, then `delta(G) = 5` (`LouYuK4.bipartite_min_4ext_deg_five`).
5. At `v = 10`, `delta(G)` belongs to `{5, 9}`. At `v = 12`, `delta(G) != 8`.
6. Combined with Lou and Yu's 2004 dichotomy (`not IsBipartite G -> forall v, 8 <= G.degree v`, passed as an explicit hypothesis `hLouYu2004` rather than an axiom), the minimum degree `delta(G)` belongs to `{5, 8, 9}` (`LouYuK4.lou_yu_k4_minDegree_spectrum`).
7. All three values 5, 8, and 9 are attained by connected minimally 4-extendable graphs on at most 16 vertices, namely `K_{5,5}` on 10 vertices, `G_4 = (K_8 + K_8) + M_8` on 16 vertices, and `K_10` on 10 vertices (`LouYuK4.lou_yu_k4_attainability`).

## Proof overview

Let `G` be a minimally 4-extendable graph on `v` vertices and let `F = G^c` be its complement. To prove `delta(G) <= 9`, assume for contradiction that every vertex of `G` has degree at least 10.

1. At `v = 10`, every vertex already has degree at most 9.
2. At `v = 12`, `Delta(F) <= 1`, so `F` is a matching. Deleting any edge of `G` leaves every 4-set with a perfect matching, so `G` cannot be minimally 4-extendable (`LouYuK4.nu_eq_12_upper`).
3. At `v = 14`, `Delta(F) <= 3`. Every 8-set of `G` has a perfect matching by Dirac's bound (`hasPM_eight_of_compl_le_three`). Minimality forces each of the at least 140 ordered edges `(u, v)` of `G` to trigger a 6-vertex Tutte obstruction in `F + uv` (`obstructed_edge_six_cases`), while global charging bounds the total number of obstructed ordered pairs by `42 + 14 + 42 = 98 < 140` (`LouYuK4.nu_eq_14_upper`).
4. At `v = 16`, `Delta(F) <= 5`. The proof splits into two stages.
   - **Closure elimination (`LouYuK4/Order16Closure.lean`).** By Tutte's theorem, an 8-vertex graph `H` whose complement `X` has `Delta(X) <= 5` lacks a perfect matching if and only if `X` contains `K_5`, `K_3 v 3K_1`, or `K_{3,5}` (`not_hasPM_eight_of_compl_le_five`). We prove a pure 4-case hitting lemma (`exists_good_eight_of_ten`): every 10-vertex graph with maximum degree at most 5 contains an 8-vertex induced subgraph avoiding all three obstructions. If `F` contains `K_5` or `K_3 v 3K_1`, the complement of the obstruction has 10 or 11 vertices, so it contains a good 8-set whose complementary 8-set lacks a perfect matching, violating 4-extendability. If `F` contains `K_{3,5}` and no smaller obstruction, the same argument forces a disjoint twin `K_{3,5}` on the remaining 8 vertices. Deleting an edge of `G` between the two 3-sides preserves the exact set of good 8-sets, violating minimality. Thus `F` avoids all three obstructions (`nu_eq_16_no_bad_eight`).
   - **Global charging (`LouYuK4/Order16Count.lean`).** Every ordered edge `(u, v)` of `G` must create one of five 8-vertex Tutte obstructions in `F + uv` with `Delta <= 6` (`not_hasPM_eight_of_compl_le_six`): `K_5`, `K_3 v 3K_1` (two subcases), `K_{3,5}`, `K_2 v 5K_1`, or `K_1 v K_{3,3}`. Charging ordered pairs to degree-5 vertices, open twins `O`, and closed twins `C` (which are disjoint, so `|O| + |C| <= 16`) bounds the total number of obstructed ordered edges by `32 + 32 + 4(|O| + |C|) <= 128 < 160` (`nu_eq_16_upper`).

## Module structure

Line counts were measured with `wc -l LouYuK4.lean LouYuK4/*.lean`.

| File | Lines | Contents |
| --- | ---: | --- |
| `LouYuK4/Defs.lean` | 236 | `HasPM`, `IsKExtendable`, `IsMinimallyKExtendable`, and Gan and Huang Lemma 3.3 |
| `LouYuK4/SmallTutte.lean` | 854 | Tutte odd-component wrapper and complete 4-, 6-, and 8-vertex obstruction classifications |
| `LouYuK4/SmallOrders.lean` | 978 | Order `v = 10` (`delta != 8`), order `v = 12` (`delta != 8` and `delta <= 9`), and order `v = 14` (`delta <= 9`) |
| `LouYuK4/Order16Closure.lean` | 1,312 | 10-vertex hitting lemma (`exists_good_eight_of_ten`) and closure elimination (`nu_eq_16_no_bad_eight`) |
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

The script builds `LouYuK4`, confirms no `sorry`, `admit`, `axiom`, or `native_decide` appears in any proof, and prints the axiom dependencies of every main theorem. Expected output ends with:

```text
'LouYuK4.nu_eq_12_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.nu_eq_14_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.nu_eq_16_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.plummer_min_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.bipartite_min_4ext_deg_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.lou_yu_k4_order_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.lou_yu_k4_minDegree_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'LouYuK4.lou_yu_k4_attainability' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: LouYuK4 verified with standard axioms only.
```

## References

- M. D. Plummer, *On n-extendable graphs*, Discrete Mathematics 31 (1980), 201 to 205.
- D. Lou and Q. Yu, *Connectivity of k-extendable graphs with large k*, Discrete Applied Mathematics 136 (2004), 55 to 61.
- C. He, H. Lu, and L. Xue, *Minimal 1-extendable graphs*, Journal of Graph Theory (2026).
- Z. Gan and Y. Huang, *Minimum degree of minimally k-extendable graphs with large k*, [arXiv:2611.22690v1](https://arxiv.org/abs/2611.22690) (2026).
