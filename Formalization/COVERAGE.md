# MainResults.tex coverage

This table matches every mathematical item in `MainResults.tex` to its Lean declaration.

| Source item | Lean declaration | File |
|---|---|---|
| Multiplicity vectors `X_{h,k}` and `M_{h,k}` | `Senger.X`, `Senger.M`, `Senger.card_X` | `RequestProject/Main.lean` |
| `h`-fold sumset and `B_h` definition | `Senger.hSumset`, `Senger.IsBh`, `Senger.isBh_iff_card` | `RequestProject/Main.lean` |
| First collision-propagation lemma | `Senger.bhStar_propagation` (and core `Senger.propagate_collision`) | `RequestProject/SengerMainTheorem.lean`, `RequestProject/Main.lean` |
| Exact `k`-subsets of `[q]` | `Senger.qSubsets`, `Senger.mem_qSubsets_iff`, `Senger.card_qSubsets` | `RequestProject/SengerCounting.lean` |
| Equivalent increasing tuples and reordering invariance | `Senger.IncreasingTuple`, `Senger.tupleSet_bijective`, `Senger.card_increasingTuples`, `Senger.hSumset_invariant_under_reordering` | `RequestProject/SengerCounting.lean` |
| Positive/negative parts, balance, weight | `Senger.posPart`, `Senger.negPart`, `Senger.Balanced`, `Senger.weight`, `Senger.sum_negPart_eq_weight` | `RequestProject/Main.lean` |
| Primitive relation and canonical sign representative | `Senger.Primitive`, `Senger.CanonicalSign`, `Senger.canonicalRepresentative`, `Senger.canonicalSign_exactly_one` | `RequestProject/SengerRelations.lean` |
| Finite relation set `R_{h,k}` | `Senger.R`, `Senger.mem_R_iff` | `RequestProject/SengerRelations.lean` |
| Relevant coordinate bounds | `Senger.relevant_coordinate_bound`, `Senger.mem_relationBox_iff` | `RequestProject/SengerRelations.lean` |
| Collision iff a member of `R` is satisfied | `Senger.collision_iff_exists_mem_R` | `RequestProject/SengerRelations.lean` |
| Explicit `|R| ≤ (2h+1)^(k-1)` and polynomial bound | `Senger.card_R_le`, `Senger.card_R_le_explicit_bigO` | `RequestProject/SengerRelations.lean` |
| Rank-counting lemma and `r=1,2` cases | `Senger.rank_counting`, `Senger.rank_counting_one`, `Senger.rank_counting_two` | `RequestProject/SengerCounting.lean` |
| Proportion of `B_h` sets tends to one | `Senger.nonBh_count_bound`, `Senger.bh_proportion_tendsto_one` | `RequestProject/SengerCounting.lean` |
| Exactly one primitive relevant relation up to sign | `Senger.ExactlyOnePrimitiveRelation` | `RequestProject/SengerConstruction.lean` |
| Bridge to operational unique direction | `Senger.exactlyOne_implies_uniqueDirection` | `RequestProject/SengerConstruction.lean` |
| Exact unique-relation cardinality lemma | `Senger.card_hSumset_exactly_one` (using core `Senger.card_hSumset_unique_relation`) | `RequestProject/SengerConstruction.lean`, `RequestProject/Main.lean` |
| Numerical example `A={1,2,3}`, `h=4` | `Senger.example_fourfold_AP`, `Senger.example_fourfold_AP_card` | `RequestProject/Main.lean` |
| Initial triple and relation `(s-1,-s,1)` | `Senger.initialTriple`, `Senger.initialRelation` | `RequestProject/SengerConstruction.lean` |
| Primitivity, weight, satisfaction, uniqueness on triple | `Senger.initialRelation_primitive`, `Senger.initialRelation_weight`, `Senger.initialTriple_satisfies`, `Senger.initialTriple_unique` | `RequestProject/SengerConstruction.lean` |
| Forbidden extension bound and at least `q/2` choices | `Senger.forbidden_extension_count`, `Senger.many_permissible_extensions` | `RequestProject/SengerConstruction.lean` |
| Ordered extension construction and lower bound | `Senger.constructedTuples`, `Senger.constructedTuples_lower_bound` | `RequestProject/SengerConstruction.lean` |
| At-most-`k!` label multiplicity and set conversion | `Senger.tupleSet_fiber_card_le_factorial`, `Senger.constructedSets_lower_bound` | `RequestProject/SengerConstruction.lean` |
| Listed size `P_ell` | `Senger.P` | `RequestProject/SengerMainTheorem.lean` |
| Central Theorem part (i) | `Senger.central_part_i` | `RequestProject/SengerMainTheorem.lean` |
| Central Theorem part (ii) | `Senger.central_part_ii` | `RequestProject/SengerMainTheorem.lean` |
| Central Theorem part (iii), including `ell=0` | `Senger.central_part_iii` | `RequestProject/SengerMainTheorem.lean` |
| Combined Central Theorem | `Senger.central_theorem` | `RequestProject/SengerMainTheorem.lean` |
| Eventual frequency comparison | `Senger.listed_more_frequent_than_unlisted` | `RequestProject/SengerMainTheorem.lean` |
| Consecutive gaps | `Senger.consecutive_gap` | `RequestProject/Main.lean` |
| Full corollary | `Senger.frequency_and_gap_corollary` | `RequestProject/SengerMainTheorem.lean` |

All asymptotic conclusions are stated as explicit eventual real inequalities whose constants are independent of `q`; `h` and `k` are parameters fixed outside the limit/eventual quantifiers.
