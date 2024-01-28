| Task                               | Solved? | Possible Reason         |
| ---------------------------------- | ------- | ----------------------- |
| `tree/maxPathWeight.ceg`           | failed  | scheduler               |
| `tree/sorted.ceg`                  | failed  | generalization          |
| `tree/sumTree.ceg`                 | solved  |                         |
| `list/sumhom.ceg`                  | failed  | scheduler               |
| `list/minhom.ceg`                  | failed  | scheduler               |
| `numbers/int_nat_toint`            | failed  | bug in egg + shceduler  |
| `ptree/sum.ceg`                    | failed  | need stronger induction |
| `indexed_list/search.ceg`          | solved  |                         |
| `indexed_list/position_polynomial` | failed  | incomplete              |
| `mts-hard.ceg`                     | solved  |                         |
|                                    |         |                         |
|                                    |         |                         |

For `indexed_list/position_polynomial`, lemma `spec (repr xs) + a * (len xs) = res a xs` is required, but lhs will never occur if only case-split is applied.

For `ptree/num`, a nested data structure is involved, thus the direct inductive hypothesis does not apply.

`int_nat_toint_milstones` lists the lemmas required by `int_nat_toint`. `egg` reports an error when generating the explanation for one lemma. If we do not require generating explanations (by annotating a code fragment in function `find_proof` in `goal.rs`), our approach will fail due to the poor scheduler.