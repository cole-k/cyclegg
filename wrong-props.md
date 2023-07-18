# Invalid props

## Methodology
Tested using cyclic lemmas + half lemmas

## Results

- prop_04
  - Prop: (S (count n xs)) = (count n (Cons n xs))
  - Reason: UNKNOWN (0.09 sec)
  - Suspected Reason: Depth exceeded
- prop_20:
  - (len (sort xs)) = (len xs)
  - Reason: UNKNOWN (1.05 sec)
  - Suspected Reason: Timeout
- prop_53
  - (count n xs) = (count n (sort xs))
  - Reason: UNKNOWN (10.63 sec)
  - Suspected Reason: Timeout
- prop_54
  - (sub (add m n) n) = m
  - Reason: UNKNOWN (0.24 sec)
  - Suspected Reason: Need to prove lemma on smaller part
- prop_65
  - (lt i (S (add m i))) = True
  - Reason: UNKNOWN (0.12 sec)
  - Suspected Reason: Need to prove lemma on smaller part
- prop_66
  - (leq (len (filter p xs)) (len xs)) = True
  - Reason: UNKNOWN (0.32 sec)
  - Suspected Reason: Timeout
- prop_68
  - (leq (len (delete n xs)) (len xs)) = True
  - Reason: UNKNOWN (2.12 sec)
  - Suspected Reason: Timeout
- prop_69
  - (leq n (add m n)) = True
  - Reason: UNKNOWN (0.08 sec)
  - Known Reason: Need to prove lemma on smaller part
    - Can prove: (leq k (add m (S n))) = (leq k (S (add m n)))
    - Gets stuck: (leq n (add m (S n))) = (leq n (S (add m n)))
      - Reason: Cannot recurse
- prop_72
  - (rev (drop i xs)) = (take (sub (len xs) i) (rev xs))
  - Reason: UNKNOWN (2.18 sec)
  - Suspected Reason: Timeout
- prop_74
  - (rev (take i xs)) = (drop (sub (len xs) i) (rev xs))
  - Reason: UNKNOWN (13.05 sec)
  - Suspected Reason: Timeout
- prop_78
  - (sorted (sort xs)) = True
  - Reason: INVALID (0.03 sec)
  - Suspected Reason: Depth exceeded
- prop_81
  - (take n (drop m xs)) = (drop m (take (add n m) xs))
  - Reason: UNKNOWN (3.97 sec)
  - Suspected Reason: Timeout
- prop_47
  - (height (mirror t)) = (height t)
  - Reason: UNKNOWN (many many sec)
  - Suspected Reason: Timeout