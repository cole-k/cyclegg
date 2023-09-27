# CLAM benchmarks

This is an analysis of the CLAM benchmarks included in CVC4's benchmark suite.

## CLAM benchmarks annotated with necessary lemmas

This is a more human-readable list of each of the goals that the authors of CVC4
thought required lemmas (the `sg` goals) and the lemmas they thought they
required. As can be seen in the CVC4 -i results on the `sg` sets, most of the
lemmas are sufficient to prove these goals with a relatively simple inductive
solver (CVC4 -i). Note that some of the proposed lemmas cannot be proven using
CVC4 -i (such as G62 or G73), although most can.

A goal being absent means that it does not require a lemma (likely it is a lemma itself).

Definitions of the functions can be found in
[ind/benchmarks-dt/clam](./ind/benchmarks-dt/clam) in the respective goal files.

- **G1**: `double x = plus x x`
   - G51: `plus x (succ y) = succ (plus x y)`
- **G2**: `len (append x y) = len (append y x)`
   - G52: `len (append x (cons y z)) = succ (len (append x z))`
- **G3**: `len (append x y) = plus (len x) (len y)`
   - G51: `plus x (succ y) = succ (plus x y)`
- **G4**: `len (append x x) = double (len x)`
   - G52: `len (append x (cons y z)) = succ (len (append x z))`
- **G5**: `len (rev x) = len x`
   - G53: `len (append x (cons y nil)) = succ (len x)`
- **G6**: `len (rev (append x y)) = plus (len x) (len y)`
   - G52: `len (append x (cons y z)) = succ (len (append x z))`
- **G7**: `len (qreva x y) = plus (len x) (len y)`
   - G51: `plus x (succ y) = succ (plus x y)`
   - `qreva` is analgous to `append (rev x) y` but done by just consing the head
     of `x` onto `y` until it runs out.
- **G8**: `drop x (drop y z) = drop y (drop x z)`
   - G54: `drop (succ w) (drop x (cons y z)) = drop w (drop x z)`
- **G9**: `drop w (drop x (drop y z)) = drop y (drop x (drop w z))`
   - G56: `drop (succ v) (drop w (drop x (cons y z))) = drop v (drop w (drop x z))`
   - G57: `drop (succ u) (drop v (drop (succ w) (cons x (cons y z)))) = drop (succ u) (drop v (drop w (cons x z)))`
- **G10**: `rev (rev x) = x`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
- **G11**: `rev (append (rev x) (rev y)) = append y x`
    - G59: `rev (append x (append y (cons z nil))) = cons z (rev (append x y))`
    - G60: `rev (append (append x (cons y nil)) nil) = cons y (rev (append x nil))`
- **G12**: `qreva x y = append (rev x) y`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G13**: `half (plus x x) = x`
    - G51: `plus x (succ y) = succ (plus x y)`
- **G14**: `sorted (sort x) = True`
    - G62: `sorted x => sorted (insort y x)`
- **G15**: `plus x (succ x) = succ (plus x x)`
    - G51: `plus x (succ y) = succ (plus x y)`
- **G16**: `even (plus x x) = True`
    - G51: `plus x (succ y) = succ (plus x y)`
- **G17**: `rev (rev (append x y)) = append (rev (rev x)) (rev (rev y))`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
- **G18**: `rev (append (rev x) y) = append (rev y) x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
    - G63: `append (append x y) (cons z nil) = append x (append y (cons z nil))`
- **G19**: `append (rev (rev x)) y = rev (rev (append x y))`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
- **G20**: `even (len (append x x)) = True`
    - G52: `len (append x (cons y z)) = succ (len (append x z))`
- **G21**: `rotate (len x) (append x y) = append y x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
    - G63: `append (append x y) (cons z nil) = append x (append y (cons z nil))`
- **G22**: `even (len (append x y)) = even (len (append y x))`
    - G64: `even (len (append w z)) = even (len (append w (cons x (cons y z))))`
- **G23**: `half (len (append x y)) = half (len (append y x))`
    - G65: `len (append w (cons x (cons y z))) = succ (succ (len (append w z)))`
- **G24**: `even (plus x y) = even (plus y x)`
    - G66: `even (plus x y) = even (plus x (succ (succ y)))`
- **G25**: `even (len (append x y)) = even (plus (len x) (len y))`
    - G66: `even (plus x y) = even (plus x (succ (succ y)))`
- **G26**: `half (plus x y) = half (plus y x)`
    - G67: `plus x (succ (succ y)) = succ (succ (plus x y))`
- **G27**: `rev x = qreva x nil`
    - G75: `append (rev x) y = qreva x y`
- **G28**: `revflat x = qrevaflat x nil`
    - G76: `append (revflat x) y = qrevaflat x y`
    - the `flat` functions appear to operate on trees by flattening them.
- **G29**: `rev (qreva x nil) = x`
    - G77: `rev (qreva x y) = append (rev y) x`
    - G78: `rev (qreva x (rev y)) = append y x`
- **G30**: `rev (append (rev x) nil) = x`
    - G79: `rev (append (rev x) y) = append (rev y) x`
    - G80: `rev (append (rev x) (rev y)) = append y x`
- **G31**: `qreva (qreva x nil) nil = x`
    - G81: `qreva (qreva x y) nil = append (rev y) x`
    - G82: `qreva (qreva x (rev y)) nil = append y x`
- **G32**: `rotate (len x) x = x`
    - G83: `rotate (len x) (append x y) = append y x`
- **G33**: `fac x = qfac x (succ zero)`
    - G84: `mult (fac x) y = qfac x y`
    - `qfac` is an accumulating factorial. `fac` is a regular definition.
- **G34**: `mult x y = qmult x y zero`
    - G85: `plus (mult x y) z = qmult x y z`
    - `qmult` is an accumulating multiply.
- **G35**: `exp x y = qexp x y (succ zero)`
    - G86: `mult (exp x y) z = qexp x y z`
    - `qexp` is an accumulating exponential.
- **G48**: `len (sort x) = len x`
    - G68: `len (insort x y) = succ (len y)`
- **G49**: `mem x (sort y) => mem x y`
    - G69: `not (= x y) => (=> (mem x (insort y z)) (mem x z))`
- **G50**: `count x (sort y) = count x y`
    - G70: `count x (insort x y) = succ (count x y)`
    - G71: `not (= x y) => (= (count x (insort y z)) (count x z))`
- **G75**: `append (rev x) y = qreva x y`
    - G72: `append (append x y) z = append x (append y z)`
- **G76**: `append (revflat x) y = qrevaflat x y`
    - G72: `append (append x y) z = append x (append y z)`
- **G77**: `rev (qreva x y) = append (rev y) x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G78**: `rev (qreva x (rev y)) = append y x`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G79**: `rev (append (rev x) y) = append (rev y) x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G80**: `rev (append (rev x) (rev y)) = append y x`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G81**: `qreva (qreva x y) nil = append (rev y) x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G82**: `qreva (qreva x (rev y)) nil = append y x`
    - G58: `rev (append x (cons y nil)) = cons y (rev x)`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
- **G83**: `rotate (len x) (append x y) = append y x`
    - G61: `append (append x (cons y nil)) z = append x (cons y z)`
    - G72: `append (append x y) z = append x (append y z)`
- **G84**: `mult (fac x) y = qfac x y`
    - G73: `mult (mult x y) z = mult x (mult y z)`
- **G85**: `plus (mult x y) z = qmult x y z`
    - G74: `plus (plus x y) z = plus x (plus y z)`
- **G86**: `mult (exp x y) z = qexp x y z`
    - G73: `plus (plus x y) z = plus x (plus y z)`

## CVC4 -i results
To obtain results, run
```shell
$ python3 run-benchmarks.py cvc4 ind/benchmarks-dt/clam/ -o results-clam.csv -t 5000
```

Can prove the following
- G2-G3
- G8-G9
- G22
- G24-G25
- G36-G39
- G43-G47
- G51-G61
- G63-G72
- G74

## CVC4 -i results with lemmas
To obtain results, run
```shell
$ python3 run-benchmarks.py cvc4 ind/benchmarks-dt/clam/sg -o results-clam-sg.csv -t 5000
```

Can prove all _except_
- G6
- G23
- G26
- G81-G82
- G84-86

Total provable: 42

## Cyclegg
Run on 239f4ad with
```shell
$ cargo run --release -- examples/clam.ceg -t 2
```

3 goals (G14, G49, G50) do not have some lemmas that CVC4 gets because we don't
support conditional lemmas yet.

Can prove all _except_
- G6-G7
- G12
- G14 (needs conditional lemma)
- G18
- G21
- G24
- G31
- G49-G50 (needs conditional lemmas)
- G75-G86

Total provable: 28
