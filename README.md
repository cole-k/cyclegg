# Cyclegg

**🚧 Here be dragons: research code ahead! 🚧**

## Overview

`cyclegg` is a fast theorem prover for equational reasoning powered by e-graphs. It
has two main contributions.

1. Efficient, exhaustive search of induction hypothesis and lemma applications.

<details>
<summary>Example: (add x y) = (add y x)</summary>
It can prove the above property (commutativity of addition) without
needing to discover any helper lemmas. It does this by applying the inductive
hypothesis several times in somewhat unconventional ways.
</details>

2. Lemma discovery based on subterms which appear in the goal.

<details>
<summary>Example: (rev (rev xs)) = xs</summary>
It can prove that reversing a list twice gives the same list by discovering and proving the lemma (Cons x (rev xs)) = (rev (append xs (Cons x Nil))).
</details>

`cyclegg` is fast: both of these examples run in under 50ms.

A sketch of its general algorithm can be found [here](./docs/proof-algorithm.md).

## Running

To run `cyclegg` on the IsaPlanner benchmarks, run the below command.

```shell
$ cargo run -r -- examples/isaplanner.ceg --timeout 5
```

Run with `--help` to see an overview of the different command-line flags.

``` shell
$ cargo run -- --help
```

## Preliminary results

As of 2a6aa34, when run with a timeout of 5s.

- IsaPlanner benchmarks: 78/86
- CLAM benchmarks: 30/50

## The name

`cyclegg` was originally based on [CycleQ](https://github.com/ec-jones/cycleq)
and its idea was to improve cyclic proof search using an e-graph (specifically,
the [egg](https://github.com/egraphs-good/egg) e-graph library). We have since
focused on the improvements e-graphs give to proof search as opposed to e-graphs
plus cyclic proofs. So the "cycl-" part of the name is now a misnomer. We'll
probably change the name soon.

## TODO

### Organizational
- Create goals inside parser, do not expose RawGoal
- Decouple proof generation from proof search (e.g. put Defs, Proof term somewhere else)
- Make partial applications without $ work
- Move from SymbolLang to a proper language.
    - See babble for inspiration (https://github.com/dcao/babble/blob/main/src/ast_node.rs)
- Emit a proof data structure
    - Right now we just emit strings that are (mostly) valid LiquidHaskell.
    - Creating a proper equational proof data structure would allow us to emit to other backends.
    - It would also be cleaner.

### Search
- In cyclic mode: use multi-patterns instead of requiring that the premise has no extra vars?      

### Proofs
- Conditional props proof generation
    - Add explanation for conditional unions (cannot just `union_trusted`).
    - Include the premise into the LH precondition
        - This can be accomplished by taking a witness of the precondition as an argument.
    - How to include the proof of the condition holding?
        - To use a conditional lemma you need a witness of the condition. We can take the e-graph from
          which we are getting the explanation and ask it to explain why the e-classes of the condition
          are equal and use those to build a proof. In LH this would look something like
          
          ```haskell
          let conditionWitness =   condLHS 
                               ==. condLHS'
                               ? lemma lemmaArgs
                               ==. condRHS
                               *** QED
           in conditionalLemma conditionWitness args
          ```
