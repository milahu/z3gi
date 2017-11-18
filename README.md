Grammatical inference using the Z3 SMT solver
=============================================

Z3GI is a Python tool and library that uses the [Z3 SMT solver][z3] for learning minimal consistent state machine models from labeled strings or input/output taces.

[z3]: https://github.com/Z3Prover/z3

Introduction
------------

Grammatical inference is the research field that is concerned with learning the set of rules that describe the behavior of a system, such as a network protocol, a piece of software, or a (formal) language.
One of the best studied problems in grammatical inference is that of finding a deterministic finite automaton (DFA) of minimal size that accepts a given set of positive strings and rejects a given set of negative strings.
This problem is can be very hard, as it has been shown to be NP-complete.
Z3GI provides different ways of solving this (and similar) problem(s) using satisfiability modulo theories (SMT).

Installing with pip (recommended)
---------------------------------

The recommended way of installing Z3GI is with `pip`:

```
$ pip install z3gi
```

Installing from sources
-----------------------

Alternatively, you can install Z3GI by cloning this repository, and installing using `setuptools`:

```
$ git clone https://gitlab.science.ru.nl/rick/z3gi.git
$ python z3gi/setup.py install
```

Getting started
---------------

Consider a deterministic finite automaton (DFA) that accepts strings of `0`s and `1`s in which the number of `0`s minus twice the number of `1`s is either 1 or 3 more than a multiple of 5 (such a DFA is described [here][dfa]).

[dfa]: http://abbadingo.cs.nuim.ie/dfa.html

A training file `train.txt` for this DFA could read (if you have the sources of this package, this file can be found at `docs/train.txt`):

```
16 2
1 4 1 0 0 0
1 4 0 1 0 0
1 4 0 0 1 0
1 5 1 0 1 1 1
1 6 1 1 1 1 0 1
1 6 0 1 0 0 0 0
1 6 1 0 0 0 0 0
1 7 0 0 0 1 1 0 1
1 7 0 0 0 0 1 0 1
0 3 1 0 1
0 4 0 0 0 0
0 4 1 1 0 1
0 5 0 0 0 0 0
0 5 0 0 1 0 1
0 6 0 1 0 1 1 1
0 7 1 0 0 0 1 1 1
```

In this [Abbadingo file][abbadingo], the first line is a header, giving the number of strings in the file (16) and the number of symbols (2).
Each line after the header has the format 

[abbadingo]: http://abbadingo.cs.nuim.ie/data-sets.html

```
label n symbol1 symbol2 ... symboln
```

Where label `1` means accepted, and the label `0` means rejected.

We can use Z3GI to learn a model for the strings in `train.txt` as follows:

```
$ python -m z3gi --model -f train.txt
```

This produces the following output:

```
Learned model:
[state3 = 3,
start = 0,
state0 = 0,
n = 5,
state2 = 2,
state4 = 4,
1 = INPUT!val!0,
state1 = 1,
0 = INPUT!val!1,
out = [3 -> True, 4 -> True, else -> False],
trans = [(0, INPUT!val!0) -> 3,
        (0, INPUT!val!1) -> 4,
        (4, INPUT!val!0) -> 2,
        (3, INPUT!val!0) -> 4,
        (3, INPUT!val!1) -> 2,
        (2, INPUT!val!0) -> 1,
        (1, INPUT!val!1) -> 3,
        (4, INPUT!val!1) -> 1,
        else -> 0]]
```

We can interpret this learned model as follows.
- `0 = INPUT!val!1` and `1 = INPUT!val!0` provide identifiers for `0` and `1` (notice that the values in the identifiers and the actual inputs are different!)
- `n = 5` indicates that the learned model has 5 states
- `state0 = 0` through `state4 = 4` provide the identifiers for these states
- `out` describes an output function for these states (`True` if it is accepting and `False` if it is rejecting)
- `trans` desribes a transition function for states and symbols to states (e.g. `(0, INPUT!val!0) -> 3)` describes a transition from `state0` with `1` to `state3`)

Using z3gi in Python
--------------------

Let's learn the same model (from `train.txt`) in Python:

1. Open your Python interpreter:

    ```
    $ python
    ```
2. Let's use a different encoder this time:

    ```
    >>> from z3gi.encoders import expressive
    >>> encoder = expressive.Encoder()
    ```
3. Create a sample:

    ```
    >>> from z3gi.sample import Sample
    >>> sample = Sample(encoder)
    ```
4. Add constraints for strings in `train.txt` to the sample:

    ```
    >>> from z3gi.parsers import abbadingo
    >>> for string, label in abbadingo.read(open('train.txt', 'r'), header=1):
    ...     sample[string] = label
    ...
    ```
5. Obtain the model!

    ```
    >>> model = sample.model()
    >>> print(model)
    ```