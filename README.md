Grammatical inference using the Z3 SMT solver
=============================================

Z3GI is a Python tool and library that uses the [Z3 SMT solver][z3] for learning minimal consistent state machine models from labeled strings or input/output taces.

[z3]: https://github.com/Z3Prover/z3

Introduction
------------

Grammatical inference is the research field that is concerned with learning the set of rules that describe the behavior of a system, such as a network protocol, a piece of software, or a (formal) language.
Z3GI provides different ways of solving this (and similar) problem(s) using satisfiability modulo theories (SMT).

Installing with pip (recommended)
---------------------------------

To be enabled.

Installing from sources
-----------------------

Alternatively, you can install Z3GI by cloning this repository, and installing using `setuptools`:

```
$ git clone https://gitlab.science.ru.nl/rick/z3gi.git
$ python z3gi/setup.py install
```

Getting started - learning from traces
---------------

Consider a deterministic finite automaton (DFA) corresponding to the regex (ab)*.

The training file at `resources\traces\regex_example` for this DFA reads:

```
1 a b
1 a b a b
0 a
0 b
0 a b a
0 a a
0 a b b
0 a b a a
```

Each line represents an observation comprising elements separated by spaces. 
For a DFA, the observation has the syntax:
```
label symbol1 symbol2 ... symboln
```

The symols form a string, the label indicates that the DFA accepts the string (if its value is `1`) or 
that it rejects the string (if its value is `0`). 
In the current version, we require that the first observation introduces all inputs in the alphabet.


We can use Z3GI to learn a model for the observations in `regex_example` as follows:

```
$ python z3gi -m traces -a DFA -f resources\traces\regex_example
```

This produces an output containing:

```
Learned model:
 {'q0': False, 'q1': True, 'q2': True}
acc_seq(q0) =
acc_seq(q1) = q0 a -> q1
acc_seq(q2) = q0 a -> q1 , q1 b -> q2
q0
        a -> q1
        b -> q0
q1
        a -> q0
        b -> q2
q2
        a -> q1
        b -> q0
```

The model description is split into 3 (or 2) sections.
- the first section indicates acceptance/rejection of each state
- the second section indicates access sequences to the state, in later versions, this section may be ommitted
- the first section describes the transition for the DFA
 


Learning scalable systems
-----------------------

Z3GI implements several scalable systems such as Sets or Login Systems. What these
systems have in common is that they are configurable in size. A greater size leads
results in a bigger system. Z3GI can be used to learn these systems. 

To give an example, suppose we want to learn a Login system with 2 users 
which is structured as a Mealy machine. To learn this system we run:

```
$ python z3gi -m scalable -a MealyMachine -sc Login -s 2
```

Learning .dot models
-----------------------

We can apply Z3GI to learn simulations of .dot models. In particular, we can
learn the Mealy machine models obtained by various case-studies which are included 
in the `resources\models` directory. 

Say we want to learn the biometric passport. We then need to run:

```
$ python z3gi -m dot -a MealyMachine -f resources\models\biometric.dot
```

For bigger models which are more difficult to test, we may require an external
test algorithm. We provide a Windows binary for the [Yannakakis test algorithm][yan].
You can activate this algorithm using the `-y path_bin` option. By using `-m dotnorst`,
Z3GI will attempt to learn without using resets.


Our implementation currently only supports Mealy machines, though functionality 
for other formalisms will be added in the future. Note there is currently no 
standard .dot format for register automata. Also note that the Yannakakis test
algorithm only works on Mealy machines and requires resets.

[yan]: https://gitlab.science.ru.nl/moerman/Yannakakis


Learning randomly generated Mealy machines without reset
-----------------------

Z3GI can be used to learn without reset randomly generated Mealy machines with the
property that they are strongly connected (though not necessarily minimal). 

Say we want to learn a randomly generated Mealy machine with 2 inputs, 2 outputs 
and 3 states. Then we run:

```
$ z3gi -m randnorst -a MealyMachine -ni 2 -no 2 -ns 3
```