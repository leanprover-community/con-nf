# The consistency of New Foundations

[![.github/workflows/push_main.yml](https://github.com/leanprover-community/con-nf/actions/workflows/push_main.yml/badge.svg)](https://github.com/leanprover-community/con-nf/actions/workflows/push_main.yml)

In 1937, Quine proposed a set theory called "New Foundations", and since 2010, Randall Holmes has claimed to have a proof of its consistency.
In this repository, we use the formal theorem prover Lean to verify the difficult part of his proof, thus proving that New Foundations is indeed consistent.

See [our website](https://leanprover-community.github.io/con-nf/) for more information, the [documentation of our Lean code](https://leanprover-community.github.io/con-nf/doc/), and the [draft paper](https://zeramorphic.github.io/con-nf-paper/main.l.pdf) aiming to translate the Lean definitions into English.

To run our code locally, install [elan](https://github.com/leanprover/elan), clone the repository, and run the following command in a terminal in the repository's root directory.
```
lake exe cache get
```
The code can then be viewed in an editor such as Visual Studio Code, or compiled directly from the command-line using `lake build`.

## Objective

It is known that New Foundations is consistent if and only if a theory called Tangled Type Theory (TTT) is consistent (see theorem 1 [here](https://randall-holmes.github.io/Papers/tangled.pdf)).
We aim to formally construct a model of TTT in Lean, thus proving (on paper) that New Foundations is consistent, or in short, Con(NF).
We are working from the paper proofs in [untangled.pdf](https://randall-holmes.github.io/Nfproof/untangled.pdf), [retangled.pdf](https://randall-holmes.github.io/Nfproof/retangled.pdf), and a [new document](https://randall-holmes.github.io/Nfproof/newnfdoc.pdf), but many alterations and additions have been made to make the proof compatible with Lean's type theory.

Note that this project depends on [mathlib](https://github.com/leanprover-community/mathlib4), the community mathematical library written in Lean.
This allows us to use familiar results about things like cardinals and groups without having to prove them ourselves.

Every definition and theorem in mathlib and this project have been checked by Lean's trusted kernel, which computationally verifies that the proofs we have constructed are indeed correct.
However, Lean cannot check that the statements of the definitions and theorems match their intended English equivalents, so when drawing conclusions from the code in this project, translation to and from English must be done with care.

## Tangled type theory

TTT is a many-sorted set theory with equality "=" and the membership relation "∈".
The sorts are indexed by a limit ordinal λ, and elements of λ are called type indices.
A formula "x = y" is well-formed if x and y have the same type, and a formula "x ∈ y" is well-formed if x has any type less than y.

One of the axioms of tangled type theory is extensionality, which stipulates that a set of type α is uniquely determined by its elements of *any* type β < α.
This is strange: for example, if two sets of type α differ, they have different type β elements for *every* β < α.
This property makes it difficult to construct models of TTT.

## Strategy

Our construction of the model uses the following rough strategy.

### Construction of the base type

Let λ be a limit ordinal, κ > λ be a regular uncountable ordinal, and μ > κ be a strong limit cardinal with cofinality at least κ.
Sets of size less than κ are called *small*.

We first construct an auxiliary type at level -1, called the *base type*, below all types that will eventually become part of the model.
Elements of this type are called atoms (although they are not atoms in the ZFU or NFU sense, for instance).
There are μ atoms, divided into *litters* of size κ.

### Constructing each type

At each type level α, we will produce a collection of model elements called *tangles*.
We also produce a group of permutations, called *allowable permutations*, which act on the type of tangles.
Each tangle is stipulated to have a *support* under the action of allowable permutations; this is a small set of objects called *addresses*.

Each tangle at level α will be given a preferred extension of some type β < α, and we can recover from a tangle's elements which extension it prefers.
The extensions of such a tangle in other lower types can be deduced from its β-extension.
This allows us to satisfy TTT's extensionality axiom.

### Controlling the size of each type

Each type α can only be constructed under the assumption that all types β < α are of size exactly μ.
It is easy to prove that the type of α-tangles has cardinality at least μ, so we need to show that there are at most μ elements of this set.
We do this by showing that there are not that many fundamentally different descriptions of tangles under the action of allowable permutations.
This requires the [freedom of action theorem](https://leanprover-community.github.io/con-nf/doc/ConNF/FOA/Result.html#ConNF.StructApprox.freedom_of_action), which is a technical lemma that allows us to construct allowable permutations.

### Finishing the induction

We can then run the above process recursively to produce the types of tangles at all type levels α.
We then check that our construction indeed produces a model of TTT by checking that it satisfies a finite axiomatisation of the theory.
