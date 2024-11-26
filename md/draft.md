# Formal semanantics of Programming Languages in Lean

## Notation

The parts of the text that could require further exploration or sources are
==marked like this==.

## Introduction

Proof assistants such as Lean and Coq have gained significant popularity in
recent years, specifically in the field of formal verification. As software
systems become ==increasingly more complex==, and are responsible for more
critical tasks, the need for formal verification becomes more apparent. Formal
verification is a technique that uses mathematical logic to prove the
correctness of a system, usually hardware or software. It involves using formal
methods and tools to prove that the system satisfies a set of well defined
properties that model the desired behavior. A classic approach to formal
verification is Hoare logic, a formal system that deconstructs programs into
components each with a set of pre and post conditions, these conditions and
components, called commands, are represented as _Hoare triples_ of the form:

```text
{P} C {Q}
```

where P is the precondition, C is the command, and Q is the postcondition. By
using inference rules, Hoare logic can be used to prove the correctness of a
program by proving that the postcondition of the program is satisfied given the
precondition. However, reasoning about loops and recursion can be difficult in
Hoare logic, as it requires the use of invariants to prove the termination of
the program. We will see that this is a common problem when reasoning about
programs in general, as proving the termination of a given program is a
non-trivial task, and in the most general case, is undecidable, this is known as
the famous ==_Halting Problem_==.

The inference rules for Hoare logic however are dependent on the _semantics_ of
the programming language, the object of study of this text. The semantics of a
programming language are the rules that define the meaning of the programs, we
will see that these rules can present themselves in different forms, such as
operational semantics, denotational semantics, and axiomatic semantics. In this
text we will focus on operational semantics, and denotational semantics.
Axiomatic semantics, such as Hoare logic, are derived from operational
semantics.

These formal methods ensure _correctness_ of the programs, and are a more
rigorous approach to program verification than testing. Testing can only show
the presence of bugs, but not their absence, and is not exhaustive. In this way
formal methods are more suitable for critical systems, such as avionics, medical
devices, and financial systems, where the cost of failure is high. Alongside the
correctness gains, formal methods can also improve the performance of programs,
verified toolchains, ==such as CompCert, have been shown== to produce more
efficient code than their unverified counterparts. This is due to more
aggressive optimizations being possible when the correctness of the program is
guaranteed: runtime checks can be removed, aggresive flow analysis can be
performed, and dead code can be eliminated. Some of these optimizations can be
performed by modern compilers, using static analysis, but the guarantees
provided by formal methods are stronger, as we said before we can ensure
_termination_ in some cases.

## A variety of proof assistants

Some of the most popular proof assistants are Coq, Isabelle, and Lean. Coq and
Lean use the _Calculus of Inductive Constructions_ as their logical foundation,
while Isabelle uses _Higher Order Logic_. To understand the differences between
the two approaches, we must first understand the _Curry-Howard isomorphism_ that
is the basis of all proof assistants. ==The Curry-Howard isomorphism states that
there is a correspondence between proofs and programs, and between propositions
and types==. This means that we can use the type system of a programming
language to encode theorems, and the programs as proofs of these theorems, in
this way we can use the type checker of the programming language to verify the
correctness of the proofs. This is the basis of all proof assistants, and is the
reason why they are so powerful, as we can use the type system to encode complex
mathematical theorems, and the proof assistant to verify their correctness.
==The proof assistants as we can see are more proof checkers than proof
assistants, as they do not help in the construction of the proofs, but rather in
the verification of their correctness.==

The _Calculus of Constructions_ is a _type theory_ that serves as a programming
language and foundation for ==_constructive_ mathematics==. At its core, is a
higher order typed lambda calculus, with dependent types, and a universe
hierarchy. To understand what all of this means, we must first understand the
basics of type theory, lambda calculus, and dependent types.

## The basics of type theory

Type theory is a branch of mathematical logic that deals with the study of
types, an abstraction similar in some ways to the more familiar sets, and
functions, not as defined in set theory, but as a primitive notion.

As an informal introduction to types we can think of them as sets with
additional structure, this structure dictates with functions can be applied to
them. For example, we can define a type `Nat` that represents the natural
numbers, and define a function `add` that takes two natural numbers and returns
their sum. This ensures that the function `add` can only be applied to natural
numbers, and not to any other type. This is the essence of type theory, the
ability to restrict the domain of functions to certain types, and to ensure that
the functions are applied to the correct types. This is known as _type safety_,
and is a key feature of type theory.

Type theory can be used as a foundation of mathematics, in the same way that set
theory is used. In fact, type theory and set theory are closely related, and
both can be used to formalize mathematics. However, there are some key
differences between the two.

The most important difference between type theory and set theory is that type
theory its own deductive system, while set theory is formulated within
first-order logic. This means that set theory has two primitive notions, sets
and propositions, while type theory has types and functions. With just these two
we can recreate all first-order logic, and in fact, we can use types to encode
propositions, and functions to encode proofs.

This makes type theory ==more expressive than set theory, as we can use types to
encode propositions, and vice versa==. This also means that we can encode sets
in type theory as a function that takes an arbitary type `α` and returns a
proposition:

```lean
def Set (α: Type u) := α → Prop
```

==We use the term proposition to refer to a type that can be either true or
false, not to be confused with the propositions of logic, which are statements
susceptible to proof==. This function corresponds to the concept of _membership_
in set theory, and can be used to define the membership of an element `x` in a
set `S` as `Set x S`, which is true if `x` is a member of `S`, and false
otherwise.

But what is this `Prop` type that we mentioned before? `Prop` is, not
surprisingly, a type, so it has type `Type`, in fact any type has type `Type`,
even `Type`, this paradox, known as ==_Girard's paradox_==, is a well known
problem in type theory and the analogous to _Russell's paradox_ in set theory.
==Historically this problem has been solved with System U==. To make sense of
this `Type` and avoid some problems we have to introduce _type universes_.

To avoid Girard's paradox, a type cannot have itself as its type, to avoid this
we introduce a hierarchy of types, called _type universes_, each universe
contains the types of the previous universe, and is contained in the next
universe. In this case `Type: Type 1`, `Type 1: Type 2`, and so on. The function
type inhabits the smallest universe that contains the types of its domain and
codomain. For example, `Nat -> Nat` inhabits `Type 1`, and `Type 1 -> Type 2`
inhabits `Type 3`.

The first type universe, `Type 0`, contains the types of the programming
language itself, such as `Nat`, `Bool`, and `List`. The second type universe,
`Type 1`, contains the types of the first universe, and so on.

For now we have focused on types, but we need a way to create values of these
types, this is done using _type constructors_, which are functions that create
elements of a type and define the possible forms an element of a type can take.
For example, we can define a type `Bool` that represents the booleans, and
define two constructors `True` and `False` that create the elements of the type.
This ensures that the elements of the type are either `True` or `False`, and no
other value.

## Inductive types

Of course, defining finite types such as `Bool` is not very interesting, we need
a way to define infinite types, such as the natural numbers. This is done using
_inductive types_, which are types that are defined by a set of constructors
that define the possible forms an element of the type can take. For example, we
can define the natural numbers as an inductive type with two constructors,
`Zero` and `Succ`, that create the elements of the type, in a way analogous to
the _Peano axioms_.

```lean
inductive Nat : Type
| Zero : Nat
| Succ : Nat -> Nat
```

Similar to the classic principle of induction, we have defined a base case
`Zero` and an inductive case `Succ`, that creates the successor of a natural
number. In this way we can create the natural numbers as an inductive type, and
define functions that operate on them, such as addition, multiplication, and
exponentiation. This is the essence of inductive types, the ability to define
types that are created by a set of constructors, and define functions that
operate on them. And as is the case in classical mathematics, we can use
induction to prove properties of these types, in this case _structural
induction_. To use this proof technique we must ensure that the inductive type
is _well-founded_, that is, that the constructors of the type are applied a
finite number of times to create an element of the type.

## Dependent types

But what if we want to define a type that depends on a value? For example, a
list of natural numbers, we could define a different type for each of the types
of the possible arguments, but this would be cumbersome, and not very useful.
This is solved using _dependent types_, ==which are types that depend on a
value==. We can define our list as:

```lean
inductive List (α: Type u) : Type u
| Nil : List α
| Cons : α -> List α -> List α
```

In this definition, `List` is a type constructor that takes a type `α` and
returns a type `List α`, dependent on the value of `α`. This allows us to define
a list of natural numbers as `List Nat`, a list of booleans as `List Bool`, and
so on. In this manner dependent types allow us to define our structures in a
more general way, and avoid repeating proofs for each type.

## Pi types

Dependent types are not only useful for defining data structures, but also for
defining functions. In type theory, functions are first class citizens, and can
be passed as arguments, returned as results, and stored in data structures. The
type of a function is called a _Pi type_, and is a dependent type that depends
on a value. For example, we can define the type of the function `add` as:

```lean
def add : Nat -> Nat -> Nat
```

This definition states that `add` is a function that takes two natural numbers
and returns a natural number. This is a simple example of a Pi type, but we can
define more complex types, such as functions that take functions as arguments,
or functions that return functions as results. This is the essence of Pi types,
the ability to define functions as types, and use them to encode complex logic.

==We can define for example the cartesian product of two types as a function
that takes a type `α` and returns a function that takes a type `β` and returns
the type `α x β`, this is the type of pairs of elements of `α` and `β`==. This
is

```lean
def Prod (α: Type u) (β: Type v) : Type (max u v) := λ (α: Type u), λ (β: Type v), α x β
```

Pi types can also be used to define _sum types_, _dependent functions_, etc...
And are one of the most powerful features of type theory.

## Type theory and proofs

Now, why is type theory so important for proof assistants? As we mentioned
before, by the Curry-Howard isomorphism, we can use types to encode
propositions, also called theorems, and type constructors, aka functions, to
encode proofs. In fact, the way to prove a proposition in these type theories is
to construct a value of the type that encodes the proposition, this is called
_proof by construction_. This is the basis of all proof assistants, and is the
reason why they are so powerful, as we can use the type system to encode complex
mathematical theorems, and the proof assistant to verify their correctness.

As we mentioned before, Coq and Lean use the _Calculus of Inductive
Constructions_ as their logical foundation, while Isabelle uses _Higher Order
Logic_. ==HOL is not a type theory, so its outside the scope of this text, but
is also a powerfull proof assistant with a large user base, in fact, we will
reference the book "Concrete Semantics with Isabelle/HOL" in some parts of this
text, as the proofs in the book can be easily translated to Lean==.

## Lean vs Coq

We've seen that Lean and Coq share much of their type theory, so what are the
key differences between the two? The most important difference is that Lean is
designed to be proof-irrelevant. Proof-irrelevance is a property of a type
theory that states that all proofs of a proposition are definitionally equal,
meaning that they are indistinguishable by the type checker. This aligns with
the idea that propositions in constructive mathematics are concerned with the
existence of a proof, not with the specific proof itself. This is in contrast to
Coq, which is proof-relevant, meaning that the specific proof of a proposition
matters, and can be used in further proofs.
