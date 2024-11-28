---
title: "Formal semantics of Programming Languages in Lean (Draft)"
author: "Ricardo Maurizio Paul"
date: "January 1, 2025"
geometry: "left=2cm,right=2cm,top=2cm,bottom=3cm"
# output: "pdf_document"
---

## Observations

- The parts of the text that could require further exploration or sources are
  ==marked like this==.
- We use the lambda calculus notation for functions.
- Typesetting is not final. Use XeLaTex for special characters.

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

$$ \{P\} \ C \ \{Q\} $$

where P is the precondition, C is the command, and Q is the postcondition. By
using inference rules, Hoare logic can be used to show the correctness of a
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

==Proof of the relevance that program correctness has gained in recent years is
the adoption of the _Rust_ programming language, which has a strong type system
that ensures memory safety and thread safety, and is designed to prevent common
programming errors, such as null pointer dereferences, buffer overflows, and
data races. It ensures these properties by using a _borrow checker_ that
enforces strict rules on the use of memory, and by using a _type system_ that
ensures correctness of the programs. The borrow checker is based on
_substructural logic_ and _linear types_, concepts that we will not cover in
this text, but that encode in the language itself the rules of the type system,
ensuring that the programs are well-typed, and that the memory is used
correctly.==

## Proof assistants

### Historical background

Proof assistants, or interactive theorem provers, are software systems that aid
in the construction and verification of mathematical proofs using computers. The
inception of proof assistants can be traced back to the 1950s and 1960s, with
the _Logic Theorist_[^logictheorist] and ==_Automath_== systems. These were the
first systems to use a computer to check mathematical proofs. ==They were
created before the advent of modern type theory and the Curry-Howard
isomorphism, and used a different logical foundation based on _natural
deduction_==. Although interesting these systems were limited in scope, and
could only prove simple theorems.

[^logictheorist]:
    [Logic Theorist on Wikipedia](https://en.wikipedia.org/wiki/Logic_Theorist)

In the 1970s more powerful systems were developed, such as ==_LCF_==, based on
Dana Scott's _Logic of Computable Functions_, this was one of the first systems
to use proofs by induction, a feature fundamental to reason about recursively
defined functions and that we will see in this text. The creation of the
programming language ML, ==the father of all functional languages==, is also
attributed to the development of LCF, ==as it was designed for writing tactics
in LCF==. The modern approach of "step by step" proof construction, used by all
modern assistants, was also pioneered by LCF.

The 1970s also saw the development of ideas such as type theory, in particular
Martin-Löf type theory, and the Curry-Howard isomorphism, two key concepts that
are the basis of all modern proof assistants. In the 1980s this ideas were
implemented in systems such as ==_Nuprl_== and ==_Coq_==. Nuprl is one of the
first systems to use a constructive type theory at its core, were proofs are
first class objects, emphasizing their computational content and allowing
==_code extraction_ of programs from verified proofs==. Nuprl also introduced
dependent types, a powerful feature that allows the type of a value to depend on
the value itself. With this system a great deal of mathematics can be encoded
and proved.

A little later came Coq, a system based on the ==CIC (Calculus of Inductive
Constructions)==, a type theory that extends the Calculus of Constructions with
inductive types. Coq is one of the most popular proof assistants, and is widely
used in academia and industry to this day. We will see that the CIC is also the
basis of Lean, a more recent proof assistant that has gained significant
popularity in recent years.

While this asvancements where made with the theories of dependent types another
line of research was being developed, the ==_HOL_== family of proof assistants,
based on _Higher Order Logic_, a logic that extends first-order logic with
higher order quantifiers. These systems are based on the _LCF_ architecture, and
use a _kernel_ to ensure the correctness of the proofs. The most popular system
in this family is ==_Isabelle_==, a powerful proof assistant that ==is as
powerful as Coq and Lean==, but with a different logical foundation.

This brings us to Lean, the proof assistant that we will use in this text. Lean
is a modern proof assistant developed by Leonardo de Moura at Microsoft Research
and based on the CIC. We can see Lean as an evolution of Coq, with a more modern
syntax, and a more powerful type system, later we will discuss the differences
in more detail.

Leaving HOL aside, all these systems are based on the Curry-Howard isomorphism,
a fundamental concept that relates proofs and programs. To understand it we must
first introduce the basics of type theory.

## Type theory

Type theory is not a single theory, but a family of related theories that share
the same basic principles. We will focus on a family of type theories known as
Martin-Löf type theory, which was developed by Per Martin-Löf in the 1970s as a
foundation for constructive mathematics. Since its inception, type theory has
been strongly connected to $\lambda$-calculus, a formal system for expressing
computation based on function abstraction and application. This connection
arises thanks to the works of Alonzo Church, who showed that the
$\lambda$-calculus is equivalent to the Turing machine, and can be used to
define computable functions.

### Type theory vs set theory[^HoTTref]

[^HoTTref]:
    This section can mostly be copy and pasted from the HoTT book. The only
    problem is the exposition in the book introduce first all the concepts and
    then the examples, while in this text we will introduce the concepts and
    examples together. This means, for example, introducing natural numbers much
    earlier.

Type theory is a branch of mathematical logic that deals with the study of
types, an abstraction similar in some ways to the more familiar sets.

Like _sets_ are a primitive notion in set theory, _types_ are a primitive notion
in type theory, alongside _functions_. This two primitives ensure that functions
are only applied to the correct types, this is known as _type safety_. This
concept may be familiar to programmers, as it is the basis of static type
systems in programming languages, such as Haskell, Rust, and Scala.

As an informal introduction to types we can think of them as sets with
additional structure which dictates with functions can be applied to them. For
example, we can define a type $\mathbb{N}$ that represents the natural numbers,
and define a function $\texttt{add}: \mathbb{N} \to \mathbb{N} \to \mathbb{N}$
that takes two natural numbers and returns their sum. This ensures that the
function $\texttt{add}$ can only be applied to natural numbers, and not to any
other type.

A key point to remark is that types don't _contain_ values, they _classify_
values, while in set theory a value is a _member_ of a set, in type theory a
value _has_ a type. ==This is a subtle difference, but an important one, as it
allows us to reason about the properties of values based on their types, and to
ensure that the values are used correctly in the program==. The analogous to the
membership notation in set theory is the ==_typing judgement_== in type theory,
which is written as $x: \alpha$, and reads as "x has type $\alpha$".

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
in type theory as a function that takes an arbitary type $\alpha$ and returns a
proposition:

$$\texttt{Set} \ (\alpha : \texttt{Type}) := \alpha \to \texttt{Prop}$$

In this definition the precise type of $\texttt{Set}$ depends on the type
$\alpha$, this is what's commonly known as a ==polymorphic type==, and allows us
to define a type that depends on another type.

==We use the term proposition to refer to a type that can be either true or
false, not to be confused with the propositions of logic, which are statements
susceptible to proof==. This function corresponds to the concept of _membership_
in set theory, and can be used to define the membership of an element $x$ in a
set $S$ as $\texttt{Set} \ x \ S$, which is true if $x$ is a member of $S$, and
false otherwise.

### Equality

Equality in type theory is slightly more complex than in classic mathematics,
the equality that we have by default is _definitional equality_. That is two
terms are equal if they can be transformed into each other via _rewriting
rules_. The reduction rules of type theories typically include:

- $\beta$-reduction. Replacing a function application with the function body
  where the argument is substituted for the bound variable.
- $\delta$-reduction. Replacing a constant with its definition.
- $\iota$-reduction. Simplifying expressions involving constructors and pattern
  matching for inductive data types.

==These rules normally satisfy a series of desirable properties, such as
_confluence_, _termination_, and _consistency_, that ensure that the reduction
process is well defined, and that the equality relation is an equivalence
relation. In some cases other nice properties are added, such as _congruence_,
_strong normalization_, and _canonicity_==.

Another type of equality is _propositional equality_, which is states that two
terms are equal if they can be proven to be equal in the type theory. This is
more akin to the classic notion of equality, and is used to prove properties of
the terms. ==A special case of propositional equality is _functional
extensionality_[^funext], which states that two functions are equal if they are
equal for all arguments, a classic result of set theory that follows from the
axiom of extensionality, which states that two sets are equal if they contain
the same elements==. ==(The relationship may depend on axiom K)==.

Another important axiom is ==_propositional extensionality_==[^propext], which
states that two propositions are definitionally equal if they are equivalent,
that is, if they imply each other. This is a key property of type theory, as it
allows us to rewrite propositions in proofs, and simplify the reasoning process.

[^funext]:
    [Functional extensionality on nLab](https://ncatlab.org/nlab/show/function+extensionality)

[^propext]:
    [Propositional extensionality on nLab](https://ncatlab.org/nlab/show/propositional+extensionality)

### Universes

But what is this $\texttt{Prop}$ type that we mentioned before? $\texttt{Prop}$
is, not surprisingly, a type, so it has type $\texttt{Type}$, in fact any type
has type $\texttt{Type}$, even $\texttt{Type}: \texttt{Type}$. This lead to
==_impredicativity_==.

Impredicativity[^impred] arises when a definition of an object or type relies on
a quantifier that ranges over a totality encompassing the very object being
defined. This self-referential aspect can lead to logical paradoxes, akin to
Russell's Paradox in set theory, where a set is defined to contain all sets that
do not contain themselves.

The type theory analosous to Russell's paradox is the ==_Girard's paradox_==, in
a system that allows impredicativity, we can define a type $U$ that contains all
types that do not contain themselves, and then ask if $U: U$, if it is, then it
should not be of type $U$, and if it is not, then it should be. A system that
shows this paradox is not very useful for theorem proving, as it is
inconsistent, so any proposition can be proven. [^systemU] To avoid this, we
introduce a hyerarchy of _type universes_.

[^impred]:
    [Impredicativity on Wikipedia](https://en.wikipedia.org/wiki/Impredicativity)

[^systemU]: ==Historically this problem has been solved with System U==.

Each universe is a ==_collection_ of types, wether they are types or not depends
on the particular type theory==, in Lean and Coq they are not. Each universe
contains the types of the previous universe, and is contained in the next
universe. For example:~ $\texttt{Type}: \texttt{Type} \ 1$,
$\texttt{Type} \ 1: \texttt{Type} \ 2$, and so on. The function type inhabits
the smallest universe that contains the types of its domain and codomain. For
example, $\mathbb{N} \to \mathbb{N}: \texttt{Type} \ 1$, and
$\texttt{Type} \ 1 \to \texttt{Type} \ 2: \texttt{Type} \ 3$.

The first type universe, $\texttt{Type} \ 0$, contains the types of the
programming language itself, such as $\mathbb{N}$, $\texttt{Bool}$, and
$\texttt{List}$. The second type universe, $\texttt{Type} \ 1$, contains the
types of the first universe, and so on. The type $\texttt{Prop}$ is a special
type that sits alongside $\texttt{Type} \ 0$ at the bottom of the hierarchy,
this prevents defining a proposition in terms of itself, or any other type, for
that matter, and avoids paradoxes.

### Constructors

For now we have focused on types, but we need a way to create values of these
types, this is done using ==_type constructors_==, which are functions that
create elements of a type and define the possible forms an element of a type can
take. For example, we can define a type $\texttt{Bool}$ that represents the
booleans, and define two constructors $\texttt{true}$ and $\texttt{false}$ that
create the elements of the type. This ensures that the elements of the type are
either $\texttt{true}$ or $\texttt{false}$, and no other value.

### Inductive types

Of course, defining finite types such as $\texttt{Bool}$ is not very
interesting, we need a way to define infinite types, such as the natural
numbers. This is done using _inductive types_, which are types that are defined
by a set of constructors that define the possible forms an element of the type
can take. For example, we can define the natural numbers as an inductive type
with two constructors, $\texttt{zero}$ and $\texttt{succ}$, that create the
elements of the type, in a way analogous to the _Peano axioms_.

$$
\texttt{zero} : \mathbb{N} \qquad
    \texttt{succ}: \mathbb{N} \to \mathbb{N}
$$

Similar to the classic principle of induction, we have defined a base case
$\texttt{zero}$ and an inductive case $\texttt{succ}$, that creates the
successor of a natural number. In this way we can create the natural numbers as
an inductive type, and define functions that operate on them, such as addition,
multiplication, and exponentiation. This is the essence of inductive types, the
ability to define types that are created by a set of constructors, and define
functions that operate on them. And as is the case in classical mathematics, we
can use induction to prove properties of these types, ==in this case _structural
induction_==.

Following the natural number example, let's construct a function
$f: \mathbb{N} \to C$ by recursion on the naturals, it's enough to provide a
base case $c_0 : C$ and a "next step" function $c_s: \mathbb{N} \to C \to C$,
then we can define $f$ as:

$$ f \ 0 = c_0 $$

$$ f \ (\texttt{succ} \ n) = c_s \ n \ (f \ n) $$

To use this proof technique we must ensure that the inductive type is
_well-founded_, that is, that the constructors of the type are applied a finite
number of times to create an element of the type.

### Dependent function type or $\Pi$-type

In type theory, functions are first class citizens, and can be passed as
arguments, returned as results, and stored in data structures. In some cases we
need to define functions whose return type depends on the value of the
arguments, this is done using _Pi types_, which are types that depend on a
value.

The notation for a Pi type is $\Pi_{x: \alpha} B \ x$, where $x$ is the argument
on which the type depends, $A$ is the type of the argument, and $B$ is a family
of types indexed by $x$ ($B: \alpha \to \texttt{Type}$). For example, we can
define a function that takes a natural

To better understand this we introduce an example were $\Pi$-types are used to
to define a vector of a given length, which type depends on the length of the
vector:

$$
 \Pi_{n: \mathbb{N}} \texttt{Vec} \ \alpha \ n
$$

with constructors:

$$ \texttt{nil} : \texttt{Vec} \ \alpha \ 0 $$

$$
  \texttt{cons} : \Pi_{n: \mathbb{N}}
  (\alpha \to \texttt{Vec} \ \alpha \ n
    \to \texttt{Vec} \ \alpha \ (\texttt{succ} \ n))
$$

In this way $\Pi$-types give us a way to type complex data structures, such as
lists, trees, and graphs, that depend on the values of their elements,
==ensuring type safety==.

## The Curry-Howard isomorphism

The Curry-Howard isomorphism is a result that establishes a correspondence
between _propositions_ and _types_ and between _terms_ and _proofs_. In broad
terms, every proposition $P$ in the logic corresponds to a type $\alpha \ P$ in
the system, every connective in the logic ($\wedge$, $\vee$, $\Rightarrow$, ...)
corresponds to a _type constructor_ in the system ($\times$, $+$, $\to$, ...),
and every proof of a proposition corresponds to a term $a : \alpha \ P$ of the
type.

==Let's consider the example of implication ($\Rightarrow$) in propositional
logic, the proposition $P \Rightarrow Q$ states that if $P$ is true, then $Q$
must be true. In type theory this corresponds to the function type
$\alpha \ P \to \alpha \ Q$, which states that if we have a proof of $P$, then
we can construct a proof of $Q$. The proof of the proposition corresponds to a
term of the type, and the proof of the implication corresponds to a function
that takes a proof of $P$ and returns a proof of $Q$==.

This correspondence is not limited to propositional logic, but extends to
predicate logic, and higher order logics. For example, the universal quantifier
$\forall$ corresponds to the dependent function type $\Pi$, and the existential
quantifier $\exists$ corresponds to the ==dependent pair type $\Sigma$==. This
correspondence is the basis of all modern proof assistants, and allows us to
reason about programs using the tools of logic, and vice versa.

The _type checker_ of the system then allows us to _verify_ the proofs, by
checking that the terms are well-typed, and that the terms correspond to valid
proofs. This mechanism ensures that the proofs are correct, and that the
programs are well-typed.

## Proof irrelevance

We've seen that Lean and Coq share much of their type theory, so what are the
key differences between the two? The most important difference is that Lean is
designed to be proof-irrelevant. Proof-irrelevance is a property of a type
theory that states that all proofs of a proposition are definitionally equal,
meaning that they are indistinguishable by the type checker.

==For example, imagine we have two proofs of the fact that $2 + 2 = 4$, one that
uses the Peano axioms, and another that uses the definition of addition. In a
proof-irrelevant type theory, these two proofs would be considered equal, and
could be used interchangeably==.

Why does this matter? First of all it helps to simplify complex proofs, as we
don't have to worry about the details of the proof, only that it exists. This
also has computational benefits, as we can erase the proofs from the final
program, and only keep the results.

It also aids in ==_code extraction_==, the process of extracting a program from
proofs and definitions. This is a key feature when using Lean as tool in formal
verification, as we can first formally prove the correctness of the program, and
then extract an efficient implementation from the proof. Irrelevancy ensures
that the extracted code is independent of the proof used. ==Code extraction is
an area where Lean 4 has made significant improvements over Lean 3, as it
supports a better compiler backend, and more target languages.==

Proof irrelevance is also supported in Coq, but not as a definitional equality,
but a set of axioms that ensure that all proofs of a proposition are equal. In
Coq $\texttt{Prop}$ is a universe, separate from data types which reside in
$\texttt{Type}$, inside this universe two proofs of the same proposition are
_propositionally equal_. Coq also supports definitional proof irrelevance, by
using the $\texttt{SProp}$ but it's not the default.

## Semantics[^winskel]

[^winskel]: This section can be mostly copy and pasted from Winskel's book.

Now that we have introduced type theory and proof assistants, we can move on to
using them to define the semantics of programming languages. Semantics are the
study of the ==_meaning_ of programs==, and can be defined in different ways, we
will focus on operational semantics, and denotational semantics.

We first describe a simple imperative language $\texttt{IMP}$ that we will use
to illustrate the concepts. $\texttt{IMP}$ is a simple language that consists of
a set of commands, such as assignment, sequencing, conditionals, and loops. It
is constrained by design to be simple, so that we can focus on introducing the
techniques of formal semantics, but this approach can be extended to widely used
languages, such as C, Java, and Python.

### Syntax

As an informal introduction to the syntax of $\texttt{IMP}$ we can define the
"syntactic sets" of the language as:

- Integers $n \in \mathbb{Z}$.
- Boolean values $b \in \texttt{Bool} = \{\texttt{true}, \texttt{false}\}$.
- Variables $x \in \texttt{Var}$, that store integers.
- Arithmetic expressions $a \in \texttt{Aexp}$, that can be constants,
  variables, or arithmetic operations.
- Boolean expressions $b \in \texttt{Bexp}$, that can be constants, variables,
  or boolean operations.
- Commands $c \in \texttt{Com}$, that can be assignments, conditionals, loops,
  or sequences of commands.

Now we could define the syntax of $\texttt{Aexp}$ in Backus-Naur form:

$$
a ::= n \ | \ x \ | \ a_1 + a_2 \ | \ a_1 - a_2 \ | \ a_1 * a_2
$$

the syntax of $\texttt{Bexp}$ as:

$$
b ::= \texttt{true} \ | \ \texttt{false} \ | \ !b \ | \ b_1 \land b_2 \ | \ b_1 \lor b_2 \ | \ a_1 = a_2 \ | \ a_1 \leq a_2
$$

and the syntax of $\texttt{Com}$ as:

$$
c ::= skip \ | \ x := a \ | \ c_1; c_2 \ | \
      \texttt{if} \ b \ \texttt{then} \ c_1 \ \texttt{else} \ c_2 \ \texttt{end} \ | \
      \texttt{while} \ b \ \texttt{loop} \ c \ \texttt{end}
$$

In the Lean project the syntax of $\texttt{IMP}$ is defined in the file
[Lang.lean](https://github.com/remind-me-later/SemanticsLean/blob/main/Semantics/Imp/Lang.lean)
where the previous definitions are encoded as inductive types, we reproduce here
the definition of the syntax of arithmetic expressions and commands:

```lean
inductive Aexp where
  | val_1 : Int -> Aexp
  | var_1 : String -> Aexp
  -- arithmetic
  | add_1 : Aexp -> Aexp -> Aexp
  | sub_1 : Aexp -> Aexp -> Aexp
  | mul_1 : Aexp -> Aexp -> Aexp
```

```lean
inductive Com where
  | skip_1
  | cat_1   : Com -> Com -> Com
  | ass_1   : String -> Aexp -> Com
  | if_1    : Bexp -> Com -> Com -> Com
  | while_1 : Bexp -> Com -> Com
```

We can now define some _abuses of notation_ or _coercions_, for example we can
transform the integers of the meta-language (Lean) into integers of
$\texttt{IMP}$ we can do this by ==instantiating some classes==:

```lean
instance: OfNat Aexp n := <Aexp.val_1 n>
instance: Add Aexp := <Aexp.add_1>
instance: Sub Aexp := <Aexp.sub_1>
instance: Neg Aexp := <fun a => Aexp.sub_1 0 a>
instance: Mul Aexp := <Aexp.mul_1>

-- x + 3
#check Aexp.var_1 "x" + 3

-- x * -3
#check Aexp.var_1 "x" * -3
```

After defining some parsing rules we can typecheck an $\texttt{IMP}$ program
like this:

```lean
#check [|
n = 5; i = 2; res = 1;

while i <= n loop
    res = res * i;
    i = i + 1
end
|]
```

### States

As we've seen in the syntax our imperative language supports a feature that
characterizes
