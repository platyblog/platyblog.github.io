+++
date = "2017-10-23"
title = "To depend or not to depend"
author = "Yannick Zakowski"
description = "Investigating the use of dependent types to formalise Graphical Linear Algebra"
tags = []
categories = ["Coq"]
+++

Vincent recently pointed us to an introduction[^1] to a quite sexy recent mathematical theory: *Graphical Linear Algebra* (GLA).
We discuss in this blog post the use of dependent types to formalise this theory, following attempts conducted with Pierre.

# Graphical Linear Algebra

The theory of linear algebra is part of the compulsory credentials of any undergrad in mathematics, and crept into numerous scientific fields. Everywhere, the story follows the same (very) rough framework (overlooking the question of the underlying field and so-on).

1. Define vector spaces;

2. define morphisms between those spaces, which turn to be linear mappings;

3. notice that there is a 1-to-1 mapping relating linear transformations and matrices.

Hence, matrices constitute the *language* of linear algebra. Mathematicians, quite satisfied with this language, have used it to explore the *theory* of linear algebra with the great success that we know of.
Graphical linear algebra offers *another language* to describe *the same theory*. The intent is to provide a different intuition about the field, an approach which proved fruitful during the 20th to discover new results in many fields. We will not cover the link between the language of GLA and linear algebra in this post, but rather take it for granted, and ponder the best way to formalise it in Coq.

# The language

We briefly cover the language of GLA. However, the problem this blog post is concerned with is essentially independent from GLA in particular, and even more so from linear algebra. If you already know GLA or do not care about it, this section can be soundly skipped.

An element of GLA is a *diagram*, a series of boxes aligned horizontally and connected by wires. It can be thought of as a circuit, taking inputs at its left handside, and processing them from left to right, resulting in outputs. It naturally is meant to be represented and manipulated graphically, we shall do our best to remain readable in a purely textual form. The language is made of three kinds of components.

- Generators, *i.e.* elementary diagrams. Those are the basic blocks.

- Combinators, *i.e.* operations allowing to build diagrams out of simpler ones.

- Equations, *i.e.* rules identifying diagrams which are built differently, but should be thought of as equivalent.

### The generators

We detail briefly the basic blocks of the language, using wonders of ASCII art and a tidbit of imagination:

- $∅$ is the empty diagram. Nothing comes in, nothing comes out.

- $--$ is a simple wire. One input, one output: it can be thought of as the identity from F¹ to F¹.

- $∘-$ has no input, but one output: it is a constant! Let's call it *zero* suggestively.

- $-∘$ is the symmetric of zero: it is a dead-en! It *discards* its input.

- $-<$ is the *duplicate* diagram. Takes one input, returns two which should be interpreted as two copies.

- $>-$ is the *addition* diagram. Symmetric to the previous one, can be interpreted as resulting the sum of two inputs.

- $><$ is a bit weirder. It simply takes two inputs, and twists these entries to return them in the reversed order.

### The combinators

All those are basic, atomic, diagrams. Remains to combine them in order to build greater glorious diagrams. If we think about them graphically, two natural ways come to mind: pile them up, or chain them horizontally.

- $G₁ ⊕ G₂$ is the diagram resulting from putting $G$₁ on top of $G$₂. The resulting diagram can be thought of as two circuits working in parallel with no interaction.

- $G₁ ∘ G₂$ connects $G$₂ on the right of $G$₁. Here begins our sufferings: we do not want no dangling wires! This operation can only be performed if the number of wires getting out of $G$₁ is exactly equal to the number of wires getting in $G$₂ (not unlike a certain condition over the product of matrices...). This condition shall be the main focus of our attention once we get to the formalisation.

### The equations

Armed with our set of generators and our two combinators, we can span a whole family of diagrams. 

However, a lot of them look awfully alike! We probably do not want to differentiate based on the order in which we built our diagrams. $(G₁ ⊕ G₂) ⊕ G₃$ should be the same as $G₁ ⊕ (G₂ ⊕ G₃)$ for instance. 

But more fundamentally, we claim that we are designing a language to exactly represent linear algebra. We therefore better axiomatise it somewhere.
For instance, we hinted that $--$ really is nothing but the identity. So should $G ∘ --$ and $-- ∘ G$ really be any different from $G$? 

The following set of equations wraps up everything we need to get started.

- Three rules to axiomatise the addition.

  + $>< ∘ >- == >-$                     (commutativity)
  + $(-- ⊕ >-) ∘ >- == (>- ⊕ --) ∘ >-$  (associativity)
  + $-- == (o- ⊕ --) ∘ >-$              (zero is neutral)

- Three rules to axiomatise the copy.

  + $-< == -< ∘ ><$                     (commutativity)
  + $-< ∘ (-< ⊕ --) == -< ∘ (--  ⊕ -<)$ (associativity)
  + $-< ∘ (-o ⊕ --) == --$              (discard is neutral)

- Four rules to axiomatise their interaction.

  + $>- ∘ -< == (-< ⊕ -<) ∘ (-- ⊕ >< ⊕ --) ∘ (>- ⊕ >-)$
  + $>- ∘ -o == -o ⊕ -o$
  + $o- ∘ -< == o- ⊕~ o-$
  + $o- ∘ -o == ∅$

- Axiomatisation of the identities. -n- denotes n wires piled up one onto each other.

  + $-n- ∘ G == G == G ∘ -n-$
  + $∅ ⊕ G  == G == G ⊕ ∅$

- The order in which one we build a diagram does not matter

  + $G₁ ∘ (G₂ ∘ G₃) == (G₁ ∘ G₂) ∘ G₃$                (associativity of $∘$)
  + $G₁ ⊕~ (G₂ ⊕~ G₃) == (G₁ ⊕~ G₂) ⊕~ G₃$         (associativity of $⊕$)
  + $(G₁ ⊕ G₃) ∘ (G₂ ⊕ G₄) == (G₁ ∘ G₂) ⊕ (G₃ ∘ G₄)$

- These rules should be compositional: if two sub-diagrams are equivalent, substituting one for the other in the bigger diagram should lead to equivalent diagrams. We obtain this by stating that == is a congruence closure for both $∘$ and $⊕$.

  + $G₁ == G₁' -> G₂ == G₂' -> G₁ ∘ G₂ == G₁' ∘ G₂' $
  + $G₁ == G₁' -> G₂ == G₂' -> G₁ ⊕ G₂ == G₁' ⊕ G₂'$
  
- Finally, we take the reflexive, transitive and symmetric closure of the relation. 

  + $G == G$
  + $G₁ == G₂ -> G₂ == G₁$
  + $G₁ == G₂ -> G₂ == G₃ -> G₁ == G₃$

# Formalising GLA in Coq

*In progress, to consider a small subset and illustrate the biniou*

[^1]: https://graphicallinearalgebra.net/
