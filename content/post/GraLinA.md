+++
date = "2017-07-02"
title = "To depend or not to depend"
author = "Yannick Zakowski"
description = "Investigating the use of dependent types to formalise Graphical Linear Algebra"
tags = []
categories = ["Coq"]
+++

Vincent recently pointed us to an introduction[^1] to a quite sexy recent mathematical theory: *Graphical Linear Algebra* (GLA).
We discuss in this blog post the use of dependent types to formalise this theory, following attempts conducted with Pierre.

#2 Graphical Linear Algebra

The theory of linear algebra is part of the compulsory credentials of any undergrad in mathematics, and crept into numerous scientific fields. Everywhere, the story follows the same (very) rough framework (overlooking the question of the underlying field and so-on).
..* Define vector spaces;
..* define morphisms between those spaces, which turn to be linear mappings;
..* notice that there is a 1-to-1 mapping relating linear transformations and matrices.
Hence, matrices constitute the *language* of linear algebra. Mathematicians, quite satisfied with this language, have used it to explore the *theory* of linear algebra with the great success that we know of.
Graphical linear algebra offers *another language* to describe *the same theory*. The intent is to provide a different intuition about the field, an approach which proved fruitful during the 20th to discover new results in many fields. We will not cover the link between the language of GLA and linear algebra in this post, but rather take it for granted, and ponder the best way to formalise it in Coq.

#2 The language

An element of GLA is a *diagram*, a series of boxes aligned horizontally and connected by wires. The language is made of three kinds of components.
..* Generators, *i.e.* elementary diagrams. Those are the basic blocks.
..* Combinators, *i.e.* operations allowing to build diagrams out of simpler ones.
..* Equations, *i.e.* rules identifying diagrams which are built differently, but should be thought of as equivalent.
For instance, the simplest diagram is a straight wire, denoted here by "--". It has exactly one incoming and one outing wires, and one can think of it as the identity from F¹ to F¹. 
As a first approximation, GLA can be described by the following BNF:
> GLA := \emptyset | ∅



[^1]: https://graphicallinearalgebra.net/
