+++
date = "2017-02-01"
title = "$\\mathbb{N}\\rightarrow\\mathbb{B}$ is a searchable set"
author = "Alix"
description = "First post ever"
tags = []
categories = ["math"]
+++
I never quite understood why all the crazy magic in this 
[post](http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/) actually works, 
nor did I manage to grok Escardo's [paper](http://www.cs.bham.ac.uk/~mhe/papers/exhaustive.pdf). 
But I will try to write what I understood so far.

Escardo shows that the Cantor space ($\mathbb{N}\rightarrow\mathbb{B}$ where $\mathbb{B}$ 
is the set of booleans) admits exhaustive search, 
meaning that for any total predicate $\varphi$, it is possible to find a witness $w$ such that
$\varphi(w)$ is _true_ or show that such a witness doesn't exist in finite time.

This is seemingly impossible as the Cantor space is clearly infinite. 
However, the main point is that $\varphi$ is a _total_ predicate, 
meaning that for every $u$, $\varphi(u)$ takes a finite time to compute. 
It is thus necessary that for every _u_, there exists some $n$ such that $\varphi$ 
only uses $u\_0, ..., u\_n$ to compute its result $\varphi(u)$.

Let's call $\eta(u)$ the number such that $\varphi$ only needs 
$u\_0, ..., u\_{\eta(u)}$ to compute $\varphi(u)$. If $\eta$ could be bounded, 
then we would only need to feed a finite number of imputs to $\varphi$ to search 
through the whole Cantor space.

Indeed, suppose that $\eta$ can be bounded by $k$, then necessarily if the length 
of the longest common prefix between $u$ and $v$ is greater than $k$ 
(i.e. $u\_0 = v\_0, ..., u\_k~ = v\_k$) then $\varphi(u) = \varphi(v)$ because 
$\varphi$ cannot differentiate $u$ from $v$ by definition of $\eta$.

How can we show that $\eta$ is bounded? Suppose that it isn't, 
then there must be a sequence $u^0, u^1, ...$ such that $\eta(u^0) < \eta(u^1) < \eta(u^2) < ...$
For all $p > 0$, the longest common prefix of $u^0$ and $u^p$ is strictly smaller than 
$\eta(u^0)$, otherwise $\varphi$ wouldn't be able to differentiate $u^0$ from $u^p$ by definition 
of $\eta(u^0)$. However, there is only a finite number of possible prefix smaller than $\eta(u^0)$, 
thus according to the pigeonhole principle, there must be a subsequence 
$u^{r\_0(0)}, u^{r\_0(1)}, ...$ such that they all have a same common prefix of at 
least length 1 and we can choose them so that $1 \leq \eta(u^{r\_0(0)}) < \eta(u^{r\_0(1)}), ...$ 
By reiterating the process, we can build a new subsequence $u^{r\_1(0)}, u^{r\_1(1)}, ...$
such that they all have a same common prefix of at least length 2 and 
$2 \leq \eta(u^{r\_1(0)}) < \eta(u^{r\_1(1)}), ...$, etc.

Finally, the term $w = \lambda x. u^{r\_x(0)}$ is such $\eta(w) \geq p$ for any $p$ as 
$w$ has the same $p$-length prefix as $u^{r\_p(0)}$. This is obviously impossible 
as it would need to be infinite. Therefore $\eta$ must be bounded.

However, this only proves that such a bound exists, we still do not know how to find its value, 
which is necessary to know when to stop while searching for a witness.

