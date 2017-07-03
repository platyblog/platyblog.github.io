+++
date = "2017-07-02"
title = "De la finitude de l'être"
author = "Yannick"
description = "A small, interesting constructivist problem"
tags = []
categories = ["math"]
+++
A reddit user, /u/INL_TT, has recently proposed a few problems to be solved using your favourite proof assistant. The last one has been particularly interesting: [coq-math-problems](https://coq-math-problems.github.io/Problem5/).

The problem is taken from a paper by Coquand and Spiwack[^1] investigating ways to formalise in a constructivist context the notion of finite set. A common characterisation of a finite set A is the impossibility to inject the natural numbers into A. Or phrased differently, any stream of elements of A contains a duplicate. Formally, naming this characterisation _streamless_:

```Coq
Definition streamless (X : Set) := forall f : nat -> X,
  {i : nat & {j : nat & i <> j /\ f i = f j}}.
```

The problem is simply to show that the streamless property is stable under sum.

```Coq
Theorem streamless_sum : forall X Y, 
    streamless X -> streamless Y -> streamless (X + Y).
```

Let's first understand why the problem is non-trivial.

Let $f: \mathbb N \rightarrow X + Y$. Classically, we obviously know that the stream $f$ contains either an infinity of elements of $X$ or an infinity of elements of $Y$, maybe of both. By extracting such a substream, any of our oracles would allow us to conclude.

However one cannot in general decide which of $X$ or $Y$ to chose: we therefore are seemingly unable to build neither a stream of $X$ nor a stream of $Y$, rendering our hypotheses useless.

One could therefore ponder whether our definition of finite set can be reduced to one allowing us to only manipulate a list of values, rather than a stream. Indeed, a finite set $A$ is intuitively characterised by a finite cardinal, i.e. we can find a list of values containing any element of $A$. It however turns out that this alternative definition is strictly stronger, the streamless characterisation does not allow us to compute the cardinal of our set.

It feels like we cannot extract a stream of one of our types, and it feels like we cannot reduce our definition to a list: I've been completely stuck! The first assertion of the previous sentence however turns out to be wrong, as David Reboullet found out and shared the following proof with us. It goes as follows.

Assume that $f~0 = inl~ x_0$. While we indeed cannot directly extract a substream of X, we can create one by filling out the elements of Y by the dummy value we found, $x_0$. Let us name $proj_f$ this stream.

Now we can ask our oracle for a collision in $proj_f.$ We obtain two distinct indices $n_1,~n_2$ such that $proj_f(n_1) = proj_f(n_2)$. This may feel useless granted the collision is likely to be two occurrences of $x_0,$ but we actually do get something by looking at these indices in our original stream $f:$

* Either we find two elements of X: the collision was real, we won!

* Or we found at least one element of Y: in addition to $x_0$, we have a couple in X * Y, and their indices in $f$.

We therefore are able to build a function get_next which associates to a stream either a pair of elements, or a collision. Formally in Coq, we simply need to duplicate the code to account whether (f 0) is in X or in Y. With sub_stream_l and sub_stream_r are the obvious projections:

```Coq
  Context {X Y: Set}.
  Variable finite_X: streamless X.
  Variable finite_Y: streamless Y.

  Program Definition get_next (f: nat -> X + Y):
    {n: nat * nat & {z: X * Y & f (fst n) = inl (fst z) /\
                                f (snd n) = inr (snd z)}} +
    {i : nat & {j : nat & i <> j /\ f i = f j}} := 
    match f 0 with
    | inl x0 =>
      match finite_X (sub_stream_l f x0) with
        existT _ n1 (existT _ n2 (conj ineq collision)) =>
        match (f n1, f n2) with
        | (inl x1, inl x2) =>
          inr (existT _ n1 (existT _ n2 (conj ineq _)))
        | (inr y, _) => inl (existT _ (0,n1) (existT _ (x0,y) _))
        | (_, inr y) => inl (existT _ (0,n2) (existT _ (x0,y) _))
        end
      end
    | inr y0 => 
      match finite_Y (sub_stream_r f y0) with
        existT _ n1 (existT _ n2 (conj ineq collision)) =>
        match (f n1, f n2) with
        | (inr y1, inr y2) => inr (existT _ n1 (existT _ n2 (conj ineq _)))
        | (inl x, _) => inl (existT _ (n1,0) (existT _ (x,y0) _))
        | (_, inl x) => inl (existT _ (n2,0) (existT _ (x,y0) _))
        end
      end
    end.
  Next Obligation.
    clear Heq_anonymous1.
    unfold sub_stream_l in collision; rewrite <- H0, <- H1 in collision.
    rewrite collision; reflexivity.
  Qed.
  Next Obligation.
    clear Heq_anonymous1.
    unfold sub_stream_r in collision; rewrite <- H0, <- H1 in collision.
    rewrite collision; reflexivity.
  Qed.
```

The important intuition is that our oracle can therefore be used at any moment to know whether I can still find both an element of X and one of Y in my stream. We can therefore now leverage get_next in order to build a stream of pairs in X * Y, until a collision is found and we propagate this collision for the remaining indices.

By recurrence on the index, we define the following stream g:

```
 g 0 = get_next f

 g (S n) = inr collision when g n = inr collision \\ we keep a found collision

 g (S n) = let n1,n2 be the indices of (g n) in 
           let k := max(n1,n2) in
           let H := get_next (fun n => f(n + k)) in \\ we shift f and query get_next 
           if H = inr collision
           then inr collision
           else let n1',n2' be the indices of H in
                n1' + max (n1,n2), n2' + max(n1,n2)
```
                   
More formally, in Coq, we obtain: 

```Coq
  Lemma helping_arith: forall n m p, n <> m -> n + p <> m + p.
      intros; omega.
  Qed.

  Fixpoint lift_get_next (f: nat -> X + Y) n:
    {n: nat * nat & {z: X * Y & f (fst n) = inl (fst z) /\
                                f (snd n) = inr (snd z)}} +
    {i : nat & {j : nat & i <> j /\ f i = f j}} :=
    match n with
    | 0 => get_next f 
    | S m =>
      match lift_get_next f m with
      | inl (existT _ (n1,n2) (existT _ _ _)) =>
        match get_next (shift f (S (max n1 n2))) with
        | inl (existT _ (n1',n2') (existT _ (x,y) H)) =>
          inl (existT _ (n1' + S (max n1 n2), n2' + S (max n1 n2)) 
                        (existT _ (x,y) H))
        | inr (existT _ n1' (existT _ n2' (conj ineq eq))) => 
          inr (existT _ (n1' + S (max n1 n2))
                        (existT _ (n2' + S (max n1 n2))
                         (conj (helping_arith n1' n2' (S (max n1 n2)) ineq) eq)))
        end
      | inr witness => inr witness
      end
    end.

```

We have built this way a new stream which only contains either collisions of the original stream, or elements of the original stream. The key difference with the first one we built is that we tagged X and Y on the same side of the sum. If we are looking say for elements of X, then for any index, we can find an X, or we find a collision.

Asking once again the oracle what it has to say about the projection of (lift_get_next f) over X is enough to conclude. Indeed, once again, we can test the returned indices against the original stream. Two cases are possible:

* Either both indices correspond to a pair of elements in (lift_get_next f). We have found a collision.

* Or at least one of them is not a pair in (lift_get_next f). But then it contains a collision instead.

Hence the result.

Proving it formally, we as usual need to duplicate the code, as well as reason a bit about (lift_get_next f) to ensure that the indices we obtain are indeed not the same:

```Coq
  Lemma lift_get_next_monotone:
    forall f n n1 n2 H1 m1 m2 H2,
      (lift_get_next f n = inl (existT _ (n1,n2) H1)) ->
      (lift_get_next f (S n) = inl (existT _ (m1,m2) H2)) ->
      n1 < m1 /\ n2 < m2.
  Proof.
    intros; cbn in H0.
    rewrite H in H0.
    destruct H1 as ([x1 y1] & eq1 & eq1').
    destruct H2 as ([x2 y2] & eq2 & eq2').
    cbn in *.
    destruct (get_next (shift f (S (max n1 n2)))) eqn:eq;
        [| destruct s as (i & j & ineq & ?); inversion H0].
    destruct s as ([i j] & [x y] & Eq & Eq').
    inversion H0; clear H0.
    subst; cbn in *.
    split; rewrite Nat.add_comm; apply lt_plus_trans; unfold lt; apply le_n_S.
    apply Max.le_max_l.
    apply Max.le_max_r.
  Qed.

  Lemma lift_get_next_monotone_strong:
    forall f d n m (eqd: d = m - n) (lt: n < m) n1 n2 H1 m1 m2 H2,
      (lift_get_next f n = inl (existT _ (n1,n2) H1)) ->
      (lift_get_next f m = inl (existT _ (m1,m2) H2)) ->
      n1 < m1 /\ n2 < m2.
  Proof.
    intros.
    generalize dependent m; revert m1 m2 H2.
    induction d as [| d IH]; intros; [omega |].
    cbn in *.
    destruct d as [| d].
    - clear IH.
      assert (m = S n) by omega; subst m.
      eapply lift_get_next_monotone; eauto. 
    - destruct m as [| m]; [omega |].
      assert (eqd': S d = m - n) by omega; clear eqd.
      generalize H0; intros Hyp; cbn in H0.
      destruct (lift_get_next f m) eqn:eq; [| inversion H0].
      destruct s as ([i j] & [x y] & Eq & Eq').
      destruct (get_next (shift f (S (max i j)))) eqn:eq';
        [| destruct s as (? & ? & ineq & ?); inversion H0].
      destruct s as ([i' j'] & [x' y'] & Eq'' & Eq''').
      inversion H0; clear H0.
      subst; unfold fst, snd in *.
      destruct lift_get_next_monotone with (1 := eq) (2 := Hyp).
      eapply IH in eq; eauto; [| omega]; clear IH; destruct eq as [ineq1 ineq2].
      clear Hyp eq' H.
      split; omega.
  Qed.
      
  Lemma lift_get_next_somewhat_inj:
    forall f n m (ineq: n <> m) n1 n2 H1 m1 m2 H2,
      (lift_get_next f n = inl (existT _ (n1,n2) H1)) ->
      (lift_get_next f m = inl (existT _ (m1,m2) H2)) ->
      n1 <> m1 /\ n2 <> m2.
  Proof.
    intros f n m ineq; intros.
    destruct (lt_eq_lt_dec n m) as [[? | ?] | ?].
    edestruct lift_get_next_monotone_strong; eauto; omega.
    omega.
    edestruct lift_get_next_monotone_strong; eauto; omega.
  Qed.

  (* We project lift_get_next *)
  Definition proj_lift_get_next (f: nat -> X + Y): (nat -> X) + (nat -> Y) :=
    match f 0 with
    | inl x0 => inl (fun n =>
                      match lift_get_next f n with
                      | inl (existT _ _ (existT _ (x,_) _)) => x
                      | inr _ => x0
                      end)
    | inr y0 => inr (fun n =>
                      match lift_get_next f n with
                      | inl (existT _ _ (existT _ (_,y) _)) => y
                      | inr _ => y0
                      end)
    end.                   

  Theorem streamless_sum : streamless (X + Y).
  Proof.
    intros f.
    set (g := proj_lift_get_next f); unfold proj_lift_get_next in g.
    destruct (f 0) as [x0 | y0].
    - destruct g as [h | h] eqn:H; subst g; inversion H; clear H.
      destruct (finite_X h) as (n1 & n2 & ineq & H).
      subst h.
      destruct (lift_get_next f n1) as [([? ?] & [? ?] & [? ?]) | 
                collision] eqn:H1; [| exact collision].
      destruct (lift_get_next f n2) as [([? ?] & [? ?] & [? ?]) | 
                collision] eqn:H2; [| exact collision].
      unfold fst, snd in *; subst.
      exists n, n3; split; [| rewrite e,e1; reflexivity].
      refine (match (lift_get_next_somewhat_inj f n1 n2 ineq n n0 _ n3 n4 _ H1 H2)
              with conj X _ => X end). 
    - destruct g as [h | h] eqn:H; subst g; inversion H; clear H.
      destruct (finite_Y h) as (n1 & n2 & ineq & H).
      subst h.
      destruct (lift_get_next f n1) as [([? ?] & [? ?] & [? ?]) | collision] eqn:H1; [| exact collision].
      destruct (lift_get_next f n2) as [([? ?] & [? ?] & [? ?]) | collision] eqn:H2; [| exact collision].
      unfold fst, snd in *; subst.
      exists n0, n4; split; [| rewrite e0,e2; reflexivity].
      refine (match (lift_get_next_somewhat_inj f n1 n2 ineq n n0 _ n3 n4 _ H1 H2)
              with conj _ X => X end). 
  Qed.
```

The Coq proof in one piece can be [found here](https://platyblog.github.io/post/streamless/streamless.v).

Quite fun how such a simple statement can reveal itself to be quite subtle! Once again, congratulations to David for finding this proof. I did not check it against the one from the paper but would imagine them to match.

[^1]:[Constructively finite?](http://assert-false.net/arnaud/papers/Constructively%20Finite.pdf) 
