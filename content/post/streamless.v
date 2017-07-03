Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.

Definition streamless (X : Set) := forall f : nat -> X,
  {i : nat & {j : nat & i <> j /\ f i = f j}}.

Section Proof.
  Context {X Y: Set}.
  Variable finite_X: streamless X.
  Variable finite_Y: streamless Y.

  (** The shifting of a stream **)
  Definition shift {A: Set} (f: nat -> A) k :=
    fun n => f (n + k).

  Lemma shift_correct: forall {A: Set} (f: nat -> A) k n,
      shift f k n = f (n + k).
  Proof.
    trivial.
  Qed.

  (** Projections of a stream of a sum type over a side, by substituing values of the other type for a default value **)
  Definition sub_stream_l (f: nat -> X + Y) (x0: X): nat -> X :=
    fun n => match f n with
          | inl x => x
          | inr _ => x0
          end.
  Definition sub_stream_r (f: nat -> X + Y) (y0: Y): nat -> Y :=
    fun n => match f n with
          | inl _ => y0
          | inr y => y
          end.

  (**
 Given a stream in X + Y, by extracting the substream on the side of its first value, our oracle gives us one of two things:
   - either a duplicate which does not contain the placeholder, hence a true duplicate;
   - or a duplicate containing a placeholder, but hence an element of the other type in the stream: we found a pair in X*Y
   **)
  Program Definition get_next (f: nat -> X + Y):
    {n: nat * nat & {z: X * Y & f (fst n) = inl (fst z) /\ f (snd n) = inr (snd z)}} +
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

  Lemma helping_arith: forall n m p, n <> m -> n + p <> m + p.
      intros; omega.
  Qed.

  Fixpoint lift_get_next (f: nat -> X + Y) n:
    {n: nat * nat & {z: X * Y & f (fst n) = inl (fst z) /\ f (snd n) = inr (snd z)}} +
    {i : nat & {j : nat & i <> j /\ f i = f j}} :=
    match n with
    | 0 => get_next f 
    | S m =>
      match lift_get_next f m with
      | inl (existT _ (n1,n2) (existT _ _ _)) =>
        match get_next (shift f (S (max n1 n2))) with
        | inl (existT _ (n1',n2') (existT _ (x,y) H)) =>
          inl (existT _ (n1' + S (max n1 n2), n2' + S (max n1 n2)) (existT _ (x,y) H))
        | inr (existT _ n1' (existT _ n2' (conj ineq eq))) => 
          inr (existT _ (n1' + S (max n1 n2))
                      (existT _ (n2' + S (max n1 n2))
                              (conj (helping_arith n1' n2' (S (max n1 n2)) ineq) eq)))
        end
      | inr witness => inr witness
      end
    end.

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

  Lemma streamless_sum_aux : streamless (X + Y).
  Proof.
    intros f.
    set (g := proj_lift_get_next f); unfold proj_lift_get_next in g.
    destruct (f 0) as [x0 | y0].
    - destruct g as [h | h] eqn:H; subst g; inversion H; clear H.
      destruct (finite_X h) as (n1 & n2 & ineq & H).
      subst h.
      destruct (lift_get_next f n1) as [([? ?] & [? ?] & [? ?]) | collision] eqn:H1; [| exact collision].
      destruct (lift_get_next f n2) as [([? ?] & [? ?] & [? ?]) | collision] eqn:H2; [| exact collision].
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

End Proof.

Theorem streamless_sum : forall X Y, streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros; apply streamless_sum_aux; auto.
Qed.