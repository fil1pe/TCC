Require Import List Lia.
Import ListNotations.

(*
  The Pigeonhole Principle: if l2 is a subset of l1 and its length is greater than the length of l2
  then it repeats an element.
*)

Lemma pigeonhole {X} (l1 l2 : list X) :
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, In x l2 -> In x l1) -> length l2 > length l1 ->
  exists l2a l2b l2c y, l2 = l2a ++ [y] ++ l2b ++ [y] ++ l2c.
Proof.
  intro eq_dec; revert l1; induction l2 as [|y l2 IH]; intros l1 H H0.
  - simpl in H0; nia.
  - destruct l1 as [|x l1].
    destruct (H y); left; auto.
    destruct (in_dec eq_dec y l2) as [H1|H1].
    + apply in_split in H1; destruct H1 as [l2a [l2b H1]]; subst;
      exists nil, l2a, l2b, y; auto.
    + assert (H2: In y (x::l1)). apply H; left; auto.
      apply in_split in H2; destruct H2 as [l1a [l1b H2]];
      destruct IH with (l1a ++ l1b) as [l2a [l2b [l2c [z H4]]]].
      * intros z H3; apply in_or_app; rewrite H2 in H; specialize (H z);
        assert (H4: In z (l1a ++ y :: l1b)). apply H; right; auto.
        apply in_app_or in H4; destruct H4 as [H4|H4].
        left; auto.
        destruct H4 as [H4|H4].
        subst; contradiction.
        right; auto.
      * assert (H3: length l1 = length (l1a ++ l1b)). {
          rewrite app_length; assert (H3: length ([x] ++ l1) = length (l1a ++ [y] ++ l1b)).
            simpl ([x] ++ l1); rewrite H2; auto.
          rewrite app_length, app_length, app_length in H3; simpl in H3; nia.
        }
        simpl in H0; rewrite app_length; rewrite app_length in H3; nia.
      * exists (y::l2a), l2b, l2c, z; subst; auto.
Qed.