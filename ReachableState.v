Require Import Nat PeanoNat List DFA Digraph DFA_Digraph.
Import ListNotations.

(* A state is reachable iff there exists a xtransition from the start state to it. *)
Definition reachable_state g q := exists w, ixtransition g w = Some q.

(*
  If there exists a start state, then a given q is a reachable state iff q is reachable from the
  start state in the digraph.
*)
Lemma dfa_digraph_reachable g q q' :
  start g = Some q' -> reachable_state g q <-> q = q' \/ reachable (dfa_digraph g) q' q.
Proof.
  intro H; split; intro H0.
  - destruct H0 as [w H0]; unfold ixtransition in H0; rewrite H in H0;
    generalize dependent q'; generalize dependent q;
    induction w as [|a w IH] using rev_ind; intros q q' H H0.
    + left; injection H0; auto.
    + rewrite xtransition_app in H0; simpl in H0; destruct (xtransition g (Some q') w) as [q''|] eqn:H1.
      2: discriminate.
      fold (xtransition g (Some q'') [a]) in H0;
      pose H1 as H2;
      apply IH in H2.
      2: auto.
      replace (xtransition g (Some q'') [a]) with (transitionf g q'' a) in H0.
      2: simpl; destruct (transitionf g q'' a); auto.
      destruct H2 as [H2|H2]; subst; right.
      * apply reach_neigh, dfa_digraph_neighbor; exists a; auto.
      * apply reach_trans with q''.
        auto.
        apply reach_neigh, dfa_digraph_neighbor; exists a; auto.
  - destruct H0 as [H0|H0].
    + exists nil; unfold ixtransition; simpl; rewrite H; auto.
    + apply reachable'_correct in H0; remember (dfa_digraph g); induction H0; subst.
      * apply dfa_digraph_neighbor in H0; destruct H0 as [a H0];
        exists [a]; unfold ixtransition; simpl; rewrite H, H0; auto.
      * destruct IHreachable' as [w H2].
        1,2: auto.
        apply dfa_digraph_neighbor in H1; destruct H1 as [a H1];
        exists (w ++ [a]); unfold ixtransition; rewrite xtransition_app;
        unfold ixtransition in H2; rewrite H2;
        simpl; rewrite H1; auto.
Qed.

(* Decidability of reachable state *)
Theorem reachable_state_dec g q :
  {reachable_state g q} + {~ reachable_state g q}.
Proof.
  destruct (start g) as [q0|] eqn:H.
  2: right; unfold reachable_state, ixtransition; intros [w contra]; rewrite H in contra;
  rewrite xtransition_none in contra; discriminate.
  destruct (Nat.eq_dec q q0) as [H0|H0].
  - left; exists nil; unfold ixtransition; rewrite H; subst; auto.
  - pose proof dfa_digraph_reachable as H1; destruct H1 with g q q0.
    auto.
    destruct (reachable_dec Nat.eq_dec (dfa_digraph g) q0 q) as [H4|H4].
    + left; auto.
    + right; intro contra; apply H2 in contra; destruct contra as [contra|contra]; contradiction.
Qed.