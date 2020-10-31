Require Import Nat PeanoNat List DFA Digraph.
Import ListNotations.

Fixpoint transition_edges g q symbols :=
  match symbols with
  | a::symbols =>
    match transitionf g q a with
    | Some q' => edge q q'::transition_edges g q symbols
    | None => transition_edges g q symbols
    end
  | nil => nil
  end.

Lemma transition_edges_correct g q q' l :
  In (edge q q') (transition_edges g q l) <-> exists a, In a l /\ transitionf g q a = Some q'.
Proof.
  induction l as [|a' l IH]; split.
  - contradiction.
  - intros [a [[] _]].
  - simpl; intro H; destruct (transitionf g q a') as [q''|] eqn:H0. destruct H as [H|H].
    2,3: apply IH in H; destruct H as [a'' H]; exists a''; split; intuition.
    exists a'; split.
    + left; auto.
    + injection H; intros; subst; auto.
  - intros [a [H H0]]; destruct H as [H|H]; subst.
    + simpl; rewrite H0; left; auto.
    + simpl; destruct (transitionf g q a'); try right; apply IH; exists a; intuition.
Qed.

Fixpoint dfa_digraph' g states : digraph :=
  match states with
  | q::states => transition_edges g q (alphabet g) ++ dfa_digraph' g states
  | nil => nil
  end.

Lemma dfa_digraph'_correct g l q1 q2 :
  In (edge q1 q2) (dfa_digraph' g l) <-> In q1 l /\ exists a, transitionf g q1 a = Some q2.
Proof.
  induction l as [|q l IH]; split.
  - contradiction.
  - intros [[] _].
  - simpl; intro H; apply in_app_or in H; destruct H as [H|H].
    + assert (q1 = q). {
        clear IH l. induction (alphabet g) as [|a l IH].
        - contradiction.
        - simpl in H; destruct (transitionf g q a); try (destruct H as [H|H]).
          2,3: apply IH; auto.
          injection H; auto.
      } subst.
      apply transition_edges_correct in H; destruct H as [a [_ H]]; split; try (exists a); intuition.
    + apply IH in H; intuition.
  - simpl; intros [H [a H0]]; apply in_or_app; destruct H as [H|H]; subst.
    + left; apply transition_edges_correct; exists a; split.
      try (apply transition_alphabet in H0); auto.
      auto.
    + right; apply IH; split; try (exists a); intuition.
Qed.

Definition dfa_digraph g := dfa_digraph' g (states g).

Lemma dfa_digraph_correct g q1 q2 :
  neighbor (dfa_digraph g) q1 q2 <-> exists a, transitionf g q1 a = Some q2.
Proof.
  split; intro H.
  - apply dfa_digraph'_correct in H; destruct H as [_ H]; auto.
  - destruct H as [a H]; apply dfa_digraph'_correct; split.
    2: auto.
    apply transition_states in H; auto.
    exists a; auto.
Qed.