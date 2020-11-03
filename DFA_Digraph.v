Require Import Nat PeanoNat List DFA Digraph.
Import ListNotations.

(* We can reduce a DFA into a digraph making its transition become edges. *)

Fixpoint transition_edges g q l :=
  match l with
  | a::l =>
    match transitionf g q a with
    | Some q' => edge q q'::transition_edges g q l
    | None => transition_edges g q l
    end
  | nil => nil
  end.

Fixpoint transition_edges_states g l : digraph :=
  match l with
  | q::l => transition_edges g q (alphabet g) ++ transition_edges_states g l
  | nil => nil
  end.

Definition dfa_digraph g := transition_edges_states g (states g).

(* Two states are vertices iff there exists a transition between them. *)
Lemma dfa_digraph_neighbor g q1 q2 :
  neighbor (dfa_digraph g) q1 q2 <-> exists a, transitionf g q1 a = Some q2.
Proof.
  assert (P: forall q1 q2 l, In (edge q1 q2) (transition_edges g q1 l) <-> exists a, In a l /\ transitionf g q1 a = Some q2). {
    clear q1 q2; intros q1 q2 l; induction l as [|b l IH]; split.
    - contradiction.
    - intros [a [[] _]].
    - simpl; intro H; destruct (transitionf g q1 b) as [q3|] eqn:H0. destruct H as [H|H].
      2,3: apply IH in H; destruct H as [a'' H]; exists a''; split; intuition.
      exists b; split.
      + left; auto.
      + injection H; intros; subst; auto.
    - intros [a [H H0]]; destruct H as [H|H]; subst.
      + simpl; rewrite H0; left; auto.
      + simpl; destruct (transitionf g q1 b); try right; apply IH; exists a; intuition.
  }
  assert (P0: forall q1 q2 l, In (edge q1 q2) (transition_edges_states g l) <-> In q1 l /\ exists a, transitionf g q1 a = Some q2). {
    clear q1 q2; intros q1 q2 l; induction l as [|q l IH]; split.
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
      apply P in H; destruct H as [a [_ H]]; split; try (exists a); intuition.
    + apply IH in H; intuition.
  - simpl; intros [H [a H0]]; apply in_or_app; destruct H as [H|H]; subst.
    + left; apply P; exists a; split.
      apply transitionf_defined in H0; intuition.
      auto.
    + right; apply IH; split; try (exists a); intuition.
  }
  split; intro H.
  - apply P0 in H; destruct H as [_ H]; auto.
  - destruct H as [a H]; apply P0; split.
    2: auto.
    apply transitionf_defined in H; intuition.
    exists a; auto.
Qed.