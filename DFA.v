Require Import Nat PeanoNat List NatListSet Lia.
Import ListNotations.

Inductive dfa_component :=
  | state (q : nat) (accept : bool)
  | symbol (a: nat)
  | transition (q a q':nat).

Definition dfa := list dfa_component.

Fixpoint states g :=
  match g with
  | state q accept::g => add q (states g)
  | symbol a::g => states g
  | transition q a q'::g => add q (add q' (states g))
  | nil => nil
  end.

Fixpoint alphabet g :=
  match g with
  | state q accept::g => alphabet g
  | symbol a::g => add a (alphabet g)
  | transition q a q'::g => add a (alphabet g)
  | nil => nil
  end.

Fixpoint transitionf g (q a:nat) :=
  match g with
  | transition q1 a' q2::g =>
    match andb (q =? q1) (a =? a') with
    | true => Some q2
    | false => transitionf g q a
    end
  | _::g => transitionf g q a
  | nil => None
  end.

Fixpoint start g :=
  match g with
  | state q accept::g => Some q
  | symbol a::g => start g
  | transition q a q'::g => Some q
  | nil => None
  end.

Fixpoint accept g (q:nat) :=
  match g with
  | state q' b::g => 
    match q =? q' with
    | true => b
    | false => accept g q
    end
  | _::g => accept g q
  | nil => false
  end.


Lemma transition_states g a q1 q2 :
  transitionf g q1 a = Some q2 -> In q1 (states g).
Proof.
  intro H;
  induction g as [|x g IH].
  - discriminate.
  - simpl in *; destruct x.
    + apply add_correct; right; auto.
    + intuition.
    + destruct (q1 =? q) eqn:H0, (a =? a0) eqn:H1.
      1,2: apply EqNat.beq_nat_true in H0; subst; apply add_correct; intuition.
      1,2: apply add_correct; right; apply add_correct; right; auto.
Qed.

Lemma transition_alphabet g a q1 q2 :
  transitionf g q1 a = Some q2 -> In a (alphabet g).
Proof.
  intro H; induction g as [|x g IH].
  - discriminate.
  - simpl in *; destruct x.
    + intuition.
    + apply add_correct; right; auto.
    + destruct (a =? a0) eqn:H0, (q1 =? q) eqn:H1.
      1,2: apply EqNat.beq_nat_true in H0; subst; apply add_correct; intuition.
      1,2: apply add_correct; right; auto.
Qed.

Fixpoint xtransition g (q:option nat) (w:list nat) :=
  match q with
  | Some q =>
    match w with
    | a::w => xtransition g (transitionf g q a) w
    | nil => Some q
    end
  | None => None
  end.

Definition ixtransition g w := xtransition g (start g) w.

Fixpoint states_opt' (l:list nat) :=
  match l with
  | q::l => Some q::states_opt' l
  | nil => nil
  end.
Definition states_opt g := None::states_opt' (states g).

Definition accept_opt g q :=
  match q with
  | Some q => accept g q
  | None => false
  end.

Definition acceptsb g w := accept_opt g (ixtransition g w).

Lemma xtransition_none g w :
  xtransition g None w = None.
Proof.
  destruct w; auto.
Qed.

Lemma xtransition_not_in_alphabet g q a :
  ~ In a (alphabet g) -> xtransition g q [a] = None.
Proof.
  intro H; destruct q as [q|].
  - replace (xtransition g (Some q) [a]) with (transitionf g q a).
    2: simpl; destruct (transitionf g q a); auto.
    destruct (transitionf g q a) as [q'|] eqn:H0.
    + apply transition_alphabet in H0; contradiction.
    + auto.
  - auto.
Qed.

Lemma xtransition_app g q w1 w2 :
  xtransition g q (w1 ++ w2) = xtransition g (xtransition g q w1) w2.
Proof.
  revert q;
  induction w1 as [|a w1 IH]; intro q.
  - simpl; destruct q; auto.
  - simpl; destruct q.
    + rewrite IH; auto.
    + rewrite xtransition_none; auto.
Qed.

Lemma xtransition_nil g q :
  xtransition g q [] = q.
Proof.
  destruct q as [q|]; auto.
Qed.

Lemma ex_xtransition_undef g q :
  exists a, xtransition g q [a] = None.
Proof.
  destruct q as [q|].
  - assert (H: exists a, ~ In a (alphabet g)). {
      exists (max_in_list (alphabet g) + 1); intro H;
      apply max_in_list_correct in H; nia.
    }
    destruct H as [a H]; exists a.
    replace (xtransition g (Some q) [a]) with (transitionf g q a).
    2: simpl; destruct (transitionf g q a); auto.
    destruct (transitionf g q a) eqn:H0.
    + apply transition_alphabet in H0; contradiction.
    + auto.
  - exists O; auto.
Qed.

Lemma states_opt'_correct q l :
  In (Some q) (states_opt' l) <-> In q l.
Proof.
  induction l as [|q' l IH]; split.
  1,2: contradiction.
  - intros [H|H].
    + left; injection H; auto.
    + right; apply IH; auto.
  - intros [H|H].
    + left; subst; auto.
    + right; apply IH; auto.
Qed.

Lemma start_in_states g :
  In (start g) (states_opt g).
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH].
  2,4: right; apply states_opt'_correct, add_correct; intuition.
  left; auto.
  auto.
Qed.

Lemma states_opt_correct g q1 :
  In q1 (states g) <-> In (Some q1) (states_opt g).
Proof.
  unfold states_opt.
  induction (states g) as [|q l IH]; split.
  - intros [].
  - intros [H|[]]; discriminate.
  - intros [H|H].
    + subst; right; left; auto.
    + apply IH in H; destruct H as [H|H].
      discriminate.
      right; right; auto.
  - intros [H|[H|H]].
    + discriminate.
    + injection H; intros; subst; intuition.
    + right; apply IH; intuition.
Qed.

Lemma transition_state_opt g q a :
  In (transitionf g q a) (states_opt g).
Proof.
  induction g as [|x g IH].
  - left; auto.
  - assert (H: In (transitionf g q a) (states_opt (x :: g)) ->
    In (transitionf (x :: g) q a) (states_opt (x :: g))). {
      intro H; simpl in *; destruct x as [ | | q1 b q2]; auto.
      destruct ((q =? q1) && (a =? b))%bool; auto.
      right; apply states_opt'_correct; apply add_correct;
      right; apply add_correct; intuition.
    }
    assert (H0: forall q x, In q (states_opt g) -> In q (states_opt (x::g))). {
      clear H IH x q a; intros [q|] x H.
      - apply states_opt_correct; destruct H as [H|H].
        discriminate.
        apply states_opt'_correct in H.
        simpl; destruct x as [q'| |q' a q''].
        apply add_correct; intuition.
        auto.
        apply add_correct; right; apply add_correct; intuition.
      - left; auto.
    }
    apply H, H0; auto.
Qed.

Lemma xtransition_in_states_opt g q w :
  In q (states_opt g) -> In (xtransition g q w) (states_opt g).
Proof.
  revert q; induction w as [|a w IH]; intros q H.
  - simpl; destruct q; auto.
  - destruct q as [q|].
    2: left; auto.
    apply IH, transition_state_opt.
Qed.

Lemma in_states_opt_dec g q :
  {In q (states_opt g)} + {~ In q (states_opt g)}.
Proof.
  apply in_dec; intros [x|] [y|]; try (destruct (Nat.eq_dec x y)); auto.
  2,3: right; intros; discriminate.
  right; intro contra; injection contra; intros; contradiction.
Qed.

Lemma app_accept g1 g2 q :
  accept (g1 ++ g2) q = true -> accept g1 q = true \/ accept g2 q = true.
Proof.
  revert q; induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; auto.
  intro q; simpl; destruct (q =? q1); auto.
Qed.

Lemma accept_app g1 g2 q :
  accept g1 q = true -> accept (g1 ++ g2) q = true.
Proof.
  induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; simpl;
  try discriminate; try (destruct (q =? q1)); auto.
Qed.

Lemma accept_state g q :
  accept g q = true -> In q (states g).
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH]; simpl; intro H; auto.
  - discriminate.
  - destruct (q =? q1) eqn:H0.
    + apply EqNat.beq_nat_true in H0; subst; apply add_correct; intuition.
    + apply add_correct; right; auto.
  - apply add_correct; right; apply add_correct; right; auto.
Qed.

Lemma accept_app_r g1 g2 q :
  ~ In q (states g1) -> accept g2 q = true -> accept (g1 ++ g2) q = true.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intros H H0; auto.
  - destruct (q =? q3) eqn:H1.
    + apply EqNat.beq_nat_true in H1; subst; assert (In q3 (add q3 (states g1)));
      try (apply add_correct); intuition.
    + apply IH; auto; intro contra; assert (In q (add q3 (states g1)));
      try (apply add_correct; right); intuition.
  - apply IH; auto; intro contra; assert (In q (add q3 (add q4 (states g1))));
    try (apply add_correct; right; apply add_correct); intuition.
Qed.

Lemma transitionf_app g1 g2 q1 q2 a :
  transitionf g1 q1 a = Some q2 -> transitionf (g1 ++ g2) q1 a = Some q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intro H; auto;
  try discriminate; try (destruct (andb (q1 =? q3) (a =? b))); auto.
Qed.

Lemma app_transitionf g1 g2 q1 q2 a :
  transitionf (g1 ++ g2) q1 a = Some q2 -> transitionf g1 q1 a = Some q2 \/ transitionf g2 q1 a = Some q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intro H;
  try (destruct (andb (q1 =? q3) (a =? b))); auto.
Qed.

Lemma transitionf_app_r g1 g2 q1 q2 a :
  ~ In q1 (states g1) -> transitionf g2 q1 a = Some q2 -> transitionf (g1 ++ g2) q1 a = Some q2.
Proof.
  intros H1 H0; assert (H: transitionf g1 q1 a = None).
    destruct (transitionf g1 q1 a) eqn:H; auto;
    apply transition_states in H; contradiction.
  clear H1; induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl in *; auto.
  destruct (andb (q1 =? q3) (a =? b)); try discriminate; auto.
Qed.

Module DFAExamples.

Definition dfa1 := [state 0 true; transition 0 0 1; transition 1 1 0].
Compute states dfa1.
Compute alphabet dfa1.
Compute accept dfa1 0.
Compute accept dfa1 1.
Compute ixtransition dfa1 [0;1;0;1].
Compute acceptsb dfa1 [0;1;0;1].

End DFAExamples.