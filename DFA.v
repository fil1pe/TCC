Require Import Nat PeanoNat List NatListSet Lia.
Import ListNotations.

(*
  DFA: Deterministic Finite Automaton
  A DFA is a machine that processes any given sequence of symbols (word) deterministically.
  Its result is either recognized or not and done by transitioning states based on a transition
  function. The word is said to be recognized if the deterministic extended transition along the
  sequence ends in an accept state.
*)

(* It is defined through a list of symbols, states and transition rules. *)

Inductive dfa_component :=
  | state (q : nat) (accept : bool)
  | symbol (a: nat)
  | transition (q a q':nat).

Definition dfa := list dfa_component.

(* The states of a given DFA g. *)
Fixpoint states g :=
  match g with
  | state q accept::g => add q (states g)
  | symbol a::g => states g
  | transition q a q'::g => add q (add q' (states g))
  | nil => nil
  end.

(* Its alphabet: the list of symbols which compound the recognized words. *)
Fixpoint alphabet g :=
  match g with
  | state q accept::g => alphabet g
  | symbol a::g => add a (alphabet g)
  | transition q a q'::g => add a (alphabet g)
  | nil => nil
  end.

(* Its transition function. *)
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

(* Its start state: the first state in g. *)
Fixpoint start g :=
  match g with
  | state q accept::g => Some q
  | symbol a::g => start g
  | transition q a q'::g => Some q
  | nil => None
  end.

(* Checks if a given q is an accept state. *)
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


(* The extended transition function *)
Fixpoint xtransition g (q:option nat) (w:list nat) :=
  match q with
  | Some q =>
    match w with
    | a::w => xtransition g (transitionf g q a) w
    | nil => Some q
    end
  | None => None
  end.

(* The xtransition function from the start state *)
Definition ixtransition g w := xtransition g (start g) w.

(* Maps the states of the DFA [q1, q2, ..., qn] to [None, Some q1, Some q2, ..., Some qn]. *)
Fixpoint states_opt' (l:list nat) :=
  match l with
  | q::l => Some q::states_opt' l
  | nil => nil
  end.
Definition states_opt g := None::states_opt' (states g).

(* Checks if a given q is Some q' such that q' is an accept state. *)
Definition accept_opt g q :=
  match q with
  | Some q => accept g q
  | None => false
  end.

(* A word w is accepted/recognized by the DFA if the ixtransition over w returns an accept state. *)
Definition acceptsb g w := accept_opt g (ixtransition g w).

(* If the transition function is defined for q1 and a, then q1 is a state and a is in the alphabet. *)
Lemma transitionf_defined g q1 a q2 :
  transitionf g q1 a = Some q2 -> In q1 (states g) /\ In a (alphabet g).
Proof.
  intro H; induction g as [|[q3 acc|b|q3 b q4] g IH].
  discriminate. 1-3: split.
  1,4: apply IH in H; apply in_add__in_cons; right.
  1-4: intuition.
  1,2: simpl in H; destruct (q1 =? q3) eqn:H0, (a =? b) eqn:H1; apply in_add__in_cons;
       try apply EqNat.beq_nat_true in H0; try apply EqNat.beq_nat_true in H1; subst.
  1,2,5,6,7,8: intuition.
  1,2: right; apply in_add__in_cons; intuition.
Qed.

(* xtransition from the undefined state (None) is always undefined. *)
Lemma xtransition_none g w :
  xtransition g None w = None.
Proof.
  destruct w; auto.
Qed.

(* xtransition over any symbol that is not in the alphabet is undefined. *)
Lemma xtransition_not_in_alphabet g q a :
  ~ In a (alphabet g) -> xtransition g q [a] = None.
Proof.
  intro H; destruct q as [q|].
  - replace (xtransition g (Some q) [a]) with (transitionf g q a).
    2: simpl; destruct (transitionf g q a); auto.
    destruct (transitionf g q a) as [q'|] eqn:H0.
    + apply transitionf_defined in H0; destruct H0 as [_ H0]; contradiction.
    + auto.
  - auto.
Qed.

(*
  xtransition from q over (w1 ++ w2) is equal to xtransition over w2 from
  xtransition from q over w1.
*)
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

(* xtransition from any q over the empty word results in q. *)
Lemma xtransition_nil g q :
  xtransition g q [] = q.
Proof.
  destruct q as [q|]; auto.
Qed.

(* There always exists a input such that xtransition over it is undefined. *)
Lemma ex_xtransition_undef g q :
  exists a, xtransition g q [a] = None.
Proof.
  destruct q as [q|].
  - assert (H: exists a, ~ In a (alphabet g)). {
      exists (max_in_list (alphabet g) + 1); intro H;
      apply leq_max_in_list in H; nia.
    }
    destruct H as [a H]; exists a.
    replace (xtransition g (Some q) [a]) with (transitionf g q a).
    2: simpl; destruct (transitionf g q a); auto.
    destruct (transitionf g q a) eqn:H0.
    + apply transitionf_defined in H0; destruct H0 as [_ H0]; contradiction.
    + auto.
  - exists O; auto.
Qed.

(* Proof states_opt is correct *)

Lemma some_state_in_states_opt g q1 :
  In (Some q1) (states_opt g) <-> In q1 (states g).
Proof.
  assert (P: forall q l, In (Some q) (states_opt' l) <-> In q l). {
    intros q l; induction l as [|q' l IH]; split.
    1,2: contradiction.
    - intros [H|H].
      + left; injection H; auto.
      + right; apply IH; auto.
    - intros [H|H].
      + left; subst; auto.
      + right; apply IH; auto.
  }
  split.
  - intro H; apply P; destruct H as [H|H]; try discriminate; auto.
  - intro H; apply P in H; right; auto.
Qed.

Lemma none_in_states_opt g :
  In None (states_opt g).
Proof.
  left; auto.
Qed.

(* The start state is either in the list of states or None. *)
Lemma start_in_states_opt g :
  In (start g) (states_opt g).
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH].
  - left; auto.
  - replace (start (state q1 acc :: g)) with (Some q1);
    try apply some_state_in_states_opt, in_add__in_cons;
    intuition.
  - auto.
  - replace (start (transition q1 a q2 :: g)) with (Some q1);
    try apply some_state_in_states_opt, in_add__in_cons;
    intuition.
Qed.

(* No matter the inputs, transitionf is always either in the list of states or None. *)
Lemma transitionf_in_states_opt g q a :
  In (transitionf g q a) (states_opt g).
Proof.
  induction g as [|x g IH].
  - left; auto.
  - assert (H: In (transitionf g q a) (states_opt (x :: g)) ->
    In (transitionf (x :: g) q a) (states_opt (x :: g))). {
      intro H; simpl transitionf; destruct x as [ | | q1 b q2]. 1,2: auto.
      destruct (andb (q =? q1) (a =? b)). 2: auto.
      apply some_state_in_states_opt; simpl; apply in_add__in_cons;
      right; apply in_add__in_cons; intuition.
    }
    assert (H0: forall q x, In q (states_opt g) -> In q (states_opt (x::g))). {
      clear H IH x q a; intros [q|] x H.
      - apply some_state_in_states_opt; apply some_state_in_states_opt in H;
        simpl; destruct x as [q1| |q1 a q2];
        try apply in_add__in_cons;
        try right; try apply in_add__in_cons;
        intuition.
      - left; auto.
    }
    apply H, H0; auto.
Qed.

(* xtransition from a state or None is in the list of states or None. *)
Lemma xtransition_in_states_opt g q w :
  In q (states_opt g) -> In (xtransition g q w) (states_opt g).
Proof.
  revert q; induction w as [|a w IH]; intros q H.
  - simpl; destruct q; auto.
  - destruct q as [q|].
    2: left; auto.
    apply IH, transitionf_in_states_opt.
Qed.

(* Decidability of states and None *)
Lemma in_states_opt_dec g q :
  {In q (states_opt g)} + {~ In q (states_opt g)}.
Proof.
  apply in_dec; intros [x|] [y|]; try (destruct (Nat.eq_dec x y)); auto.
  2,3: right; intros; discriminate.
  right; intro contra; injection contra; intros; contradiction.
Qed.

(*
  If a given q is an accept state of the concatenation of two DFAs g1 and g2
  it is an accept state of g1 or g2.
*)
Lemma app_accept g1 g2 q :
  accept (g1 ++ g2) q = true -> accept g1 q = true \/ accept g2 q = true.
Proof.
  revert q; induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; auto.
  intro q; simpl; destruct (q =? q1); auto.
Qed.

(* If q is an accept state of g1, then it is an accept state of g1 concatenated with any DFA g2. *)
Lemma accept_app g1 g2 q :
  accept g1 q = true -> accept (g1 ++ g2) q = true.
Proof.
  induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; simpl;
  try discriminate; try (destruct (q =? q1)); auto.
Qed.

(* If q is not a state of g1 and is an accept state of g2, then it is an accept state of g1 ++ g2. *)
Lemma accept_app_r g1 g2 q :
  ~ In q (states g1) -> accept g2 q = true -> accept (g1 ++ g2) q = true.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intros H H0; auto.
  - destruct (q =? q3) eqn:H1.
    + apply EqNat.beq_nat_true in H1; subst; assert (In q3 (add q3 (states g1)));
      try (apply in_add__in_cons); intuition.
    + apply IH; auto; intro contra; assert (In q (add q3 (states g1)));
      try (apply in_add__in_cons; right); intuition.
  - apply IH; auto; intro contra; assert (In q (add q3 (add q4 (states g1))));
    try (apply in_add__in_cons; right; apply in_add__in_cons); intuition.
Qed.

(* If q is not an accept state in g1 nor g2, it will not be an accept state in their concatenation. *)
Lemma accept_app_false g1 g2 q :
  accept g1 q = false -> accept g2 q = false -> accept (g1 ++ g2) q = false.
Proof.
  intros H H0; induction g1 as [|[q1 acc|b|q1 b q2] g1 IH]; simpl in *;
  try destruct (q =? q1); auto.
Qed.

(* If q is an accept state, it is in the list of states. *)
Lemma accept_in_states g q :
  accept g q = true -> In q (states g).
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH]; simpl; intro H; auto.
  - discriminate.
  - destruct (q =? q1) eqn:H0.
    + apply EqNat.beq_nat_true in H0; subst; apply in_add__in_cons; intuition.
    + apply in_add__in_cons; right; auto.
  - apply in_add__in_cons; right; apply in_add__in_cons; right; auto.
Qed.

(*
  If q2 is the result of a given transition in the concatenation of two DFAs g1 and g2
  it is the result of the same transition in g1 or g2.
*)
Lemma app_transitionf g1 g2 q1 q2 a :
  transitionf (g1 ++ g2) q1 a = q2 -> transitionf g1 q1 a = q2 \/ transitionf g2 q1 a = q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intro H;
  try (destruct (andb (q1 =? q3) (a =? b))); auto.
Qed.

(*
  If a state q2 is the result of a given transition in g1, it is the result of the same transition
  in g1 ++ g2.
*)
Lemma transitionf_app g1 g2 q1 q2 a :
  transitionf g1 q1 a = Some q2 -> transitionf (g1 ++ g2) q1 a = Some q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intro H; auto;
  try discriminate; try (destruct (andb (q1 =? q3) (a =? b))); auto.
Qed.

(* If a given transition is not defined in g1, its result in g1 ++ g2 is equal to its result in g2. *)
Lemma transitionf_app_r g1 g2 q1 q2 a :
  transitionf g1 q1 a = None -> transitionf g2 q1 a = q2 -> transitionf (g1 ++ g2) q1 a = q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intros;
  try (destruct (andb (q1 =? q3) (a =? b))); try discriminate; auto.
Qed.

(* If a given transition is undefined in g2, its result in g1 ++ g2 is equal to the result in g1. *)
Lemma transitionf_app_none g1 g2 q1 q2 a :
  transitionf g1 q1 a = q2 -> transitionf g2 q1 a = None -> transitionf (g1 ++ g2) q1 a = q2.
Proof.
  intros H H0; destruct q2 as [q2|].
  - apply transitionf_app; auto.
  - apply transitionf_app_r; auto.
Qed.

(* If q is a state of g1 or None, then q is a state of g1 concatenated with another DFA or None. *)
Lemma states_opt_app g1 g2 q :
  In q (states_opt g1) -> In q (states_opt (g1++g2)).
Proof.
  intro H; induction g1 as [|[q1 acc|a|q1 a q2] g1 IH].
  - simpl; destruct H as [H|[]]; auto.
  - destruct q as [q|].
    2: left; auto.
    apply some_state_in_states_opt in H; simpl in H; apply in_add__in_cons in H; destruct H as [H|H].
    subst; apply some_state_in_states_opt, in_add__in_cons; left; auto.
    apply some_state_in_states_opt; simpl; apply in_add__in_cons; right; apply some_state_in_states_opt;
    apply IH, some_state_in_states_opt; auto.
  - auto.
  - destruct q as [q|].
    2: left; auto.
    apply some_state_in_states_opt in H; simpl in H; apply in_add__in_cons in H; destruct H as [H|H].
    subst; apply some_state_in_states_opt, in_add__in_cons; left; auto.
    apply in_add__in_cons in H; destruct H as [H|H].
    subst; apply some_state_in_states_opt; simpl; apply in_add__in_cons;
    right; apply in_add__in_cons; left; auto.
    apply some_state_in_states_opt in H; apply some_state_in_states_opt; simpl; apply in_add__in_cons;
    right; apply in_add__in_cons; right; apply some_state_in_states_opt; auto.
Qed.

(* If q is a state of g2 or None, then q is a state of another DFA concatenated with g2 or None. *)
Lemma states_opt_app_r g1 g2 q :
  In q (states_opt g2) -> In q (states_opt (g1++g2)).
Proof.
  destruct q as [q|].
  2: left; auto.
  intro H; apply some_state_in_states_opt in H; apply some_state_in_states_opt;
  induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; simpl in *.
  - auto.
  - apply in_add__in_cons; intuition.
  - auto.
  - apply in_add__in_cons; right; apply in_add__in_cons; intuition.
Qed.
