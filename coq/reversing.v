Require Import List Bool nfa.
Include ListNotations.


(* Reverte a palavra *)
Fixpoint revert {A} (w:list A) :=
  match w with
  | nil => nil
  | a::w => revert w ++ [a]
  end.

(* Prova da propriedade distributiva da reversão de palavra *)
Lemma revert_distr {A} (w1 w2:list A) :
  revert (w1 ++ w2) = revert w2 ++ revert w1.
Proof.
  induction w1; simpl.
  - rewrite app_nil_r; auto.
  - rewrite IHw1, app_assoc; auto.
Qed.

(* Prova de que reverter a palavra duas vezes resulta na palavra original *)
Lemma revert_twice {A} (w:list A) :
  w = revert (revert w).
Proof.
  induction w.
  - auto.
  - simpl; rewrite revert_distr, <- IHw; auto.
Qed.

(* Reverte o autômato *)
Fixpoint revert_nfa {A B} (g:nfa_comp_list A B) :=
  match g with
  | nil => nil
  | start q::g => accept q::revert_nfa g
  | accept q::g => start q::revert_nfa g
  | trans q a q'::g => trans q' a q::revert_nfa g
  | x::g => x::revert_nfa g
  end.

(* Prova de que o autômato resultante é realmente um autômato *)
Lemma reverted_is_nfa {A B} (g:nfa_comp_list A B) :
  is_nfa g -> is_nfa (revert_nfa g).
Proof.
  intros. inversion H.
  apply (is_nfa_cons (revert_nfa g) eq); auto.
Qed.

(* Prova de que reverter o autômato duas vezes resulta no autômato inicial *)
Lemma revert_nfa_twice {A B} (g:nfa_comp_list A B) :
  g = revert_nfa (revert_nfa g).
Proof.
  induction g.
  - auto.
  - simpl; destruct a; simpl; rewrite <- IHg; auto.
Qed.

(* Prova de que um estado inicial torna-se final *)
Lemma revert_start {A B} (g:nfa_comp_list A B) q :
  In q (start_states g) -> In q (accept_states (revert_nfa g)).
Proof.
  intros.
  induction g.
  - destruct H.
  - simpl in H; destruct a.
    1-2,4-5: try right; try right; intuition.
    destruct H.
    + left; intuition.
    + right; intuition.
Qed.

(* Prova de que um estado final torna-se inicial *)
Lemma revert_accept {A B} (g:nfa_comp_list A B) q :
  In q (accept_states g) -> In q (start_states (revert_nfa g)).
Proof.
  intros.
  induction g.
  - destruct H.
  - simpl in H; destruct a.
    1-3,5: try right; try right; intuition.
    destruct H.
    + left; intuition.
    + right; intuition.
Qed.

(* Prova da reversão de transições *)
Lemma revert_trans {A B} (g:nfa_comp_list A B) q a q' :
  In (trans q a q') g -> In (trans q' a q) (revert_nfa g).
Proof.
  intros.
  induction g.
  - destruct H.
  - simpl in H; destruct a0.
    1-4: destruct H; try discriminate; right; intuition.
    destruct H.
    + injection H; intros; subst; left; auto.
    + right; intuition.
Qed.

(* Prova do caminho reverso *)
Lemma reverted_path {A B} (g:nfa_comp_list A B) q1 q2 w :
  path g q1 q2 w <-> path (revert_nfa g) q2 q1 (revert w).
Proof.
  assert (forall (g:nfa_comp_list A B) q1 q2 w, path g q1 q2 w -> path (revert_nfa g) q2 q1 (revert w)). {
    clear g q1 q2 w; intros.
    induction H.
    - constructor.
    - rewrite revert_distr. apply path_left with q2.
      2: auto.
      apply revert_trans; auto.
  }
  split; intros.
  - apply H; auto.
  - rewrite revert_twice; replace g with (revert_nfa (revert_nfa g)).
    2: symmetry; apply revert_nfa_twice.
    apply H; auto.
Qed.

(* Prova de que a linguagem do autômato resultante é reversa *)
Lemma reverted_nfa_lang {A B} eq eq' (g:nfa_comp_list A B) w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  accepts eq eq' g w <-> accepts eq eq' (revert_nfa g) (revert w).
Proof.
  intros H H0; assert (forall g w, accepts eq eq' g w -> accepts eq eq' (revert_nfa g) (revert w)). {
    unfold accepts, has_accept_state; clear g w; intros.
    destruct H1 as [q [H1 H2]].
    apply ext_transition_list in H1; destruct H1 as [q0 [H1 H3]].
    exists q0; split.
    2: apply revert_start; auto.
    apply (path_ext_transition eq eq' g q0 q w H H0) in H3.
    apply (ext_transition_single eq eq' (revert_nfa g) (start_states (revert_nfa g)) q q0 (revert w)); split.
    1: apply revert_accept; auto.
    apply path_ext_transition.
    1-2: auto.
    apply reverted_path in H3; auto.
  }
  split; intros.
  - intuition.
  - rewrite (revert_nfa_twice g), revert_twice.
    intuition.
Qed.

(* Prova de que, se não houver estados iniciais, não haverá estados finais no autômato revertido *)
Lemma revert_nfa_start_nil {A B} {g:nfa_comp_list A B} :
  start_states g = [] -> accept_states (revert_nfa g) = [].
Proof.
  intros.
  induction g.
  1: auto.
  destruct a.
  1,2,4,5: auto.
  inversion H.
Qed.








