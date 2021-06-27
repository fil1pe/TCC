Require Import List Bool sets nfa.
Include ListNotations.


(* Define as restrições dos autômatos finitos determinísticos *)
Inductive is_dfa' : forall {A B}, nfa_comp_list A B -> Prop :=
  | cons_empty_dfa {A B} : is_nfa (@nil (@nfa_comp A B)) -> is_dfa' (@nil (@nfa_comp A B))
  | cons_dfa_state {A B} (g:nfa_comp_list A B) q : is_dfa' g -> is_dfa' (state q::g)
  | cons_dfa_symbol {A B} (g:nfa_comp_list A B) a : is_dfa' g -> is_dfa' (symbol a::g)
  | cons_dfa_accept {A B} (g:nfa_comp_list A B) q : is_dfa' g -> is_dfa' (accept q::g)
  | cons_dfa_start_repeat {A B} (g:nfa_comp_list A B) q : is_dfa' g -> In q (start_states g) -> is_dfa' (start q::g)
  | cons_dfa_start {A B} (g:nfa_comp_list A B) q : is_dfa' g -> start_states g = [] -> is_dfa' (start q::g)
  | cons_dfa_trans_repeat {A B} (g:nfa_comp_list A B) q a q' : is_dfa' g -> In (trans q a q') g -> is_dfa' (trans q a q'::g)
  | cons_dfa_trans {A B} (g:nfa_comp_list A B) q a q' : is_dfa' g -> (forall q', ~ In (trans q a q') g) -> is_dfa' (trans q a q'::g).

Definition is_dfa {A B} (G:nfa A B) :=
  match G with
  | nfa_cons _ _ g eq eq' H H0 => is_dfa' g
  end.


(* Função de transição extendida para autômatos determinísticos *)
Definition dfa_transition {A B} eq eq' (g:nfa_comp_list A B) q w :=
  match q with
  | None => None
  | Some q => match (ext_transition eq eq' g [q] w) with
              | nil => None
              | q::_ => Some q
              end
  end.


(* Def. estados indistinguíveis de um autômato determinístico *)
Definition dfa_indisting_states {A B} eq eq' (g:nfa_comp_list A B) q1 q2 :=
  forall w, in_opt (dfa_transition eq eq' g (Some q1) w) (Some (accept_states g)) <-> in_opt (dfa_transition eq eq' g (Some q2) w) (Some (accept_states g)).


(* Todo autômato determinístico é não-determinístico *)
Lemma dfa_is_nfa {A B} (g:nfa_comp_list A B) (H:is_dfa' g) :
  is_nfa g.
Proof.
  induction H.
  1: auto.
  1-7: inversion IHis_dfa'; apply is_nfa_cons with eq eq'; auto.
Qed.

(* Só existe um estado inicial em um autômato determinístico *)
Lemma dfa_start {A B} (g:nfa_comp_list A B) q0 q :
  is_dfa' g -> In q0 (start_states g) -> In q (start_states g) -> q = q0.
Proof.
  intros.
  induction H; auto.
  - inversion H0.
  - simpl in H0, H1; destruct H0, H1; subst; auto.
  - simpl in H0, H1; rewrite H2 in H0, H1; destruct H0, H1; subst.
    + auto.
    + inversion H1.
    + inversion H0.
    + inversion H1.
Qed.

(* A transição sempre resulta no mesmo estado, quando definida *)
Lemma dfa_trans {A B} eq eq' (g:nfa_comp_list A B) q0 q q' a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' g ->
  In q (transition eq eq' g q0 a) ->
  In q' (transition eq eq' g q0 a) ->
  q' = q.
Proof.
  intros.
  apply (transition_in eq eq' g q0 a q H H0) in H2;
  apply (transition_in eq eq' g q0 a q' H H0) in H3.
  induction H1.
  1: destruct H2.
  1-5: destruct H2, H3; try discriminate; apply (IHis_dfa' eq eq' q0 q q' a); auto.
  - destruct H2, H3.
    + injection H2; injection H3; intros; subst; auto.
    + injection H2; intros; subst; auto.
      apply (IHis_dfa' eq eq' q0 q q' a); auto.
    + injection H3; intros; subst; auto.
      apply (IHis_dfa' eq eq' q0 q q' a); auto.
    + apply (IHis_dfa' eq eq' q0 q q' a); auto.
  - destruct H2, H3.
    + injection H2; injection H3; intros; subst; auto.
    + injection H2; intros; subst; auto.
      apply H4 in H3; destruct H3.
    + injection H3; intros; subst; auto.
      apply H4 in H2; destruct H2.
    + apply (IHis_dfa' eq eq' q0 q q' a); auto.
Qed.

Lemma dfa_trans_ext {A B} eq eq' (g:nfa_comp_list A B) q0 q q' w l :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' g ->
  ext_transition eq eq' g [q0] w = l ->
  In q l ->
  In q' l ->
  q' = q.
Proof.
  intros.
  rewrite <- H2 in H3, H4.
  clear H2.
  generalize dependent q;
  generalize dependent q';
  generalize dependent q0;
  induction w; intros.
  1: destruct H3, H4; subst; try (destruct H3); try (destruct H2); auto.
  simpl in H3, H4; rewrite app_nil_r in H3, H4.
  assert (forall q q', In q (transition eq eq' g q0 a) ->
  In q' (transition eq eq' g q0 a) -> q' = q).
    intros; apply dfa_trans with eq eq' g q0 a; auto.
  induction (transition eq eq' g q0 a).
  1: rewrite ext_transition_nil in H3; destruct H3.
  replace (a0::l0) with ([a0] ++ l0) in H3, H4.
  2: auto.
  rewrite ext_transition_states_app in H3, H4.
  apply in_app_or in H3; apply in_app_or in H4.
  destruct H3, H4.
  - apply (IHw a0); auto.
  - clear IHl0; induction l0.
    1: rewrite ext_transition_nil in H4; destruct H4.
    replace (a1 :: l0) with ([a1] ++ l0) in H4.
    2: auto.
    rewrite ext_transition_states_app in H4; apply in_app_or in H4;
    destruct H4.
    + assert (a1 = a0).
        apply H2. 1: left; auto. right; left; auto.
      subst; apply IHw with a0; auto.
    + apply IHl0.
      1: auto.
      intros; apply H2.
      * destruct H5; subst.
        1: left; auto.
        right; right; auto.
      * destruct H6; subst.
        1: left; auto.
        right; right; auto.
  - clear IHl0; induction l0.
    1: rewrite ext_transition_nil in H3; destruct H3.
    replace (a1 :: l0) with ([a1] ++ l0) in H3.
    2: auto.
    rewrite ext_transition_states_app in H3; apply in_app_or in H3;
    destruct H3.
    + assert (a1 = a0).
        apply H2. 1: left; auto. right; left; auto.
      subst; apply IHw with a0; auto.
    + apply IHl0.
      1: auto.
      intros; apply H2.
      * destruct H5; subst.
        1: left; auto.
        right; right; auto.
      * destruct H6; subst.
        1: left; auto.
        right; right; auto.
  - apply IHl0.
    1,2: auto.
    intros; apply H2; right; auto.
Qed.

(* Prova de que a junção de dois autômatos sem estado inicial não tem estado inicial *)
Lemma start_states_app_nil {A B} (g1 g2:nfa_comp_list A B) :
  start_states g1 = nil -> start_states g2 = nil ->
  start_states (g1 ++ g2) = nil.
Proof.
  intros; induction g1.
  1: simpl; rewrite H0; auto.
  destruct a.
  1,2,4,5: auto.
  simpl in H; discriminate.
Qed.

(* Prova de que a junção de um DFA com uma lista de estados de aceitação é um DFA *)
Lemma app_accept_is_dfa' {A B} (g:nfa_comp_list A B) l :
  is_dfa' g ->
  (forall c, In c l -> exists q, c = accept q) ->
  is_dfa' (g ++ l).
Proof.
  intros; induction H.
  - simpl; induction l.
    1: apply cons_empty_dfa; auto.
    destruct a.
    + assert (In (state q) (state q::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + assert (In (symbol a) (symbol a::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + assert (In (start q) (start q::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + apply cons_dfa_accept, IHl.
      intros; apply H0; intuition.
    + assert (In (trans q a q') (trans q a q'::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
  - apply cons_dfa_state; intuition.
  - apply cons_dfa_symbol; intuition.
  - apply cons_dfa_accept; intuition.
  - simpl; apply cons_dfa_start_repeat.
    1: intuition.
    apply in_app_start_states_or; intuition.
  - simpl; apply cons_dfa_start.
    1: intuition.
    apply start_states_app_nil.
    1: auto.
    clear IHis_dfa' H1 H g q; induction l.
    1: auto.
    destruct a.
    1,2,4,5: intuition.
    assert (In (start q) (start q::l)).
      intuition.
    apply H0 in H; destruct H; discriminate.
  - simpl; apply cons_dfa_trans_repeat.
    1: intuition.
    apply in_or_app; intuition.
  - simpl; apply cons_dfa_trans.
    1: intuition.
    intros q'' contra.
    apply in_app_or in contra; destruct contra.
    1: apply H1 in H2; auto.
    apply H0 in H2; destruct H2; discriminate.
Qed.













