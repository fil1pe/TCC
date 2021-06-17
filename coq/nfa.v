Require Import List Bool sets.
Include ListNotations.


(* Define as componentes de um autômato *)
Inductive nfa_comp {A B} :=
  | state (q:A)
  | symbol (a:B)
  | start (q:A)
  | accept (q:A)
  | trans (q:A) (a:B) (q':A).

(* Define lista de componentes de autômato, ou pseudoautômato *)
Definition nfa_comp_list A B := list (@nfa_comp A B).

(* Define as restrições dos autômatos *)
Inductive is_nfa : forall {A B}, nfa_comp_list A B -> Prop :=
  | is_nfa_cons {A B} (g: nfa_comp_list A B) (eq:A->A->bool) (eq':B->B->bool) :
      (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq a b=true) -> is_nfa g.
Inductive nfa A B :=
  | nfa_cons (g:nfa_comp_list A B) (eq:A->A->bool) (eq':B->B->bool) (H:forall q1 q2, q1=q2 <-> eq q1 q2=true)
      (H0:forall a b, a=b <-> eq a b=true).

(* Obtém a lista de estados de um pseudoautômato *)
Fixpoint states {A B} (g:nfa_comp_list A B) :=
  match g with
  | nil => nil
  | state q::g => q::states g
  | start q::g => q::states g
  | accept q::g => q::states g
  | trans q a q'::g => q::q'::states g
  | _::g => states g
  end.

(* Obtém o alfabeto de um pseudoautômato *)
Fixpoint alphabet {A B} (g:nfa_comp_list A B) :=
  match g with
  | nil => nil
  | symbol a::g => a::alphabet g
  | trans q a q'::g => a::alphabet g
  | _::g => alphabet g
  end.

(* Obtém os estados iniciais de um pseudoautômato *)
Fixpoint start_states {A B} (g:nfa_comp_list A B) :=
  match g with
  | nil => nil
  | start q::g => q::start_states g
  | _::g => start_states g
  end.

(* Obtém os estados finais de um pseudoautômato *)
Fixpoint accept_states {A B} (g:nfa_comp_list A B) :=
  match g with
  | nil => nil
  | accept q::g => q::accept_states g
  | _::g => accept_states g
  end.

(* A função de transição de um pseudoautômato para os decisores de igualdade *)
Fixpoint transition {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) q a :=
  match g with
  | nil => nil
  | trans q1 b q2::g =>
    if (eq q q1 && eq' a b) then
      q2::transition eq eq' g q a
    else
      transition eq eq' g q a
  | _::g => transition eq eq' g q a
  end.

(* Prova de consistência da função de transição *)
Lemma transition_in {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) q a q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  In (trans q a q') g <-> In q' (transition eq eq' g q a).
Proof.
  intros.
  assert (forall q, eq q q = true).
    intros; apply H; intuition.
  assert (forall a, eq' a a = true).
    intros; apply H0; intuition.
  intros; induction g.
  - split; intros; destruct H3.
  - split; intros.
    + destruct H3.
      * subst; simpl; rewrite H1, H2; left; auto.
      * apply IHg in H3; destruct a0; simpl.
        1-4: auto.
        destruct (eq q q0 && eq' a a0);
        try right; auto.
    + destruct a0.
      1-4: right; intuition.
      simpl in H3.
      destruct (eq q q0 && eq' a a0) eqn:H4.
      destruct H3.
      2,3: right; intuition.
      subst; left.
      apply andb_true_iff in H4; destruct H4.
      apply H in H3; apply H0 in H4; subst.
      auto.
Qed.

(* A sua versão extendida *)
Fixpoint ext_transition {A B} eq eq' (g:nfa_comp_list A B) Q w :=
  match w with
  | nil => Q
  | a::w => ext_transition eq eq' g (
              (fix f Q :=
                match Q with
                | nil => nil
                | q::Q => transition eq eq' g q a ++ f Q
                end) Q
            ) w
  end.

(* Um lema útil *)
Lemma ext_transition_app {A B} eq eq' (g:nfa_comp_list A B) Q w1 w2 :
  ext_transition eq eq' g Q (w1 ++ w2) = ext_transition eq eq' g (ext_transition eq eq' g Q w1) w2.
Proof.
  generalize dependent Q.
  induction w1.
  - auto.
  - intros; apply IHw1.
Qed.

Lemma ext_transition_nil {A B} eq eq' (g:nfa_comp_list A B) w :
  ext_transition eq eq' g nil w = nil.
Proof.
  intros; induction w; auto.
Qed.

(* Se uma transição é não vazia, a anterior também é *)
Lemma ext_transition_app_not_nill {A B} eq eq' (g:nfa_comp_list A B) Q w1 w2 :
  ext_transition eq eq' g Q (w1 ++ w2) <> nil ->
  ext_transition eq eq' g Q w1 <> nil.
Proof.
  intros H H0.
  rewrite ext_transition_app, H0 in H.
  induction w2; intuition.
Qed.

(* A transição partindo da concatenação de estados é igual à concatenação das transições em separado *)
Lemma ext_transition_states_app {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 w :
  ext_transition eq eq' g (Q1 ++ Q2) w = ext_transition eq eq' g Q1 w ++ ext_transition eq eq' g Q2 w.
Proof.
  induction w using rev_ind.
  1: auto.
  repeat rewrite ext_transition_app. rewrite IHw.
  clear IHw; remember (ext_transition eq eq' g Q1 w) as Q3; clear HeqQ3;
  remember (ext_transition eq eq' g Q2 w) as Q4; clear HeqQ4 Q1 Q2.
  simpl; induction Q3.
  1: auto.
  simpl; rewrite IHQ3, app_assoc; auto.
Qed.

(* Se a transição resultando em um estado parte de um único estado, então aquele está na transição deste concatenado a outros *)
Lemma ext_transition_single {A B} eq eq' (g:nfa_comp_list A B) Q q q' w :
  In q Q /\ In q' (ext_transition eq eq' g [q] w) -> In q' (ext_transition eq eq' g Q w).
Proof.
  intros.
  destruct H as [H H0].
  induction Q.
  - destruct H.
  - destruct w.
    + destruct H0 as [H0|[]]; subst; auto.
    + destruct H.
      subst; simpl; simpl in H0; rewrite app_nil_r in H0.
      1,2: simpl; rewrite ext_transition_states_app; apply in_or_app; intuition.
Qed.

(* Se a transição para um estado parte de uma lista de estados, então existe um estado nessa lista que levaria àquele *)
Lemma ext_transition_list {A B} eq eq' (g:nfa_comp_list A B) Q q' w :
  In q' (ext_transition eq eq' g Q w) -> exists q, In q Q /\ In q' (ext_transition eq eq' g [q] w).
Proof.
  intros.
  generalize dependent q';
  induction w using rev_ind; intros.
  - simpl in *; exists q'; split; intuition.
  - rewrite ext_transition_app in H.
    assert (exists q'', In q'' (ext_transition eq eq' g Q w) /\ In q' (ext_transition eq eq' g [q''] [x])). {
      clear IHw.
      induction (ext_transition eq eq' g Q w).
      - destruct H.
      - apply in_app_or in H; destruct H.
        + exists a; simpl; split.
          1: auto.
          rewrite app_nil_r; auto.
        + apply IHl in H; destruct H as [q'' [H H0]]; exists q''; intuition.
    }
    destruct H0 as [q'' [H0 H1]].
    apply IHw in H0.
    destruct H0 as [q [H0 H2]]; exists q; split.
    1: auto.
    rewrite ext_transition_app.
    apply ext_transition_single with q''; intuition.
Qed.

(* Prova de que a transição extendida sobre estados retorna estados *)
Lemma ext_transition_in_states {A B} eq eq' (g:nfa_comp_list A B) Q q' w :
  (forall q, In q Q -> In q (states g)) ->
  In q' (ext_transition eq eq' g Q w) -> In q' (states g).
Proof.
  intros.
  generalize dependent Q;
  induction w; intros.
  1: auto.
  replace (a::w) with ([a]++w) in H0.
  2: auto.
  rewrite ext_transition_app in H0.
  apply IHw with (ext_transition eq eq' g Q [a]).
  2: auto.
  clear IHw H0; intros.
  induction Q.
  1: destruct H0.
  replace (a0::Q) with ([a0] ++ Q) in H0.
  2: auto.
  rewrite ext_transition_states_app in H0.
  apply in_app_or in H0; destruct H0.
  2: apply IHQ; intros; try (apply H; right); auto.
  simpl in H0; rewrite app_nil_r in H0.
  clear IHQ H; induction g.
  1: destruct H0.
  destruct a1.
  1-4: try right; auto.
  simpl in H0; destruct (eq a0 q0 && eq' a a1).
  2: right; right; auto.
  destruct H0.
  1: subst; right; left; auto.
  right; right; auto.
Qed.

(* Definição de existência de estado final em lista *)
Definition has_accept_state {A B} (g:nfa_comp_list A B) Q :=
  exists q, In q Q /\ In q (accept_states g).

(* Verifica se existe um estado final *)
Fixpoint has_accept_stateb {A B} eq (g:nfa_comp_list A B) Q :=
  match Q with
  | nil => false
  | q::Q => inb eq q (accept_states g) || has_accept_stateb eq g Q
  end.

(* Prova de que a definição está correta *)
Lemma has_accept_stateb_correct {A B} eq (g:nfa_comp_list A B) Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  has_accept_stateb eq g Q = true <-> has_accept_state g Q.
Proof.
  unfold has_accept_state; intros.
  induction Q.
  - split; intros.
    + destruct g; discriminate.
    + destruct H0; destruct H0; inversion H0.
  - simpl; split; intros.
    + apply orb_prop in H0; destruct H0.
      * apply inb_correct in H0.
        -- exists a; split; auto.
        -- auto.
      * apply IHQ in H0; destruct H0; exists x; intuition.
    + apply orb_true_intro; destruct H0; destruct H0; destruct H0.
      * subst; left; apply inb_correct; auto.
      * right; apply IHQ; exists x; intuition.
Qed.

(* Definição de palavra aceita *)
Definition accepts {A B} eq eq' (g:nfa_comp_list A B) w :=
  has_accept_state g (ext_transition eq eq' g (start_states g) w).

(* Verifica se uma palavra é aceita *)
Definition acceptsb {A B} eq eq' (g:nfa_comp_list A B) w :=
  has_accept_stateb eq g (ext_transition eq eq' g (start_states g) w).


(** Estados alcançáveis **)
Definition reachable_state {A B} eq eq' (g:nfa_comp_list A B) q :=
  exists w, In q (ext_transition eq eq' g (start_states g) w).


(** Caminhos **)

(* Definição de caminho dentro de um autômato *)
Inductive path {A B} (g:nfa_comp_list A B) : A->A->list B->Prop :=
  | path_nil (q:A) : path g q q nil
  | path_next q1 q2 q3 w a : path g q1 q2 w -> In (trans q2 a q3) g -> path g q1 q3 (w ++ [a]).

(* Definição reversa *)
Lemma path_left {A B} (g:nfa_comp_list A B) q1 q2 q3 a w :
  In (trans q1 a q2) g -> path g q2 q3 w -> path g q1 q3 (a::w).
Proof.
  intros.
  induction H0.
  - replace [a] with ([] ++ [a]).
    2: auto.
    apply path_next with q1.
    1: constructor.
    auto.
  - replace (a::w ++ [a0]) with ((a::w) ++ [a0]).
    2: auto.
    apply path_next with q2.
    2: auto.
    intuition.
Qed.

(* Existe caminho sse existe transição estendida *)
Lemma path_ext_transition {A B} eq eq' (g:nfa_comp_list A B) q q' w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  In q' (ext_transition eq eq' g [q] w) <-> path g q q' w.
Proof.
  intros; split; intros.
  - generalize dependent q'; induction w using rev_ind; intros.
    + destruct H1.
      2: destruct H1.
      subst; constructor.
    + rewrite ext_transition_app in H1.
      assert (exists q'', In q'' (ext_transition eq eq' g [q] w) /\ In q' (ext_transition eq eq' g [q''] [x])). {
        clear IHw.
        induction (ext_transition eq eq' g [q] w).
        - destruct H1.
        - apply in_app_or in H1; destruct H1.
          + exists a; simpl; split.
            1: auto.
            rewrite app_nil_r; auto.
          + apply IHl in H1; destruct H1 as [q'' [H1 H2]]; exists q''; intuition.
      }
      destruct H2 as [q'' [H2 H3]].
      apply path_next with q''.
      1: intuition.
      simpl in H3; rewrite app_nil_r in H3; apply transition_in in H3; auto.
  - induction H1.
    + left; auto.
    + rewrite ext_transition_app; apply ext_transition_single with q2; split.
      1: auto.
      simpl; rewrite app_nil_r; apply (transition_in eq eq' g q2 a q3 H H0); auto.
Qed.


(** Autômatos com estados-lista **)

(* Decisor da igualdade *)
Fixpoint lists_eq {A} (eq:A->A->bool) l1 l2 :=
  match l1, l2 with
  | nil, nil => true
  | x1::l1, x2::l2 => eq x1 x2 && lists_eq eq l1 l2
  | _, _ => false
  end.

(* Prova de que a definição está correta *)
Lemma lists_eq_correct {A} {eq:A->A->bool} (H:forall q1 q2, q1=q2 <-> eq q1 q2=true) :
  forall q1 q2, q1=q2 <-> lists_eq eq q1 q2=true.
Proof.
  split; intros.
  - symmetry in H0; subst.
    induction q1.
    1: auto.
    simpl; apply andb_true_intro; split.
    1: apply H; auto.
    auto.
  - generalize dependent q2; induction q1; intros.
    + destruct q2.
      1: auto.
      discriminate.
    + destruct q2.
      1: discriminate.
      simpl in H0.
      apply andb_prop in H0; destruct H0.
      apply H in H0; symmetry in H0.
      apply IHq1 in H1; subst.
      auto.
Qed.

(** Normalizar autômato de listas **)

(*Fixpoint normalize_nfa' {A B} eq (g l:nfa_comp_list (list A) B) :=
  match l with
  | nil => nil
  | trans Q a Q'::l => trans (get_set eq Q (states g)) a (get_set eq Q' (states g))::normalize_nfa' eq g l
  | start Q::l => start (get_set eq Q (states g))::normalize_nfa' eq g l
  | accept Q::l => accept (get_set eq Q (states g))::normalize_nfa' eq g l
  | state Q::l => state (get_set eq Q (states g))::normalize_nfa' eq g l
  | symbol a::l => symbol a::normalize_nfa' eq g l
  end.

Lemma normalized_nfa' {A B} eq (g l l':nfa_comp_list (list A) B) Q Q' :
  (forall x x', x=x' <-> eq x x'=true) ->
  subset l g ->
  subset l' g ->
  In Q (states (normalize_nfa' eq g l)) ->
  In Q' (states (normalize_nfa' eq g l')) ->
  (eq_sets Q Q' <-> Q = Q').
Proof.
  intros.
  induction l.
  - destruct H2.
  - assert (subset l g).
      unfold subset in H0; unfold subset; intuition.

    assert (forall q, In q (states g) -> get_set eq q (states g) = Q -> (eq_sets Q Q' <-> Q = Q')). {
      clear H4 IHl H2 H0; intros.
      induction l'.
      - destruct H3.
      - assert (subset l' g).
          unfold subset in H1; unfold subset; intuition.
        destruct a0.
        2: intuition.
        1-4: destruct H3.
        2,4,6: intuition.
        1-5: admit.
    }

    simpl in H1; simpl in H2; destruct a.
    2: intuition.
    1-4: destruct H2.
    2,4,6: intuition.
    5: destruct H2.
    6: intuition.

    1-4: apply (H5 q); auto.
    5: apply (H5 q'); auto.
    
Admitted.

Definition normalize_nfa {A B} eq (g:nfa_comp_list (list A) B) :=
  normalize_nfa' eq g g.

Lemma normalized_nfa {A B} eq (g:nfa_comp_list (list A) B) Q Q' :
  In Q (states (normalize_nfa eq g)) -> In Q' (states (normalize_nfa eq g)) ->
  eq_sets *)











