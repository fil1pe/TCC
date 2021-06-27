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
      (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) -> is_nfa g.
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

(* Prova de que os estados iniciais estão contidos nos estados *)
Lemma start_states_subset {A B} (g:nfa_comp_list A B) :
  subset (start_states g) (states g).
Proof.
  induction g; intros q H.
  1: destruct H.
  simpl in H; destruct a.
  1,2,4,5: try right; intuition.
  destruct H; subst.
  1: left; auto.
  right; intuition.
Qed.

(* Prova de que o estado inicial é um estado *)
Lemma start_state_is_state {A B} (g:nfa_comp_list A B) q :
  In q (start_states g) ->
  In q (states g).
Proof.
  intros; induction g.
  1: destruct H.
  destruct a.
  1,2,4,5: try right; intuition.
  destruct H.
  1: subst; left; auto.
  right; intuition.
Qed.

(* Os estados de dois autômatos concatenados são a concatenação dos estados deles *)
Lemma in_app_states_or {A B} (g1 g2:nfa_comp_list A B) q :
  In q (states (g1 ++ g2)) <-> In q (states g1) \/ In q (states g2).
Proof.
  intros.
  induction g1.
  - split; intros.
    1: intuition.
    destruct H.
    2: intuition.
    destruct H.
  - destruct a; split; intros.
    + destruct H; subst.
      1: left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      1: left; intuition.
      right; intuition.
    + intuition.
    + intuition.
    + destruct H; subst.
      1: left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      1: left; intuition.
      right; intuition.
    + destruct H; subst.
      1: left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      1: left; intuition.
      right; intuition.
    + destruct H; subst.
      1: left; left; intuition.
      destruct H; subst.
      1: left; right; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      1: left; intuition.
      apply or_assoc in H; destruct H; subst; right; intuition.
Qed.

(* Os estados iniciais de dois autômatos concatenados são a concatenação dos estados iniciais deles *)
Lemma in_app_start_states_or {A B} (g1 g2:nfa_comp_list A B) q :
  In q (start_states (g1 ++ g2)) <-> In q (start_states g1) \/ In q (start_states g2).
Proof.
  intros; induction g1.
  {
    split; intros.
    1: intuition.
    destruct H.
    1: destruct H.
    auto.
  }
  destruct a.
  1,2,4,5: auto.
  simpl; split; intros.
  - destruct H; subst.
    1: left; left; auto.
    apply or_assoc; right; intuition.
  - apply or_assoc in H; destruct H; subst.
    1: left; auto.
    right; apply IHg1; auto.
Qed.

(* Se existe uma transição a um estado q, então esse estado está nos estados *)
Lemma trans_in_states {A B} (g:nfa_comp_list A B) q a q' :
  In (trans q a q') g -> In q (states g).
Proof.
  intros; induction g; destruct H; subst.
  1: left; intuition.
  destruct a0; try right; try right; intuition.
Qed.

(* Se existe uma transição definida para algum símbolo a, então esse símbolo está no alfabeto *)
Lemma trans_in_alphabet {A B} (g:nfa_comp_list A B) q a q' :
  In (trans q a q') g -> In a (alphabet g).
Proof.
  intros.
  induction g; destruct H.
  1: subst; left; auto.
  destruct a0; simpl; try right; intuition.
Qed.

(* Prova de que todos os elementos retornados pela função estados são estados *)
Lemma states_in {A B} (g:nfa_comp_list A B) q :
  In q (states g) -> In (state q) g \/ In (start q) g \/ In (accept q) g \/
  exists q' a, In (trans q a q') g \/ In (trans q' a q) g.
Proof.
  intros; induction g.
  1: destruct H.
  destruct a.
  - destruct H; subst.
    1: intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - apply IHg in H; destruct H as [H|[H|[H|[q' [b [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', b; intuition.
  - destruct H; subst.
    1: intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - destruct H; subst.
    1: intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - destruct H; subst.
    1: right; right; right; exists q', a; intuition.
    destruct H; subst.
    1: right; right; right; exists q0, a; intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q'' [b [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q'', b; intuition.
Qed.

(* Prova de consistência da função que retorna os estados de aceitação *)
Lemma accept_states_in {A B} (g:nfa_comp_list A B) q :
  In q (accept_states g) <-> In (accept q) g.
Proof.
  intros; induction g.
  1: split; intros; destruct H.
  destruct a; split; intros.
  1,3,5,9: intuition.
  1-3,6: destruct H; try discriminate; intuition.
  1: destruct H; subst; intuition.
  destruct H.
  1: injection H; intros; subst; left; auto.
  right; intuition.
Qed.

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

(* Uma versão mais genérica daquela prova de consistência *)
Lemma transition_in_ext {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) Q q a q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  In q Q -> In (trans q a q') g ->
  In q' (ext_transition eq eq' g Q [a]).
Proof.
  intros; induction Q; destruct H1.
  1: subst; apply in_or_app; left; apply transition_in; auto.
  apply in_or_app; right; intuition.
Qed.

(* A 'volta' *)
Lemma in_transition_ext {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) Q q' a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  In q' (ext_transition eq eq' g Q [a]) ->
  exists q, In q Q /\ In (trans q a q') g.
Proof.
  intros.
  induction Q as [|q Q IH].
  1: destruct H1.
  apply in_app_or in H1; destruct H1.
  - apply transition_in in H1.
    2,3: auto.
    exists q; intuition.
  - apply IH in H1; destruct H1 as [q0 H1]; exists q0; intuition.
Qed.

(* Um lema útil *)
Lemma ext_transition_app {A B} eq eq' (g:nfa_comp_list A B) Q w1 w2 :
  ext_transition eq eq' g Q (w1 ++ w2) = ext_transition eq eq' g (ext_transition eq eq' g Q w1) w2.
Proof.
  generalize dependent Q.
  induction w1.
  - auto.
  - intros; apply IHw1.
Qed.

(* Prova de que a transição está contida nos estados *)
Lemma ext_transition_subset {A B} eq eq' (g:nfa_comp_list A B) q w :
  subset q (states g) ->
  subset (ext_transition eq eq' g q w) (states g).
Proof.
  intros H q' H0; generalize dependent q; induction w; intros.
  1: apply H; auto.
  replace (a::w) with ([a]++w) in H0.
  2: auto.
  rewrite ext_transition_app in H0.
  apply IHw with (ext_transition eq eq' g q [a]).
  2: auto.
  clear IHw H0 q'; intros q' H0; induction q.
  1: auto.
  simpl in H0; apply in_app_or in H0; destruct H0.
  - clear H IHq; induction g.
    1: destruct H0.
    destruct a1.
    1-4: try right; intuition.
    simpl in H0; destruct (eq a0 q0 && eq' a a1).
    2: right; intuition.
    destruct H0.
    1: subst; right; left; auto.
    right; intuition.
  - apply IHq.
    2: auto.
    intros q'' H1; apply H; intuition.
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

(* Prova de que a transição a partir de estados equivalentes resulta em estados equivalentes *)
Lemma ext_transition_eq_sets {A B} eq eq' (g: nfa_comp_list A B) w :
  forall Q1 Q2, eq_sets Q1 Q2 ->
  eq_sets (ext_transition eq eq' g Q1 w) (ext_transition eq eq' g Q2 w).
Proof.
  induction w; intros.
  1: auto.
  replace (a::w) with ([a] ++ w).
  2: auto.
  rewrite ext_transition_app, ext_transition_app.
  apply IHw; clear IHw.
  assert (forall s1 s2, (forall x, In x s1 -> In x s2) -> forall x, In x (ext_transition eq eq' g s1 [a]) -> In x (ext_transition eq eq' g s2 [a])). {
    clear H Q1 Q2; intros; induction s1.
    1: destruct H0.
    replace (ext_transition eq eq' g (a0 :: s1) [a]) with (transition eq eq' g a0 a ++ ext_transition eq eq' g s1 [a]) in H0.
    2: auto.
    apply in_app_or in H0.
    destruct H0.
    - clear IHs1; specialize (H a0); induction s2.
      1: destruct H; intuition.
      assert (In a0 (a1::s2)).
        apply H; intuition.
      destruct H1.
      1,2: simpl; apply in_or_app.
      1: subst; intuition.
      right; apply IHs2; intuition.
    - apply IHs1.
      1: intros; apply H; intuition.
      auto.
  }
  split; intros.
  - apply H0 with Q1.
    2: auto.
    intros; apply H; auto.
  - apply H0 with Q2.
    2: auto.
    intros; apply H; auto.
Qed.

(* Prova de que a equivalência entre estados e transições é equivalentes se os estados envolvidos são equivalentes *)
Lemma eq_setsb_ext_transition {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 Q3 Q4 w :
  (forall x x', x=x' <-> eq x x'=true) ->
  eq_setsb eq Q1 Q2 = true ->
  eq_setsb eq Q3 Q4 = true ->
  eq_setsb eq Q3 (ext_transition eq eq' g Q1 w) = eq_setsb eq Q4 (ext_transition eq eq' g Q2 w).
Proof.
  intros.
  destruct (eq_setsb eq Q3 (ext_transition eq eq' g Q1 w)) eqn:H2;
  destruct (eq_setsb eq Q4 (ext_transition eq eq' g Q2 w)) eqn:H3.
  1,4: auto.
  - apply eq_setsb_correct in H0;
    apply eq_setsb_correct in H1;
    apply eq_setsb_correct in H2.
    2-8: auto.
    assert (eq_setsb eq Q4 (ext_transition eq eq' g Q2 w) = true).
    2: rewrite H4 in H3; discriminate.
    apply eq_setsb_correct.
    1: auto.
    apply eq_sets_transitive with (ext_transition eq eq' g Q1 w).
    2: apply ext_transition_eq_sets; auto.
    apply eq_sets_transitive with Q3; auto.
  - apply eq_setsb_correct in H0;
    apply eq_setsb_correct in H1;
    apply eq_setsb_correct in H3.
    2-8: auto.
    assert (eq_setsb eq Q3 (ext_transition eq eq' g Q1 w) = true).
    2: rewrite H4 in H2; discriminate.
    apply eq_setsb_correct.
    1: auto.
    apply eq_sets_transitive with (ext_transition eq eq' g Q2 w).
    2: apply ext_transition_eq_sets, eq_sets_comm; auto.
    apply eq_sets_transitive with Q4.
    2: apply eq_sets_comm.
    1,2: auto.
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
Lemma path_left {A B} (g:nfa_comp_list A B) q1 q3 a w :
  (forall q2, In (trans q1 a q2) g -> path g q2 q3 w -> path g q1 q3 (a::w)) /\
  (path g q1 q3 (a::w) -> exists q2, In (trans q1 a q2) g /\ path g q2 q3 w).
Proof.
  split; intros.
  - induction H0.
    + replace [a] with ([] ++ [a]).
      2: auto.
      apply path_next with q1.
      1: constructor.
      auto.
    + replace (a::w ++ [a0]) with ((a::w) ++ [a0]).
      2: auto.
      apply path_next with q2.
      2: auto.
      intuition.
  - generalize dependent q3.
    induction w using rev_ind; intros.
    + exists q3; split.
      2: constructor.
      inversion H.
      assert (w = nil /\ a0 = a).
        replace [a] with (nil ++ [a]) in H0;
        try apply app_inj_tail in H0; auto.
      destruct H5; subst.
      inversion H1; subst.
      1: auto.
      destruct w; discriminate.
    + inversion H; subst.
      assert (w0 = a::w).
        replace (a::w ++ [x]) with ((a::w) ++ [x]) in H0;
        try apply app_inj_tail in H0; intuition.
      subst; apply IHw in H1; destruct H1 as [q5 H1];
      exists q5; split.
      1: intuition.
      apply path_next with q2.
      1: intuition.
      injection H0; intros; apply app_inj_tail in H2; destruct H2;
      subst; intuition.
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

(* Se há um caminho de q a q' por w em um dado autômato g1 ou g2, então existe esse caminho
na junção de g1 e g2. *)
Lemma path_app {A B} (g1 g2:nfa_comp_list A B) q q' w :
  path g1 q q' w \/ path g2 q q' w -> path (g1 ++ g2) q q' w.
Proof.
  intros.
  destruct H; induction H.
  1,3: constructor.
  1,2: apply path_next with q2;
    try apply in_or_app; intuition.
Qed.












