Require Import List Bool sets nfa dfa reversing.
Include ListNotations.


Definition n2dfa {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) : nfa_comp_list (list A) B.
Admitted.

Lemma n2dfa_nil {A B} eq eq' {g:nfa_comp_list A B} :
  accept_states g = [] -> n2dfa eq eq' g = [].
Proof.
Admitted.

Lemma n2dfa_states {A B eq eq'} {g:nfa_comp_list A B} Q :
  In Q (states (n2dfa eq eq' (revert_nfa g))) ->
  forall q, In q Q -> In q (states g).
Proof.
Admitted.

Lemma n2dfa_eq_states {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  In Q1 (states brz) -> In Q2 (states brz) ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
Admitted.

Lemma n2dfa_path {A B eq eq'} {g:nfa_comp_list A B} {Q q' w} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  let g' := (n2dfa eq eq' g) in
  (forall Q', path g' Q Q' w /\ In q' Q' -> exists q, path g q q' w /\ In q Q) /\
  (forall q, path g q q' w /\ In q Q -> exists Q', path g' Q Q' w /\ In q' Q').
Proof.
Admitted.

Lemma n2dfa_is_dfa {A B eq eq'} {g:nfa_comp_list A B} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' (n2dfa eq eq' g).
Proof.
Admitted.

Lemma n2dfa_accept {A B eq eq'} {g:nfa_comp_list A B} {Q} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := n2dfa eq eq' g in
  In Q (states g') ->
  In Q (accept_states g') <-> exists q, In q Q /\ In q (accept_states g).
Proof.
Admitted.