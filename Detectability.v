Require Import Coq.Lists.List Omega Coq.Bool.Bool.
Import ListNotations.
Require Import DFA.
Local Open Scope Z_scope.

Module Type ObsDFA <: DFA.
  Variables (A B : Type).
  Variable Q : list A.
  Variable E : list B.
  Variable Eu : list B.
  Variable delta : A -> B -> A.
  Variable q0 : A.
  Variable sink : A.
  Variable Qm : list A.
  Axiom Eu_correct : forall e, In e Eu -> In e E.
  Axiom delta_correct : forall q e, delta q e <> sink -> (In e E /\ In q Q /\ q <> sink /\ In (delta q e) Q).
  Axiom q0_correct : In q0 Q.
  Axiom Qm_correct : forall q, In q Qm -> In q Q.
  Axiom sink_correct : In sink Q /\ sink <> q0.
  Axiom A_decidable : forall x y : A, {x = y} + {x <> y}.
  Axiom B_decidable : forall x y : A, {x = y} + {x <> y}.
End ObsDFA.

Module Detectability (G:ObsDFA).

Include DFAUtils G.

Definition Eu := G.Eu.
Definition Eu_correct := G.Eu_correct.







