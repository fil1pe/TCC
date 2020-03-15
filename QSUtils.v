Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition optZ_eq (a b:option Z) :=
  match a, b with
    Some x, Some y => x =? y |
     None ,  None  => true   |
      _   ,   _    => false
  end.

Definition optZ_ge (a b:option Z) :=
  match a, b with
    Some x, Some y => x >=? y |
      _   ,   _    => false
  end.

Fixpoint count_none (l:list (option Z)) : nat :=
  match l with
     []  => 0                                                        |
    x::l => if optZ_eq x None then 1 + count_none l else count_none l
  end.

Fixpoint update {A} (l:list (option A)) (n:nat) (a:A) :=
  match l, n with
    x::l, S n => x::update l n a |
    x::l,  O  => Some a::l       |
     l  ,  _  => l
  end.

Fixpoint initial_solution (n:nat) : list (option Z) :=
  match n with
     O    => []                          |
    S n   => initial_solution n ++ [None]
  end.

Fixpoint update_last {A} (o:A) (s:list (option A)) :=
  match s with
    x::[] => [Some o]           |
    x::l  => x::update_last o l |
    []    => []
  end.

Fixpoint foreach {A B} (l:list A) (f:A->B) (c:B->B->B) (b:B) :=
  match l with
     []  => b                        |
    x::l => c (f x) (foreach l f c b)
  end.

Fixpoint all_but_last_le l n :=
  match l with
      x::[]   => true                             |
    Some m::l => (m <=? n) && all_but_last_le l n |
       _      => true
  end.

Definition max a b :=
  match a, b with
     None ,  None  => None                                |
    Some x,  None  => Some x                              |
     None , Some x => Some x                              |
    Some x, Some y => if (x >=? y) then Some x else Some y
  end.

Fixpoint max_lists l1 l2 :=
  match l1, l2 with
    x::l1, y::l2 => max x y :: (max_lists l1 l2) |
      _  ,   _   => []
  end.

Fixpoint extract o l1 l2 b :=
  match l1 with
    x::[] => if optZ_eq x (Some o) then (l2, b) else (l2, false) |
    x::l1 => extract o l1 (l2 ++ [x]) b                          |
     []   => (l2, false)
  end.

Lemma fst_extract' : forall o a l1 l2 b,
  fst (extract o (l1 ++ [a]) l2 b) = l2 ++ l1.
Proof.
  intros o a l1 l2 b.
  generalize dependent l2.
  induction l1.
  - intro l2.
    destruct a as [z|]; simpl; try (destruct (z =? o), b; simpl);
    rewrite app_nil_r; reflexivity.
  - intro l2.
    simpl.
    destruct (l1 ++ [a]) eqn:eq.
      * destruct l1; discriminate eq.
      * destruct a0 eqn:eqa0;
        rewrite IHl1;
        rewrite <- app_assoc;
        rewrite <- eqa0;
        replace ([a0] ++ l1) with (a0 :: l1);
        reflexivity.
Qed.

Lemma fst_extract : forall o a l b,
  fst (extract o (l ++ [a]) [] b) = l.
Proof.
  intros o a l b.
  remember (fst (extract o (l ++ [a]) [] b)) as aux.
  replace l with ([] ++ l).
  rewrite Heqaux.
  apply fst_extract'.
  reflexivity.
Qed.