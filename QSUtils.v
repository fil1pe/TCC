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

Fixpoint initial_solution (n:nat) : list (option Z) :=
  match n with
     O    => []                          |
    S n   => initial_solution n ++ [None]
  end.

Fixpoint update {A} (l:list (option A)) (n:nat) (a:A) :=
  match l, n with
    x::l, S n => x::update l n a |
    x::l,  O  => Some a::l       |
     l  ,  _  => l
  end.

Fixpoint foreach {A B} (l:list A) (f:A->B) (c:B->B->B) (b:B) :=
  match l with
     []  => b                        |
    x::l => c (f x) (foreach l f c b)
  end.

Fixpoint all_le l n :=
  match l with
    Some m::l => (m <=? n) && all_le l n |
        _     => true
  end.

Fixpoint all_but_first_le l n :=
  match l with
    x::l => all_le l n |
      _  => true
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

Definition extract o s b :=
  match s with
    x::s => if optZ_eq x (Some o) then (s, b) else (s, false) |
     []  => ([], false)
  end.

Lemma extract_true : forall s b,
  snd (extract 0 s b) = true ->
  b = true.
Proof.
  intros s b H.
  induction s.
  simpl in H. discriminate H.
  simpl in H.
  destruct (optZ_eq a (Some 0)); simpl in H.
  apply H.
  discriminate H.
Qed.