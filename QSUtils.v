Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition Return {A} a:A := a.

Fixpoint update {A} (l:list A) (n:nat) (a:A) :=
  match l, n with
    x::l, S n => x::update l n a |
    x::l,  O  => a::l            |
     l  ,  _  => l
  end.

Fixpoint initial_solution (n:nat) :=
  match n with
     O    => []                         |
    S n   => initial_solution n ++ [-1]
  end.

Fixpoint end_0 (s:list Z) :=
  match s with
    x::[] => [0]        |
    x::l  => x::end_0 l |
    []    => []
  end.

Fixpoint end_1 (s:list Z) :=
  match s with
    x::[] => [1]        |
    x::l  => x::end_1 l |
    []    => []
  end.

Fixpoint all_but_last_le (l:list Z) n :=
  match l with
    x::[] => true                             |
    x::l  => (x <=? n) && all_but_last_le l n |
     []   => true
  end.

Definition max3 (a b c:Z) :=
  if (a >=? b) && (a >=? c) then a
  else if (b >=? a) && (b >=? c) then b
  else c.

Definition min3 (a b c:Z) :=
  if (a <=? b) && (a <=? c) then a
  else if (b <=? a) && (b <=? c) then b
  else c.

Fixpoint max3_lists (l1 l2 l3:list Z) :=
  match l1, l2, l3 with
    x1::l1, x2::l2, x3::l3 => max3 x1 x2 x3::max3_lists l1 l2 l3 |
      _   ,   _   ,    _   => []
  end.

Fixpoint min_lists (l1 l2 l3:list Z) :=
  match l1, l2, l3 with
    x1::l1, x2::l2, x3::l3 => min3 x1 x2 x3::max3_lists l1 l2 l3 |
      _   ,   _   ,    _   => []
  end.

Fixpoint extract_0 (l1 l2:list Z) b :=
  match l1 with
    x::[] => if x =? 0 then (l2, b) else (l2, false) |
    x::l1 => extract_0 l1 (l2 ++ [x]) b              |
      []  => (l2, false)
  end.

Fixpoint extract_1 (l1 l2:list Z) b :=
  match l1 with
    x::[] => if x =? 1 then (l2, b) else (l2, false) |
    x::l1 => extract_1 l1 (l2 ++ [x]) b              |
      []  => (l2, false)
  end.