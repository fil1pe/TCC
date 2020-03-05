Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition Return {A} a:A := a.

Fixpoint change {A} (l:list A) (n:nat) (a:A) :=
  match l, n with
    x::l, S n => x::change l n a |
    x::l,  O  => a::l            |
     l  ,  _  => l
  end.

Fixpoint initial_solution' (n:nat) :=
  match n with
     O    => []                         |
    S n   => initial_solution' n ++ [-1]
  end.

Definition initial_solution n := initial_solution' n ++ [1].

Fixpoint valid (s:list Z) :=
  match s with
    x::[] => [0]        |
    x::l  => x::valid l |
    []    => []
  end.

Fixpoint invalid (s:list Z) :=
  match s with
    x::[] => [1]          |
    x::l  => x::invalid l |
    []    => []
  end.

Definition max3 (a b c:Z) :=
  if (a >=? b) && (a >=? c) then a
  else if (b >=? a) && (b >=? c) then b
  else c.

Fixpoint max3_lists (l1 l2 l3:list Z) :=
  match l1, l2, l3 with
    x1::l1, x2::l2, x3::l3 => max3 x1 x2 x3::max3_lists l1 l2 l3 |
      _   ,   _   ,    _   => []
  end.

Fixpoint extract_invalid (l1 l2:list Z) :=
  match l1 with
    x::[] => if x =? 0 then (l2, true) else (l2, false) |
    x::l1 => extract_invalid l1 (l2 ++ [x])             |
      []  => (l2, false)
  end.