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

Fixpoint initial_solution (n:nat) : list (option Z) :=
  match n with
     O    => []                         |
    S n   => initial_solution n ++ [None]
  end.

Fixpoint end_0 s:list (option Z) :=
  match s with
    x::[] => [Some 0]   |
    x::l  => x::end_0 l |
    []    => []
  end.

Fixpoint end_1 s:list (option Z) :=
  match s with
    x::[] => [Some 1]   |
    x::l  => x::end_1 l |
    []    => []
  end.

Fixpoint all_but_last_le (l:list (option Z)) n :=
  match l with
      x::[]   => true                             |
    Some m::l => (m <=? n) && all_but_last_le l n |
       _      => true
  end.

Definition max (a b:option Z) :=
  match a, b with
    None, None => None
    Some x, None => Some x
    None, Some x => Some x
    Some x, Some y => if (x >=? y) then Some x else Some y
  end.

Fixpoint max3_lists (l1 l2 l3:list (option Z)) :=
  match l1, l2, l3 with
    x::l1, y::l2, z::l3 => max (max x y) z::(max3_lists l1 l2 l3) |
    [],[],[] => []
  end.

Fixpoint extract_0 (l1 l2:list Z) b :=
  match l1 with
    Some x::[] => if x =? 0 then (l2, b) else (l2, false) |
    x::l1 => extract_0 l1 (l2 ++ [x]) b              |
      []  => (l2, false)
  end.

Fixpoint extract_1 (l1 l2:list Z) b :=
  match l1 with
    Some x::[] => if x =? 1 then (l2, b) else (l2, false) |
    x::l1 => extract_1 l1 (l2 ++ [x]) b              |
      []  => (l2, false)
  end.
