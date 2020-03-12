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

Definition max (a b:Z) :=
  if (a >=? b) then a
  else b.

Definition max3 (a b c:option Z) :=
  match a, b, c with
    None, None, None       => None                  |
    Some a, None, None     => Some a                |
    None, Some a, None     => Some a                |
    None, None, Some a     => Some a                |
    Some a, None, Some b   => Some (max a b)        |
    Some a, Some b, None   => Some (max a b)        |
    None, Some a, Some b   => Some (max a b)        |
    Some a, Some b, Some c => Some (max (max a b) c)
  end.

Fixpoint max3_lists (l1 l2 l3:list (option Z)) :=
  match l1, l2, l3 with
    Some m1::l1, Some m2::l2, Some m3::l3 => Some (max3 m1 m2 m3)::max3_lists l1 l2 l3 |
    Some m1::l1, None::l2, Some m3::l3 => Some (max3 m1 m2 m3)::max3_lists l1 l2 l3 |
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