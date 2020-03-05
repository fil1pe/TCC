Require Import Coq.Init.Nat Coq.Lists.List Omega Utils DFA.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Fixpoint verify_upper_bound' (q:nat) (m:Z) (s:list Z) (n:nat) :=
  match n with O => s | S n =>

    if (states_num <=? q)%nat then
        Return valid s
    else if nth q s (-1) =? -1 then
        let s' := change s q m in
        Return max3_lists (verify_upper_bound' (transition q add) (m+1) s' n)
                          (verify_upper_bound' (transition q rem) (m-1) s' n)
                          (verify_upper_bound' (transition q oth)   m   s' n)
    else if nth q s (-1) >=? m then
        Return valid s
    else
        Return invalid s

  end.

Fixpoint verify_upper_bound'' (q:nat) (m:Z) (s:list Z) (n:nat) :=
  match n with O => s | S n =>

    if (states_num <=? q)%nat then
        Return valid s
    else if nth q s (-1) =? -1 then
        let s'   := change s q m in
        let s''  := verify_upper_bound'' (transition q add) (m+1) s'  n in
        let s''' := verify_upper_bound'' (transition q oth)   m   s'' n in
        Return max3_lists s'' s''' (verify_upper_bound'' (transition q rem) (m-1) s''' n)
    else if nth q s (-1) >=? m then
        Return valid s
    else
        Return invalid s

  end.

Definition verify_upper_bound :=
  extract_invalid (verify_upper_bound'' 0 0 (initial_solution states_num) (states_num+2)) [].

Compute verify_upper_bound.