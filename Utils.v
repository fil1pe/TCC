Require Import Coq.Lists.List.
Import ListNotations.

(* If a list is not empty, the default value passed to function last
  will not matter. *)
Lemma last_any_default : forall {X} (l : list X) (a b : X),
  l <> nil ->
  last l a = last l b.
Proof.
  intros X l a b H; induction l as [|x l IH].
  - contradiction.
  - destruct l.
    + auto.
    + simpl in *; apply IH; intro contra; discriminate.
Qed.