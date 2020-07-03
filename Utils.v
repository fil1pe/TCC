Require Import Coq.Lists.List Omega.
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

(* Every list of length at least 1 is not empty (and vice versa). *)
Lemma length_not_nil : forall {X} (l : list X),
  l <> nil <-> length l >= 1.
Proof.
  intros X l; destruct l as [|x l]; split; intro H.
  - contradiction.
  - simpl in H; omega.
  - simpl; omega.
  - intro contra; inversion contra.
Qed.