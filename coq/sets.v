Require Import List Bool.
Include ListNotations.


(* Verifica se um elemento x pertence a l *)
Fixpoint inb {A} (eq:A->A->bool) x l :=
  match l with
  | nil => false
  | x'::l => eq x x' || inb eq x l
  end.

(* Prova de que a definição está correta *)
Lemma inb_correct {A} (eq:A->A->bool) x l :
  (forall x x', x=x' <-> eq x x'=true) ->
  inb eq x l = true <-> In x l.
Proof.
  intros.
  induction l.
  - split; intros; inversion H0.
  - simpl; destruct (eq x a) eqn:H0.
    + split; intros.
      * left; symmetry; apply H; auto.
      * auto.
    + split; intros.
      * right; apply IHl; auto.
      * destruct H1.
        -- symmetry in H1; apply H in H1; rewrite H1 in H0; discriminate H0.
        -- apply IHl; auto.
Qed.

(* Definição de subconjunto de lista *)
Definition subset {A} (s1 s2:list A) :=
  forall x, In x s1 -> In x s2.

(* Verifica se s1 está contido em s2 *)
Fixpoint subsetb {A} (eq:A->A->bool) s1 s2 :=
  match s1 with
  | nil => true
  | x::s1 => inb eq x s2 && subsetb eq s1 s2
  end.

(* Prova de que a definição está correta *)
Lemma subsetb_correct {A} (eq:A->A->bool) s1 s2 :
  (forall x x', x=x' <-> eq x x'=true) ->
  subsetb eq s1 s2 = true <-> subset s1 s2.
Proof.
  unfold subset; intros.
  induction s1.
  - split; intros.
    + inversion H1.
    + auto.
  - simpl; split; intros.
    + destruct H1.
      * subst; apply (inb_correct eq).
        -- apply H.
        -- apply andb_prop in H0; destruct H0; auto.
      * apply andb_prop in H0; destruct H0;
        destruct IHs1; apply H3 with (x:=x) in H2; auto.
    + apply andb_true_intro; split.
      * apply inb_correct.
        -- auto.
        -- apply H0; left; auto.
      * apply IHs1; intros; apply H0; right; auto.
Qed.

(* Equivalência de listas-conjuntos *)
Definition eq_sets {A} (s1 s2:list A) :=
  forall x, In x s1 <-> In x s2.

(* Prova da propriedade comutativa da equivalência *)
Lemma eq_sets_comm {A} (s1 s2:list A) :
  eq_sets s1 s2 -> eq_sets s2 s1.
Proof.
  unfold eq_sets; intros; split; intros;
  apply H; auto.
Qed.

(* Prova da propriedade transitiva da equivalência *)
Lemma eq_sets_trans {A} (s1 s2 s3:list A) :
  eq_sets s1 s2 -> eq_sets s1 s3 -> eq_sets s2 s3.
Proof.
  unfold eq_sets; intros; split; intros.
  - apply H0, H; auto.
  - apply H, H0; auto.
Qed.

(* Verifica se duas listas-conjuntos são equivalentes *)
Definition eq_setsb {A} (eq:A->A->bool) s1 s2 :=
  subsetb eq s1 s2 && subsetb eq s2 s1.

(* Prova de que a definição está correta *)
Lemma eq_setsb_correct {A} (eq:A->A->bool) s1 s2 :
  (forall x x', x=x' <-> eq x x'=true) ->
  eq_setsb eq s1 s2 = true <-> eq_sets s1 s2.
Proof.
  unfold eq_setsb; split; intros.
  - apply andb_true_iff in H0; destruct H0.
    pose proof subsetb_correct eq.
    split; intros.
    + apply (H2 s1 s2) in H; destruct H as [H _].
      apply H in H0; intuition.
    + apply (H2 s2 s1) in H; destruct H as [H _].
      apply H in H1; intuition.
  - apply andb_true_iff; split;
      apply subsetb_correct;
        try (unfold subset; intros; destruct H0 with x); auto.
Qed.


(* Verifica se um elemento (que pode ser indefinido) está em uma lista (que pode ser indefinida) *)
Definition in_opt {A} (x:option A) l :=
  match x with
  | None => False
  | Some x => match l with
              | None => False
              | Some l => In x l
              end
  end.

(**
(* Pega uma lista-conjunto equivalente dentro de uma lista *)
Fixpoint get_set {A} (eq:A->A->bool) s l :=
  match l with
  | nil => s
  | s'::l => if (eq_setsb eq s s') then s'
             else get_set eq s l
  end.

(**)
Lemma eq_set_get_trans {A} (eq:A->A->bool) s1 s2 l :
  (forall x x' : A, x = x' <-> eq x x' = true) ->
  eq_sets s1 s2 <->
  eq_sets s1 (get_set eq s2 l).
Proof.
  intros; induction l.
  - intuition.
  - simpl; destruct (eq_setsb eq s2 a) eqn:H0.
    2: auto.
    apply eq_setsb_correct in H0.
    + split; intros.
      * pose proof @eq_sets_trans A s2 s1 a.
        apply eq_sets_comm in H1; intuition.
      * apply eq_sets_comm in H0; apply eq_sets_comm in H1;
        apply (eq_sets_trans a s1 s2); intuition.
    + auto.
Qed.

(**)
Lemma get_set_unique {A} (eq:A->A->bool) s1 s1' s2 s2' l :
  (forall x x' : A, x = x' <-> eq x x' = true) ->
  In s1 l -> In s2 l ->
  get_set eq s1 l = s1' -> get_set eq s2 l = s2' ->
  (eq_sets s1' s2' <-> s1' = s2').
Proof.
  intros; split; intros.
  2: subst; unfold eq_sets; rewrite H4; intuition.
  induction l.
  - destruct H0.
  - assert (forall s, eq_setsb eq s s = true). {
      intros; apply eq_setsb_correct.
      auto.
      unfold eq_sets; intuition.
    }
    simpl in *; destruct H0; destruct H1; subst.
    + auto.
    + rewrite H5; rewrite H5 in H4; destruct (eq_setsb eq s2 s1) eqn:H0.
      1: auto.
      apply eq_set_get_trans in H4. 2: auto.
      apply eq_sets_comm in H4.
      apply (eq_setsb_correct eq s2 s1) in H; apply H in H4; rewrite H4 in H0;
      discriminate.
    + rewrite H5; rewrite H5 in H4; destruct (eq_setsb eq s1 s2) eqn:H1.
      1: auto.
      pose proof eq_set_get_trans eq s2 s1.
      apply eq_sets_comm, eq_set_get_trans, eq_sets_comm in H4.
      apply (eq_setsb_correct eq s1 s2) in H4. 2-3: auto. rewrite H4 in H1;
      discriminate.
    + destruct (eq_setsb eq s1 a) eqn:H2; destruct (eq_setsb eq s2 a) eqn:H3.
      1,4: intuition.
      apply eq_set_get_trans, eq_sets_comm, (eq_setsb_correct eq s2 a) in H4.
      rewrite H4 in H3; discriminate.
      1-2: auto.
      apply eq_sets_comm, eq_set_get_trans, eq_sets_comm, (eq_setsb_correct eq s1 a) in H4.
      rewrite H4 in H2; discriminate.
      1-2: auto.
Qed.

(* Verifica se uma lista-conjunto está dentro de uma lista *)
Fixpoint set_in_list {A} (eq:A->A->bool) s l :=
  match l with
  | nil => false
  | s'::l => eq_setsb eq s s' || set_in_list eq s l 
  end.


**)






