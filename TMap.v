(* ************************************************************************** *)
(*                                                                            *)
(* Verified Smart Contract                                                    *)
(*                                                                            *)
(*   ZeroK Team                                                               *)
(*                                                                            *)
(* ************************************************************************** *)

Set Implicit Arguments.

Class BEq A := 
{
  beq : A -> A -> bool;
  beq_true_eq: forall a a' : A, beq a a' = true -> a = a';
  beq_false_neq : forall a a' : A, beq a a' = false -> a <> a';
  eq_beq_true : forall a a' : A, a = a' -> beq a a' = true;
  neq_beq_false : forall a a' : A, a <> a' -> beq a a' = false
}.

Class BZero A `{BEq A} : Type := 
{
  zero: A;
}.

Section BoolEq.

Context `{A: Type}.
Context `{BEq A}.

Lemma beq_dec: forall (a a': A),
    beq a a' = true \/ beq a a' = false.
Proof.
Admitted.

Lemma beq_sym: forall (a a': A) b,
    beq a a' = b 
    -> beq a' a = b.
Proof.
Admitted.

Lemma beq_refl : forall m, beq m m = true.
Proof.
Admitted.

Lemma beq_trans : forall m n k, beq m n = true
  -> beq n k = true 
  -> beq m k = true.
Proof.
Admitted.

Lemma beq_sym2 : forall m n, 
  beq m n = beq n m.
Proof.
Admitted.

(* Ltac beq_rewrite t := *)
(*   match t with  *)
(*     | beq ?x ?y = ?f => *)
(*       let Hb := fresh "Hb" in *)
(*         (assert (Hb : t);  *)
(*           [solvebnat | rewrite Hb; clear Hb]) *)
(*     | _ => *)
(*       match type of t with *)
(*         | beq_nat ?x ?y = true => rewrite (beq_true_eq x y t) *)
(*         | _ => rewrite t *)
(*       end *)
(*   end. *)

(* Tactic Notation "rewbnat" constr (t) := beq_rewrite t *)


(* Tactic Notation "rewbnat" constr (t) "in" hyp (H) := *)
(*   match t with  *)
(*     | beq_nat ?x ?y = ?f => *)
(*       let Hb := fresh "Hb" in *)
(*         (assert (Hb : t);  *)
(*           [solvebnat | rewrite Hb in H; clear Hb]) *)
(*     | blt_nat ?x ?y = ?f => *)
(*       let Hb := fresh "Hb" in *)
(*         (assert (Hb : t);  *)
(*           [solvebnat | rewrite Hb in H; clear Hb]) *)
(*     | _ => *)
(*       match type of t with *)
(*         | beq_nat ?x ?y = true => rewrite (beq_true_eq x y t) in H *)
(*         | _ => rewrite t in H *)
(*       end *)
(*   end. *)

End BoolEq.

Ltac simplbeq := 
  match goal with

    (* beq rewrite directly *)
    | [H : beq ?x ?y = ?f 
      |- context [(beq ?x ?y)]] =>
       rewrite H; simplbeq
    | [H : beq ?x ?y = ?f,
       H0 : context [(beq ?x ?y)] |- _ ] =>
       rewrite H in H0; simplbeq
         
    (* beq_refl *)
    | [ |- context [(beq ?x ?x)] ] =>
      rewrite (beq_refl x); simplbeq
    | [H : context [(beq ?x ?x)] |- _ ] => 
      rewrite (beq_refl x) in H; simplbeq

    (* beq_sym *)
    | [ H : beq ?x ?y = ?b 
        |- context [(beq ?y ?x)] ] =>
      rewrite (beq_sym x y H); simplbeq
    | [H : beq ?x ?y = ?b,
       H0 : context [(beq ?y ?x)] |- _ ] => 
      rewrite (beq_sym x y H) in H0; simplbeq

    | [ H : ?x <> ?y |- context [(beq ?x ?y)] ] => 
      rewrite (neq_beq_false x y H); simplbeq
    | [ H : ?x <> ?y, 
        H0 : context [(beq ?x ?y)] |- _ ] => 
      rewrite (neq_beq_false x y H) in H0; simplbeq

    | [ H : ?y <> ?x |- context [(beq ?x ?y)] ] => 
      rewrite (neq_beq_false x y (sym_not_eq H)); simplbeq
    | [ H : ?y <> ?x, 
        H0 : context [(beq ?x ?y)] |- _ ] => 
      rewrite (neq_beq_false x y (sym_not_eq H)) in H0; simplbeq
        
    | [H : ?x = ?x |- _ ] => clear H; simplbeq
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H
    | _ => idtac
  end.

Ltac decbeq x y :=
  let Hb := fresh "Hb" in
    (destruct (beq_dec x y) as [Hb | Hb]; simplbeq).

Ltac beq_elimH H := 
  match goal with

    | H : beq ?a ?b = true |- _ =>
        generalize (beq_true_eq a b H); clear H; intro H

    | H : beq ?a ?b = false |- _ =>
        generalize (beq_false_neq a b H); clear H; intro H

    | _ => fail 1 "not beq found"
  end.

Ltac beq_elim := 
  match goal with

    | H : beq ?a ?b = true |- _ =>
        generalize (beq_true_eq a b H); clear H; intro H; beq_elim

    | H : beq ?a ?b = false |- _ =>
        generalize (beq_false_neq a b H); clear H; intro H; beq_elim

    | _ => idtac
  end.

Ltac beq_intro := 
  match goal with

    | |- beq ?a ?b = true =>
        apply (eq_beq_true a b)

    | |- beq ?a ?b = false =>
        apply (neq_beq_false a b)

    | _ => fail 1 "the goal is not bnat"
  end.

Ltac beq_solve :=
  beq_elim; beq_intro; auto with arith.

Ltac beq_rewrite t :=
  match t with 
    | beq ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t); 
          [beq_solve | rewrite Hb; clear Hb])
    | _ =>
      match type of t with
        | beq ?x ?y = true => rewrite (beq_true_eq x y t)
        | _ => rewrite t
      end
  end.

Ltac beq_rewriteH t H :=
  match t with 
    | beq ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t); 
          [beq_solve | rewrite Hb in H; clear Hb])
    | _ =>
      match type of t with
        | beq ?x ?y = true => rewrite (beq_true_eq x y t) in H
        | _ => rewrite t in H
      end
  end.

Tactic Notation "rewb" constr (t) := beq_rewrite t.

Tactic Notation "rewb" constr (t) "in" hyp (H) := beq_rewrite t H.

Section TMAP.

Context `{A: Type}.
Context `{B: Type}.
Context `{BEq A}.
Context `{BZero B}.

Definition tmap :=  A -> B.

Definition tmap_emp : tmap := 
  fun _ => zero.

Definition tmap_sig (a : A) (b : B) := 
  fun a' => if beq a a' then b else zero.

(* Definition tmap_get (m : tmap) (a : A) := m a. *)

Definition tmap_upd (m : tmap) (a : A) (b : B) : tmap :=
  fun a' => if (beq a a') then b else m a. 

Lemma tmap_extensionality: forall (m1 m2 : tmap), 
  (forall a, m1 a = m2 a) -> m1 = m2.
Proof.
Admitted.

Lemma tmap_emp_zero : forall a,
    tmap_emp a = zero.
Proof.
  intros.
  unfold tmap_emp.
  trivial.
Qed.

Lemma tmap_get_upd_eq : forall (m : tmap) a v,
    (tmap_upd m a v) a = v.
Proof.
Admitted.

Lemma tmap_upd_m_eq : forall (m : tmap) a,
    (tmap_upd m a (m a)) = m.
Proof.
Admitted.

Lemma tmap_get_upd_eq2 : forall (m : tmap) a1 a2 v,
    beq a1 a2 = true
    -> (tmap_upd m a1 v) a2 = v.
Proof.
Admitted.

Lemma tmap_get_upd_ne : forall (m : tmap) a a' v,
    beq a a' = false
    ->  (tmap_upd m a v) a' = m a'.
Proof.
Admitted.

Lemma tmap_upd_upd_ne : forall (m : tmap) a a' v v',
    beq a a' = false 
    -> tmap_upd (tmap_upd m a v) a' v' = tmap_upd (tmap_upd m a' v') a v.
Proof.
Admitted.

Lemma tmap_upd_upd_eq : forall (m : tmap) a v v',
    tmap_upd (tmap_upd m a v) a v' = tmap_upd m a v'.
Proof.
Admitted.

Lemma tmap_upd_upd_eq2 : forall (m : tmap) a a' v v',
    beq a a' = true
    -> tmap_upd (tmap_upd m a v) a' v' = tmap_upd m a' v'.
Proof.
Admitted.

Hint Extern 1 => match goal with
                 | [ H : tmap_emp _ = _ |- _ ] =>
                   rewrite tmap_emp_zero in H; discriminate
                 end.

Hint Rewrite tmap_get_upd_eq tmap_get_upd_ne using congruence.

End TMAP.

Require Export Bool.

Ltac beq_destructH H pat := 
  let H0 := fresh "H" in
    (rename H into H0;
    match type of (H0) with
      | (andb ?a ?b = true) => 
        destruct (andb_prop a b H0) as pat; clear H0
      | (orb ?a ?b = true) =>
        destruct (orb_prop a b H0) as pat; clear H0
      | _ => fail "not destructable" 
    end).

Tactic Notation "desb" hyp (H) "as" simple_intropattern (pat) := beq_destructH H pat.

Ltac simplb := 
  match goal with

    (* beq rewrite directly *)
    | [H : negb ?x = true
       |- _ ] =>  apply (proj1 (negb_true_iff _)) in H; simplb

    | [H : negb ?x = false
       |- _ ] =>  apply (proj1 (negb_false_iff _)) in H; simplb

    | _ => idtac
  end.

Ltac tmap_simpl := 
  match goal with

    | [ |- context [(tmap_upd ?m ?a1 ?v) ?a1]] =>
      rewrite (tmap_get_upd_eq m a1 v); auto; tmap_simpl

    | [ H: context [(tmap_upd ?m ?a1 ?v) ?a1]
      |- _ ]=>
      rewrite (tmap_get_upd_eq m a1 v) in H; auto; tmap_simpl

    | [H : beq ?a1 ?a2 = true
       |- context [(tmap_upd ?m ?a1 ?v) ?a2]] =>
      rewrite (tmap_get_upd_eq2 m a1 a2 v); auto; tmap_simpl
    | [H : beq ?a2 ?a1 = true
       |- context [(tmap_upd ?m ?a1 ?v) ?a2]] =>
      rewrite (tmap_get_upd_eq2 m a1 a2 v (beq_sym a2 a1 H)); auto; tmap_simpl

    | [H : beq ?a1 ?a2 = true,
       H1: context [(tmap_upd ?m ?a1 ?v) ?a2]
      |- _ ]=>
      rewrite (tmap_get_upd_eq2 m a1 a2 v) in H1; auto; tmap_simpl
    | [H : beq ?a2 ?a1 = true,
       H1: context [(tmap_upd ?m ?a1 ?v) ?a2]
       |- _ ]=>
      rewrite (tmap_get_upd_eq2 m a1 a2 v (beq_sym a2 a1 H)) in H1; auto; tmap_simpl

    | [H : beq ?a1 ?a2 = false
       |- context [(tmap_upd ?m ?a1 ?v) ?a2]] =>
      rewrite (tmap_get_upd_ne m a1 a2 v H); auto; tmap_simpl
    | [H : beq ?a2 ?a1 = false
       |- context [(tmap_upd ?m ?a1 ?v) ?a2]] =>
      rewrite (tmap_get_upd_ne m a1 a2 v (beq_sym a2 a1 H)); auto; tmap_simpl

    | [H : beq ?a1 ?a2 = false,
       H1: context [(tmap_upd ?m ?a1 ?v) ?a2]
       |- _ ] =>
      rewrite (tmap_get_upd_ne m a1 a2 v H) in H1; auto; tmap_simpl
    | [H : beq ?a2 ?a1 = false,
       H1: context [(tmap_upd ?m ?a1 ?v) ?a2]
       |- _ ] =>
      rewrite (tmap_get_upd_ne m a1 a2 v (beq_sym a2 a1 H)) in H1; auto; tmap_simpl

(* upd_upd_eq *)
    | [H : beq ?a1 ?a2 = true
       |- context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a2 ?v2]] =>
      rewrite (tmap_upd_upd_eq2 m a1 a2 v1 v2 H); auto; tmap_simpl
    | [H : beq ?a2 ?a1 = true
       |- context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a2 ?v2]] =>
      rewrite (tmap_upd_upd_eq2 m a1 a2 v1 v2 (beq_sym a2 a1 H)); auto; tmap_simpl
    | [H : beq ?a1 ?a2 = true,
       H1: context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a2 ?v2]
      |- _ ]=>
      rewrite (tmap_upd_upd_eq2 m a1 a2 v1 v2) in H1; auto; tmap_simpl
    | [H : beq ?a2 ?a1 = true,
       H1: context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a2 ?v2]
       |- _ ]=>
      rewrite (tmap_upd_upd_eq2 m a1 a2 v1 v2 (beq_sym a2 a1 H)) in H1; auto; tmap_simpl
    | [ |- context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a1 ?v2]] =>
      rewrite (tmap_upd_upd_eq m a1 v1 v2); auto; tmap_simpl
    | [H : context [tmap_upd (tmap_upd ?m ?a1 ?v1) ?a1 ?v2]
      |- _ ]=>
      rewrite (tmap_upd_upd_eq m a1 v1 v2) in H; auto; tmap_simpl

(* upd_meq *)

    | [ |- context [tmap_upd ?m ?a (?m ?a)]] =>
      rewrite (tmap_upd_m_eq m a); auto; tmap_simpl
    | [ H : context [tmap_upd ?m ?a (?m ?a)]
        |- _ ] =>
      rewrite (tmap_upd_m_eq m a) in H; auto; tmap_simpl

(* tmap_emp *)
    | [ H : context [tmap_emp _ ] |- _ ] =>
      rewrite tmap_emp_zero in H; tmap_simpl

    | [ |- context [tmap_emp _ ] ] =>
      rewrite tmap_emp_zero; tmap_simpl

    | _ => idtac
  end. 

Tactic Notation "simpltm" := tmap_simpl.

Notation "$0" := (tmap_emp).

Notation "m $+ { k <- v }" := (tmap_upd m k v) (at level 50, left associativity).

Unset Implicit Arguments.
