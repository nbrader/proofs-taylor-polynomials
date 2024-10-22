Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.
Require Import CoqUtilLib.Iteration.

Require Import TaylorPolynomials.Differentiation.
Require Import TaylorPolynomials.Summation.
Require Import TaylorPolynomials.Unproven.


Lemma iter_additive : forall (D : (R -> R) -> (R -> R)),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (f g : R -> R) (n : nat),
    iter D n (fun x => f x + g x) = fun x => iter D n f x + iter D n g x.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- (D_additive (iter D n f) (iter D n g)).
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma iter_homog : forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (f : R -> R) (s : R) (n : nat),
    iter D n (fun x => s * f x) = fun x => s * iter D n f x.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- (D_homog (iter D n f) s).
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma iter_expand_inner : forall (D : (R -> R) -> (R -> R)),
  forall (f : R -> R) (n : nat),
  iter D (S n) f = iter D n (D f).
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl in *.
    rewrite IHn.
    reflexivity.
Qed.

Lemma iter_D_additive :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (order : nat),
    forall (f g : R -> R), iter D order (fun x => f x + g x) = fun x => iter D order f x + iter D order g x.
Proof.
  intros D D_additive D_homog order f g.
  induction order.
  - reflexivity.
  - simpl.
    rewrite <- (D_additive (iter D order f) (iter D order g)).
    rewrite <- IHorder.
    reflexivity.
Qed.

Lemma iter_D_homog :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (order : nat),
    forall (f : R -> R), forall (s : R), iter D order (fun x => s * f x) = fun x => s * iter D order f x.
Proof.
  intros D D_homog order f s.
  induction order.
  - reflexivity.
  - simpl.
    rewrite <- (D_homog (iter D order f) s).
    rewrite <- IHorder.
    reflexivity.
Qed.

Lemma zero_nth_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (n : nat),
  forall (x : R), iter D (n+1) (fun _ => 0) x = (fun _ => 0) x.
Proof.
  intros.
  replace (0) with (0*1) by field.
  rewrite (iter_D_homog D D_homog (n+1) (fun _ => 1) 0).
  field.
Qed.

Lemma zero_nth_deriv_extensional :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (n : nat),
  iter D (n+1) (fun _ => 0) = (fun _ => 0).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply (zero_nth_deriv D D_homog).
Qed.

Theorem nth_pow_lesser_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n i : nat), (i < n)%nat -> iter D i (fun x => x^n) = fun x => INR (fact n) / INR (fact (n-i)) * x^(n-i).
Proof.
  intros.
  destruct n.
  - inversion H.
  - induction i.
    + simpl.
      rewrite Nat.add_comm.
      rewrite Nat.mul_comm.
      rewrite mult_n_Sm.
      apply functional_extensionality.
      intros.
      replace (INR (fact n * S n) / INR (fact n * S n)) with (INR 1).
      * simpl.
        ring.
      * unfold Rdiv.
        rewrite Rinv_r.
        -- reflexivity.
        -- assert ((0 < fact n)%nat).
           {
             induction n.
             - simpl.
               auto.
             - simpl.
               assert ((0 < S n)%nat).
               {
                 unfold lt.
                 apply le_n_S.
                 apply Nat.le_0_l.
               }
               specialize (IHn H0). clear H0.
               
               unfold lt in *.

               apply le_equiv.
               apply le_equiv in IHn.
               destruct IHn.
               
               rewrite <- H0.
               simpl.
               exists ((x0 + n * S x0)%nat).
               reflexivity.
           }
           admit.
    + simpl.
      admit.
      
      (* assert (i = O).
      {
        rewrite Nat.lt_succ_r in H.
        apply (max_r i O) in H.
        rewrite max_i_0 in H.
        apply H.
      }
      clear H.
      rewrite H0. clear H0.

      simpl.
      apply functional_extensionality.
      intros.
      field.
    + unfold lt in H.
      apply le_S_n in H.
    
      replace (fun x : R => x ^ 1) with (fun x : R => x) by (apply functional_extensionality; intros; ring).
    rewrite iter_expand_inner.
    replace (fun x : R => x ^ S n) with (fun x : R => x ^ (n+1)%nat) by (apply functional_extensionality; intros; rewrite Nat.add_1_r; reflexivity).
    rewrite (nth_pow_deriv D linear_deriv D_product_rule).
    rewrite (iter_D_homog D D_homog).
    rewrite IHn.
    simpl.
    rewrite plus_INR.
    rewrite plus_INR.
    rewrite mult_INR.
    rewrite Rmult_plus_distr_r.
    simpl (INR 1).
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    reflexivity. *)
Admitted.

Theorem nth_pow_equal_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n : nat), iter D n (fun x => x^n) = fun _ => INR (fact n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite iter_expand_inner.
    replace (fun x : R => x ^ S n) with (fun x : R => x ^ (n+1)%nat) by (apply functional_extensionality; intros; rewrite Nat.add_1_r; reflexivity).
    rewrite (nth_pow_deriv D linear_deriv D_product_rule).
    rewrite (iter_D_homog D D_homog).
    rewrite IHn.
    simpl.
    rewrite plus_INR.
    rewrite plus_INR.
    rewrite mult_INR.
    rewrite Rmult_plus_distr_r.
    simpl (INR 1).
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    reflexivity.
Qed.

Theorem nth_pow_greater_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n i : nat), (i > n)%nat -> iter D i (fun x => x^n) = fun _ => 0.
Proof.
  intros.
  (* Use le_equiv and a new lemma for splitting and iteration into two applied after each other to reduce this to the above lemmas of nth_pow_lesser_deriv and nth_pow_equal_deriv *)

  (* intros D unit_deriv linear_deriv D_additive D_homog D_product_rule n i i_gt_n.



  assert (forall i : nat, (i > n)%nat -> exists j : nat, i = S j).
  {
    intros.
    destruct i0.
    - inversion H.
    - exists i0. reflexivity.
  }
  apply H in i_gt_n as H0. clear H.
  destruct H0 as [j H].

  rewrite H.
  induction i.
  - inversion H.
  - 



  induction n.
  - rewrite iter_expand_inner.
    simpl.
    rewrite unit_deriv.
    replace (fun _ : R => 0) with (fun _ : R => 0*0) by (apply functional_extensionality; intros; ring).
    rewrite (iter_D_homog D D_homog).
    apply functional_extensionality.
    intros.
    ring.
  - rewrite iter_expand_inner.
    replace (fun x : R => x ^ S n) with (fun x : R => x ^ (n+1)%nat) by (apply functional_extensionality; intros; rewrite Nat.add_1_r; reflexivity).
    rewrite (nth_pow_deriv D linear_deriv D_product_rule n).
    rewrite (iter_D_homog D D_homog). *)
Admitted.

Lemma iter_D_additive_over_summation :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (degree order : nat) (F_ : nat -> R -> R) (x : R),
    iter D order (summation F_ degree) x = summation (fun i => iter D order (F_ i)) degree x.
Proof.
  intros D D_additive D_homog degree order F x.
  simpl.
  induction degree as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl.
    replace (0) with (0*1) by field.
    rewrite (iter_D_homog D D_homog order (fun _ => 1) 0).
    field.
  
  - (* Inductive step: n -> S n *)
    simpl.
    rewrite <- IH.
    rewrite (iter_D_additive D D_additive D_homog order).
    reflexivity.
Qed.
