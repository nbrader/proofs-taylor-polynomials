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
Require Import TaylorPolynomials.IteratedDifferentiation.
Require Import TaylorPolynomials.Lemmas.
Require Import TaylorPolynomials.Summation.
Require Import Psatz.

(*
    Return to IteratedDifferentiation.v when proven.
*)
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


(*
    Return to IteratedDifferentiation.v when proven.
*)
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
