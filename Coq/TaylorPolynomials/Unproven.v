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
Search fact.
(*
    Return to IteratedDifferentiation.v when proven.
*)
Theorem nth_pow_less_or_equal_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n i : nat), (i <= n)%nat -> iter D i (fun x => x^n) = fun x => INR (fact n / fact (n-i)) * x^(n-i).
Proof.
  intros.
  induction i.
  - simpl in *.
    apply functional_extensionality.
    intros.
    replace (n - 0)%nat with n by lia.
    replace (x ^ n) with (1 * (x ^ n)) at 1 by ring.
    f_equal.
    rewrite Nat.div_same by apply fact_neq_0.
    reflexivity.
  - destruct n.
    + inversion H.
    + assert (i <= n)%nat by lia.
      clear H.
      assert (i <= S n)%nat by lia.
      apply IHi in H. clear IHi.
      replace (iter D (S i) (fun x : R => x ^ S n)) with (D (iter D i (fun x : R => x ^ S n))) by reflexivity.
      rewrite H. clear H.
      replace (S n) with (n+1)%nat by ring.

      (* rewrite (nth_pow_deriv D linear_deriv D_product_rule). *)
      
      admit.
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
