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

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (order : nat),
    forall (f g : R -> R), iter D order (fun x => f x + g x) = fun x => iter D order f x + iter D order g x.
Proof.
  intros D D_additive order f g.
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

(* Theorem nth_pow_lesser_deriv : *)
(*
    Find this in Unproven.v

    Return here when proven.
*)

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

(* Theorem nth_pow_greater_deriv : *)
(*
    Find this in Unproven.v

    Return here when proven.
*)

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
    rewrite (iter_D_additive D D_additive order).
    reflexivity.
Qed.
