Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.
Require Import Psatz.

Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.
Require Import CoqUtilLib.Iteration.

Require Import TaylorPolynomials.Differentiation.
Require Import TaylorPolynomials.Summation.
Require Import TaylorPolynomials.Lemmas.


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

Theorem nth_pow_greater_than_or_equal_to_deriv :
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
      assert (exists k, (S n - i)%nat = (k+1)%nat).
      {
        exists (n-i)%nat.
        lia.
      }
      destruct H as [k H].
      assert (k = (n-i)%nat) as k_implem by lia.
      rewrite H. clear H.
      rewrite D_homog.
      rewrite (nth_pow_deriv D linear_deriv D_product_rule).
      apply functional_extensionality.
      intros.
      replace (INR (fact (S n) / fact (k + 1)) * (INR (k + 1) * x ^ k)) with (INR (fact (S n) / fact k) * x ^ k).
      * rewrite k_implem. clear k_implem.
        rewrite Nat.sub_succ.
        reflexivity.
      * rewrite <- Rmult_assoc.
        rewrite <- mult_INR.
        replace (k + 1)%nat with (S k) by lia.
        rewrite (fact_simpl k).
        f_equal.
        f_equal.
        rewrite (Nat.mul_comm (fact (S n) / (S k * fact k)) (S k)).
        rewrite <- (Nat.Lcm0.divide_div_mul_exact (fact (S n)) (S k * fact k) (S k)).
        -- rewrite Nat.Div0.div_mul_cancel_l.
           ++ reflexivity.
           ++ rewrite k_implem. clear k_implem.
              apply Nat.neq_sym.
              apply O_S.
        -- rewrite <- (fact_simpl k).
           rewrite k_implem. clear k_implem.
           rewrite <- (Nat.sub_succ_l i n H0).
           assert (S n - i <= S n)%nat as H by lia.
           rewrite <- (split_factorial_le ((S n) - i) (S n) H).
           rewrite Nat.mul_comm.
           apply Nat.divide_factor_r.
Qed.

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

Theorem nth_pow_less_than_deriv :
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
  unfold gt in H.
  unfold lt in H.
  induction H.
  - simpl.
    rewrite (nth_pow_equal_deriv D linear_deriv D_homog D_product_rule).
    replace (INR (fact n)) with (INR (fact n) * 1) by ring.
    rewrite D_homog.
    rewrite unit_deriv.
    apply functional_extensionality.
    intros.
    ring.
  - simpl.
    rewrite IHle.
    simpl.
    replace (0) with (0 * 1) by ring.
    rewrite D_homog.
    apply functional_extensionality.
    intros.
    ring.
Qed.

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

Lemma iter_D_chain_of_linear :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_chain_rule : forall (f g : R -> R), D (fun x => f (g x)) = fun x => D f (g x) * D g x),

  forall (F : R -> R) (a : R),
  forall (n : nat),
    iter D n (fun x' : R => F (x' + a)) 0 = iter D n F a.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite Rplus_0_l.
    reflexivity.
  - admit.
    (* rewrite iter_expand_inner.
    simpl.
    rewrite IHn.
    rewrite (D_chain_of_linear D unit_deriv linear_deriv D_additive D_homog D_chain_rule F a). *)
Admitted.

Lemma iter_D_chain_of_linear_example :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (D_chain_rule : forall (f g : R -> R), D (fun x => f (g x)) = fun x => D f (g x) * D g x),

  exists (F : R -> R) (a : R),
  exists (n : nat),
    iter D n (fun x' : R => F (x' + a)) 0 = iter D n F a.
Proof.
  intros.
  exists (fun x => x^3).
  exists 10.
  exists 2%nat.
  unfold iter.
  rewrite (D_chain_rule (fun x => x^3) (fun x => x + 10)).
  replace (0 + 10) with 10 by ring.
  replace 3%nat with (2+1)%nat by ring.
  rewrite D_additive.
  rewrite linear_deriv.
  replace 10 with (10*1) by ring.
  rewrite D_homog.
  rewrite unit_deriv.
  rewrite (nth_pow_deriv D linear_deriv D_product_rule).
  rewrite D_product_rule.
  rewrite D_product_rule.
  rewrite D_product_rule.
  replace 2%nat with (1+1)%nat by ring.
  rewrite (nth_pow_deriv D linear_deriv D_product_rule).
  replace (INR (1 + 1 + 1)) with (INR (1 + 1 + 1) * 1) by ring.
  rewrite D_homog.
  rewrite unit_deriv.
  rewrite D_additive.
  rewrite D_product_rule.
  rewrite (D_chain_rule (fun x => x^(1+1)) (fun x => x + 10 * 1)).
  rewrite D_additive.
  rewrite D_product_rule.
  rewrite (nth_pow_deriv D linear_deriv D_product_rule).
  rewrite unit_deriv.
  rewrite linear_deriv.
  replace 10 with (10*1) by ring.
  rewrite D_homog.
  rewrite unit_deriv.
  replace 0 with (0*1) by ring.
  rewrite D_homog.
  rewrite unit_deriv.
  ring.
Qed.
