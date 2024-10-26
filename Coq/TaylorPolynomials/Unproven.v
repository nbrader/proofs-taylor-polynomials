Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
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
Require Import TaylorPolynomials.Product.
Require Import Psatz.
Require Import Lia.

(*
    Return to Lemmas.v when proven.
*)
Lemma fact_product_equiv : forall (i : nat), fact i = product_nat (fun x => S x) i.
Proof.
  intros.
  induction i.
  - simpl.
    reflexivity.
  - replace (fact (S i)) with ((S i) * fact i)%nat by (simpl; reflexivity).
    rewrite IHi. clear IHi.
    reflexivity.
Qed.

Lemma neq_implies_gt_or_lt (x y : nat) : (x <> y)%nat -> (x > y)%nat \/ (y > x)%nat.
Proof.
  lia.
Qed.

(*
    Return to Lemmas.v when proven.
*)
Lemma split_factorial : forall (i m : nat), (i < m)%nat -> ((fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m).
Proof.
  intros.
  rewrite !fact_product_equiv.
  induction i, m.
  - reflexivity.
  - simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - inversion H.
  - apply le_S in H.
    apply le_S_n in H.
    apply IHi in H as H2. clear IHi.
    rewrite <- H2.
    rewrite product_nat_expand_upper at 1.
    rewrite (Nat.mul_comm (S i) (product_nat (fun x : nat => S x) i)).
    rewrite <- Nat.mul_assoc.
    f_equal.
    replace (S m - i)%nat with (S (S m - S i)).
    + rewrite product_nat_expand_lower at 1.
      replace (i + 1)%nat with (S i) by lia.
      rewrite Nat.mul_comm.
      replace (fun x : nat => (S i + S x)%nat) with (fun i0 : nat => (i + S (S i0))%nat).
      -- reflexivity.
      -- apply functional_extensionality.
         intros.
         lia.
    + destruct i.
      * simpl.
        rewrite Nat.sub_0_r.
        reflexivity.
      * apply le_S_n in H.
        simpl.
        rewrite Nat.sub_succ_r.
        rewrite Nat.succ_pred.
        --reflexivity.
        --lia.
Qed.

Lemma split_factorial_2 : forall (i m : nat), (i = m)%nat -> ((fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m).
Proof.
  intros.
  rewrite !fact_product_equiv.
  rewrite H.
  induction m.
  - reflexivity.
  - simpl.
    admit.
Admitted.

Lemma split_factorial_3 : forall (i m : nat), (i <= m)%nat -> ((fact i * product_nat (fun x => i + S x) (m-i))%nat = fact m).
Proof.
    admit.
Admitted.

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
           rewrite <- (split_factorial_3 ((S n) - i) (S n) H).
           rewrite Nat.mul_comm.
           apply Nat.divide_factor_r.
Qed.


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
  (* Use le_equiv and a new lemma for splitting iteration into two applied after each other to reduce this to the above lemmas of nth_pow_lesser_deriv and nth_pow_equal_deriv *)

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
