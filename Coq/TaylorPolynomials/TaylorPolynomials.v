(*

This project serves as a way for me to practice proving theorms in Coq.
For a much better library which proves Taylor's Thoerem, see the following:
  http://coquelicot.saclay.inria.fr/html/Coquelicot.Derive.html

*)

Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Rfunctions.
Require Import Psatz.
Import ListNotations.
Open Scope R_scope.

Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.
Require Import CoqUtilLib.Iteration.

Require Import FreeMonoid.MonoidFree.
Require Import FreeMonoid.StructMonoid.

Require Import TaylorPolynomials.Combinatorics.
Require Import TaylorPolynomials.Differentiation.
Require Import TaylorPolynomials.Integration.
Require Import TaylorPolynomials.IteratedDifferentiation.
Require Import TaylorPolynomials.Lemmas.
Require Import TaylorPolynomials.Summation.


(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Taylor_0_implem :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (*
    Given the above then Taylor 1%nat a F must have this implementation: fun x => (D F a)*(x-a) + F a
  *)
  forall (F : R -> R), forall (a : R), Taylor 0%nat a F = fun (x : R) => F a.
Proof.
  intros.
  
  assert (Taylor_0_deriv_is_0 : forall (a : R) (F : R -> R), D (Taylor 0%nat a F) = fun x => 0).
  {
    intros.
    specialize (Taylor_degree 0%nat a0 F0).
    simpl in Taylor_degree.
    apply Taylor_degree.
  }

  assert (Taylor_agrees_at_a_1a : forall (a : R) (F : R -> R), iter D 0 (Taylor 0%nat a F) a = iter D 0 F a) by (intros; apply (Taylor_agrees_at_a 0%nat 0%nat a0 F0 (Nat.le_refl 0%nat))).
  assert (Taylor_agrees_at_a_1b : forall (a : R) (F : R -> R), Taylor 0%nat a F a = F a) by auto.
  assert (Taylor_agrees_at_a_1c : forall (a : R) (F : R -> R), iter D 0 (Taylor 1%nat a F) a = F a) by auto.
  assert (Taylor_1_equals_F_at_a : forall (a : R) (F : R -> R), Taylor 1%nat a F a = F a) by (apply Taylor_agrees_at_a_1c). clear Taylor_agrees_at_a_1a Taylor_agrees_at_a_1c.

  apply (zero_integral (Taylor 0%nat a F)) in Taylor_0_deriv_is_0. clear zero_integral.
  destruct Taylor_0_deriv_is_0 as [x Taylor_0_is_c].
  assert (linear_coeff_def_is_F_a : Taylor 0%nat a F a = x) by (rewrite Taylor_0_is_c; reflexivity).
  rewrite Taylor_agrees_at_a_1b in linear_coeff_def_is_F_a. clear Taylor_agrees_at_a_1b.
  rewrite <- linear_coeff_def_is_F_a in Taylor_0_is_c. clear linear_coeff_def_is_F_a.
  apply Taylor_0_is_c.
Qed.

(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Taylor_1_implem :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (*
    Given the above then Taylor 1%nat a F must have this implementation: fun x => (D F a)*(x-a) + F a
  *)
  forall (F : R -> R), forall (a : R), Taylor 1%nat a F = fun x => (D F a)*(x-a) + F a.
Proof.
  (* intros Taylor D
         zero_integral constant_integral
         Taylor_1_second_deriv_is_0
         Taylor_1_equals_F_at_a
         Taylor_1_deriv_equals_F_deriv_at_a
         F a. *)
  intros.
  (*
    Givens:
      lin_f''(x) = 0
      lin_f(a) = f(a)
      lin_f'(a) = f'(a)
  *)

  assert (Taylor_1_second_deriv_is_0 : forall (a : R) (F : R -> R), D (D (Taylor 1%nat a F)) = fun x => 0).
  {
    intros.
    specialize (Taylor_degree 1%nat a0 F0).
    simpl in Taylor_degree.
    apply Taylor_degree.
  }

  assert (Taylor_agrees_at_a_1a : forall (a : R) (F : R -> R), iter D 0 (Taylor 0%nat a F) a = iter D 0 F a) by (intros; apply (Taylor_agrees_at_a 0%nat 0%nat a0 F0 (Nat.le_refl 0%nat))).
  assert (Taylor_agrees_at_a_1b : forall (a : R) (F : R -> R), iter D 0 (Taylor 1%nat a F) a = F a) by auto.
  assert (Taylor_1_equals_F_at_a : forall (a : R) (F : R -> R), Taylor 1%nat a F a = F a) by (apply Taylor_agrees_at_a_1b). clear Taylor_agrees_at_a_1a Taylor_agrees_at_a_1b.

  assert (Taylor_agrees_at_a_2a : forall (a : R) (F : R -> R), iter D 1 (Taylor 1%nat a F) a = iter D 1 F a) by (intros; apply (Taylor_agrees_at_a 1%nat 1%nat a0 F0 (Nat.le_refl 1%nat))).
  assert (Taylor_agrees_at_a_2b : forall (a : R) (F : R -> R), iter D 1 (Taylor 1%nat a F) a = D F a) by auto.
  assert (Taylor_1_deriv_equals_F_deriv_at_a : forall (a : R) (F : R -> R), D (Taylor 1%nat a F) a = D F a) by (apply Taylor_agrees_at_a_2b). clear Taylor_agrees_at_a_2a Taylor_agrees_at_a_2b.

  apply (zero_integral (D (Taylor 1%nat a F))) in Taylor_1_second_deriv_is_0. clear zero_integral.
  destruct Taylor_1_second_deriv_is_0 as [x first_deriv_Taylor_1_is_c].
  assert (linear_coeff_def_is_D_F_a : D (Taylor 1%nat a F) a = x) by (rewrite first_deriv_Taylor_1_is_c; reflexivity).
  rewrite Taylor_1_deriv_equals_F_deriv_at_a in linear_coeff_def_is_D_F_a. clear Taylor_1_deriv_equals_F_deriv_at_a.
  (*
    Given
      lin_f''(x) = 0
      zero_integral
    then
      lin_f'(x) = c
  *)
  
  (*
    Given
      lin_f'(x) = c
      lin_f'(a) = f'(a)
    then
      c = f'(a)
  *)

  apply (constant_integral (Taylor 1%nat a F) x) in first_deriv_Taylor_1_is_c. clear constant_integral.
  destruct first_deriv_Taylor_1_is_c as [x0 Taylor_1_def].
  assert (algebra_1 : Taylor 1%nat a F a = x * a + x0) by (rewrite Taylor_1_def; reflexivity).
  rewrite Taylor_1_equals_F_at_a in algebra_1. clear Taylor_1_equals_F_at_a.
  rewrite <- linear_coeff_def_is_D_F_a in algebra_1.
  assert (constant_term_def : x0 = F a - (D F a) * a) by (rewrite algebra_1; ring). clear algebra_1.
  (*
    Given
      lin_f'(x) = c
      constant_integral
    then
      lin_f(x) = c*x + c'
  *)
  
  (*
    Given
      lin_f(x) = c*x + c'
      c = f'(a)
      lin_f(a) = f(a)
    then
      c' = f(a) - f'(a) * a
  *)

  rewrite constant_term_def in Taylor_1_def. clear constant_term_def.
  rewrite <- linear_coeff_def_is_D_F_a in Taylor_1_def. clear linear_coeff_def_is_D_F_a.
  assert (algebra_2 : ((fun x : R => D F a * x + (F a - D F a * a)) = (fun x : R => D F a * (x - a) + F a))) by (apply functional_extensionality; intros; ring).
  rewrite algebra_2 in Taylor_1_def. clear algebra_2.
  (*
    Given
      lin_f(x) = c*x + c'
      c = f'(a)
      c' = f(a) - f'(a) * a
    Then:
      lin_f(x) = f'(a)*(x-a) + f(a)
  *)

  apply Taylor_1_def.
Qed.

Theorem Maclaurin_implem :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (n : nat),
    Taylor n 0 F = summation (fun k x' => (iter D k F 0 / INR (fact k)) * x' ^ k) (S n).
Proof.
  intros.
  apply (nth_integral_of_zero D constant_integral D_additive D_homog D_product_rule integration_constant (S n) (Taylor n 0 F)) in Taylor_degree.
  destruct Taylor_degree as [c Taylor_degree].
  specialize Taylor_agrees_at_a with (degree:=n) (a:=0) (F:=F) as Taylor_agrees_at_0. clear Taylor_agrees_at_a.
  rewrite Taylor_degree in *. clear Taylor_degree.

  apply summation_irrelevance_of_large_coeffs.
  intros i max_i_is_n.
  specialize (Taylor_agrees_at_0 i).
  
  assert (c_implem : c i = iter D i F 0 / INR (fact i)).
  {
    rewrite (iter_D_additive_over_summation D D_additive D_homog) in Taylor_agrees_at_0.
    apply Taylor_agrees_at_0 in max_i_is_n as ith_deriv. clear Taylor_agrees_at_0.
    replace (fun i0 : nat => iter D i (fun x' : R => c i0 * x' ^ i0)) with (fun i0 : nat => fun x : R => c i0 * iter D i (fun x' : R => x' ^ i0) x) in ith_deriv by (apply functional_extensionality; intros; rewrite (iter_D_homog D D_homog); reflexivity).
    rewrite <- ith_deriv. clear ith_deriv.

    rewrite summation_app.
    assert (S i <= S n)%nat.
    {
      apply le_n_S in max_i_is_n.
      apply max_i_is_n.
    }
    rewrite (split_summation_R (fun i0 : nat => c i0 * iter D i (fun x' : R => x' ^ i0) 0) (S i) (S n) H). clear H.

    replace (S n - S i)%nat with (n - i)%nat by auto.
    assert (summation_R (fun j : nat => c (j + S i)%nat * iter D i (fun x' : R => x' ^ (j + S i)) 0) (n - i) = 0).
    {
      assert (summation_R (fun j : nat => c (j + S i)%nat * iter D i (fun x' : R => x' ^ (j + S i)) 0) (n - i) = summation_R (fun _ : nat => 0) (n - i)).
      {
        case (n - i)%nat.
        - reflexivity.
        - intros.
          apply (summation_R_irrelevance_of_large_coeffs n0 (fun j : nat => c (j + S i)%nat * iter D i (fun x' : R => x' ^ (j + S i)) 0) (fun _ : nat => 0)).
          intros.

          assert (i <= i0 + S i)%nat.
          {
            rewrite <- Nat.add_succ_comm.
            apply Nat.le_add_l.
          }
          
          pose proof (nth_pow_greater_than_or_equal_to_deriv D linear_deriv D_homog D_product_rule (i0 + S i) i) as nth_pow_greater_than_or_equal_to_deriv.
          rewrite (nth_pow_greater_than_or_equal_to_deriv H0).
          assert (0 ^ (i0 + S i - i) = 0).
          {
            assert (exists c : nat, (i0 + S i - i)%nat = S c).
            {
              exists i0.
              assert ((S i - i)%nat = S O) as succ_i_minus_i_is_1.
              {
                rewrite Nat.sub_succ_l.
                - rewrite Nat.sub_diag.
                  reflexivity.
                - apply Nat.le_refl.
              }
              rewrite <- Nat.add_sub_assoc by apply Nat.le_succ_diag_r.
              rewrite succ_i_minus_i_is_1 by apply le_n_S.
              ring.
            }
            destruct H1.
            rewrite H1. clear H1.
            simpl.
            ring.
          }
          rewrite H1.
          ring.
      }
      rewrite H. clear H.
      apply summation_n_zeros.
    }
    rewrite H. clear H.
    rewrite Rplus_0_l.

    rewrite (split_summation_R (fun i0 : nat => c i0 * iter D i (fun x' : R => x' ^ i0) 0) i (S i) (Nat.le_succ_diag_r i)).

    assert (summation_R (fun i0 : nat => c i0 * iter D i (fun x' : R => x' ^ i0) 0) i = 0).
    {
      assert (summation_R (fun i0 : nat => c i0 * iter D i (fun x' : R => x' ^ i0) 0) i = summation_R (fun _ : nat => 0) i).
      {
        case i.
        - reflexivity.
        - intros.
          apply (summation_R_irrelevance_of_large_coeffs n0 (fun i0 : nat => c i0 * iter D (S n0) (fun x' : R => x' ^ i0) 0) (fun _ : nat => 0)).
          intros.

          assert (S n0 > i0)%nat.
          {
            unfold gt.
            unfold lt.
            apply le_n_S.
            apply H.
          }
          
          pose proof (nth_pow_less_than_deriv D unit_deriv linear_deriv D_additive D_homog D_product_rule i0 (S n0)) as nth_pow_less_than_deriv.
          rewrite (nth_pow_less_than_deriv H0).
          ring.
      }
      rewrite H. clear H.
      apply summation_n_zeros.
    }
    rewrite H. clear H.
    rewrite Rplus_0_r.

    assert (summation_R (fun j : nat => c (j + i)%nat * iter D i (fun x' : R => x' ^ (j + i)) 0) (S i - i) = INR (fact i) * c i).
    {
      assert ((S i - i)%nat = S O) as succ_i_minus_i_is_1.
      {
        rewrite Nat.sub_succ_l.
        - rewrite Nat.sub_diag.
          reflexivity.
        - apply Nat.le_refl.
      }
      rewrite succ_i_minus_i_is_1. clear succ_i_minus_i_is_1.
      simpl.
      pose proof (nth_pow_equal_deriv D linear_deriv D_homog D_product_rule) as nth_pow_equal_deriv.
      rewrite nth_pow_equal_deriv.
      ring.
    }
    rewrite H. clear H.
    field.
    apply not_0_INR.
    apply fact_neq_0.
  }
  rewrite c_implem by apply H.
  reflexivity.
Qed.

Theorem Taylor_nth :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (n : nat) (a : R) (F : R -> R), exists c_ : nat -> R, Taylor n a F = summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) (S n).
Proof.
  intros.
  pose proof (nth_integral_of_zero D constant_integral D_additive D_homog D_product_rule integration_constant).
  apply H.
  apply Taylor_degree.
Qed.

(* pascal_step2 *)
(* pascal_step3 *)
(* simpl_fact *)

Theorem Taylor_a_equiv :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (D_chain_rule : forall (f g : R -> R), D (fun x => f (g x)) = fun x => D f (g x) * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (n : nat) (a : R) (F : R -> R), Taylor n a F = fun x => Taylor n 0 (fun x' => F (x'+a)) (x-a).
Proof.
  intros.
  
  specialize (Taylor_nth Taylor D constant_integral D_additive D_homog D_product_rule integration_constant Taylor_degree) with (n := n) (a := a) (F := F) as Taylor_nth_1.
  destruct Taylor_nth_1 as [c1_ Taylor_nth_1].
  specialize (Taylor_nth Taylor D constant_integral D_additive D_homog D_product_rule integration_constant Taylor_degree) with (n := n) (a := 0) (F := (fun x' : R => F (x' + a))) as Taylor_nth_2.
  destruct Taylor_nth_2 as [c2_ Taylor_nth_2].

  rewrite Taylor_nth_1.
  rewrite Taylor_nth_2.

  apply functional_extensionality.
  intros.

  specialize Taylor_agrees_at_a with (degree := n) (order := n) (a := a) (F := F) as Taylor_agrees_at_a_1.
  specialize (Taylor_agrees_at_a_1 (Nat.le_refl n)).
  simpl in Taylor_agrees_at_a_1.
  rewrite Taylor_nth_1 in Taylor_agrees_at_a_1. clear Taylor_nth_1.

  specialize Taylor_agrees_at_a with (degree := n) (order := n) (a := 0) (F := (fun x' : R => F (x' + a))) as Taylor_agrees_at_a_2.
  specialize (Taylor_agrees_at_a_2 (Nat.le_refl n)).
  simpl in Taylor_agrees_at_a_2.
  rewrite Taylor_nth_2 in Taylor_agrees_at_a_2. clear Taylor_nth_2.

  rewrite    (summation_app (fun (i : nat) (x' : R) => c2_ i *  x'      ^ i)).
  rewrite <- (summation_app (fun (i : nat) (x' : R) => c2_ i * (x' - a) ^ i)).

  assert (c1_ = fun j => summation_R_from_and_to (fun i : nat => (iter D i F a / INR (fact i)) * INR (from_n_choose_k i j) * (-a) ^ (i-j)) j n).
  {
    admit.
  }

  assert (c2_ = fun i => iter D i F a / INR (fact i)).
  {
    admit.
  }

  rewrite H.
  rewrite H0.

  assert (exists (n : nat), summation (fun (i : nat) (x' : R) => summation_R_from_and_to (fun i0 : nat => iter D i0 F a / INR (fact i0) * INR (from_n_choose_k i0 i) * (- a) ^ (i0 - i)) i n * x' ^ i) (S n) x = summation (fun (i : nat) (x' : R) => iter D i F a / INR (fact i) * (x' - a) ^ i) (S n) x).
  {
      exists 4%nat.
      unfold summation_R_from_and_to.
      simpl.
      ring.
  }

  unfold summation_R_from_and_to.
  rewrite summation_app.
  rewrite summation_app.
  unfold from_n_choose_k.
  simpl.
  replace (n - n + 1)%nat with 1%nat by (rewrite Nat.sub_diag; ring).
  replace (fun i : nat => iter D (n + i) F a / INR (fact (n + i)) * INR (fact (n + i) / (fact n * fact (n + i - n))) * (- a) ^ (n + i - n)) with (fun i : nat => iter D (n + i) F a / INR (fact (n + i)) * INR (fact (n + i) / (fact n * fact i)) * (- a) ^ i).
  + replace (summation_R (fun i : nat => iter D (n + i) F a / INR (fact (n + i)) * INR (fact (n + i) / (fact n * fact i)) * (- a) ^ i) 1) with (summation_R (fun i : nat => (iter D (n + i) F a / INR (fact n * fact i)) * (- a) ^ i) 1).
    - replace (fun i : nat => summation_R (fun i0 : nat => iter D (i + i0) F a / INR (fact (i + i0)) * INR (fact (i + i0) / (fact i * fact (i + i0 - i))) * (- a) ^ (i + i0 - i)) (n - i + 1) * x ^ i) with (fun i : nat => summation_R (fun i0 : nat => iter D (i + i0) F a / INR (fact i * fact i0) * (- a) ^ i0) (n - i + 1) * x ^ i).
      * simpl.
        rewrite Nat.add_0_r.
        rewrite Rplus_0_r.
        rewrite Rmult_1_r.
        rewrite Nat.mul_1_r.
        admit.
      * apply functional_extensionality.
        intros.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros.
        replace (x0 + x1 - x0)%nat with x1%nat by (rewrite Nat.add_comm; rewrite <- (Nat.add_sub_assoc x1 x0 x0 (Nat.le_refl x0)); rewrite Nat.sub_diag; ring).
        f_equal.
        rewrite Rdiv_def.
        rewrite Rdiv_def.
        rewrite Rmult_assoc.
        f_equal.
        rewrite Rmult_comm.
        rewrite <- Rdiv_def.

        (*
        Goal: / INR (fact x0 * fact x1) = INR (fact (x0 + x1) / (fact x0 * fact x1)) / INR (fact (x0 + x1))

        This would be easily proven if we weren't dealing with division of natural numbers.
        *)

        induction x0, x1.
        -- simpl.
           field.
        -- simpl (fact 0).
           rewrite Nat.mul_1_l.
           rewrite Nat.add_0_l.
           rewrite (Nat.div_same (fact (S x1)) (fact_neq_0 (S x1))).
           rewrite INR_1.
           rewrite Rdiv_1_l.
           reflexivity.
        -- simpl (fact 0).
           rewrite Nat.mul_1_r.
           rewrite Nat.add_0_r.
           rewrite (Nat.div_same (fact (S x0)) (fact_neq_0 (S x0))).
           rewrite INR_1.
           rewrite Rdiv_1_l.
           reflexivity.
        -- replace (fact (S x0 + S x1)) with (S (x0 + S x1) * fact (x0 + S x1))%nat by (rewrite Nat.add_succ_l; rewrite fact_simpl; reflexivity).
           rewrite mult_INR.
           rewrite mult_INR.
           rewrite Nat.Lcm0.divide_div_mul_exact.
           ** rewrite mult_INR.
              rewrite Rdiv_mult_l_l by (apply not_0_INR; apply not_eq_sym; apply O_S).
              replace (INR (fact (x0 + S x1) / (fact (S x0) * fact (S x1))) / INR (fact (x0 + S x1))) with ((INR (fact (x0 + S x1) / (fact x0 * fact (S x1))) / INR (fact (x0 + S x1))) * / INR (S x0)).
              --- rewrite <- IHx0.
                  assert (fact_S : forall n : nat, fact (S n) = ((S n) * fact n)%nat) by (simpl; reflexivity).
                  rewrite fact_S.
                  rewrite <- Rinv_mult.
                  rewrite <- mult_INR.
                  rewrite <- mult_INR.
                  rewrite <- (Nat.mul_assoc (fact x0) (fact (S x1)) (S x0)).
                  rewrite (Nat.mul_comm (fact (S x1)) (S x0)).
                  rewrite (Nat.mul_assoc (fact x0) (S x0) (fact (S x1))).
                  rewrite (Nat.mul_comm (fact x0) (S x0)).
                  reflexivity.
              --- replace (fact (S x0) * fact (S x1))%nat with ((S x0) * fact x0 * fact (S x1))%nat by (simpl; reflexivity).
                  replace (fact (x0 + S x1) / (S x0 * fact x0 * fact (S x1)))%nat with (fact (x0 + S x1) / (fact x0 * fact (S x1)) / S x0)%nat.
                  *** admit.
                  *** admit.
           ** induction x0, x1.
              --- simpl.
                  exists 1%nat.
                  reflexivity.
              --- exists 1%nat.
                  simpl (fact 1).
                  rewrite Nat.mul_1_l.
                  rewrite Nat.mul_1_l.
                  rewrite Nat.add_0_l.
                  reflexivity.
              --- exists 1%nat.
                  simpl (fact 1).
                  rewrite Nat.mul_1_l.
                  rewrite Nat.mul_1_r.
                  rewrite Nat.add_1_r.
                  reflexivity.
              --- admit.
           (* rewrite <- Nat.Div0.div_mul_cancel_l. *)

        (* rewrite <- (split_factorial_le x0 (x0 + x1) (Nat.le_add_r x0 x1)).
        replace (x0 + x1 - x0)%nat with x1 by (rewrite Nat.add_comm; rewrite <- (Nat.add_sub_assoc x1 x0 x0 (Nat.le_refl x0)); rewrite Nat.sub_diag; ring). *)


        (* Search fact.

        rewrite Rinv_div.
        fold (Rdiv (fact x0 * fact x1) (INR (fact (x0 + x1)))).
        Search Rinv.
        rewrite <- mult_INR.
        rewrite <- Rmult_div_swap.
        rewrite <- Rmult_div_assoc.
        Search INR.
        Search Nat.div.

        rewrite Rdiv_def.
        rewrite Rmult_div_swap. *)
    - simpl.
      replace (n + 0)%nat with n by ring.
      rewrite Rplus_0_r.
      rewrite Rplus_0_r.
      rewrite Rmult_1_r.
      rewrite Rmult_1_r.
      rewrite Nat.mul_1_r.
      rewrite (Nat.div_same (fact n) (fact_neq_0 n)).
      rewrite INR_1.
      rewrite Rmult_1_r.
      reflexivity.
  + apply functional_extensionality.
    intros.
    replace (n + x0 - n)%nat with x0%nat by (rewrite Nat.add_comm; rewrite <- (Nat.add_sub_assoc x0 n n (Nat.le_refl n)); rewrite Nat.sub_diag; ring).
    ring.
Admitted.

Theorem Taylor_implem :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (D_chain_rule : forall (f g : R -> R), D (fun x => f (g x)) = fun x => D f (g x) * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (a : R) (n : nat),
    Taylor n a F = summation (fun k x' => (iter D k F a / INR (fact k)) * (x' - a) ^ k) (S n).
Proof.
  intros.
  pose proof Taylor_a_equiv.
  specialize Taylor_a_equiv with
    (Taylor := Taylor)
    (D := D)
    (zero_integral := zero_integral)
    (constant_integral := constant_integral)
    (unit_deriv := unit_deriv)
    (linear_deriv := linear_deriv)
    (D_additive := D_additive)
    (D_homog := D_homog)
    (D_product_rule := D_product_rule)
    (D_chain_rule := D_chain_rule)
    (integration_constant := integration_constant)
    (Taylor_degree := Taylor_degree)
    (Taylor_agrees_at_a := Taylor_agrees_at_a)
    (F := F)
    (a := a)
    (n := n) as Taylor_a_equiv.
  rewrite Taylor_a_equiv.
  rewrite (Maclaurin_implem Taylor D zero_integral constant_integral unit_deriv linear_deriv D_additive D_homog D_product_rule integration_constant Taylor_degree Taylor_agrees_at_a (fun x' : R => F (x' + a)) n).
  apply functional_extensionality.
  intros.
  rewrite summation_app.
  rewrite summation_app.
  f_equal.
  apply functional_extensionality.
  intros i.
  f_equal.
  f_equal.
  apply (iter_D_chain_of_linear D unit_deriv linear_deriv D_additive D_homog D_chain_rule F a i).
Qed.

Lemma Taylor_deriv :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (D_chain_rule : forall (f g : R -> R), D (fun x => f (g x)) = fun x => D f (g x) * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  forall (Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0),

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  forall (Taylor_agrees_at_a : forall (degree order : nat) (a : R) (F : R -> R), (order <= degree)%nat -> iter D order (Taylor degree a F) a = iter D order F a),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (a : R) (n : nat),
    D (Taylor (S n) a F) = Taylor n a (D F).
Proof.
  intros.
  
  rewrite (Taylor_implem Taylor D zero_integral constant_integral unit_deriv linear_deriv D_additive D_homog D_product_rule D_chain_rule integration_constant Taylor_degree Taylor_agrees_at_a F a ((S n))).
  rewrite (Taylor_implem Taylor D zero_integral constant_integral unit_deriv linear_deriv D_additive D_homog D_product_rule D_chain_rule integration_constant Taylor_degree Taylor_agrees_at_a (D F) a n).

  apply functional_extensionality.
  intros.
  replace (D (summation (fun (k : nat) (x' : R) => iter D k F a / INR (fact k) * (x' - a) ^ k) (S (S n))) x) with (iter D 1%nat (summation (fun (k : nat) (x' : R) => iter D k F a / INR (fact k) * (x' - a) ^ k) (S (S n))) x) by reflexivity.
  rewrite (iter_D_additive_over_summation D D_additive D_homog (S (S n)) 1%nat (fun (k : nat) (x' : R) => iter D k F a / INR (fact k) * (x' - a) ^ k) x).
  rewrite summation_expand_lower.

  assert (iter D 1 (fun x' : R => iter D 0 F a / INR (fact 0) * (x' - a) ^ 0) x = 0).
  {
    simpl.
    rewrite D_homog.
    rewrite unit_deriv.
    ring.
  }
  rewrite H. clear H.

  rewrite Rplus_0_r.

  f_equal.
  apply functional_extensionality.
  intros i.

  apply functional_extensionality.
  intros x'.
  
  replace (iter D 1) with D by reflexivity.
  rewrite D_homog.
  rewrite iter_expand_inner.
  unfold Rminus at 1.
  rewrite (D_chain_rule (fun x0 : R => x0 ^ S i) (fun x0 : R => x0 + - a)).
  rewrite D_additive.
  replace (-a) with (-a * 1) by ring.
  rewrite D_homog.
  rewrite linear_deriv.
  rewrite unit_deriv.

  replace (S i) with (i+1)%nat by ring.
  rewrite (nth_pow_deriv D linear_deriv D_product_rule).
  replace (x' + - a * 1) with (x' - a) by ring.
  replace (1 + - a * 0) with 1 by ring.
  rewrite Rmult_1_r.
  rewrite <- Rmult_assoc.
  f_equal.
  rewrite <- Rmult_div_swap.
  rewrite <- Rmult_div_assoc.
  replace (i + 1)%nat with (S i) by ring.
  rewrite fact_simpl.
  rewrite mult_INR.
  rewrite Rdiv_mult_distr.
  rewrite Rdiv_diag.
  - field.
    apply INR_fact_neq_0.
  - apply not_0_INR.
    apply not_eq_sym.
    exact (O_S i).
Qed.
