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
    Given the above then Taylor 0%nat a F must have this implementation: fun x => F a
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
          assert (0 ^ (i0 + S i - i) = 0) as pow_zero_eq.
          {
            assert (exists c : nat, (i0 + S i - i)%nat = S c) as exists_succ.
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
            destruct exists_succ as [c_val c_eq].
            rewrite c_eq. clear c_eq.
            simpl.
            ring.
          }
          rewrite pow_zero_eq.
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

  (* Proof by induction on n *)
  induction n as [|n' IH].

  - (* Base case: n = 0 *)
    (* Use Taylor_0_implem to show both sides equal fun x => F a *)
    pose proof (Taylor_0_implem Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a F a) as T0_a.
    pose proof (Taylor_0_implem Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a (fun x' => F (x' + a)) 0) as T0_0.
    rewrite T0_a.
    rewrite T0_0.
    apply functional_extensionality. intros x.
    (* LHS: F a, RHS: F (0 + a) = F a *)
    replace (0 + a) with a by ring.
    reflexivity.

  - (* Inductive case: n = S n' *)
    (* IH: forall a F, Taylor n' a F = fun x => Taylor n' 0 (fun x' => F (x'+a)) (x-a) *)
    (* Goal: Taylor (S n') a F = fun x => Taylor (S n') 0 (fun x' => F (x'+a)) (x-a) *)

    (* Strategy: Show that derivatives are equal and values at one point are equal,
       then use integration_constant to conclude functions are equal. *)

    (* Step 1: Alternative approach - show both polynomials agree on all derivatives at a *)
    (* Instead of showing D f = D g directly, we'll show that for all orders k <= S n',
       the k-th derivatives evaluated at a are equal. This uniquely determines the polynomial. *)

    (* Actually, we can use a more direct approach: show that the RHS satisfies the same
       characterization as the LHS (Taylor polynomial axioms), so they must be equal. *)

    (* For now, we'll admit this and note that it requires showing:
       For all k <= S n': iter D k (Taylor (S n') a F) a = iter D k (fun x => Taylor (S n') 0 (fun x' => F (x'+a)) (x-a)) a

       The LHS equals iter D k F a by Taylor_agrees_at_a.
       The RHS can be computed using iter_D_chain_of_linear and the inductive hypothesis.
    *)

    assert (deriv_eq: D (Taylor (S n') a F) = D (fun x => Taylor (S n') 0 (fun x' => F (x'+a)) (x-a))).
    {
      (* This would require proving a relationship between derivatives of Taylor polynomials
         that we don't have access to yet, since Taylor_deriv depends on this theorem.
         The proof would proceed by:
         1. Getting polynomial representations using Taylor_nth
         2. Computing derivatives term-by-term
         3. Using IH to show they match
         4. Potentially proving Taylor_deriv without using Taylor_implem (which uses this theorem) and then moving to before this theorem so we can avoid circularity.
         But this is quite involved. For a simpler proof, we'd need additional lemmas. *)
      admit.
    }

    (* Step 2: Use integration_constant to get Taylor (S n') a F = fun x => (Taylor (S n') 0 ...) x + c *)
    apply integration_constant in deriv_eq.
    destruct deriv_eq as [c Hc].

    (* Step 3: Show c = 0 by evaluating at x = a *)
    assert (c_zero: c = 0).
    {
      (* Evaluate Hc at x = a *)
      assert (eval_at_a: Taylor (S n') a F a = Taylor (S n') 0 (fun x' => F (x' + a)) (a - a) + c).
      {
        rewrite Hc. reflexivity.
      }

      (* LHS: Taylor (S n') a F a = F a by Taylor_agrees_at_a *)
      assert (LHS_eq: Taylor (S n') a F a = F a).
      {
        pose proof (Taylor_agrees_at_a (S n') O%nat a F (Nat.le_0_l (S n'))) as H.
        simpl in H. exact H.
      }

      (* RHS: Taylor (S n') 0 (fun x' => F (x' + a)) (a - a) + c
             = Taylor (S n') 0 (fun x' => F (x' + a)) 0 + c
             = F (0 + a) + c (by Taylor_agrees_at_a)
             = F a + c *)
      assert (RHS_eq: Taylor (S n') 0 (fun x' => F (x' + a)) (a - a) + c = F a + c).
      {
        replace (a - a) with 0 by ring.
        pose proof (Taylor_agrees_at_a (S n') O%nat 0 (fun x' => F (x' + a)) (Nat.le_0_l (S n'))) as H.
        simpl in H.
        rewrite H.
        replace (0 + a) with a by ring.
        reflexivity.
      }

      rewrite LHS_eq in eval_at_a.
      rewrite RHS_eq in eval_at_a.
      (* Now we have: F a = F a + c, so c = 0 *)
      symmetry in eval_at_a.
      apply (Rplus_eq_compat_l (- F a)) in eval_at_a.
      ring_simplify in eval_at_a.
      exact eval_at_a.
    }

    (* Step 4: Conclude Taylor (S n') a F = fun x => Taylor (S n') 0 ... *)
    rewrite Hc.
    rewrite c_zero.
    apply functional_extensionality. intros x.
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
