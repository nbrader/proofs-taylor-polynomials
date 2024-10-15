Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import CoqUtilLib.OptionFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.
As such, I'll assume only the properties of differentiation I require.
*)

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
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (le m n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (*
    Given the above then Taylor 1%nat a F must have this implementation: fun x => (D F a)*(x-a) + F a
  *)
  forall (F : R -> R), forall (a : R), Taylor 0%nat a F = fun (x : R) => F a.
Proof.
  intros Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a F a.

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
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (le m n) -> iter D m (Taylor n a F) a = iter D m F a) ->

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
  intros Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a F a.
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

Lemma Taylor_1_example_lemma_1 :
  (* Taylor 1%nat f is the linearisation of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (le m n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (*
    Given the above then
      Taylor 1%nat 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7
  *)
  Taylor 1%nat 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7.
Proof.
  intros Taylor D
         zero_integral constant_integral linear_integral
         Taylor_degree Taylor_agrees_at_a.
  pose proof (Taylor_1_implem Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a (fun x => 3*x*x*x + 5*x*x - 7) 0).
  assert ((fun x : R => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * (x-0) + (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0)
         = fun x : R => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7) by (apply functional_extensionality; intros; ring).
          
  rewrite H.
  apply H0.
Qed.

Theorem nth_pow_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n : nat), D (fun x => x^(n+1)) = fun x => INR (n+1) * x^n.
Proof.
  intros D linear_deriv D_product_rule.
  induction n as [|n IH]; intros.
  - simpl.
    replace (fun x : R => x * 1) with (fun x : R => x) by (apply functional_extensionality; intros; ring).
    replace (1 * 1) with (1) by ring.
    apply linear_deriv.
  - replace (fun x : R => x ^ (S n + 1)) with (fun x : R => x * x ^ (S n)) by (apply functional_extensionality; intros; rewrite pow_add; rewrite pow_1; rewrite Rmult_comm; auto).
    rewrite D_product_rule.
    rewrite linear_deriv.
    replace (fun x0 : R => x0 ^ S n) with (fun x : R => x ^ (n + 1)) by (apply functional_extensionality; intros; f_equal; apply Nat.add_1_r).
    rewrite IH.
    apply functional_extensionality.
    intros.
    replace (1 * x ^ S n) with (x ^ S n) by ring.
    replace (x * (INR (n + 1) * x ^ n)) with ((INR (n + 1) * x ^ (S n))) by (simpl; ring).
    rewrite tech_pow_Rplus.
    reflexivity.
Qed.

Theorem poly_term_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (n : nat), forall (c : R), D (fun x => c*x^(n+1)) = fun x => c * INR (n+1) * x^n.
Proof.
  intros D linear_deriv D_homog D_product_rule.
  intros.
  replace (fun x : R => c * INR (n + 1) * x ^ n) with (fun x : R => c * D (fun x => x^(n+1)) x) by (apply functional_extensionality; intros; rewrite Rmult_assoc; rewrite (nth_pow_deriv D linear_deriv D_product_rule n); reflexivity).
  apply functional_extensionality.
  intros.
  rewrite D_homog.
  reflexivity.
Qed.

Lemma Taylor_1_example_lemma_2 :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),
  forall (quadratic_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x*x) <-> exists (c' : R), f = fun x => (1/3)*c*x*x*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (*
    Given the above then
      D (fun x => 3*x*x*x + 5*x*x - 7) = fun x => 9*x*x + 10*x.
  *)
  D (fun x => 3*x*x*x + 5*x*x - 7) = fun x => 9*x*x + 10*x.
Proof.
  assert ((fun x => 3*x*x*x + 5*x*x - 7) = fun x => (3*x*x*x + 5*x*x) + (- 7)) by (apply functional_extensionality; auto).
  intros.
    rewrite H.
    rewrite (D_additive (fun x => 3*x*x*x + 5*x*x) (fun x => - 7)).
    assert (D (fun x => - 7) = fun x => 0).
    {
      assert (exists (c : R), ((fun (x : R) => - 7) = (fun x => c))).
      {
        exists (-7).
        reflexivity.
      }
      apply (zero_integral (fun x => - 7)).
      apply H0.
    }
    rewrite H0.
    apply functional_extensionality.
    intro.
    assert (D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0) x + 0 = D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0) x) by ring. rewrite H1. clear H1.
    rewrite (D_additive (fun x => 3*x*x*x) (fun x => 5*x*x)).
    assert (D (fun x => 5*x*x) = fun (x : R) => 10*x).
    {
      assert (exists (c' : R), (fun x => 5*x*x) = fun (x : R) => (1/2)*10*x*x + c').
      {
        exists (0).
        apply functional_extensionality.
        intros.
        field.
      }
      apply (linear_integral (fun x => 5*x*x)).
      apply H1.
    }
    rewrite H1.
    assert (D (fun x => 3*x*x*x) = fun (x : R) => 9*x*x).
    {
      assert (exists (c' : R), (fun x => 3*x*x*x) = fun (x : R) => (1/3)*9*x*x*x + c').
      {
        exists (0).
        apply functional_extensionality.
        intros.
        field.
      }
      apply (quadratic_integral (fun x => 3*x*x*x)).
      apply H2.
    }
    rewrite H2.
    field.
Qed.

Theorem Taylor_1_example :
  (* Taylor 1%nat f is the linearisation of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),
  forall (quadratic_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x*x) <-> exists (c' : R), f = fun x => (1/3)*c*x*x*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (le m n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (*
    Given the above then
      Taylor 1%nat 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => -7.
  *)
  Taylor 1%nat 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => -7.
Proof.
  intros Taylor D
         zero_integral constant_integral linear_integral quadratic_integral
         D_additive D_homog
         Taylor_degree Taylor_agrees_at_a.
  pose proof (Taylor_1_example_lemma_1 Taylor D zero_integral constant_integral linear_integral Taylor_degree Taylor_agrees_at_a).
  rewrite H.
  apply functional_extensionality.
  intros.
  pose proof (Taylor_1_example_lemma_2 D zero_integral constant_integral linear_integral quadratic_integral D_additive D_homog).
  rewrite H0.
  ring.
Qed.

Theorem quadratic_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  D (fun x => x*x) = fun x => 2*x.
Proof.
  intros.
  rewrite (D_product_rule (fun x => x) (fun x => x)).
  rewrite linear_deriv.
  apply functional_extensionality.
  intro.
  ring.
Qed.

Theorem cubic_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  D (fun x => x*x*x) = fun x => 3*x*x.
Proof.
  intros.
  rewrite (D_product_rule (fun x => x * x) (fun x => x)).
  rewrite (D_product_rule (fun x => x) (fun x => x)).
  rewrite linear_deriv.
  apply functional_extensionality.
  intro.
  ring.
Qed.

Theorem linear_integral :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)
  forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'.
Proof.
  intros.
  split.
  - intros.
    pose proof (quadratic_deriv D linear_deriv D_product_rule).
    assert (D (fun x : R => c / 2 * (x * x)) = (fun x : R => c * x)).
    {
      rewrite D_homog.
      rewrite H0.
      apply functional_extensionality.
      intro.
      field.
    }
    clear H0.
    rewrite <- H1 in H. clear H1.
    assert ((fun x : R => c / 2 * (x * x)) = (fun x : R => 1 / 2 * c * x * x)) by (apply functional_extensionality; intro; field). rewrite H0 in H. clear H0.
    assert (forall (c0 : R) (f : R -> R), D f = (fun x0 : R => D f x0 + D (fun _ : R => c0) x0)).
    {
      intro.
      assert (D (fun _ : R => c0) = (fun _ : R => 0)).
      {
        apply (zero_integral (fun _ : R => c0)).
        exists c0.
        reflexivity.
      }
      rewrite H0. clear H0.
      intro.
      apply functional_extensionality.
      intros.
      field.
    }
    assert (forall (c0 : R) (f : R -> R), (fun x0 : R => D f x0 + D (fun _ : R => c0) x0) = (fun x0 : R => D (fun x : R => f x + c0) x0)).
    {
      intros.
      apply functional_extensionality.
      intro.
      rewrite D_additive.
      reflexivity.
    }
    assert (forall (c0 : R) (f : R -> R), D f = D (fun x : R => f x + c0)).
    {
      intros.
      rewrite (H0 c0).
      rewrite (H1 c0).
      reflexivity.
    }
    clear H0 H1.
    assert (forall (c0 : R) (f g : R -> R), (f = fun x => g x + c0) -> D f = D g).
    {
      intros.
      rewrite H0.
      symmetry.
      rewrite <- (H2 c0).
      apply functional_extensionality.
      intro.
      reflexivity.
    }
    clear H2.
    apply integration_constant.
    apply H.
  - intros.
    destruct H.
    rewrite H.
    rewrite D_additive.
    replace x with (x * 1) by ring.
    rewrite (D_homog (fun _ => 1) x).
    rewrite unit_deriv.
    replace (x * 0) with 0 by ring.
    replace (D (fun x1 : R => 1 / 2 * c * x1 * x1)) with (fun x1 : R => c * x1).
    {
      apply functional_extensionality.
      intro.
      field.
    }
    apply functional_extensionality.
    intro.
    assert ((fun x1 : R => 1 / 2 * c * x1 * x1) = (fun x1 : R => 1 / 2 * c * (x1 * x1))) by (apply functional_extensionality; intro; ring).
    rewrite H0.
    rewrite (D_homog (fun x0 : R => x0 * x0) (1/2 * c)).
    rewrite (quadratic_deriv D linear_deriv D_product_rule).
    field.
Qed.

Theorem quadratic_integral :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (unit_deriv : D (fun x => 1) = fun _ => 0),
  forall (linear_deriv : D (fun x => x) = fun x => 1),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (D_product_rule : forall (f g : R -> R), D (fun x => f x * g x) = fun x => D f x * g x + f x * D g x),
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)
  forall (f : R -> R) (c : R), (D f = fun x => c*x*x) <-> exists (c' : R), f = fun x => (1/3)*c*x*x*x + c'.
Proof.
  intros D zero_integral constant_integral unit_deriv linear_deriv
         D_additive D_homog D_product_rule integration_constant f c.

  (* Step 1: Assume D f = fun x => c * x^2 *)
  split.
  - intro H.
    (* We aim to show that f = (1/3) * c * x^3 + c' *)
    
    (* Step 2: Consider a candidate solution *)
    (* Let g(x) = (1/3) * c * x^3. By differentiating this, we get g'(x) = c * x^2 *)
    assert (H2 : D (fun x => (1/3) * c * (x*x*x)) = fun x => c * x*x).
    { (* Derive this from the linearity and power rule of the derivative *)
      (* Use D_homog and D_product_rule to handle the derivative of x^3 *)
      (* Proof omitted, but follows from applying the hypothesis *)
      rewrite (D_homog (fun x : R => (x*x*x)) (1 / 3 * c)).
      rewrite (cubic_deriv D linear_deriv D_product_rule).
      apply functional_extensionality.
      intro.
      field.
    }
    
    assert (H1 : D (fun x => (1/3) * c * x*x*x) = fun x => c * x*x).
    {
      replace (fun x0 : R => 1 / 3 * c * x0 * x0 * x0) with (fun x : R => (1/3*c) * (x*x*x)) by (apply functional_extensionality; intro; field).
      apply H2.
    }
    
    (* Step 3: Since D f = D g, apply integration_constant *)
    specialize (integration_constant f (fun x => (1/3) * c * x*x*x)).
    assert (D f = D (fun x => (1/3) * c * x*x*x)) by (rewrite H1; apply H).
    specialize (integration_constant H0).
    destruct integration_constant as [c' Hf].
    exists c'.

    (* Now, f = g + c', which means f = (1/3) * c * x^3 + c' *)
    apply Hf.
  
  - intro Hf.
    (* Assume f = (1/3) * c * x^3 + c', show D f = fun x => c * x^2 *)
    destruct Hf as [c' Hf].
    subst f.
    (* Apply the derivative to the expression (1/3) * c * x^3 + c' *)
    rewrite D_additive.
    assert (D (fun _ : R => c') = (fun _ : R => 0)).
    {
      apply (zero_integral (fun _ : R => c')).
      exists c'.
      reflexivity.
    }
    rewrite H. clear H.
    pose proof (cubic_deriv D linear_deriv D_product_rule).
    assert (D (fun x : R => (1/3*c) * (x*x*x)) = (fun x : R => c * (x*x))).
    {
      rewrite (D_homog (fun x : R => (x*x*x)) (1 / 3 * c)).
      rewrite (cubic_deriv D linear_deriv D_product_rule).
      apply functional_extensionality.
      intro.
      field.
    }
    replace (fun x0 : R => 1 / 3 * c * x0 * x0 * x0) with (fun x : R => (1/3*c) * (x*x*x)) by (apply functional_extensionality; intro; field).
    apply functional_extensionality.
    intro.
    rewrite H0.
    field.
    (* Derive that D f = fun x => c * x^2 *)
    (* Proof omitted for brevity, but follows directly *)
Qed.

Fixpoint summation (F_ : nat -> R -> R) (n : nat) : R -> R := fun (x : R) =>
  match n with
    | O => 0
    | S n' => F_ n' x + summation F_ n' x
  end.

Lemma summation_expand_lower :
  forall (F_ : nat -> R -> R) (n : nat) (x : R),
    summation F_ (S n) x = summation (fun i x' => F_ (S i) x') n x + F_ O x.
Proof.
  intros.
  induction n.
  - simpl.
    ring.
  (* - replace (summation F_ (S (S n)) x) with (F_ (S n) x + summation F_ (S n) x) by auto. *)
  - replace (summation (fun (i : nat) (x' : R) => F_ (S i) x') (S n) x) with (F_ (S n) x + summation (fun (i : nat) (x' : R) => F_ (S i) x') n x) by auto.
    rewrite Rplus_assoc.
    rewrite <- IHn. clear IHn.
    reflexivity.
Qed.

Lemma D_additive_over_summation :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F_ : nat -> R -> R) (n : nat) (x : R),
    D (summation F_ n) x = summation (fun i => D (F_ i)) n x.
Proof.
  intros D D_additive D_homog F n x.
  simpl.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl.
    replace (0) with (0*1) by field.
    rewrite (D_homog (fun _ => 1) 0).
    field.
  
  - (* Inductive step: n -> S n *)
    simpl.
    rewrite <- IH.
    rewrite D_additive.
    reflexivity.
Qed.

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

Theorem nth_integral_of_zero :
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

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (n : nat) (f : R -> R), iter D n f = (fun _ => 0) -> exists (c_ : nat -> R), f = summation (fun i x' => (c_ i) * x'^i) n.
Proof.
  intros Taylor D constant_integral D_additive D_homog D_product_rule integration_constant n.
  induction n.

  - (* Base case: n = 0 *)
    simpl in *.
    intros f f_at_0th_D.
    exists (fun _ => 0).
    apply f_at_0th_D.
  
  - (* Inductive step: n -> S n *)
    intros f f_at_nth_D.
    rewrite iter_expand_inner in f_at_nth_D.
    apply IHn in f_at_nth_D. clear IHn.
    destruct f_at_nth_D as [c IH].
    assert (summation (fun (i : nat) (x' : R) => c i * x' ^ i) n = D (summation (fun (i : nat) (x' : R) => c i / INR (S i) * x' ^ (S i)) n)).
    {
      apply functional_extensionality.
      intros.
      rewrite (D_additive_over_summation D D_additive D_homog).

      assert (linear_deriv : D (fun x => x) = fun x => 1).
      {
        apply constant_integral.
        exists 0.
        apply functional_extensionality.
        intros.
        field.
      }
      f_equal.
      apply functional_extensionality.
      intros.

      rewrite D_homog.
      replace (S x0) with (x0 + 1)%nat by ring.
      rewrite (nth_pow_deriv D linear_deriv D_product_rule x0).
      apply functional_extensionality.
      intros.
      field.
      rewrite plus_INR.
      simpl.
      intro.
      assert (INR x0 + 1 = 0 -> INR x0 = 0 /\ 1 = 0) by (apply (Rplus_eq_R0 (INR x0) 1 (pos_INR x0) Rle_0_1)).
      apply H0 in H. clear H0.
      destruct H.
      apply eq_sym in H0.
      assert (0 < 1) by apply Rlt_0_1.
      apply Rlt_not_eq in H1.
      contradiction.
    }

    rewrite H in IH. clear H.
    apply integration_constant in IH.
    destruct IH as [c0 f_impl].
    set (d := fun i => match i with
                | 0%nat => c0
                | S i' => c i' / INR (S i') end).
    exists d.
    assert (summation (fun (i : nat) (x' : R) => d i * x' ^ i) (S n) = fun x => summation (fun (i : nat) (x' : R) => c i / INR (S i) * x' ^ S i) n x + d O * x ^ O).
    {
      apply functional_extensionality.
      intros.
      rewrite (summation_expand_lower (fun (i : nat) (x' : R) => d i * x' ^ i) n).
      reflexivity.
    }
    rewrite H. clear H.

    apply functional_extensionality.
    intros.

    assert (d 0%nat * x ^ 0 = c0).
    {
      unfold d.
      simpl.
      ring.
    }
    rewrite H. clear H.

    rewrite f_impl.
    reflexivity.
Qed.


(* Admitted *)

Theorem nth_integration_constant :
  (* Taylor n f is the Taylor polynomial of degree n of f *)
  forall (Taylor : nat -> R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (INR m <= INR n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (f g : R -> R) (n : nat), iter D n f = iter D n g -> exists (c_ : nat -> R), f = (fun x : R => g x + summation (fun i x' => (c_ i) * x'^i) n x).
Proof.
  intros Taylor D zero_integral constant_integral D_additive D_homog Taylor_degree Taylor_agrees_at_a f g n f_and_g_agree_at_nth_D.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl in *.
    exists (fun _ => 0).
    rewrite <- f_and_g_agree_at_nth_D.
    apply functional_extensionality.
    intros.
    ring.
  
  - (* Inductive step: n -> S n *)
    simpl.

    assert (iter D (S n) (fun x => f x - g x) = fun _ => 0).
    {
      simpl in *.
      unfold Rminus.
      rewrite iter_additive by (intros; apply D_additive).
      rewrite D_additive.
      rewrite f_and_g_agree_at_nth_D.
      rewrite <- D_additive.
      rewrite <- iter_additive by (intros; apply D_additive).
      replace (fun x : R => g x + - g x) with (fun _ : R => 0) by (apply functional_extensionality; intros; ring).
      replace (0) with (0*1) by field.
      rewrite (iter_homog D D_homog (fun _ => 1) 0) by (intros; apply D_homog).
      rewrite D_homog.
      apply functional_extensionality.
      intros.
      now ring.
    }
    clear f_and_g_agree_at_nth_D.

    simpl in H.
    apply zero_integral in H.
    destruct H as [c H].
    induction n. (*  <--- This could have probably just been "case".  *)
    + simpl.
      exists (fun _ => c).
      simpl in H.
      replace (c * 1 + 0) with (c) by ring.
      replace (fun x : R => g x + c) with (fun x : R => (fun x' : R => g x') x + (fun x : R => f x - g x) x).
      * apply functional_extensionality.
        intros.
        ring.
      * apply functional_extensionality.
        intros.
        assert (f x - g x = c).
        {
          set (F := (fun x : R => f x - g x)).
          (* pose proof (eq_refl (F x)). *)
          assert (F = (fun _ : R => c)) by (unfold F; apply H).
          assert (F x = f x - g x) by (unfold F; reflexivity).
          assert (F x = (fun _ : R => c) x) by (rewrite H0; reflexivity).
          rewrite H1 in H2.
          apply H2.
        }
        rewrite <- H0.
        reflexivity.
    + simpl in *.
      destruct IH as [c_ IH].
      * admit.
      * exists c_.
        replace (fun x : R => g x + (c_ (S n) * (x * x ^ n) + (c_ n * x ^ n + summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) n x))) with (fun x : R => g x + (c_ n * x ^ n + summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) n x) + c_ (S n) * (x * x ^ n)) by (apply functional_extensionality; intros; ring).
        replace (fun x : R => g x + (c_ n * x ^ n + summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) n x) + c_ (S n) * (x * x ^ n)) with (fun x2 : R => f x2 + (fun x => c_ (S n) * (x * x ^ n)) x2) by (rewrite IH; reflexivity).
        assert (c_ (S n) = 0).
        {
          (* apply constant_integral in H. *)
          (* apply nth_pow_deriv in H. *)
          (* apply IH. *)
          rewrite IH in H.
          replace (fun x : R => g x + (c_ n * x ^ n + summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) n x) - g x) with (fun x : R => c_ n * x ^ n + summation (fun (i : nat) (x' : R) => c_ i * x' ^ i) n x) in H by (intros; apply functional_extensionality; intros; ring).
          
          admit.
        }
        rewrite H0.
        apply functional_extensionality.
        intros.
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
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (INR m <= INR n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (a : R) (n : nat),
    Taylor n a F = fun x => summation (fun k x' => (iter D k F a) * (x' - a) ^ k / INR (fact k)) (S n) x.
Proof.
  intros Taylor D zero_integral constant_integral integration_constant Taylor_degree Taylor_agrees_at_a F a.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl.
    replace (fun _ : R => F a * 1 / 1) with (fun _ : R => F a) by (apply functional_extensionality; intros; field).
    specialize (Taylor_agrees_at_a 0%nat 0%nat a F).
    replace (INR 0 <= INR 0 -> iter D 0 (Taylor 0%nat a F) a = iter D 0 F a) with (INR 0 <= INR 0 -> Taylor 0%nat a F a = F a) in Taylor_agrees_at_a by (try (rewrite H0); reflexivity).
    specialize (Taylor_agrees_at_a (Rle_refl (INR 0))).
    specialize (Taylor_degree 0%nat a F).
    rewrite <- Taylor_agrees_at_a. clear Taylor_agrees_at_a.
    apply zero_integral in Taylor_degree.
    destruct Taylor_degree as [x Taylor_constant].
    rewrite Taylor_constant.
    apply functional_extensionality.
    intros.
    field.
  
  - (* Inductive step: n -> S n *)
    replace (fun x : R => summation (fun (k : nat) (x' : R) => iter D k F a * (x' - a) ^ k / INR (fact k)) (S (S n)) x) with (fun x : R => D (iter D n F) a * ((x - a) ^ S n) / INR (fact (S n)) + Taylor n a F x) by (apply functional_extensionality; intros; rewrite IH; simpl; f_equal). clear IH.

    specialize (Taylor_agrees_at_a n (S n) a F).
    assert (INR n <= INR (S n)).
    {
      rewrite S_INR.
      apply Rlt_le.
      rewrite Rplus_comm.
      rewrite <- (Rplus_0_l (INR n)) at 1.
      apply (Rplus_lt_compat_r (INR n)).
      apply Rlt_0_1.
    }
    specialize (Taylor_agrees_at_a H). clear H.

    assert (conclusion : Taylor (S n) a F = (fun x : R => D (iter D n F) a * (x - a) ^ S n / INR (fact (S n)) + Taylor n a F x)).
    {
      (* Try integrating both sides of Taylor_deriv to get an equation for "Taylor (S n) a F x" *)
      (* apply nth_integration_constant in Taylor_agrees_at_a. *)
      admit.
    }
    apply conclusion.
    
Admitted.

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
  forall (integration_constant : forall (f g : R -> R), D f = D g -> exists (c : R), f = (fun x : R => g x + c)), (* <-- Not true for functions with discontinuities *)

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (m n : nat) (a : R) (F : R -> R), (le m n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (a : R) (n : nat),
    D (Taylor (S n) a F) = Taylor n a (D F).
Proof.
  intros Taylor D zero_integral constant_integral
         unit_deriv linear_deriv D_additive D_homog D_product_rule integration_constant
         Taylor_degree Taylor_agrees_at_a F a.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    assert (Taylor_agrees_at_a_0 : Taylor 0%nat a F a = F a) by (apply (Taylor_agrees_at_a 0%nat 0%nat a F (Nat.le_refl 0))).
    (* assert (Taylor_agrees_at_a_1 : forall (a0 : R), Taylor 0%nat a0 F a0 = F a) by (intros; apply (Taylor_agrees_at_a 0%nat 0%nat a F (Nat.le_refl 0))). *)
    assert (Taylor_agrees_at_a_1 : Taylor 0%nat a (D F) = fun (x : R) => D F a) by (apply (Taylor_0_implem Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a (D F) a)).
    assert (Taylor_agrees_at_a_2 : Taylor 1%nat a F = (fun x : R => D F a * (x - a) + F a)) by (apply (Taylor_1_implem Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a F a)).

    rewrite Taylor_agrees_at_a_1.
    rewrite Taylor_agrees_at_a_2.

    apply functional_extensionality.
    intros.
    rewrite D_additive.
    replace (F a) with (F a * 1) by ring.
    rewrite D_homog.
    rewrite D_homog.
    unfold Rminus.
    rewrite D_additive.
    replace (- a) with (- a * 1) by ring.
    rewrite D_homog.
    rewrite unit_deriv.
    rewrite linear_deriv.
    field.
  
  - (* Inductive step: n -> S n *)
    admit.
Admitted.

(*

(* Closed under the global context *)
Print Assumptions iter.

(*
Axioms:
ClassicalDedekindReals.sig_forall_dec : forall P : nat -> Prop, (forall n : nat, {P n} + {~ P n}) -> {n : nat | ~ P n} + {forall n : nat, P n}
*)
Print Assumptions Taylor_0_implem.

(*
Axioms:
ClassicalDedekindReals.sig_forall_dec : forall P : nat -> Prop, (forall n : nat, {P n} + {~ P n}) -> {n : nat | ~ P n} + {forall n : nat, P n}
functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
*)
Print Assumptions Taylor_1_implem.
Print Assumptions Taylor_1_example_lemma_1.
Print Assumptions nth_pow_deriv.
Print Assumptions poly_term_deriv.
Print Assumptions Taylor_1_example_lemma_2.
Print Assumptions Taylor_1_example.
Print Assumptions cubic_deriv.
Print Assumptions quadratic_deriv.
Print Assumptions linear_integral.
Print Assumptions quadratic_integral.

(* Admitted *)
Print Assumptions Taylor_deriv.
Print Assumptions fold_left_right_equiv.
Print Assumptions Taylor_implem.          (*     <---- GOAL      *)

*)
