Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.
As such, I'll assume only the properties of differentiation I require.
*)

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

Theorem Taylor_implem :
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
  (forall (m n : nat) (a : R) (F : R -> R), (INR m <= INR n) -> iter D m (Taylor n a F) a = iter D m F a) ->

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (F : R -> R) (a : R) (n : nat),
    Taylor n a F = fun x => fold_left Rplus (map (fun k => (iter D k F a) * (x - a) ^ k / INR (fact k)) (seq 0 (S n))) 0.
Proof.
  intros Taylor D zero_integral constant_integral Taylor_degree Taylor_agrees_at_a F a.
  induction n as [|n IH]; intros.

  - (* Base case: n = 0 *)
    simpl.
    replace (fun _ : R => 0 + F a * 1 / 1) with (fun _ : R => F a) by (apply functional_extensionality; intros; field).
    specialize (Taylor_agrees_at_a 0%nat 0%nat a F).
    replace (INR 0 <= INR 0 -> iter D 0 (Taylor 0%nat a F) a = iter D 0 F a) with (INR 0 <= INR 0 -> Taylor 0%nat a F a = F a) in Taylor_agrees_at_a by (try (rewrite H0); reflexivity).
    specialize (Taylor_agrees_at_a (Rle_refl (INR 0))).
    specialize (Taylor_degree 0%nat a F).
    rewrite <- Taylor_agrees_at_a. clear Taylor_agrees_at_a.
    apply zero_integral in Taylor_degree.
    destruct Taylor_degree as [x Taylor_constant].
    rewrite Taylor_constant.
    reflexivity.
  
  - (* Inductive step: n -> S n *)
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
    specialize (Taylor_agrees_at_a H).

    (*
    Taylor : nat -> R -> (R -> R) -> R -> R
    D : (R -> R) -> R -> R
    zero_integral : forall f : R -> R, D f = (fun _ : R => 0) <-> (exists c : R, f = (fun _ : R => c))
    constant_integral : forall (f : R -> R) (c : R), D f = (fun _ : R => c) <-> (exists c' : R, f = (fun x : R => c * x + c'))
    Taylor_degree : forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = (fun _ : R => 0)
    F : R -> R
    a : R
    n : nat
    Taylor_agrees_at_a : iter D n (Taylor (S n) a F) a = iter D n F a
    IH : Taylor n a F = (fun x : R => fold_left Rplus (map (fun k : nat => iter D k F a * (x - a) ^ k / INR (fact k)) (seq 0 (S n))) 0)
    H : INR n <= INR (S n)
    *)
    assert (conclusion : Taylor (S n) a F = (fun x : R => fold_left Rplus (map (fun k : nat => iter D k F a * (x - a) ^ k / INR (fact k)) (seq 0 (S (S n)))) 0)).
    {
      (* rewrite <- fold_left_map with (f := fun k => (iter D k F a) * (x - a) ^ k / INR (fact k)) (l := seq 0 (S (S n))). *)
      admit.
    }
    apply conclusion.
    
Admitted.

(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Lin_implem :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

  (*
    Given the above then Lin a F must have this implementation: fun x => (D F a)*(x-a) + F a
  *)
  forall (F : R -> R), forall (a : R), Lin a F = fun x => (D F a)*(x-a) + F a.
Proof.
  intros Lin D
         zero_integral constant_integral
         Lin_second_deriv_is_0
         Lin_equals_F_at_a
         Lin_deriv_equals_F_deriv_at_a
         F a.
  (*
    Givens:
      lin_f''(x) = 0
      lin_f(a) = f(a)
      lin_f'(a) = f'(a)
  *)

  apply (zero_integral (D (Lin a F))) in Lin_second_deriv_is_0. clear zero_integral.
  destruct Lin_second_deriv_is_0 as [x first_deriv_Lin_is_c].
  assert (linear_coeff_def_is_D_F_a : D (Lin a F) a = x) by (rewrite first_deriv_Lin_is_c; reflexivity).
  rewrite Lin_deriv_equals_F_deriv_at_a in linear_coeff_def_is_D_F_a. clear Lin_deriv_equals_F_deriv_at_a.
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

  apply (constant_integral (Lin a F) x) in first_deriv_Lin_is_c. clear constant_integral.
  destruct first_deriv_Lin_is_c as [x0 Lin_def].
  assert (algebra_1 : Lin a F a = x * a + x0) by (rewrite Lin_def; reflexivity).
  rewrite Lin_equals_F_at_a in algebra_1. clear Lin_equals_F_at_a.
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

  rewrite constant_term_def in Lin_def. clear constant_term_def.
  rewrite <- linear_coeff_def_is_D_F_a in Lin_def. clear linear_coeff_def_is_D_F_a.
  assert (algebra_2 : ((fun x : R => D F a * x + (F a - D F a * a)) = (fun x : R => D F a * (x - a) + F a))) by (apply functional_extensionality; intros; ring).
  rewrite algebra_2 in Lin_def. clear algebra_2.
  (*
    Given
      lin_f(x) = c*x + c'
      c = f'(a)
      c' = f(a) - f'(a) * a
    Then:
      lin_f(x) = f'(a)*(x-a) + f(a)
  *)

  apply Lin_def.
Qed.

Lemma Lin_example_lemma_1 :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

  (*
    Given the above then
      Lin 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7
  *)
  Lin 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7.
Proof.
  intros Lin D
         zero_integral constant_integral linear_integral
         Lin_second_deriv_is_0
         Lin_equals_F_at_a
         Lin_deriv_equals_F_deriv_at_a.
  pose proof (Lin_implem Lin D zero_integral constant_integral Lin_second_deriv_is_0 Lin_equals_F_at_a Lin_deriv_equals_F_deriv_at_a (fun x => 3*x*x*x + 5*x*x - 7) 0).
  assert ((fun x : R => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * (x-0) + (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0)
         = fun x : R => D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0 - 7) 0 * x - 7) by (apply functional_extensionality; intros; ring).
          
  rewrite H.
  apply H0.
Qed.

Lemma Lin_example_lemma_2 :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),
  forall (quadratic_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x*x) <-> exists (c' : R), f = fun x => (1/3)*c*x*x*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

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
      apply H3.
    }
    rewrite H3.
    apply functional_extensionality.
    intro.
    assert (D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0) x + 0 = D (fun x0 : R => 3*x0*x0*x0 + 5*x0*x0) x) by ring. rewrite H4. clear H4.
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
      apply H4.
    }
    rewrite H4.
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
      apply H5.
    }
    rewrite H5.
    field.
Qed.

Theorem Lin_example :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) <-> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) <-> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x*x + c'),
  forall (quadratic_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x*x) <-> exists (c' : R), f = fun x => (1/3)*c*x*x*x + c'),
  forall (D_additive : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

  (*
    Given the above then
      Lin 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => -7.
  *)
  Lin 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => -7.
Proof.
  intros Lin D
         zero_integral constant_integral linear_integral quadratic_integral
         D_additive D_homog
         Lin_second_deriv_is_0
         Lin_equals_F_at_a
         Lin_deriv_equals_F_deriv_at_a.
  pose proof (Lin_example_lemma_1 Lin D zero_integral constant_integral linear_integral Lin_second_deriv_is_0 Lin_equals_F_at_a Lin_deriv_equals_F_deriv_at_a).
  rewrite H.
  apply functional_extensionality.
  intros.
  pose proof (Lin_example_lemma_2 Lin D zero_integral constant_integral linear_integral quadratic_integral D_additive D_homog Lin_second_deriv_is_0 Lin_equals_F_at_a Lin_deriv_equals_F_deriv_at_a).
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
