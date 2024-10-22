Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import CoqUtilLib.Iteration.

Require Import TaylorPolynomials.TaylorPolynomials.


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
  (forall (degree order : nat) (a : R) (F : R -> R), (le order degree) -> iter D order (Taylor degree a F) a = iter D order F a) ->

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
  (forall (degree order : nat) (a : R) (F : R -> R), (le order degree) -> iter D order (Taylor degree a F) a = iter D order F a) ->

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
