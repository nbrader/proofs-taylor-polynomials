Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.

As such, I'll introduce some parameters and assume only the
properties of differentiation I require.
*)

(* Lin f is the linearisation of f *)
Axiom Lin : R -> (R -> R) -> (R -> R).

Parameter F : R -> R.
Parameter F_prime : R -> R.

(* Denote the derivative by D *)
Parameter D : (R -> R) -> (R -> R).

(* Derivative properties *)
Axiom zero_integral : forall (f : R -> R), (D f = fun x => 0) -> exists (c : R), f = fun x => c.
Axiom constant_integral : forall (f : R -> R), forall (c : R), (D f = fun x => c) -> exists (c' : R), f = fun x => c*x + c'.

(* Assume the supplied functions are the true first and second order derivatives *)
Axiom F_derivative : D F = F_prime.

Axiom Lin_a_F_at_a_is_F_a : forall (a : R), D (Lin a F) a = F a.
Axiom Lin_a_F_derivative_at_a_is_F_prime_a : forall (a : R), D (Lin a F) a = F_prime a.
Axiom Lin_a_F_derivative_derivative_is_zero : forall (a : R), D (D (Lin a F)) = fun x => 0.

(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Lin_exists_uniquely : forall (a : R),
  (forall (x : R), D (D (Lin a F)) x = 0) ->
  Lin a F a = F a ->
  D (Lin a F) a = D F a -> Lin a F = fun x => (D F a)*(x-a) + F a.
Proof.
  intros.
  pose proof (Lin_a_F_derivative_derivative_is_zero a).

  apply (zero_integral (D (Lin a F))) in H2.

  destruct H2.
  assert (D (Lin a F) a = x) by (rewrite H2; reflexivity).
  rewrite H1 in H3.

  apply (constant_integral (Lin a F) x) in H2.

  destruct H2.

  assert (Lin a F a = x * a + x0) by (rewrite H2; reflexivity).
  rewrite H0 in H4.
  rewrite <- H3 in H4.
  assert (x0 = F a - (D F a) * a) by (rewrite H4; ring).
  rewrite H5 in H2.
  rewrite <- H3 in H2.
  assert ((fun x : R => D F a * x + (F a - D F a * a)) = (fun x : R => D F a * (x - a) + F a)) by (apply functional_extensionality; intros; ring).
  rewrite H6 in H2.
  apply H2.
Qed.