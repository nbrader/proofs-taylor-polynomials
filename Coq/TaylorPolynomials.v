Require Import Coq.Reals.Reals.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.

As such, I'll introduce some parameters and assume only the
properties of differentiation I require.
*)

(* Lin f is the linearisation of f *)
Axiom Lin : (R -> R) -> (R -> R).

Parameter F : R -> R.
Parameter F_prime : R -> R.

(* Denote the derivative by D *)
Parameter D : (R -> R) -> (R -> R).

(* Derivative properties *)
Axiom D_linear : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x.
Axiom D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x.

(* Assume the supplied functions are the true first and second order derivatives *)
Axiom F_derivative : D F = F_prime.
Axiom F_prime_derivative : D F_prime = fun x => 0.

Theorem Lin_exists_uniquely : forall (a : R),
  (forall (x : R), D (D (Lin F)) x = 0) ->
  Lin F a = F a ->
  D (Lin F) a = D F a -> Lin F = fun x => (D F a)*(x-a) + F a.
Proof.
  intros.

Admitted.
