Require Import Coq.Reals.Reals.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.

As such, I'll introduce some parameters and assume only the
properties of differentiation I require.
*)

(* Lin f is the linearisation of f *)
Axiom Lin : (R -> R) -> (R -> R).

Parameter f_in : R -> R.
Parameter f_in_prime : R -> R.
Parameter f_in_prime_prime : R -> R.

(* Denote the derivative by D *)
Parameter D : (R -> R) -> (R -> R).

(* Derivative properties *)
Axiom D_linear : forall (f g : R -> R), D (fun x => f x + g x) = fun x => D f x + D g x.
Axiom D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x.

(* Assume the supplied functions are the true first and second order derivatives *)
Axiom f_in_derivative : D f_in = f_in_prime.
Axiom f_in_prime_derivative : D f_in_prime = f_in_prime_prime.

Theorem Lin_exists_uniquely : forall (a : R),
  (forall (x : R), D (D (Lin f_in)) x = 0) ->
  Lin f_in a = f_in a ->
  D (Lin f_in) a = D f_in a -> Lin f_in = fun x => (D f_in a)*(x-a) + f_in a.
Proof.
  intros.

Admitted.
