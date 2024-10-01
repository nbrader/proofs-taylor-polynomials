Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.
As such, I'll assume only the properties of differentiation I require.
*)

(* The input function *)
Axiom F : R -> R.

(* Lin f is the linearisation of f *)
Axiom Lin : R -> (R -> R) -> (R -> R).

(* Denote the derivative by D *)
Axiom D : (R -> R) -> (R -> R).

(* Derivative properties *)
Axiom zero_integral : forall (f : R -> R), (D f = fun x => 0) -> exists (c : R), f = fun x => c.
Axiom constant_integral : forall (f : R -> R), forall (c : R), (D f = fun x => c) -> exists (c' : R), f = fun x => c*x + c'.

(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Lin_implem : forall (a : R),

  (* The second derivative of any linearisation of F is zero. *)
  (D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  Lin a F a = F a ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  D (Lin a F) a = D F a -> Lin a F = fun x => (D F a)*(x-a) + F a.
Proof.
  intros a Lin_second_deriv_is_0 Lin_equals_F_at_a Lin_deriv_equals_F_deriv_at_a.
  (*
    Givens:
      lin_f''(x) = 0
      lin_f(a) = f(a)
      lin_f'(a) = f'(a)
  *)

  apply (zero_integral (D (Lin a F))) in Lin_second_deriv_is_0.
  destruct Lin_second_deriv_is_0 as [x first_deriv_Lin_is_c].
  assert (linear_coeff_def_is_D_F_a : D (Lin a F) a = x) by (rewrite first_deriv_Lin_is_c; reflexivity).
  rewrite Lin_deriv_equals_F_deriv_at_a in linear_coeff_def_is_D_F_a. clear Lin_deriv_equals_F_deriv_at_a.
  (*
    Given
      lin_f''(x) = 0

    then
      lin_f'(x) = c

    and so
      c = f'(a)
  *)

  apply (constant_integral (Lin a F) x) in first_deriv_Lin_is_c.
  destruct first_deriv_Lin_is_c as [x0 Lin_def].
  assert (algebra_1 : Lin a F a = x * a + x0) by (rewrite Lin_def; reflexivity).
  rewrite Lin_equals_F_at_a in algebra_1. clear Lin_equals_F_at_a.
  rewrite <- linear_coeff_def_is_D_F_a in algebra_1.
  assert (constant_term_def : x0 = F a - (D F a) * a) by (rewrite algebra_1; ring). clear algebra_1.
  (*
    Given
      lin_f'(x) = c
    
    then
      lin_f(x) = c*x + c'
    
    and so
      c' = f(a) - f'(a) * a
  *)

  rewrite constant_term_def in Lin_def. clear constant_term_def.
  rewrite <- linear_coeff_def_is_D_F_a in Lin_def. clear linear_coeff_def_is_D_F_a.
  assert (algebra_2 : ((fun x : R => D F a * x + (F a - D F a * a)) = (fun x : R => D F a * (x - a) + F a))) by (apply functional_extensionality; intros; ring).
  rewrite algebra_2 in Lin_def. clear algebra_2.
  (*
    Thus:
      lin_f(x) = f'(a)*(x-a) + f(a)
  *)

  apply Lin_def.
Qed.