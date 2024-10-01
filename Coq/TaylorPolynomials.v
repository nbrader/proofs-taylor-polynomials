Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope R_scope.

(*
I'm going to avoid having to define differentiation, limits etc.
As such, I'll assume only the properties of differentiation I require.
*)

(* Proof that the linearisation of a function must be the Taylor polynomial of it of degree 1. *)
Theorem Lin_implem :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) -> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) -> exists (c' : R), f = fun x => c*x + c'),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

  (* The input function *)
  forall (F : R -> R),
  
  (* The point about which we linearise F *)
  forall (a : R),
  
  Lin a F = fun x => (D F a)*(x-a) + F a.
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

Theorem Lin_example :
  (* Lin f is the linearisation of f *)
  forall (Lin : R -> (R -> R) -> (R -> R)),

  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),

  (* Derivative properties *)
  forall (zero_integral : forall (f : R -> R), (D f = fun x => 0) -> exists (c : R), f = fun x => c),
  forall (constant_integral : forall (f : R -> R) (c : R), (D f = fun x => c) -> exists (c' : R), f = fun x => c*x + c'),
  forall (linear_integral : forall (f : R -> R) (c : R), (D f = fun x => c*x) -> exists (c' : R), f = fun x => 0.5*c*x*x + c'),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R) (F : R -> R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  (forall (a : R) (F : R -> R), Lin a F a = F a) ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  (forall (a : R) (F : R -> R), D (Lin a F) a = D F a) ->

  Lin 0 (fun x => 3*x*x*x + 5*x*x - 7) = fun x => (D (fun x => 3*x*x*x + 5*x*x - 7) 0)*(x-0) + (fun x => 3*x*x*x + 5*x*x - 7) 0.
Proof.
  intros Lin D
         zero_integral constant_integral linear_integral
         Lin_second_deriv_is_0
         Lin_equals_F_at_a
         Lin_deriv_equals_F_deriv_at_a.
  pose proof (Lin_implem Lin D zero_integral constant_integral Lin_second_deriv_is_0 Lin_equals_F_at_a Lin_deriv_equals_F_deriv_at_a (fun x => 3*x*x*x + 5*x*x - 7) 0).
  apply H.
Qed.
