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
Theorem Lin_exists_uniquely : forall (a : R),

  (* The second derivative of any linearisation of F is zero. *)
  (forall (a : R), D (D (Lin a F)) = fun x => 0) ->

  (* The linearisation at a of F applied to a is equal to F applied to a. *)
  Lin a F a = F a ->

  (* The first derivative of the linearisation at a of F applied to a is equal to the first derivative of F applied to a. *)
  D (Lin a F) a = D F a -> Lin a F = fun x => (D F a)*(x-a) + F a.
Proof.
  intros.
  pose proof (H a).

  apply (zero_integral (D (Lin a F))) in H2.

  destruct H2.
  assert (D (Lin a F) a = x) by (rewrite H2; reflexivity).
  rewrite H1 in H3. clear H1.

  apply (constant_integral (Lin a F) x) in H2.

  destruct H2.

  assert (Lin a F a = x * a + x0) by (rewrite H1; reflexivity).
  rewrite H0 in H2. clear H0.
  rewrite <- H3 in H2.

  assert (x0 = F a - (D F a) * a) by (rewrite H2; ring). clear H2.
  rewrite H0 in H1. clear H0.
  rewrite <- H3 in H1. clear H3.

  assert (((fun x : R => D F a * x + (F a - D F a * a)) = (fun x : R => D F a * (x - a) + F a))) by (apply functional_extensionality; intros; ring).
  rewrite H0 in H1. clear H0.
  
  apply H1.
Qed.