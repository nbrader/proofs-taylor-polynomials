Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope R_scope.

Require Import TaylorPolynomials.Summation.


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

Lemma zero_deriv :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  forall (x : R), D (fun _ => 0) x = (fun _ => 0) x.
Proof.
  intros.
  replace (0) with (0*1) by field.
  rewrite (D_homog (fun _ => 1) 0).
  field.
Qed.

Lemma zero_deriv_extensional :
  (* Denote the derivative by D *)
  forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R), forall (s : R), D (fun x => s * f x) = fun x => s * D f x),
  D (fun _ => 0) = (fun _ => 0).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply (zero_deriv D D_homog).
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

Lemma D_additive_over_summation :
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
    apply (zero_deriv D D_homog).
  
  - (* Inductive step: n -> S n *)
    simpl.
    rewrite <- IH.
    rewrite D_additive.
    reflexivity.
Qed.