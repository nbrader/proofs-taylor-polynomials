Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope R_scope.

Require Import CoqUtilLib.Iteration.

Require Import TaylorPolynomials.Differentiation.
Require Import TaylorPolynomials.IteratedDifferentiation.
Require Import TaylorPolynomials.Summation.


Theorem linear_integral_ :
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
  forall (f : R -> R) (c : R), (D f = fun x => c*x) <-> exists (c' : R), f = fun x => (1/2)*c*x^2 + c'.
Proof.
  intros.
  split.
  - intros.
    assert (quadratic_deriv : D (fun x : R => x ^ 2) = (fun x : R => 2 * x)).
    {
      pose proof (nth_pow_deriv D linear_deriv D_product_rule 1).
      simpl in *.
      rewrite H0.
      apply functional_extensionality.
      intros.
      ring.
    }
    assert (D (fun x : R => c / 2 * (x^2)) = (fun x : R => c * x)).
    {
      rewrite D_homog.
      rewrite quadratic_deriv.
      apply functional_extensionality.
      intro.
      field.
    }
    rewrite <- H0 in H. clear H0.
    assert ((fun x : R => c / 2 * (x^2)) = (fun x : R => 1 / 2 * c * x^2)) by (apply functional_extensionality; intro; field). rewrite H0 in H. clear H0.
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
    assert (quadratic_deriv : D (fun x : R => x ^ 2) = (fun x : R => 2 * x)).
    {
      pose proof (nth_pow_deriv D linear_deriv D_product_rule 1).
      simpl in *.
      rewrite H0.
      apply functional_extensionality.
      intros.
      ring.
    }
    destruct H.
    rewrite H.
    rewrite D_additive.
    replace x with (x * 1) by ring.
    rewrite (D_homog (fun _ => 1) x).
    rewrite unit_deriv.
    replace (x * 0) with 0 by ring.
    replace (D (fun x1 : R => 1 / 2 * c * x1^2)) with (fun x1 : R => c * x1).
    {
      apply functional_extensionality.
      intro.
      field.
    }
    apply functional_extensionality.
    intro.
    rewrite (D_homog (fun x0 : R => x0^2) (1/2 * c)).
    rewrite quadratic_deriv.
    field.
Qed.

Theorem quadratic_integral_ :
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
  forall (f : R -> R) (c : R), (D f = fun x => c*x^2) <-> exists (c' : R), f = fun x => (1/3)*c*x^3 + c'.
Proof.
  intros D zero_integral constant_integral unit_deriv linear_deriv
         D_additive D_homog D_product_rule integration_constant f c.

  (* Step 1: Assume D f = fun x => c * x^2 *)
  split.
  - intro H.
    (* We aim to show that f = (1/3) * c * x^3 + c' *)
    
    (* Step 2: Consider a candidate solution *)
    (* Let g(x) = (1/3) * c * x^3. By differentiating this, we get g'(x) = c * x^2 *)
    assert (H2 : D (fun x => (1/3) * c * (x^3)) = fun x => c * x^2).
    { (* Derive this from the linearity and power rule of the derivative *)
      (* Use D_homog and D_product_rule to handle the derivative of x^3 *)
      (* Proof omitted, but follows from applying the hypothesis *)
      rewrite (D_homog (fun x : R => (x^3)) (1 / 3 * c)).
      assert (cubic_deriv : D (fun x : R => x^3) = (fun x : R => 3 * x^2)).
      {
        pose proof (nth_pow_deriv D linear_deriv D_product_rule 2).
        simpl in *.
        rewrite H0.
        apply functional_extensionality.
        intros.
        ring.
      }
      rewrite cubic_deriv. clear cubic_deriv.
      apply functional_extensionality.
      intro.
      field.
    }
    
    assert (H1 : D (fun x => (1/3) * c * x^3) = fun x => c * x^2).
    {
      replace (fun x0 : R => 1 / 3 * c * x0^3) with (fun x : R => (1/3*c) * (x^3)) by (apply functional_extensionality; intro; field).
      apply H2.
    }
    
    (* Step 3: Since D f = D g, apply integration_constant *)
    specialize (integration_constant f (fun x => (1/3) * c * x^3)).
    assert (D f = D (fun x => (1/3) * c * x^3)) by (rewrite H1; apply H).
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
    assert (cubic_deriv : D (fun x : R => x^3) = (fun x : R => 3 * x^2)).
    {
      pose proof (nth_pow_deriv D linear_deriv D_product_rule 2).
      simpl in *.
      rewrite H.
      apply functional_extensionality.
      intros.
      ring.
    }
    assert (D (fun x : R => (1/3*c) * (x^3)) = (fun x : R => c * (x^2))).
    {
      rewrite (D_homog (fun x : R => (x^3)) (1 / 3 * c)).
      rewrite cubic_deriv.
      apply functional_extensionality.
      intro.
      field.
    }
    replace (fun x0 : R => 1 / 3 * c * x0 * x0 * x0) with (fun x : R => (1/3*c) * (x*x*x)) by (apply functional_extensionality; intro; field).
    apply functional_extensionality.
    intro.
    rewrite H.
    field.
    (* Derive that D f = fun x => c * x^2 *)
    (* Proof omitted for brevity, but follows directly *)
Qed.

Theorem nth_integral_of_zero :
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
  intros D constant_integral D_additive D_homog D_product_rule integration_constant n.
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

Theorem nth_integration_constant :
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

  (* The (n+1)th derivative of any Taylor polynomial of degree n of F is zero *)
  (forall (n : nat) (a : R) (F : R -> R), iter D (S n) (Taylor n a F) = fun x => 0) ->

  (* The mth derivative of the Taylor polynomial of degree n at a where m <= n is equal to the mth derivative of F applied to a *)
  (forall (degree order : nat) (a : R) (F : R -> R), (le order degree) -> iter D order (Taylor degree a F) a = iter D order F a) ->

  (* The implementation of the Taylor polynomial of degree n at a for F must be the sum of the first n terms of the Taylor series: *)
  forall (f g : R -> R) (n : nat), iter D n f = iter D n g -> exists (c_ : nat -> R), f = (fun x : R => g x + summation (fun i x' => (c_ i) * x'^i) (S n) x).
Proof.
  intros Taylor D constant_integral D_additive D_homog D_product_rule integration_constant Taylor_degree Taylor_agrees_at_a f g n f_and_g_agree_at_nth_D.
  pose proof (nth_integral_of_zero D constant_integral D_additive D_homog D_product_rule integration_constant) as nth_integral_of_zero.

  assert (iter D (S n) (fun x => f x - g x) = fun _ => 0).
  {
    simpl in *.
    unfold Rminus.

    rewrite (iter_D_additive D D_additive n f (fun x => - g x)).
    rewrite D_additive.
    rewrite f_and_g_agree_at_nth_D.
    rewrite <- D_additive.
    rewrite <- (iter_D_additive D D_additive).
    replace (fun x : R => g x + - g x) with (fun _ : R => 0) by (apply functional_extensionality; intros; ring).
    replace 0 with (0*1) by field.
    rewrite (iter_D_homog D D_homog n (fun _ => 1)).
    rewrite D_homog.
    apply functional_extensionality.
    intros.
    now ring.
  }
  clear f_and_g_agree_at_nth_D.

  apply (nth_integral_of_zero) in H.

  assert (f = g <-> (fun x => f x - g x) = fun _ => 0).
  {
    split.
    - intros.
      apply functional_extensionality.
      intros.
      rewrite H0.
      field.

    - intros.
      set (z := (fun _ : R => 0)).
      replace g with (fun x => g x + z x) by (unfold z; apply functional_extensionality; intros; ring).
      replace (fun _ : R => 0) with z in H0 by reflexivity.
      rewrite <- H0.
      apply functional_extensionality.
      intros.
      ring.
  }

  destruct H as [c IHn].
  exists c.
  replace (summation (fun (i : nat) (x' : R) => c i * x' ^ i) (S n)) with (fun x : R => f x - g x).
  apply functional_extensionality.
  intros.
  ring.
Qed.
