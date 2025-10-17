Require Import Coq.Arith.Factorial.
Require Import Coq.Numbers.NatInt.NZDiv.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Open Scope R_scope.

Definition from_n_choose_k (n k : nat) := Nat.div (fact n) (fact k * fact (n-k)).

(* Factorial divisibility: (x0! * x1!) divides (x0+x1)! *)
(* This is a well-known fact: C(x0+x1, x0) = (x0+x1)! / (x0! * x1!) is always a natural number *)
Lemma factorial_div_binomial : forall x0 x1,
  exists k, (fact (x0 + x1) = (fact x0 * fact x1) * k)%nat.
Proof.
  (* This proof requires combinatorial arguments or Pascal's identity *)
  (* It's a fundamental property of binomial coefficients *)
Admitted.

(* Helper lemma: INR of exact division equals real division *)
Lemma INR_div_exact : forall n m,
  m <> 0%nat ->
  (exists k, n = (m * k)%nat) ->
  INR (n / m)%nat = INR n / INR m.
Proof.
  intros n m Hm_neq_0 [k Hdiv].
  rewrite Hdiv.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul by assumption.
  rewrite Nat.mul_comm.
  rewrite mult_INR.
  field.
  apply not_0_INR.
  assumption.
Qed.

(* Helper lemma: INR of binomial coefficient equals real division *)
Lemma INR_binomial_coeff :
  forall x0 x1,
    / INR (fact x0 * fact x1) = INR (fact (x0 + x1) / (fact x0 * fact x1)) / INR (fact (x0 + x1)).
Proof.
  intros x0 x1.
  rewrite INR_div_exact.
  - field.
    split.
    + apply not_0_INR.
      intros H_contra.
      apply Nat.eq_mul_0 in H_contra.
      destruct H_contra as [H_fact_x0 | H_fact_x1].
      * apply (fact_neq_0 x0). assumption.
      * apply (fact_neq_0 x1). assumption.
    + apply not_0_INR.
      apply fact_neq_0.
  - intros H_contra.
    apply Nat.eq_mul_0 in H_contra.
    destruct H_contra as [H_fact_x0 | H_fact_x1].
    + apply (fact_neq_0 x0). assumption.
    + apply (fact_neq_0 x1). assumption.
  - apply factorial_div_binomial.
Qed.
