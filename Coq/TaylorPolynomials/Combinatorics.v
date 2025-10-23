Require Import Coq.Arith.Factorial.
Require Import Coq.Numbers.NatInt.NZDiv.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Require Import Psatz.
From mathcomp Require Import ssreflect ssrnat ssrbool binomial.
Open Scope R_scope.

Definition from_n_choose_k (n k : nat) := Nat.div (fact n) (fact k * fact (n-k)).

(* Factorial divisibility: (x0! * x1!) divides (x0+x1)! *)
(* This is a well-known fact: C(x0+x1, x0) = (x0+x1)! / (x0! * x1!) is always a natural number *)

(* Define binomial coefficient recursively via Pascal's identity *)
Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | _, 0 => 1
  | 0, S _ => 0
  | S n', S k' => (binom n' k' + binom n' k)%nat
  end.

(* Proving the binomial coefficient formula from scratch requires significant
   combinatorial infrastructure. For a complete proof, one would need to:
   1. Prove Pascal's identity: C(n+1, k+1) = C(n,k) + C(n, k+1)
   2. Use strong induction to show binom satisfies the factorial formula
   3. Handle edge cases carefully with divisibility lemmas

   This is a well-known result in combinatorics, and for the purposes of this
   practice project, we admit it. For production proofs, see Coquelicot or
   use the math-comp library which has comprehensive binomial coefficient support.
*)

(* Prove equivalence between Coq stdlib fact and math-comp factorial *)
Lemma fact_eq_factorial : forall n, fact n = factorial n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma factorial_div_binomial : forall x0 x1,
  exists k, (fact (x0 + x1) = (fact x0 * fact x1) * k)%nat.
Proof.
  intros x0 x1.
  (* The witness is the binomial coefficient C(x0+x1, x0) *)
  exists (binomial (x0 + x1) x0).
  (* Convert Coq stdlib fact to math-comp factorial *)
  rewrite !fact_eq_factorial.
  (* Goal: (x0 + x1)`! = (x0`! * x1`! * 'C(x0 + x1, x0))%N *)
  (* bin_fact states: 'C(n, m) * (m`! * (n - m)`!) = n`! *)
  (* Swap the order: (a * b) * c = c * (a * b) using mulnC *)
  rewrite mulnC.
  (* Goal is now: (x0 + x1)`! = ('C(x0 + x1, x0) * (x0`! * x1`!))%N *)
  (* Rewrite x1! as ((x0+x1)-x0)! *)
  rewrite [x1`!](_ : x1`! = ((x0 + x1) - x0)`!); last first.
  { by rewrite addKn. }
  (* Now goal is: (x0 + x1)`! = ('C(x0 + x1, x0) * (x0`! * ((x0 + x1) - x0)`!))%N *)
  (* Apply bin_fact which states: 'C(n, m) * (m`! * (n - m)`!) = n`! *)
  symmetry.
  apply bin_fact.
  (* Show x0 <= x0 + x1 *)
  by apply leq_addr.
Qed.

(* Helper lemma: INR of exact division equals real division *)
Lemma INR_div_exact : forall n m,
  m <> 0%nat ->
  (exists k, n = (m * k)%nat) ->
  INR (n / m)%nat = INR n / INR m.
Proof.
  intros n m Hm_neq_0 [k Hdiv].
  rewrite Hdiv.
  (* Simplify (m * k) / m = k *)
  assert (Hdiv_simp: ((m * k) / m)%nat = k).
  {
    (* Use the fact that (k * m) / m = k when m <> 0 *)
    replace (m * k)%nat with (k * m)%nat.
    - apply Nat.div_mul. assumption.
    - apply Nat.mul_comm.
  }
  rewrite Hdiv_simp.
  (* Expand INR (m * k) *)
  assert (Hmult_INR: INR (m * k)%nat = (INR m * INR k)%R).
  { apply mult_INR. }
  rewrite Hmult_INR.
  (* Now we have: INR k = INR m * INR k / INR m *)
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

(* Define a corrected binomial coefficient that properly handles k > n *)
Definition C_correct (n k : nat) : R :=
  if Nat.leb k n then C n k else 0.

(* Prove that C_correct equals INR of mathcomp's binomial *)
Lemma C_correct_eq_INR_binomial : forall n k,
  C_correct n k = INR (binomial n k).
Proof.
  intros n k.
  unfold C_correct.
  destruct (Nat.leb k n) eqn:Hle.
  - (* k <= n case *)
    apply Nat.leb_le in Hle.
    unfold C.
    destruct n as [|n'].
    + (* n = 0 *)
      destruct k as [|k'].
      * (* k = 0 *)
        rewrite (binE 0 0). simpl. field.
      * (* k > 0, but k <= 0, contradiction *)
        lia.
    + (* n = S n' *)
      (* Goal: C (S n') k = INR (binomial (S n') k) *)
      (* C (S n') k is defined as: INR (fact (S n')) / (INR (fact k) * INR (fact ((S n') - k))) *)

      (* We need to show this equals INR (binomial (S n') k) *)
      (* Use the fact that binomial (S n') k * (fact k * fact ((S n') - k)) = fact (S n') *)
      (* This comes from bin_fact in mathcomp *)

      (* First, convert Coq's fact to mathcomp's factorial *)
      rewrite !fact_eq_factorial.

      (* Now use the relationship between binomial and factorials *)
      (* bin_fact: 'C(n, m) * (m`! * (n - m)`!) = n`! when m <= n *)
      have Hk_le: (k <= S n')%N by apply/leP; lia.
      rewrite -(bin_fact Hk_le).

      (* Now we have: INR ((S n')`!) / (INR (k`!) * INR (((S n') - k)`!)) =
                       INR ('C(S n', k) * (k`! * ((S n') - k)`!)) / (INR (k`!) * INR (((S n') - k)`!)) *)

      rewrite mult_INR.
      rewrite mult_INR.

      (* Now simplify: INR('C) * INR(k`! * ((S n') - k)`!) / (INR(k`!) * INR(((S n') - k)`!)) = INR('C) *)
      (* This is: (INR('C) * (INR(k`!) * INR(((S n') - k)`!))) / (INR(k`!) * INR(((S n') - k)`!)) = INR('C) *)

      (* Factorials are always non-zero, use conversion to Coq's fact *)
      assert (H_fact_k_neq_0: k`! <> 0%N).
      { rewrite -fact_eq_factorial. apply fact_neq_0. }

      assert (H_fact_nk_neq_0: (S n' - k)`! <> 0%N).
      { rewrite -fact_eq_factorial. apply fact_neq_0. }

      assert (H_denom_neq_0: INR (k`!) * INR ((S n' - k)`!) <> 0).
      {
        apply Rmult_integral_contrapositive.
        split; apply not_0_INR; assumption.
      }

      (* Both sides have the same denominator, and numerators are equal by bin_fact *)
      (* LHS: INR ((S n')`!) / (INR (k`!) * INR ((S n' - k)`!)) *)
      (* RHS after rewrite: INR ('C * (k`! * ...)) / (INR (k`!) * INR (...)) *)
      (*                  = INR ('C) * INR (k`! * ...) / (INR (k`!) * INR (...)) *)
      (*                  = INR ('C) when we cancel the common factor *)

      (* Use the fact that (a * b) / b = a when b <> 0 *)
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (INR (binomial (S n') k))).
      admit.
  - (* k > n case *)
    apply Nat.leb_gt in Hle.
    have Hlt: (n < k)%N by apply/ltP; lia.
    rewrite bin_small; [reflexivity | exact Hlt].
Admitted.
