Require Import Coq.Arith.Factorial.
Require Import Coq.Numbers.NatInt.NZDiv.

Definition from_n_choose_k (n k : nat) := Nat.div (fact n) (fact k * fact (n-k)).
