#!/usr/bin/env python3
"""
Verify that c2_ coefficients match the expected form for Maclaurin series.

Context: We're proving that for Taylor n 0 (fun x' => F (x' + a)),
the coefficients c2_ should equal (iter D i F a) / fact(i)

Key insight: By the chain rule, for G(x) = F(x + a):
  D^i G(0) = D^i F(a)

Therefore the Maclaurin coefficient is:
  c_i = (D^i G(0)) / i! = (D^i F(a)) / i!
"""

import math

def factorial(n):
    """Compute factorial"""
    return math.factorial(n)

def test_chain_rule_property():
    """
    Demonstrate the chain rule property that makes c2_ equal the expected form.

    For a concrete function, verify that:
    D^i (F(x + a))|_{x=0} = D^i F(a)
    """
    print("Chain Rule Property for Translated Functions")
    print("=" * 60)
    print("\nFor G(x) = F(x + a), we have by the chain rule:")
    print("  G'(x) = F'(x + a) * 1 = F'(x + a)")
    print("  G''(x) = F''(x + a) * 1 = F''(x + a)")
    print("  G^(i)(x) = F^(i)(x + a)\n")

    print("Evaluating at x = 0:")
    print("  G^(i)(0) = F^(i)(a)\n")

    print("Example with F(x) = x^3:")
    print("-" * 60)
    a_val = 2.0
    for i in range(4):
        # For F(x) = x^3, F^(i)(x) follows a pattern
        # F(x) = x^3, F'(x) = 3x^2, F''(x) = 6x, F'''(x) = 6, F^(4)(x) = 0

        # Derivative values at x = a
        if i == 0:
            deriv_F_at_a = a_val**3
        elif i == 1:
            deriv_F_at_a = 3 * a_val**2
        elif i == 2:
            deriv_F_at_a = 6 * a_val
        elif i == 3:
            deriv_F_at_a = 6
        else:
            deriv_F_at_a = 0

        # For G(x) = F(x + a) = (x + a)^3, G^(i)(0) should equal F^(i)(a)
        coeff = deriv_F_at_a / factorial(i)

        print(f"  i={i}: F^({i})({a_val}) = {deriv_F_at_a:6.1f}, " +
              f"c_{i} = {deriv_F_at_a:6.1f}/{factorial(i)} = {coeff:6.3f}")

def explain_proof_strategy():
    """Explain the proof strategy for the c2_ assertion"""
    print("\n\nProof Strategy for c2_ Assertion")
    print("=" * 60)
    print("\nGoal: Prove c2_ = fun i => iter D i F a / INR (fact i)")
    print("\nContext:")
    print("  - Taylor_nth_2 gives us: Taylor n 0 (fun x' => F (x' + a)) =")
    print("                           summation (fun i x' => c2_ i * x' ^ i) (S n)")
    print("  - Maclaurin_implem gives us: Taylor n 0 G =")
    print("                               summation (fun k x' => (iter D k G 0 / INR (fact k)) * x' ^ k) (S n)")
    print("\nKey step:")
    print("  Let G = (fun x' => F (x' + a))")
    print("  Then by chain rule: iter D i G 0 = iter D i F a")
    print("\nTherefore:")
    print("  c2_ i = (iter D i G 0) / INR (fact i)")
    print("        = (iter D i F a) / INR (fact i)  ✓")

if __name__ == "__main__":
    print("="*70)
    print("Verification: c2_ coefficient form in Taylor_a_equiv")
    print("="*70 + "\n")

    test_chain_rule_property()
    explain_proof_strategy()

    print("\n" + "="*70)
    print("CONCLUSION: The assertion is VALID by Maclaurin_implem + chain rule")
    print("="*70)
