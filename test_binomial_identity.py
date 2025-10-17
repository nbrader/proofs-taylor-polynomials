#!/usr/bin/env python3
"""
Test the binomial coefficient identity needed for line 621 in TaylorPolynomials.v

Goal: / INR (fact x0 * fact x1) = INR (fact (x0 + x1) / (fact x0 * fact x1)) / INR (fact (x0 + x1))

This translates to:
  1 / (x0! * x1!) = C(x0+x1, x0) / (x0+x1)!

Where C(n,k) = n! / (k! * (n-k)!)

We need to verify:
  INR(fact(S x0 + S x1) / (fact(S x0) * fact(S x1))) = INR(fact(S x0 + S x1)) / INR(fact(S x0) * fact(S x1))

In other words, the natural division equals the real division.
"""

import math

def factorial(n):
    return math.factorial(n)

def binomial_coeff(n, k):
    """Compute binomial coefficient C(n, k)"""
    return factorial(n) // (factorial(k) * factorial(n - k))

def test_identity(x0, x1):
    """Test if the identity holds for given x0, x1"""
    # Left side: 1 / (x0! * x1!)
    left = 1.0 / (factorial(x0) * factorial(x1))

    # Right side: C(x0+x1, x0) / (x0+x1)!
    n = x0 + x1
    binom = binomial_coeff(n, x0)
    right = binom / factorial(n)

    # Also verify that the natural division equals real division
    nat_div = factorial(n) // (factorial(x0) * factorial(x1))
    real_div = factorial(n) / (factorial(x0) * factorial(x1))

    print(f"x0={x0}, x1={x1}:")
    print(f"  Left:  1/(x0!*x1!) = {left:.10f}")
    print(f"  Right: C({n},{x0})/{n}! = {right:.10f}")
    print(f"  Equal: {abs(left - right) < 1e-10}")
    print(f"  Nat div: {n}!/(x0!*x1!) = {nat_div}")
    print(f"  Real div: {n}!/(x0!*x1!) = {real_div:.1f}")
    print(f"  Divisions equal: {nat_div == int(real_div)}")
    print()

    return abs(left - right) < 1e-10

# Test for various values
print("Testing binomial coefficient identity:")
print("=" * 50)

for x0 in range(0, 10):
    for x1 in range(0, 10):
        if not test_identity(x0, x1):
            print(f"FAILED for x0={x0}, x1={x1}")
            exit(1)

print("All tests passed!")
print()
print("Key insight: fact(x0 + x1) is always divisible by (fact(x0) * fact(x1))")
print("This is because C(x0+x1, x0) = (x0+x1)! / (x0! * x1!) is always a natural number")
