#!/usr/bin/env python3
"""
Test what summation_binomial_expansion should actually state.

LHS: Σ_{i=0}^n f(i) * (x-a)^i
After binomial: Σ_{i=0}^n f(i) * [Σ_{j=0}^i C(i,j) * x^j * (-a)^(i-j)]
After distribution: Σ_{i=0}^n Σ_{j=0}^i [f(i) * C(i,j) * x^j * (-a)^(i-j)]
After exchange: Σ_{j=0}^n Σ_{i=j}^n [f(i) * C(i,j) * x^j * (-a)^(i-j)]
Factor x^j: Σ_{j=0}^n [Σ_{i=j}^n f(i) * C(i,j) * (-a)^(i-j)] * x^j

Now, if we want inner sum from 0 to (n-j):
Substitute i' = i - j, so i = i' + j
Inner sum becomes: Σ_{i'=0}^{n-j} f(i'+j) * C(i'+j, j) * (-a)^{i'}
"""

from math import comb

def summation_R(f, n):
    """summation_R f n: sums f(0) + ... + f(n-1)"""
    if n == 0:
        return 0
    return sum(f(i) for i in range(n))

def test_binomial_expansion(n_val, x_val, a_val):
    f = lambda i: i + 1  # Simple test function

    # LHS: Σ_{i=0}^n f(i) * (x-a)^i
    # summation_R ... (S n) means sum i from 0 to n
    lhs = summation_R(lambda i: f(i) * (x_val - a_val)**i, n_val + 1)

    # RHS version 1: Σ_{j=0}^n [Σ_{i=j}^n f(i) * C(i,j) * (-a)^(i-j)] * x^j
    rhs1 = summation_R(
        lambda j: summation_R(
            lambda i: f(i) * comb(i, j) * (-a_val)**(i-j) if i >= j else 0,
            n_val + 1
        ) * x_val**j,
        n_val + 1
    )

    # RHS version 2 (with change of variables):
    # Σ_{j=0}^n [Σ_{i'=0}^{n-j} f(i'+j) * C(i'+j, j) * (-a)^{i'}] * x^j
    rhs2 = summation_R(
        lambda j: summation_R(
            lambda i_prime: f(i_prime + j) * comb(i_prime + j, j) * (-a_val)**i_prime,
            n_val - j + 1
        ) * x_val**j,
        n_val + 1
    )

    # RHS version 3 (current Coq statement):
    # Σ_{j=0}^n [Σ_{i=0}^{n-j} f(i) * C(i, j) * (-a)^{i-j}] * x^j
    # This doesn't make sense for i < j!
    rhs3 = summation_R(
        lambda j: summation_R(
            lambda i: f(i) * comb(i, j) * (-a_val)**(i-j) if i >= j else 0,
            n_val - j + 1
        ) * x_val**j,
        n_val + 1
    )

    print(f"n={n_val}, x={x_val}, a={a_val}")
    print(f"LHS: {lhs}")
    print(f"RHS1 (i from j to n): {rhs1}")
    print(f"RHS2 (i' from 0 to n-j, with i=i'+j): {rhs2}")
    print(f"RHS3 (current Coq, i from 0 to n-j, no shift): {rhs3}")
    print(f"LHS == RHS1: {abs(lhs - rhs1) < 1e-10}")
    print(f"LHS == RHS2: {abs(lhs - rhs2) < 1e-10}")
    print(f"LHS == RHS3: {abs(lhs - rhs3) < 1e-10}")
    print()

# Test with several values
test_binomial_expansion(3, 2.0, 0.5)
test_binomial_expansion(4, 1.5, 0.3)
test_binomial_expansion(2, 3.0, 1.0)
