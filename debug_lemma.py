#!/usr/bin/env python3
"""Debug the helper lemma."""

def f(i, j):
    return f"f({i},{j})"

def rows_list(i_max, j_func):
    result = []
    for i in range(i_max):
        for j in range(j_func(i)):
            result.append(f(i, j))
    return result

def test_lemma(n):
    print(f"\n=== n = {n} ===")

    # LHS of lemma
    lhs_rows = rows_list(n + 1, lambda i: n + 1 - i + 1)  # S n with (S n - i + 1)
    lhs_new = [f(n + 1, 0)]
    lhs = lhs_rows + lhs_new

    # RHS of lemma
    rhs_rows = rows_list(n + 1, lambda i: n - i + 1)  # S n with (n - i + 1)
    rhs_diag = [f(i, max(0, n - i)) for i in range(n + 2)]  # seq 0 (S (S n))
    rhs = rhs_rows + rhs_diag

    print(f"LHS: {lhs}")
    print(f"RHS: {rhs}")
    print(f"Equal: {lhs == rhs}")

    # What should RHS actually be?
    print(f"\nAnalysis:")
    print(f"  LHS rows (j_func = {n+2} - i): {lhs_rows}")
    print(f"  LHS new: {lhs_new}")
    print(f"  RHS rows (j_func = {n+1} - i): {rhs_rows}")
    print(f"  RHS diag (i from 0 to {n+1}, j = {n} - i): {rhs_diag}")

for n in range(3):
    test_lemma(n)
