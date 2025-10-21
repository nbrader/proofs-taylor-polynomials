#!/usr/bin/env python3
"""
Understand the inductive step of the row_diag_same_multiset proof.

Key insight: We need to understand what new elements are added when we go from n to S n.
"""

from collections import Counter

def f(i, j):
    """Simple test function for visualization."""
    return 10 * i + j

def row_enum(n):
    """Enumerate (i,j) pairs row-by-row for triangular region with i+j <= n-1."""
    result = []
    for i in range(n):
        for j in range(n - i):
            result.append(f(i, j))
    return result

def diag_enum(n):
    """Enumerate (i,j) pairs diagonally for triangular region with i+j <= n-1."""
    result = []
    for k in range(n):
        for i in range(k + 1):
            j = k - i
            result.append(f(i, j))
    return result

def analyze_inductive_step(n):
    """
    Analyze what happens when we go from n to S n.

    In Coq terms:
    - double_sum_to_list_rows f (S n) (fun i => (n - i + 1))
      enumerates i from 0 to n-1, with j from 0 to (n - i)
      This covers (i,j) with 0 <= i < n and 0 <= j < n-i

    - double_sum_to_list_rows f (S (S n)) (fun i => (S n - i + 1))
      enumerates i from 0 to n, with j from 0 to (S n - i)
      This covers (i,j) with 0 <= i <= n and 0 <= j <= n-i
    """
    print(f"\n=== Inductive step from n={n} to S n={n+1} ===")

    # What IH gives us
    old_rows = row_enum(n)
    old_diags = diag_enum(n)

    print(f"\nIH (for n={n}):")
    print(f"  Rows:  {sorted(old_rows)}")
    print(f"  Diags: {sorted(old_diags)}")
    print(f"  Multisets equal: {Counter(old_rows) == Counter(old_diags)}")

    # What we need to prove
    new_rows = row_enum(n + 1)
    new_diags = diag_enum(n + 1)

    print(f"\nGoal (for S n={n+1}):")
    print(f"  Rows:  {sorted(new_rows)}")
    print(f"  Diags: {sorted(new_diags)}")
    print(f"  Multisets equal: {Counter(new_rows) == Counter(new_diags)}")

    # What's been added?
    added_rows = [x for x in new_rows if x not in Counter(old_rows) or
                  new_rows.count(x) > old_rows.count(x)]
    added_diags = [x for x in new_diags if x not in Counter(old_diags) or
                   new_diags.count(x) > old_diags.count(x)]

    # More precise: using Counter subtraction
    added_rows_counter = Counter(new_rows) - Counter(old_rows)
    added_diags_counter = Counter(new_diags) - Counter(old_diags)

    print(f"\nNew elements added:")
    print(f"  Rows:  {sorted(added_rows_counter.elements())}")
    print(f"  Diags: {sorted(added_diags_counter.elements())}")
    print(f"  New parts equal: {added_rows_counter == added_diags_counter}")

    # Let's understand the structure better
    print(f"\nDetailed structure:")
    print(f"  Old rows had {len(old_rows)} elements")
    print(f"  New rows have {len(new_rows)} elements")
    print(f"  Added {len(new_rows) - len(old_rows)} elements")
    print(f"  Old diags had {len(old_diags)} elements")
    print(f"  New diags have {len(new_diags)} elements")
    print(f"  Added {len(new_diags) - len(old_diags)} elements")

    # What are the new elements structurally?
    print(f"\n  New row elements come from:")
    print(f"    - New row i={n}: j in 0..0 (just j=0), giving f({n},0) = {f(n,0)}")
    print(f"    - Extensions of old rows: each row i gets one more j")
    for i in range(n):
        new_j = n - i
        print(f"      Row i={i}: new j={new_j}, f({i},{new_j}) = {f(i, new_j)}")

    print(f"\n  New diagonal elements come from:")
    print(f"    - New diagonal k={n}: i in 0..{n}, j={n}-i")
    for i in range(n + 1):
        j = n - i
        print(f"      (i={i}, j={j}): f({i},{j}) = {f(i, j)}")

if __name__ == "__main__":
    for n in range(1, 5):
        analyze_inductive_step(n)
