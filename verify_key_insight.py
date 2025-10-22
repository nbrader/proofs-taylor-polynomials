#!/usr/bin/env python3
"""
Verify the key insight for the inductive step.

Key insight:
  (rows_old_part - IH_rows) + rows_new_part == diags_new_part  (as multisets)

Where:
  - rows_old_part = double_sum_to_list_rows f n (fun i => S n - i + 1)
  - IH_rows = double_sum_to_list_rows f n (fun i => n - i + 1)
  - rows_new_part = [f n 0]
  - diags_new_part = [f i (n - i) | i <- 0..n]
"""

from collections import Counter

def f(i, j):
    return 10 * i + j

def rows_enum(i_max, j_func):
    result = []
    for i in range(i_max):
        for j in range(j_func(i)):
            result.append(f(i, j))
    return result

def verify_key_insight(n):
    print(f"\n=== n={n} ===")

    # IH rows
    ih_j_func = lambda i: n - i
    ih_rows = rows_enum(n, ih_j_func)

    # Unfolded rows old part (with NEW j_func)
    new_j_func = lambda i: n + 1 - i
    rows_old_part = rows_enum(n, new_j_func)

    # Rows new part
    rows_new_part = [f(n, 0)]

    # Diags new part
    diags_new_part = [f(i, n - i) for i in range(n + 1)]

    # The difference
    extensions = Counter(rows_old_part) - Counter(ih_rows)

    # The key equation
    lhs = Counter(list(extensions.elements()) + rows_new_part)
    rhs = Counter(diags_new_part)

    print(f"IH rows (j_func = {n} - i):            {ih_rows}")
    print(f"Rows old part (j_func = {n+1} - i):    {rows_old_part}")
    print(f"Extensions (difference):               {sorted(extensions.elements())}")
    print(f"Rows new part:                         {rows_new_part}")
    print(f"Diags new part:                        {diags_new_part}")
    print(f"")
    print(f"Extensions + rows_new:                 {sorted(lhs.elements())}")
    print(f"Diags new:                             {sorted(rhs.elements())}")
    print(f"Equal as multisets: {lhs == rhs}")

    # Let's also understand what the extensions are
    print(f"\nExtensions are:")
    for i in range(n):
        old_max_j = n - i
        new_max_j = n + 1 - i
        if new_max_j > old_max_j:
            for j in range(old_max_j, new_max_j):
                print(f"  Row i={i}: f({i},{j}) = {f(i,j)}")

if __name__ == "__main__":
    for n in range(1, 6):
        verify_key_insight(n)
