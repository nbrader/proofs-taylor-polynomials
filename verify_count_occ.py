#!/usr/bin/env python3
"""
Verify that row-by-row and diagonal-by-diagonal enumeration
produce the same multiset of values for a triangular region.
"""

from collections import Counter

def double_sum_to_list_rows(f, n, j_func):
    """Row-by-row enumeration of triangular region.

    Args:
        f: function from (i,j) to value
        n: max value of i (we enumerate i from 0 to n-1)
        j_func: function from i to max j value for that row

    Returns:
        list of f(i,j) values in row-by-row order
    """
    result = []
    for i in range(n):
        for j in range(j_func(i)):
            result.append(f(i, j))
    return result

def double_sum_to_list_diags(f, n):
    """Diagonal-by-diagonal enumeration of triangular region.

    Args:
        f: function from (i,j) to value
        n: max value of k (we enumerate k from 0 to n-1)

    Returns:
        list of f(i,j) values in diagonal order,
        where k = i + j and for each k we enumerate i from 0 to k
    """
    result = []
    for k in range(n):
        for i in range(k + 1):
            j = k - i
            result.append(f(i, j))
    return result

def test_multiset_equality(n_max=10):
    """Test that both enumerations produce the same multiset."""

    # Test function: f(i,j) = 10*i + j (simple enough to track)
    def f(i, j):
        return 10 * i + j

    for n in range(1, n_max + 1):
        # j_func(i) = n - i (since we're testing with indices 0..n-1,
        # this gives us the triangular region)
        j_func = lambda i: n - i

        rows_list = double_sum_to_list_rows(f, n, j_func)
        diags_list = double_sum_to_list_diags(f, n)

        rows_counter = Counter(rows_list)
        diags_counter = Counter(diags_list)

        print(f"\nn = {n}:")
        print(f"  Rows:  {sorted(rows_list)}")
        print(f"  Diags: {sorted(diags_list)}")
        print(f"  Multisets equal: {rows_counter == diags_counter}")

        if rows_counter != diags_counter:
            print(f"  MISMATCH!")
            print(f"    Rows counter:  {rows_counter}")
            print(f"    Diags counter: {diags_counter}")
            return False

    return True

if __name__ == "__main__":
    success = test_multiset_equality(10)
    if success:
        print("\n✓ All tests passed: multisets are equal for all tested n")
    else:
        print("\n✗ Test failed: multisets are not equal")
