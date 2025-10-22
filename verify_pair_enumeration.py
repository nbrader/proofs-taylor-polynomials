#!/usr/bin/env python3
"""
Verify the correct enumeration of pairs for the triangular region.

For a given n, we want pairs (i,j) where i+j <= n.
This forms a triangular region.

Row enumeration: for each i in 0..n, enumerate j values
Diagonal enumeration: for each k in 0..n, enumerate i values where j = k-i
"""

def pairs_by_rows_v1(n):
    """Row enumeration with j_func(i) = (n - i + 1)"""
    pairs = []
    for i in range(n + 1):
        row_size = n - i + 1
        for j in range(row_size):
            pairs.append((i, j))
    return pairs

def pairs_by_rows_v2(n):
    """Row enumeration with j_func(i) = (n - i)"""
    pairs = []
    for i in range(n + 1):
        row_size = n - i
        for j in range(row_size):
            pairs.append((i, j))
    return pairs

def pairs_by_diags(n):
    """Diagonal enumeration: for each k in 0..n, enumerate i in 0..k with j = k-i"""
    pairs = []
    for k in range(n + 1):
        for i in range(k + 1):
            j = k - i
            pairs.append((i, j))
    return pairs

def verify_triangular_region(pairs, n):
    """Check if all pairs satisfy i + j <= n"""
    for i, j in pairs:
        if i + j > n:
            return False
    return True

def check_enumeration(n):
    print(f"\n=== Testing n = {n} ===")

    # Generate pair lists
    rows_v1 = pairs_by_rows_v1(n)
    rows_v2 = pairs_by_rows_v2(n)
    diags = pairs_by_diags(n)

    print(f"Row enumeration v1 (n-i+1): {len(rows_v1)} pairs")
    print(f"  Pairs: {rows_v1}")
    print(f"  All satisfy i+j <= n: {verify_triangular_region(rows_v1, n)}")

    print(f"\nRow enumeration v2 (n-i): {len(rows_v2)} pairs")
    print(f"  Pairs: {rows_v2}")
    print(f"  All satisfy i+j <= n: {verify_triangular_region(rows_v2, n)}")

    print(f"\nDiagonal enumeration: {len(diags)} pairs")
    print(f"  Pairs: {diags}")
    print(f"  All satisfy i+j <= n: {verify_triangular_region(diags, n)}")

    # Check if they're the same multiset
    set_v1 = set(rows_v1)
    set_v2 = set(rows_v2)
    set_diags = set(diags)

    print(f"\nRow v1 == Diags: {set_v1 == set_diags}")
    print(f"Row v2 == Diags: {set_v2 == set_diags}")

    if set_v1 != set_diags:
        print(f"  V1 - Diags: {set_v1 - set_diags}")
        print(f"  Diags - V1: {set_diags - set_v1}")

    if set_v2 != set_diags:
        print(f"  V2 - Diags: {set_v2 - set_diags}")
        print(f"  Diags - V2: {set_diags - set_v2}")

# Test for several values of n
for n in range(5):
    check_enumeration(n)

print("\n=== Summary ===")
print("The triangular region {(i,j) : 0 <= i <= n, 0 <= j <= n, i+j <= n}")
print("For row i, the valid j values are 0 <= j <= n-i")
print("That's (n-i+1) values: j in {0, 1, 2, ..., n-i}")
print("\nTherefore, the correct row size function is: (n - i + 1)")
