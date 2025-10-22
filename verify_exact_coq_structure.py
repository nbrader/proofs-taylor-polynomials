#!/usr/bin/env python3
"""
Exactly match the Coq structure to understand the proof.
"""

def f(i, j):
    """Simple test function."""
    return 10 * i + j

def double_sum_to_list_rows(f_func, i_max, j_func):
    """Exact translation of Coq definition."""
    if i_max == 0:
        return []
    else:
        i_prime = i_max - 1
        # Recursive call
        rest = double_sum_to_list_rows(f_func, i_prime, j_func)
        # New row
        new_row = [f_func(i_prime, j) for j in range(j_func(i_prime))]
        return rest + new_row

def double_sum_to_list_diags(f_func, k_max):
    """Exact translation of Coq definition."""
    if k_max == 0:
        return []
    else:
        k_prime = k_max - 1
        # Recursive call
        rest = double_sum_to_list_diags(f_func, k_prime)
        # New diagonal
        new_diag = [f_func(i, k_prime - i) for i in range(k_prime + 1)]
        return rest + new_diag

def analyze_unfold(n):
    """Analyze what happens when we unfold both sides."""
    print(f"\n=== Analyzing n={n} (S n in Coq) ===")

    # IH is for n-1 (which is n in Coq when we're proving for S n)
    if n > 0:
        print(f"\nInductive Hypothesis (for n={n-1}):")
        ih_j_func = lambda i: (n - 1 - i + 1)  # = n - i
        ih_rows = double_sum_to_list_rows(f, n, ih_j_func)
        ih_diags = double_sum_to_list_diags(f, n)
        print(f"  Rows with j_func(i) = {n} - i: {ih_rows}")
        print(f"  Diags: {ih_diags}")
        print(f"  Equal: {ih_rows == ih_diags}")

    # Goal is for n (which is S n in Coq)
    print(f"\nGoal (for n={n}):")
    goal_j_func = lambda i: (n - i + 1)
    goal_rows = double_sum_to_list_rows(f, n + 1, goal_j_func)
    goal_diags = double_sum_to_list_diags(f, n + 1)
    print(f"  Rows with j_func(i) = {n + 1} - i: {goal_rows}")
    print(f"  Diags: {goal_diags}")
    print(f"  Equal: {goal_rows == goal_diags}")

    # After unfold
    print(f"\nAfter unfold:")
    # Rows unfold to:
    #   double_sum_to_list_rows f (S n) j_func
    #   = double_sum_to_list_rows f n j_func ++ map (f n) (seq 0 (j_func n))
    rows_old_part = double_sum_to_list_rows(f, n, goal_j_func)
    rows_new_part = [f(n, j) for j in range(goal_j_func(n))]
    print(f"  Rows old part (with NEW j_func): {rows_old_part}")
    print(f"  Rows new part: {rows_new_part}")
    print(f"  Rows total: {rows_old_part + rows_new_part}")
    print(f"  Matches goal: {rows_old_part + rows_new_part == goal_rows}")

    # Diags unfold to:
    #   double_sum_to_list_diags f (S n)
    #   = double_sum_to_list_diags f n ++ map (fun i => f i (n - i)) (seq 0 (n + 1))
    diags_old_part = double_sum_to_list_diags(f, n)
    diags_new_part = [f(i, n - i) for i in range(n + 1)]
    print(f"  Diags old part: {diags_old_part}")
    print(f"  Diags new part: {diags_new_part}")
    print(f"  Diags total: {diags_old_part + diags_new_part}")
    print(f"  Matches goal: {diags_old_part + diags_new_part == goal_diags}")

    # The problem!
    print(f"\nThe issue:")
    print(f"  IH rows (j_func = {n} - i):     {ih_rows if n > 0 else 'N/A'}")
    print(f"  Unfolded rows old (j_func = {n+1} - i): {rows_old_part}")
    print(f"  These are DIFFERENT! Cannot directly apply IH.")

    if n > 0:
        # What's the difference?
        print(f"\nDifference between IH and unfolded old part:")
        print(f"  IH has j_func(i) = {n} - i")
        print(f"  Unfolded old has j_func(i) = {n + 1} - i")
        print(f"  Each row in unfolded old has ONE MORE element than in IH")

if __name__ == "__main__":
    for n in range(1, 4):
        analyze_unfold(n)
