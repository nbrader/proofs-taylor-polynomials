#!/usr/bin/env python3
"""
Test the order of summation for summation_R vs sum_f_R0.

summation_R f (S n) = f(n) + summation_R f n = f(n) + f(n-1) + ... + f(0)
sum_f_R0 f n = f(0) + f(1) + ... + f(n)
"""

def summation_R(f, n):
    """
    summation_R f n sums from (n-1) down to 0 when n > 0.
    summation_R f 0 = 0
    summation_R f (S n') = f(n') + summation_R f n'
    """
    if n == 0:
        return 0
    else:
        n_prime = n - 1
        return f(n_prime) + summation_R(f, n_prime)

def sum_f_R0(f, n):
    """
    sum_f_R0 f n sums from 0 up to n.
    sum_f_R0 f 0 = f(0)
    sum_f_R0 f (S i) = sum_f_R0 f i + f(S i)
    """
    if n == 0:
        return f(0)
    else:
        i = n - 1
        return sum_f_R0(f, i) + f(n)

def f(i):
    return i * 10

print("Testing summation_R vs sum_f_R0:")
for n in range(5):
    sr = summation_R(f, n + 1)  # S n in Coq
    sf = sum_f_R0(f, n)
    print(f"n={n}: summation_R f (S {n}) = {sr}, sum_f_R0 f {n} = {sf}, equal: {sr == sf}")

# They should be equal!
print("\nExpanded view for n=3:")
print(f"summation_R f (S 3) = f(3) + f(2) + f(1) + f(0) = {summation_R(f, 4)}")
print(f"sum_f_R0 f 3 = f(0) + f(1) + f(2) + f(3) = {sum_f_R0(f, 3)}")
