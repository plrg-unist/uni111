n = int(input())

assert n >= 0

# Find the recursion depth: scale = 4 ** depth, with n // scale < 2.
scale = 1
depth = 0
while 2 * scale <= n:
    scale *= 4
    depth += 1

# The base case n // scale is either 0 or 1.
r = 0
if scale <= n:
    r = 1

# Unwind without division: keep scale fixed and multiply scaled_n by 4.
# At each level, r is the integer square root of scaled_n // scale.
scaled_n = n
while depth > 0:
    scaled_n *= 4
    r *= 2
    if (r + 1) * (r + 1) * scale <= scaled_n:
        r += 1
    depth -= 1

assert r * r <= n
assert n < (r + 1) * (r + 1)

print(r)
