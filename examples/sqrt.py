n = int(input())

assert n >= 0

r = 0
while (r + 1) * (r + 1) <= n:
    r += 1

assert r * r <= n
assert n < (r + 1) * (r + 1)

print(r)
