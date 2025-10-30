def fact(n):
  requires(n >= 0)
  # A slightly simpler postcondition to prove
  ensures(n == 0 and ret == 1 or n > 0 and ret >= 1)
  modifies() # No global state modified

  if n == 0:
    return 1
  else:
    # Recursive call
    t = fact(n - 1)
    r = n * t
    return r

assume(x >= 0)
y = fact(x)

# We can only assert the postcondition
assume(x == 3) # Test a concrete case
assert(y == 6) # This will fail, our spec is too weak!

# Let's assert the spec we *can* prove
assume(x >= 0)
y = fact(x)
assert((x == 0 and y == 1) or (x > 0 and y >= 1))