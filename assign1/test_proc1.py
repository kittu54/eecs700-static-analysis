def bump(x):
  requires(True)
  ensures(ret == old(x) + 1)
  modifies() # Modifies no global variables
  r = x + 1
  return r

# Save pre-call state of x
x_pre = x 

y = bump(x)

# { y == x_pre + 1 }
assert(y == x_pre + 1)