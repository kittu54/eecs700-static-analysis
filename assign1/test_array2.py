# Precondition
assume(i != j)

# Save old value
old_a_j = a[j]

# The store operation
a[i] = v

# { a[j] == old(a)[j] }
assert(a[j] == old_a_j)