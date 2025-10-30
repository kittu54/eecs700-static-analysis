def swap(i, j):
    requires(True)
    ensures(a[i] == old(a)[j] and a[j] == old(a)[i])
    modifies("a")
    
    tmp = a[i]
    a[i] = a[j]
    a[j] = tmp
    return 0

a[1] = 100
a[2] = 200
z = 50

# Call swap
r = swap(1, 2)

# { a[1] == 200 and a[2] == 100 and z == 50 }
assert(a[1] == 200)
assert(a[2] == 100)
assert(z == 50) # Frame condition check