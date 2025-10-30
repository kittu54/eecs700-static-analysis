def zero_x():
    requires(True)
    ensures(x == 0)
    modifies("x")
    x = 0
    return 0 # Return value doesn't matter

x = 10
y = 20

# Call the procedure
z = zero_x()

# { x == 0 and y == 20 }
assert(x == 0)
assert(y == 20) # This checks the frame condition
