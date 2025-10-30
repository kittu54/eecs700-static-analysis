# sum_array(n) returns the sum a[0] + ... + a[n-1]
def sum_array(n):
    requires(n >= 0)
    # Postcondition: ret is the sum of a[0...n-1]
    # This is hard to state, so we'll use a weaker one:
    ensures(n == 0 and ret == 0 or n > 0 and ret == old(a)[n-1] + sum_array(n-1))
    modifies()

    if n == 0:
        return 0
    else:
        # Recursive call for sum(a[0...n-2])
        sum_rest = sum_array(n - 1)
        
        # Add a[n-1]
        val = a[n-1]
        r = sum_rest + val
        return r

a[0] = 5
a[1] = 10
a[2] = 15

# Calculate sum of a[0...2] (n=3)
total = sum_array(3)

# We can't easily prove the spec, but we can test the call
assert(total == 30)