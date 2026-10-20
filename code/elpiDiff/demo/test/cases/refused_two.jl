function two(x)
    a = x
    b = x
    for i in 1:3
        a = a * x
        b = b + a
    end
    return a + b
end
