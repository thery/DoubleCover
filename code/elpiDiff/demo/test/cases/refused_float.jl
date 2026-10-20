function tri(x, n::Int)
    s = x
    for i in 1:n
        s = s + float(i)
    end
    return s
end
