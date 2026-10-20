function m1(x::Real, y::Float64)
    local z = 2x
    z -= y
    z /= 3
    z *= exp(-x)
    return log(z * z + 1) / sqrt(y * y + 1)
end


k2(x) = begin
    y = x * x
    y * y
end

nothing_ret(a::Number) = a^2 - 1   # trailing comment
