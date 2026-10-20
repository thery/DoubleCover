# a catalog of syntax for the walker (not all accepted by jlfront)
g1(x) = -2^2 * x + -1.5 * x - (-3) + x^-1 + 2x + 3(x + 1)
g2(x) = +1 + (+x) - -x
function g3(x::Float64, n::Int, b::Bool)
    local y = 1e3 * x + 1.0e-5 + .5 + 2. + 1_000 + 0x10 + 1e20 + 123456789.0
    if b && n >= 1 || !b
        y = y / 2
    elseif n == 2 || n != 3 || n ≤ 4
        y += 1
    end
    return y
end
g4(x) = x > 0 ? x : x < -1 ? -x : 0.0
function g5(x::SVector{3,Float64})
    s = zero(x[1])
    for i = 1:2:3, j in 1:2
        s += x[i]
    end
    for k ∈ 2:3
        s *= x[k - 1]
    end
    return s
end
function g6(x)
    while x > 1
        x = x / 2
    end
    return x, 1
end
g7(x) = 1 < x < 2 ? 1.0 : x
g8(x::T) where {T<:Real} = x * x * x * x
function g9(x::T; y = 1) where T
    "s"
    'c'
    x.y
    sin.(x)
    return
end
g10(x, y = 2) = x
function g11 end
function g12(x) end
h(x)::Float64 = x
