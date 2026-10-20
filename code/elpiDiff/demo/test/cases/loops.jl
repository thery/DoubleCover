using StaticArrays

function dot3(x::SVector{3}, y::SVector{3}, n::Int)
    s = 0.0
    for i = 1:n
        s += x[i] * y[i]
    end
    return s
end

function shift!(u::MVector{5}, c::Float64)
    for k ∈ 2:5
        u[k] = u[k] + c * u[k - 1]
    end
    return nothing
end

function poly(x)
    acc = 1.0
    for i in 1:3
        acc = acc * x + 1
    end
    acc
end
