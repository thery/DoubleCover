# Julia versions of the reference cases of elpiDiff, and a few more, for the
# Julia front end (jlfront.elpi) and back end (julia.elpi). See README.md.

using StaticArrays

xsin(x) = x * sin(x)

quad(x) = x * x + x

# The example of the Wikipedia article on automatic differentiation.
f(x1, x2) = x1 * x2 + sin(x1)

transcend(x, y) = sin(x) * exp(y) / sqrt(x) + log(y) - x^3 * cos(y) - y / x

function overwrite(x)
    x = 2 * x
    return x * x
end

function branch(a, p::Int)
    y = a
    if p > 0
        y = 2 * y
    else
        y = y * y
    end
    return y * a
end

# elseif, and a variable first set inside the branches
function piecewise(x)
    if x < -1
        y = -x
    elseif x < 1
        y = x * x
    else
        y = 2 * x - 1
    end
    return y * y
end

# the value of the function is the value of the if
clamp_sq(x) = x > 0 ? x * x : 0.0

function damped(x, nu)
    k = nu * nu
    s = k + 1
    y = x * x
    return y / s
end

# map: y[i] written, y never read
function square_scaled!(y::MVector{4}, x::SVector{4})
    for i in 1:4
        s = 2 * x[i]
        y[i] = s * s
    end
    return nothing
end

# fold over a real
function sumsq(x::SVector{4})
    acc = 0.0
    for i in 1:4
        acc += x[i] * x[i]
    end
    return acc
end

function prodx(x::SVector{3})
    acc = 1.0
    for i in 1:3
        acc *= x[i]
    end
    return acc
end

# fold over an array updated in place, nested loops
function advect!(u::MVector{6}, c)
    for n in 1:3
        for i in 2:6
            u[i] = u[i] - c * (u[i] - u[i-1])
        end
    end
    return nothing
end
