// examples.js: the examples menu (xsin, the default, a small program, the functions of elpiDiff's
// examples/julia/functions.jl, and one program the front end refuses).
export const EXAMPLES = [
  { name: 'xsin', code: `xsin(x) = x * sin(x)\n` },
  { name: 'a program', code:
`# A small Julia program: every function is differentiated,
# the rest (using, comments, top-level code) is ignored.
using StaticArrays

xsin(x) = x * sin(x)

function damped(x, nu)
    k = nu * nu
    s = k + 1
    return x * x / s
end

function sumsq(x::SVector{4})
    acc = 0.0
    for i in 1:4
        acc += x[i] * x[i]
    end
    return acc
end

println(xsin(0.5), " ", sumsq(SVector(1.0, 2.0, 3.0, 4.0)))
` },
  { name: 'quad', code: `quad(x) = x * x + x\n` },
  { name: 'f (Wikipedia)', code:
`# The example of the Wikipedia article on automatic differentiation.
f(x1, x2) = x1 * x2 + sin(x1)
` },
  { name: 'transcend', code: `transcend(x, y) = sin(x) * exp(y) / sqrt(x) + log(y) - x^3 * cos(y) - y / x\n` },
  { name: 'branch', code:
`function branch(a, p::Int)
    y = a
    if p > 0
        y = 2 * y
    else
        y = y * y
    end
    return y * a
end
` },
  { name: 'piecewise', code:
`# elseif, and a variable first set inside the branches
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
` },
  { name: 'clamp_sq', code:
`# the value of the function is the value of the if
clamp_sq(x) = x > 0 ? x * x : 0.0
` },
  { name: 'sumsq', code:
`using StaticArrays

# fold over a real
function sumsq(x::SVector{4})
    acc = 0.0
    for i in 1:4
        acc += x[i] * x[i]
    end
    return acc
end
` },
  { name: 'prodx', code:
`using StaticArrays

function prodx(x::SVector{3})
    acc = 1.0
    for i in 1:3
        acc *= x[i]
    end
    return acc
end
` },
  { name: 'square_scaled!', code:
`using StaticArrays

# map: y[i] written, y never read
function square_scaled!(y::MVector{4}, x::SVector{4})
    for i in 1:4
        s = 2 * x[i]
        y[i] = s * s
    end
    return nothing
end
` },
  { name: 'advect!', code:
`using StaticArrays

# fold over an array updated in place, nested loops
function advect!(u::MVector{6}, c)
    for n in 1:3
        for i in 2:6
            u[i] = u[i] - c * (u[i] - u[i-1])
        end
    end
    return nothing
end
` },
  { name: 'halve (refused: while)', code:
`# L0 has no while loop: the front end refuses it
function halve(x)
    while x > 1
        x = x / 2
    end
    return x
end
` },
];
