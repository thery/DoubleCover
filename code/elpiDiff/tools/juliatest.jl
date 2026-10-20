# juliatest.jl SOURCE.jl DIR: runs the derivatives that the tool generated in
# DIR/tangent.jl and DIR/adjoint.jl from the Julia functions of SOURCE
# (examples/julia/functions.jl), at random points:
#   - the tangent gives the value of the function, and its derivative along
#     a random direction dx agrees with central finite differences;
#   - the adjoint passes the dot-product test against the tangent:
#     <tangent dy, yb> = <dx, gradient>.

using StaticArrays, Random, LinearAlgebra
include(abspath(ARGS[1]))
include(abspath(joinpath(ARGS[2], "tangent.jl")))
include(abspath(joinpath(ARGS[2], "adjoint.jl")))

Random.seed!(1)
fails = 0; checks = 0
function check(name, what, a, b; rtol = 1e-6)
    global fails, checks
    checks += 1
    ok = isapprox(a, b; rtol = rtol, atol = 1e-9)
    ok || (fails += 1; println("FAIL $name $what: $a vs $b"))
end

# Functions of reals returning a real; kinds: :r a real, :i a passive Int.
function scalar(name, kinds, gen)
    p = getfield(Main, name)
    t = getfield(Main, Symbol(name, :_tangent))
    a = getfield(Main, Symbol(name, :_adjoint))
    for _ in 1:20
        x = [k == :r ? gen() : rand(-2:2) for k in kinds]
        r = findall(==(:r), kinds)
        dx = randn(length(r)); yb = randn()
        y, ydot = t(x..., dx...)
        check(name, "value", y, p(x...))
        h = 1e-6
        xp = copy(x); xm = copy(x); xp[r] .+= h .* dx; xm[r] .-= h .* dx
        check(name, "tangent", ydot, (p(xp...) - p(xm...)) / 2h; rtol = 1e-5)
        xb = randn(length(r))
        g = collect(a(x..., xb..., yb)) .- xb
        check(name, "adjoint", ydot * yb, dot(dx, g))
    end
end

scalar(:xsin, [:r], () -> randn())
scalar(:quad, [:r], () -> randn())
scalar(:f, [:r, :r], () -> randn())
scalar(:transcend, [:r, :r], () -> 0.5 + rand())
scalar(:overwrite, [:r], () -> randn())
scalar(:branch, [:r, :i], () -> randn())
scalar(:piecewise, [:r], () -> 3 * randn())
scalar(:clamp_sq, [:r], () -> randn())
scalar(:damped, [:r, :r], () -> randn())

# Functions of an SVector returning a real.
for name in (:sumsq, :prodx)
    p = getfield(Main, name)
    t = getfield(Main, Symbol(name, :_tangent))
    a = getfield(Main, Symbol(name, :_adjoint))
    n = name == :sumsq ? 4 : 3
    for _ in 1:20
        x = SVector{n}(randn(n)); dx = SVector{n}(randn(n)); yb = randn()
        y, ydot = t(x, dx)
        check(name, "value", y, p(x))
        h = 1e-6
        check(name, "tangent", ydot, (p(x + h * dx) - p(x - h * dx)) / 2h; rtol = 1e-5)
        xb = randn(n); g = copy(xb)
        a(x, g, yb)
        check(name, "adjoint", ydot * yb, dot(dx, g - xb))
    end
end

# square_scaled!(y, x): y written, never read.
for _ in 1:20
    x = SVector{4}(randn(4)); dx = SVector{4}(randn(4)); yb = randn(4)
    y = zeros(4); ydot = zeros(4)
    square_scaled_tangent(y, x, ydot, dx)
    y0 = MVector{4}(zeros(4)); square_scaled!(y0, x)
    check(:square_scaled, "value", y, collect(y0))
    h = 1e-6
    yp = MVector{4}(zeros(4)); ym = MVector{4}(zeros(4))
    square_scaled!(yp, x + h * dx); square_scaled!(ym, x - h * dx)
    check(:square_scaled, "tangent", ydot, (yp - ym) / 2h; rtol = 1e-5)
    xb = randn(4); g = copy(xb)
    square_scaled_adjoint(zeros(4), x, yb, g)
    check(:square_scaled, "adjoint", dot(ydot, yb), dot(dx, g - xb))
end

# advect!(u, c): u read and written.
for _ in 1:20
    u0 = randn(6); c = 0.3 * rand(); du = randn(6); dc = randn(); ub = randn(6)
    u = copy(u0); udot = copy(du)
    advect_tangent(u, c, udot, dc)
    v = MVector{6}(u0); advect!(v, c)
    check(:advect, "value", u, collect(v))
    h = 1e-6
    vp = MVector{6}(u0 + h * du); advect!(vp, c + h * dc)
    vm = MVector{6}(u0 - h * du); advect!(vm, c - h * dc)
    check(:advect, "tangent", udot, (vp - vm) / 2h; rtol = 1e-5)
    gu = copy(ub); cb0 = randn()
    cb = advect_adjoint(u0, c, gu, cb0)
    # the adjoint of an inout array replaces ub by the gradient wrt u0
    check(:advect, "adjoint", dot(udot, ub), dot(du, gu) + dc * (cb - cb0))
end

println("$checks checks, $fails failures")
exit(fails == 0 ? 0 : 1)
