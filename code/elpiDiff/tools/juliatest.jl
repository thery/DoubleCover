# juliatest.jl SOURCE.jl DIR [PASSIVE]: runs the derivatives that the tool generated in
# DIR/tangent.jl and DIR/adjoint.jl from the Julia functions of SOURCE
# (examples/julia/functions.jl), at random points:
#   - the tangent gives the value of the function, and its derivative along
#     a random direction dx agrees with central finite differences;
#   - the adjoint passes the dot-product test against the tangent:
#     <tangent dy, yb> = <dx, gradient>.
# PASSIVE is the choice of run.sh --passive (F:X,G:Y,…, F with or without its
# trailing !): those arguments are not differentiated. The tests then vary
# only the other ones, and check that the generated signatures have an X_dot
# and an X_bar for the differentiated arguments and none for the passive ones.

using StaticArrays, Random, LinearAlgebra
include(abspath(ARGS[1]))
include(abspath(joinpath(ARGS[2], "tangent.jl")))
include(abspath(joinpath(ARGS[2], "adjoint.jl")))
const PASSIVE = Set(Tuple(split(replace(p, "!" => ""), ":"))
                    for p in split(length(ARGS) >= 3 ? ARGS[3] : "", ",", keepempty = false))
passive(f, x) = (replace(string(f), "!" => ""), string(x)) in PASSIVE
const TEXT = Dict(m => read(joinpath(ARGS[2], "$m.jl"), String) for m in ("tangent", "adjoint"))

Random.seed!(1)
fails = 0; checks = 0
function check(name, what, a, b; rtol = 1e-6)
    global fails, checks
    checks += 1
    ok = isapprox(a, b; rtol = rtol, atol = 1e-9)
    ok || (fails += 1; println("FAIL $name $what: $a vs $b"))
end

# The signatures: X_dot (tangent) and X_bar (adjoint) for each argument of
# `active`, none for those of `args` that are not.
function signature(name, args, active)
    for (m, suffix) in (("tangent", "_dot"), ("adjoint", "_bar"))
        h = match(Regex("function $(name)_$m\\(([^)]*)\\)"), TEXT[m])
        ps = h === nothing ? String[] : strip.(split(h[1], ","))
        for x in args
            check(name, "signature $m $x", (string(x) * suffix) in ps, x in active)
        end
    end
end

# Functions of reals returning a real; kinds: :r a real, :i a passive Int,
# argument names `args`; a real chosen passive is :p.
function scalar(name, args, kinds, gen)
    p = getfield(Main, name)
    t = getfield(Main, Symbol(name, :_tangent))
    a = getfield(Main, Symbol(name, :_adjoint))
    kinds = [k == :r && passive(name, x) ? :p : k for (x, k) in zip(args, kinds)]
    signature(name, args, args[kinds .== :r])
    for _ in 1:20
        x = [k == :i ? rand(-2:2) : gen() for k in kinds]
        r = findall(==(:r), kinds)
        dx = randn(length(r)); yb = randn()
        y, ydot = t(x..., dx...)
        check(name, "value", y, p(x...))
        h = 1e-6
        xp = copy(x); xm = copy(x); xp[r] .+= h .* dx; xm[r] .-= h .* dx
        check(name, "tangent", ydot, (p(xp...) - p(xm...)) / 2h; rtol = 1e-5)
        xb = randn(length(r))
        g = isempty(r) ? Float64[] : collect(a(x..., xb..., yb)) .- xb
        check(name, "adjoint", ydot * yb, dot(dx, g))
    end
end

scalar(:xsin, [:x], [:r], () -> randn())
scalar(:quad, [:x], [:r], () -> randn())
scalar(:f, [:x1, :x2], [:r, :r], () -> randn())
scalar(:transcend, [:x, :y], [:r, :r], () -> 0.5 + rand())
scalar(:overwrite, [:x], [:r], () -> randn())
scalar(:branch, [:a, :p], [:r, :i], () -> randn())
scalar(:piecewise, [:x], [:r], () -> 3 * randn())
scalar(:clamp_sq, [:x], [:r], () -> randn())
scalar(:damped, [:x, :nu], [:r, :r], () -> randn())

# Functions of an SVector returning a real; x passive: a zero tangent.
for name in (:sumsq, :prodx)
    p = getfield(Main, name)
    t = getfield(Main, Symbol(name, :_tangent))
    a = getfield(Main, Symbol(name, :_adjoint))
    n = name == :sumsq ? 4 : 3
    act = !passive(name, :x)
    signature(name, [:x], act ? [:x] : [])
    for _ in 1:20
        x = SVector{n}(randn(n)); dx = SVector{n}(act ? randn(n) : zeros(n)); yb = randn()
        y, ydot = act ? t(x, dx) : t(x)
        check(name, "value", y, p(x))
        h = 1e-6
        check(name, "tangent", ydot, (p(x + h * dx) - p(x - h * dx)) / 2h; rtol = 1e-5)
        xb = randn(n); g = copy(xb)
        act ? a(x, g, yb) : a(x, yb)
        check(name, "adjoint", ydot * yb, dot(dx, g - xb))
    end
end

# square_scaled!(y, x): y written, never read.
let act = !passive(:square_scaled, :x)
    signature(:square_scaled, [:y, :x], act ? [:y, :x] : [:y])
    for _ in 1:20
        x = SVector{4}(randn(4)); dx = SVector{4}(act ? randn(4) : zeros(4)); yb = randn(4)
        y = zeros(4); ydot = zeros(4)
        act ? square_scaled_tangent(y, x, ydot, dx) : square_scaled_tangent(y, x, ydot)
        y0 = MVector{4}(zeros(4)); square_scaled!(y0, x)
        check(:square_scaled, "value", y, collect(y0))
        h = 1e-6
        yp = MVector{4}(zeros(4)); ym = MVector{4}(zeros(4))
        square_scaled!(yp, x + h * dx); square_scaled!(ym, x - h * dx)
        check(:square_scaled, "tangent", ydot, (yp - ym) / 2h; rtol = 1e-5)
        xb = randn(4); g = copy(xb)
        act ? square_scaled_adjoint(zeros(4), x, yb, g) : square_scaled_adjoint(zeros(4), x, yb)
        check(:square_scaled, "adjoint", dot(ydot, yb), dot(dx, g - xb))
    end
end

# advect!(u, c): u read and written; c may be passive.
let act = !passive(:advect, :c)
    signature(:advect, [:u, :c], act ? [:u, :c] : [:u])
    for _ in 1:20
        u0 = randn(6); c = 0.3 * rand(); du = randn(6); dc = act ? randn() : 0.0; ub = randn(6)
        u = copy(u0); udot = copy(du)
        act ? advect_tangent(u, c, udot, dc) : advect_tangent(u, c, udot)
        v = MVector{6}(u0); advect!(v, c)
        check(:advect, "value", u, collect(v))
        h = 1e-6
        vp = MVector{6}(u0 + h * du); advect!(vp, c + h * dc)
        vm = MVector{6}(u0 - h * du); advect!(vm, c - h * dc)
        check(:advect, "tangent", udot, (vp - vm) / 2h; rtol = 1e-5)
        gu = copy(ub); cb0 = randn()
        cb = act ? advect_adjoint(u0, c, gu, cb0) : (advect_adjoint(u0, c, gu); cb0)
        # the adjoint of an inout array replaces ub by the gradient wrt u0
        check(:advect, "adjoint", dot(udot, ub), dot(du, gu) + dc * (cb - cb0))
    end
end

println("$checks checks, $fails failures")
exit(fails == 0 ? 0 : 1)
