# a second catalog of syntax for the walker (facts only)
k1(x) = -2x + 2x * y + -(1) + - 1 + +1.5 + √x + x ÷ 2 + x % 2 + x' + (-x)^2 - (2)
function k3(x)
    a = b = 1
    local c
    z = [1, 2]
    w = x.y
    @show x
    q = "a$(x)b"
    v = (x -> x + 1)
    x ? 1 : 2
    t = :y
    u = 1f0 + 0b101 + 0o17 + 0x10 + 1.5f-3 + 1f7
    for (i, j) in 1:3
    end
    x |> f
    return nothing
end
k4(x) = x > 0 && x < 1 || x == 3 || x != 4
k5(x) = (x + 1) + 2 + (3 + x) * x * (x * x)
k6(x) = 1 - 2 - 3 + 4 + 5
k7(x) = x == 1 < 2 <= 3
function k8(x)::Float64
    x
end
h(x)::Float64 = x
