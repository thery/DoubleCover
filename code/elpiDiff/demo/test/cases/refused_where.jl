# where clauses are parsed; jlfront refuses the parameter type T
g8(x::T) where {T<:Real} = x * x * x
g9(x::T, y) where T = x
