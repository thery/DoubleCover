# julia2elpi.jl FILE.jl: the functions of FILE, as parsed by Julia
# (Meta.parseall), printed as Elpi facts `jl-function E`, E being the Julia
# AST written as a tree (jl-ast.elpi): an expression `j Head Args`, a symbol
# `jsym Name`, a literal `jint Text`, `jfloat Text` or `jbool Text`.
# Nothing is interpreted here: the translation to L0 is Elpi's (jlfront.elpi).

q(s) = "\"" * replace(string(s), "\\" => "\\\\", "\"" => "\\\"") * "\""

function term(x, ind)
    if x isa Symbol
        "jsym $(q(x))"
    elseif x isa Bool
        "jbool $(q(x))"
    elseif x isa Integer
        "jint $(q(x))"
    elseif x isa AbstractFloat
        "jfloat $(q(repr(x)))"
    elseif x isa Expr
        args = [a for a in x.args if !(a isa LineNumberNode)]
        isempty(args) && return "j $(q(x.head)) []"
        sub = join([ind * "  " * term(a, ind * "  ") for a in args], ",\n")
        "j $(q(x.head)) [\n$sub]"
    else
        "jother $(q(repr(x)))"
    end
end

isfunction(x) = x isa Expr && (x.head == :function ||
    (x.head == :(=) && x.args[1] isa Expr && x.args[1].head in (:call, :where)))

src = ARGS[1]
ast = Meta.parseall(read(src, String); filename = src)
for x in ast.args
    if x isa Expr && x.head == :error
        error("$src: $(x.args[1])")
    end
end
println("% the functions of $src, parsed by Julia (tools/julia2elpi.jl)")
for x in ast.args
    isfunction(x) && println("jl-function (", term(x, ""), ").")
end
