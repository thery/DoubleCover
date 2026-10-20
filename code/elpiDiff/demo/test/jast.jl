# dump Julia's AST (as Base.dump-ish S-expressions) for comparison
for x in Meta.parseall(read(ARGS[1], String)).args
    x isa LineNumberNode || (Base.remove_linenums!(x); println(x isa Expr ? Meta.show_sexpr(x) : x); println())
end
