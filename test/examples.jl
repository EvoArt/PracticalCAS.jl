# The worked examples in examples/*.qmd double as tests: every Julia cell is run
# in a fresh module (including the hidden `#| include: false` cells, which hold
# the checks as `@assert`s).
const EXAMPLES = joinpath(@__DIR__, "..", "examples")

function qmd_code(path)
    out = String[]
    inblock = false
    for l in readlines(path)
        if !inblock && startswith(l, "```{julia}")
            inblock = true
        elseif inblock && startswith(l, "```")
            inblock = false
            push!(out, "")
        elseif inblock
            push!(out, l)
        end
    end
    return join(out, "\n")
end

@testset "examples" begin
    for f in sort(filter(endswith(".qmd"), readdir(EXAMPLES)))
        @testset "$f" begin
            m = Module(Symbol(splitext(f)[1]))
            ok = try
                include_string(m, qmd_code(joinpath(EXAMPLES, f)), f)
                true
            catch err
                @error "example $f failed" exception = (err, catch_backtrace())
                false
            end
            @test ok
        end
    end
end
