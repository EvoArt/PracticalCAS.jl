# A small integration workload run while the package is precompiled, so that
# the first `integrate` of a session does not pay for compiling the integrator
# (the compiled code is cached with the package). It adds about a minute and a
# half to precompilation; set the environment variable PRACTICALCAS_FAST_PRECOMPILE
# to skip it while developing.
if ccall(:jl_generating_output, Cint, ()) == 1 && !haskey(ENV, "PRACTICALCAS_FAST_PRECOMPILE")
    let x = Sym(:x, SymInfo(true, false, nothing, false, nothing, false))
        for f in (x^2, 1 / (x^2 + 1), 1 / (x^3 + 1), 1 / (x^4 + 1), x * exp(x), exp(-x^2),
                  log(x), x * log(x), sin(x)^2, x * sin(x), x * exp(x) * sin(x), tan(x),
                  sqrt(1 - x^2), 1 / sqrt(x^2 + 1), 1 / (2 + cos(x)), exp(x) / (1 + exp(x)),
                  sin(x) / x, exp(x) / x)
            try
                integrate(f, x)
            catch
            end
        end
    end
end
