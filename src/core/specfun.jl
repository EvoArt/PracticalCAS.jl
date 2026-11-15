# Numeric values of the special functions that integration produces: the error
# functions erf and erfi, the exponential integral Ei, and the sine and cosine
# integrals Si and Ci (pure Julia, Float64, about 1e-14 relative accuracy).

const _EULERGAMMA = 0.57721566490153286061
const _SQRTPI = 1.7724538509055160273

# Maclaurin series of erf (any number type), for moderate arguments
function _erf_series(z)
    s = zero(z)
    t = z
    z2 = z * z
    for n in 0:400
        term = t / (2n + 1)
        s += term
        abs(term) <= 1e-17 * abs(s) && break
        t *= -z2 / (n + 1)
    end
    return 2 / _SQRTPI * s
end

# erfc(x) for x ≥ 2 by its continued fraction (evaluated backwards)
function _erfc_cf(x)
    f = x
    for k in 80:-1:1
        f = x + (k / 2) / f
    end
    return exp(-x * x) / (_SQRTPI * f)
end

function _nerf(x::Real)
    x = Float64(x)
    isnan(x) && return x
    abs(x) < 2.5 && return _erf_series(x)
    return sign(x) * (1 - _erfc_cf(abs(x)))
end
function _nerf(z::Complex)
    abs(z) < 5 && return _erf_series(complex(Float64(real(z)), Float64(imag(z))))
    real(z) < 0 && return -_nerf(-z)
    # continued fraction for erfc, valid in the right half-plane
    f = z
    for k in 120:-1:1
        f = z + (k / 2) / f
    end
    return 1 - exp(-z * z) / (_SQRTPI * f)
end

# erfi(x) = -i erf(ix) = 2/√π Σ x^(2n+1)/(n!(2n+1))
function _nerfi(x::Real)
    x = Float64(x)
    s = 0.0
    t = x
    x2 = x * x
    for n in 0:2000
        term = t / (2n + 1)
        s += term
        abs(term) <= 1e-17 * abs(s) && break
        t *= x2 / (n + 1)
    end
    return 2 / _SQRTPI * s
end
_nerfi(z::Complex) = -im * _nerf(im * z)

# E₁(x) for x > 0
function _nE1(x::Float64)
    if x <= 1
        s = 0.0
        t = 1.0
        for n in 1:200
            t *= -x / n
            term = t / n
            s += term
            abs(term) < 1e-17 * abs(s) && break
        end
        return -_EULERGAMMA - log(x) - s
    end
    # continued fraction (modified Lentz)
    tiny = 1e-300
    b = x + 1
    c = 1 / tiny
    d = 1 / b
    h = d
    for i in 1:500
        an = -i * i
        b += 2
        d = 1 / (an * d + b)
        c = b + an / c
        del = c * d
        h *= del
        abs(del - 1) < 1e-16 && break
    end
    return h * exp(-x)
end

function _nEi(x::Real)
    x = Float64(x)
    x == 0 && return -Inf
    x < 0 && return -_nE1(-x)
    if x < 40
        s = 0.0
        t = 1.0
        for n in 1:500
            t *= x / n
            term = t / n
            s += term
            term < 1e-17 * s && break
        end
        return _EULERGAMMA + log(x) + s
    end
    # asymptotic series
    s = 1.0
    t = 1.0
    for n in 1:40
        tn = t * n / x
        tn > t && break
        t = tn
        s += t
        t < 1e-17 && break
    end
    return exp(x) / x * s
end
function _nEi(z::Complex)
    # series, adequate for moderate |z|; the principal branch of log
    s = zero(z)
    t = one(z)
    for n in 1:2000
        t *= z / n
        term = t / n
        s += term
        abs(term) < 1e-17 * abs(s) && break
    end
    return _EULERGAMMA + log(z) + s
end

# (Ci(t), Si(t)) for t > 0, after Numerical Recipes' cisi
function _ncisi(t::Float64)
    eps = 1e-16
    tiny = 1e-300
    if t > 2
        b = complex(1.0, t)
        c = complex(1 / tiny, 0.0)
        d = 1 / b
        h = d
        for i in 2:1000
            a = -(i - 1)^2
            b += 2
            d = 1 / (a * d + b)
            c = b + a / c
            del = c * d
            h *= del
            abs(real(del) - 1) + abs(imag(del)) < eps && break
        end
        h *= complex(cos(t), -sin(t))
        return (-real(h), π / 2 + imag(h))
    end
    sum = sums = sumc = 0.0
    sgn = fact = 1.0
    odd = true
    for k in 1:200
        fact *= t / k
        term = fact / k
        sum += sgn * term
        err = term / abs(sum)
        if odd
            sgn = -sgn
            sums = sum
            sum = sumc
        else
            sumc = sum
            sum = sums
        end
        err < eps && break
        odd = !odd
    end
    return (sumc + log(t) + _EULERGAMMA, sums)
end

function _nSi(x::Real)
    x = Float64(x)
    x == 0 && return 0.0
    return sign(x) * _ncisi(abs(x))[2]
end
function _nCi(x::Real)
    x = Float64(x)
    x == 0 && return -Inf
    c = _ncisi(abs(x))[1]
    return x > 0 ? c : complex(c, π)
end
# power series (entire parts), for moderate complex arguments
function _nSi(z::Complex)
    s = zero(z)
    t = z                      # z^(2n+1)/(2n+1)!
    for n in 0:500
        term = t / (2n + 1)
        s += term
        abs(term) < 1e-17 * abs(s) && break
        t *= -z * z / ((2n + 2) * (2n + 3))
    end
    return s
end
function _nCi(z::Complex)
    s = zero(z)
    t = one(z)                 # z^(2n)/(2n)!
    for n in 1:500
        t *= -z * z / ((2n - 1) * (2n))
        term = t / (2n)
        s += term
        abs(term) < 1e-17 * abs(s) && break
    end
    return _EULERGAMMA + log(z) + s
end
