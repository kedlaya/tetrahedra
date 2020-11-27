"""
We implement the computation of torsion closures of ideals in Laurent
polynomial rings using ideas of Conway-Jones, Beukers-Smyth, Aliev-Smyth,
and Poonen-Rubinstein.
"""

# Python reminder: it is permitted but dangerous for a lambda function to
# reference variables which are in scope at its definition, because those
# variables may not have the intended values by the time the function is
# evaluated). Safer is to pass those variables in as optional arguments,
# so that the default values are evaluated at the time of definition.

from itertools import product, combinations
from sage.rings.polynomial.polydict import ETuple

### Utility functions

def column_to_unimodular(v, return_inverse=False):
    """
    Complete a unimodular column vector to a unimodular matrix.

    INPUT:

    - ``v``: a vector of integers
    - ``return_inverse``: whether or not to also return the inverse matrix
        (default: False)

    EXAMPLES::

        sage: column_to_unimodular(vector([1,0,0]))
        [1 0 0]
        [0 1 0]
        [0 0 1]
        sage: column_to_unimodular(vector([0,1,0]))
        [0 1 0]
        [1 0 0]
        [0 0 1]
        sage: column_to_unimodular(vector([5,-2,7]))
        [ 5  2  0]
        [-2 -1  0]
        [ 7  3  1]
        sage: column_to_unimodular(vector([5,-2,7]), return_inverse=True)
        (
        [ 5  2  0]  [ 1  2  0]
        [-2 -1  0]  [-2 -5  0]
        [ 7  3  1], [-1  1  1]
        )
    """
    if gcd(tuple(v)) != 1:
        raise ValueError("Vector not unimodular")
    n = len(v)
    U = identity_matrix(n)
    while True:
        w = U*v
        i = 0
        for j in range(1,n):
            if w[j] and (abs(w[j]) < abs(w[i]) or not w[i]):
                i = j
        if i>0:
            U.swap_rows(0,i)
            w = U*v
        if w[0]<0:
            U.rescale_row(0,-1)
            w = U*v
        for j in range(1,n):
            q = w[j] // w[0]
            U.add_multiple_of_row(j,0,-q)
        w = U*v
        if not any(w[j] for j in range(1,n)): 
            break
    if return_inverse:
        return ~U, U
    return ~U

def row_to_unimodular(v, return_inverse=False):
    """
    Complete a unimodular row vector to a unimodular matrix.

    INPUT:

    - ``v``: a vector of integers
    - ``return_inverse``: whether or not to also return the inverse matrix
        (default: False)

    EXAMPLES::

        sage: row_to_unimodular(vector([5,-2,7]))
        [ 5 -2  7]
        [ 2 -1  3]
        [ 0  0  1]
        sage: row_to_unimodular(vector([5,-2,7]), return_inverse=True)
        (
        [ 5 -2  7]  [ 1 -2 -1]
        [ 2 -1  3]  [ 2 -5  1]
        [ 0  0  1], [ 0  0  1]
        )
    """
    if return_inverse:
        U, V = column_to_unimodular(v, return_inverse=True)
        return U.transpose(), V.transpose()
    return column_to_unimodular(v).transpose()

def coprime_factor(x, y):
    """
    Return the largest divisor of x which is coprime to y.

    EXAMPLES::

        sage: coprime_factor(12, 8)
        3
        sage: coprime_factor(36, 12)
        1
    """
    if not x:
        return ValueError("First argument must be nonzero")
    z = x
    while True:
        d = gcd(z, y)
        if d == 1:
            return z
        z = z // d

def cyclotomic_factors(f):
    """
    Compute the cyclotomic factors of a univariate polynomial over a cyclotomic field.

    Each factor is only returned once.

    EXAMPLES::

        sage: K.<z3> = CyclotomicField(3)
        sage: P.<x> = PolynomialRing(K)
        sage: cyclotomic_factors((x-1)*(x+z3+1)*(x-2))
        (x - 1, x + z3 + 1)
        sage: cyclotomic_factors((x^2+z3+1)*(x-2))
        (x - z3, x + z3)

        sage: K.<z4> = CyclotomicField(4)
        sage: P.<x> = PolynomialRing(K)
        sage: cyclotomic_factors(2*x^2 + 4*x + 2)
        (x + 1,)

        sage: K.<z6> = CyclotomicField(6)
        sage: P.<x> = PolynomialRing(K)
        sage: cyclotomic_factors(-x^2 + z6)
        (x^2 - z6,)

        sage: K.<z12> = CyclotomicField(12)
        sage: P.<x> = PolynomialRing(K)
        sage: cyclotomic_factors(x-z12^4)
        (x - z12^2 + 1,)
        sage: cyclotomic_factors(x-z12^3)
        (x - z12^3,)
        sage: u = 16*z12^3*x^6 + (32*z12^2 - 32)*x^5 + (-64*z12^3 + 64*z12)*x^4 - 96*x^3 + 64*z12*x^2 - 32*z12^2*x + 16*z12^3
        sage: cyclotomic_factors(u)
        (x - z12^3, x + z12^3 - z12)

        sage: P.<x> = PolynomialRing(QQ)
        sage: cyclotomic_factors(x^4 - x)
        (x - 1, x^2 + x + 1)
    """
    R = f.parent()
    K = R.base_ring()
    # Early abort if K = Q: use Sage's built-in function.
    if K == QQ:
        return tuple(g for (g, _) in f.cyclotomic_part().factor())
    # Early abort if deg(f) = 1: check the root directly.
    if f.degree() == 1:
        a = f.any_root()
        if a^K.zeta_order() == 1:
            return (f,)
        return tuple()
    # Early abort if f is binomial.
    if f.number_of_terms() == 2:
        return tuple(g for (g,_) in f.factor() if g(0))
    N = K._n()
    # Find three rational primes that split completely in K at which f is integral.
    # Use these to bound the orders of roots of unity occurring in f.
    p = 1
    primes = []
    d = {}
    while len(primes) < 3:
        p += N
        if not p.is_prime():
            continue
        F = GF(p)
        a = F.multiplicative_generator()^((p-1)//N)
        P.<x1> = PolynomialRing(F)
        try:
            f1 = P({i: v.polynomial().change_ring(F)(a) for i,v in f.dict().items()})
        except ZeroDivisionError:
            continue
        primes.append(p)
        d[p] = []
        for (g, _) in f1.factor():
            if g[0] == 0:
                continue
            N1 = p^g.degree() - 1
            N2 = N1
            for (q, _) in N1.factor():
                while N2%q == 0 and power_mod(x1, N2//q, g) == 1:
                    N2 //= q
            d[p].append(N2)
    # For each root of unity of order p dividing the original polynomial,
    # for each of the three primes p in primes, d[p] contains the prime-to-p part of m.
    # Using this knowledge, we bound the possible values of m.
    d1 = {p: {} for p in primes}
    q = prod(primes)
    for p in primes:
        for m in d[p]:
            m1 = coprime_factor(m, q)
            if m1 in d1[p]:
                d1[p][m1].append(m//m1)
            else:
                d1[p][m1] = [m//m1]
    s = set.intersection(*tuple(set(d1[p].keys()) for p in primes))
    l = []
    for m1 in s:
        edges = []
        for p in primes:
            for m2 in d1[p][m1]:
                l2 = [(p1, m2.valuation(p1)) for p1 in primes if p1 != p]
                edges.append(tuple(l2))
        d2 = {p: {} for p in primes}
        for s in edges:
            (p0, v0) = s[0]
            (p1, v1) = s[1]
            if v0 not in d2[p0]:
                d2[p0][v0] = {}
            if p1 not in d2[p0][v0]:
                d2[p0][v0][p1] = []
            d2[p0][v0][p1].append(v1)
            if v1 not in d2[p1]:
                d2[p1][v1] = {}
            if p0 not in d2[p1][v1]:
                d2[p1][v1][p0] = []
            d2[p1][v1][p0].append(v0)
        (p0, p1, p2) = primes
        for v0 in set(d2[p0]):
            if p1 not in d2[p0][v0] or p2 not in d2[p0][v0]:
                continue
            for v1 in set(d2[p0][v0][p1]):
                for v2 in set(d2[p0][v0][p2]):
                    if p2 in d2[p1][v1] and v2 in d2[p1][v1][p2]:
                        l.append(m1 * p0^v0 * p1^v1 * p2^v2)
    ans = []
    h = R.one()
    for m in l:
        g = R(cyclotomic_polynomial(m))
        ans.append(f.gcd(g))
        h *= f.gcd(g)
    return tuple(h for g in ans for (h, _) in g.factor())

def cyclotomic_ext(K, h, assume_odd=False, assume_cyclotomic=False):
    """
    Compute a cyclotomic extension of a cyclotomic field.

    The polynomial `h` is assumed to be an irreducible univariate polynomial
    over `K`. If its roots are themselves roots of unity (and of odd order if 
    ``assume_odd`` is True), return the field generated by those roots. 
    Otherwise, return None.

    If ``assume_cyclotomic`` is True, we omit the check that the roots of `h`
    are roots of unity.

    EXAMPLES::

        sage: K.<z> = CyclotomicField(7)
        sage: R.<t> = PolynomialRing(K)
        sage: cyclotomic_ext(K, t^2-t+1)
        Cyclotomic Field of order 21 and degree 12
        sage: cyclotomic_ext(K, t^2-t+1, assume_cyclotomic=True)
        Cyclotomic Field of order 21 and degree 12
    """
    if h.degree() == 1:
        N = K.zeta_order()
        if assume_odd:
            N = N.odd_part()
        a = h.any_root()
        if a^N != 1:
            return None
        return K
    if assume_cyclotomic:
        R = h.parent()
        x = R.gen()
        # Under the assumption, some power of x reduces into K mod h.
        # We start by finding that power.
        m = 1
        y = x
        while y not in K:
            m += 1
            y = (y*x) % h
        # Now find the multiplicative order of x mod h.
        N = K.zeta_order()
        N1 = m*N
        for (p, _) in (2*m).factor():
            while (N1%p == 0) and (power_mod(x, N1//p, h) == 1):
                N1 //= p
        if assume_odd and (N1%2 == 0):
            return None
        N1 = lcm(N, N1)
        if N1%4 == 2:
            N1 //= 2
        return CyclotomicField(N1)
    K1.<a> = K.extension(h)
    N = K1.zeta_order()
    N1 = (N.odd_part() if assume_odd else N)
    if a^N1 != 1:
        return None
    if N == 2:
        return QQ
    if N%4:
        N //= 2
    return CyclotomicField(N)

### Operations on Laurent polynomials

def decimate(f, i, m):
    r"""
    Decimate a polynomial in a particular variable.

    If `x` is the variable in question, this means replacing `x^n` with
    `x^{\lfloor n/m \rfloor}`.

    EXAMPLES::

        sage: P.<x,y> = LaurentPolynomialRing(QQ,2)
        sage: decimate(x^3 + 2*x^2*y + y^2 - 1, 0, 2)
        2*x*y + y^2 + x - 1
    """
    P = f.parent()
    if not f:
        return P.zero()
#    if not isinstance(P, LaurentPolynomialRing_generic):
#        return f
#    n = P.ngens()
    return P({tuple(x if j != i else x//m for j, x in enumerate(v)): w
              for v,w in f.dict().items()})

def change_to_univariate(f):
    """
    Return a vector that makes ``f`` univariate, if one exists, else ``None``.

    EXAMPLES::

        sage: P.<x,y> = LaurentPolynomialRing(QQ, 2)
        sage: change_to_univariate(x^2*y^-3 - x^3*y^-1 + x^4*y)
        (-1, -2)
        sage: change_to_univariate(x^2*y^-3 - x^3*y^-1 + x^4*y^2) is None
        True
    """
    if not f:
        return None
    ex = f.exponents()
    n = f.parent().ngens()
    M = Matrix([v.esub(ex[0]) for v in ex])
    if M.nrows() == 2:
        return M.row(1)
    if M.submatrix(1, 0, 2).rank() > 1:
        return None
    if (M.rank() == 1):
        return M.row(1)
    return None

### Operations on Laurent polynomial ideals

def extend_ideals_to_cyclotomic(l, K=None):
    """
    Find a common base extension for some Laurent polynomial ideals.

    It is assumed that the base fields are all cyclotomic.

    If `K` is specified, the new base field is forced to contain `K`.

    EXAMPLES::

        sage: P.<x,y> = LaurentPolynomialRing(QQ, 2)
        sage: I = P.ideal([x+y-1])
        sage: K.<z4> = CyclotomicField(4)
        sage: l, K1 = extend_ideals_to_cyclotomic([I], K)
        sage: print(l[0].ring())
        Multivariate Laurent Polynomial Ring in x, y over Cyclotomic Field of order 4 and degree 2
    """
    N = lcm(I.base_ring().zeta_order() for I in l)
    if K is not None:
        N = lcm(N, K.zeta_order())
    if N == 2: # Early abort
        return l, QQ
    K1 = CyclotomicField(N)
    return [I.base_extend(K1) for I in l], K1

def contract_ideals_to_cyclotomic(l, K=None):
    """
    Find a common base contraction for some Laurent polynomial ideals.

    It is assumed that the ideals all have base field equal to some cyclotomic
    field, and that every coefficient is a root of unity.

    If `K` is specified, the new base field is forced to contain `K`.

    EXAMPLES::

        sage: K.<z> = CyclotomicField(36)
        sage: P.<x,y> = LaurentPolynomialRing(K, 2)
        sage: I1 = P.ideal([x + y - z^6])
        sage: I2 = P.ideal([x - y - z^8])
        sage: contract_ideals_to_cyclotomic([I1, I2])
        ([Ideal (x + y - zeta18^3) of Multivariate Laurent Polynomial Ring in x, y over Cyclotomic Field of order 18 and degree 6,
          Ideal (x - y - zeta18^4) of Multivariate Laurent Polynomial Ring in x, y over Cyclotomic Field of order 18 and degree 6],
         Cyclotomic Field of order 18 and degree 6)
    """
    if not l: # Early abort
        return [], K
    K0 = l[0].base_ring()
    if K0 == QQ: # Early abort
        return l, QQ
    N0 = K0.zeta_order()
    N1 = 2 if K is None else K.zeta_order()
    # Compute the LCM of the orders of the roots of unity appearing in the ideals (and in K).
    for I in l:
        for f in I.gens():
            for c in f.coefficients():
                if c^N1 != 1:
                    N1 = lcm(N1, c.multiplicative_order())
                    if N1 == N0: # Early abort
                        return l, K0
    K1 = QQ if N1 <= 2 else CyclotomicField(N1)
    return [I.base_extend(K1) for I in l], K1

### Sublogics in the computation of torsion closures

def univariate_logic(I, assume_odd=False, use_gb=True):
    """
    Look for a toric coordinate change which makes some generator univariate.

    Returns a list of triples (v, v1, a) to be sent to `toric_substitute` if univariate logic
    applies, otherwise None.

    If assume_odd is True, we only cover cyclotomic points of odd order.

    If use_gb is True, test generators from a Groebner basis, else use the specified ones.

    EXAMPLES::

        sage: P.<x,y,z> = LaurentPolynomialRing(QQ, 3)
        sage: I = P.ideal([x^2*y^2 - 1])
        sage: univariate_logic(I)
        [((-1, -1, 0), (-1, 0, 0), 1), ((-1, -1, 0), (-1, 0, 0), -1)]
        sage: univariate_logic(I, assume_odd=True)
        [((-1, -1, 0), (-1, 0, 0), 1)]
        sage: I = P.ideal([x^2*y^2 - 1, x + y + z])
        sage: univariate_logic(I) is None
        True
        sage: univariate_logic(I, use_gb=False)
        [((-1, -1, 0), (-1, 0, 0), 1), ((-1, -1, 0), (-1, 0, 0), -1)]
    """
    # Look for a polynomial f which becomes univariate after a coordinate change.
    v = None
    for f in (I.groebner_basis(saturate=False) if use_gb else I.gens()):
        if not f:
            continue
        if f.is_unit():
            return []
        if v is None:
            v = change_to_univariate(f)
            if v is not None:
                f0 = f
    if v is None:
        return None

    P = I.ring()
    K = P.base_ring() # Assumed to be a cyclotomic field
    v = v.apply_map(lambda x, gc=gcd(tuple(v)): x//gc)
    U, V = column_to_unimodular(v, return_inverse=True)
    # Convert f into a univariate polynomial and find its cyclotomic factors.
    f1 = f0.toric_coordinate_change(V)
    f1 = f1.__reduce__()[1][0]
    P0.<t> = PolynomialRing(K)
    f2 = P0({e[0]: c for e,c in f1.dict().items()})
    # Find the cyclotomic factors of f2.
    l = cyclotomic_factors(f2)
    v = tuple(v)
    v1 = tuple(V.row(0))
    candidates = []
    for g in l:
        K1 = cyclotomic_ext(K, g, assume_odd=assume_odd, assume_cyclotomic=True)
        if K1 is None: # This can happen if assume_odd is True.
            continue
        candidates.append((v, v1, g.any_root(K1)))
    return candidates

def cyclo_sum(a, b, p):
    """
    Return (a-b)^p / (a-b).

    EXAMPLES::

        sage: P.<x,y> = QQ[]
        sage: cyclo_sum(x, y, 5)
        x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4
    """
    return sum(a^i*b^(p-1-i) for i in range(p))

def cyclo_rel(*s):
    """
    Return relations obtained by forcing entries of s to be equally spaced around a circle.

    EXAMPLES::

        sage: P.<x,y> = QQ[]
        sage: cyclo_rel(x, y, 1)
        (x + y + 1, x^2 + x*y + y^2, x^2 + x + 1, y^2 + y + 1)
    """
    p = len(s)
    return (sum(s),) + tuple(cyclo_sum(a, b, p) for (a, b) in combinations(s, 2))

def mod_2_logic(I, assume_odd=False, use_gb=True):
    """
    Look for a generator whose mod-2 reduction has at most 6 monomials.

    Returns a list of tuples of additional generators if mod-2 logic applies, otherwise None.

    If assume_odd is True, we only cover cyclotomic points of odd order. Otherwise,
    we only consider mod-2 relations with at most 4 monomials.

    If use_gb is True, test generators from a Groebner basis, else use the specified ones.

    EXAMPLES::

        sage: P.<x,y,z> = LaurentPolynomialRing(QQ, 3)
        sage: I = P.ideal([x^2 + y^2 + z^2 + x^-2 + y^-2 + z^-2 + 2])
        sage: l = mod_2_logic(I, assume_odd=True, use_gb=False)
        sage: len(l)
        14
        sage: l[0]
        (x^2 + 1 + x^-2,
        x^4 + x^2 + 1,
        1 + x^-2 + x^-4,
        x^4 + 1 + x^-4,
        y^2 + z^2 + 1 + z^-2 + y^-2,
        y^8 + y^6 + y^4 + y^2 + 1,
        z^8 + z^6 + z^4 + z^2 + 1,
        1 + z^-2 + z^-4 + z^-6 + z^-8,
        1 + y^-2 + y^-4 + y^-6 + y^-8,
        y^8 + y^6*z^2 + y^4*z^4 + y^2*z^6 + z^8,
        y^8 + y^6*z^-2 + y^4*z^-4 + y^2*z^-6 + z^-8,
        y^8 + y^4 + 1 + y^-4 + y^-8,
        z^8 + z^4 + 1 + z^-4 + z^-8,
        z^8 + y^-2*z^6 + y^-4*z^4 + y^-6*z^2 + y^-8,
        z^-8 + y^-2*z^-6 + y^-4*z^-4 + y^-6*z^-2 + y^-8)
    """
    # Define some notations that persist over the whole subroutine.
    P = I.ring()
    Pgens = P.gens()
    n = P.ngens()
    K = P.base_ring() # Assumed to be a cyclotomic field
    z = K.gen()
    N = K.zeta_order()

    pr = (2 if K == QQ else K.prime_above(2))
    short_reductions = {m: [] for m in range(1, 13)}
    for f in (I.groebner_basis(saturate=False) if use_gb else I.gens()):
        if not f: 
            continue
        di = f.dict()
        v0 = min(c.valuation(pr) for c in di.values())
        ex = [e for e in di if di[e].valuation(pr) == v0]
        m = len(ex)
        if m > 6 or ((m > 4 or m == len(di)) and not assume_odd):
            continue
        # Compute the maximal ideal containing 2 modulo which this relation
        # can be represented as a short sum. This involves controlling both the
        # omitted terms, and the discrepancy between the retained terms and roots
        # of unity.
        q = 1
        ex = [(e, di[e]/di[ex[0]]) for e in ex]
        z2 = z^(2^(N.valuation(2)))
        ram_index = K(2).valuation(pr)
        for i in range(m):
            for j in range(N.odd_part()):
                val = (ex[i][1]-z^j).valuation(pr)
                if val > 0:
                    q = max(q, ram_index/val)
                    ex[i] = (ex[i][0], z^j)
                    break
            else:
                ex = None
                break
        if ex is None:
            continue
        for e,c in di.items():
            val = c.valuation(pr) - v0
            if val > 0:
                q = max(q, ram_index/val)
        q = 2^ceil(log(q, 2))
        short_reductions[m].append((f, ex, q))
    # Find the shortest mod-2 relation of length at most 6.
    for m in range(1, 7):
        for (f, ex, q) in short_reductions[m]:
            # If not assume_odd, replace every term with its square.
            e1 = (1 if assume_odd else 2)
            terms = [P({e: c})^(q*e1) for (e,c) in ex]
            if m == 1: # No solutions!
                return []
            elif m == 2: # Relations of type (R_2)
                candidates = [(terms[0] - terms[1],)]
            elif m == 3: # Relations of type (R_3)
                candidates = [cyclo_rel(*(terms[i] for i in range(3)))]
            elif m == 4: # Relations of type (R_2) + (R_2)
                candidates = [(terms[0] - terms[1], terms[2] - terms[3]),
                              (terms[0] - terms[2], terms[1] - terms[3]),
                              (terms[0] - terms[3], terms[1] - terms[2])]
            elif m == 5:
                # Relations of type (R_5)
                candidates = [cyclo_rel(*(terms[i] for i in range(5)))]
                # Relations of type (R_2) + (R_3)
                for (i,j) in combinations(range(5), 2):
                    candidates.append((terms[i] - terms[j],) + 
                                       cyclo_rel(*(terms[k] for k in range(5) if k not in (i,j))))
            elif m == 6:
                candidates = []
                # Relations of type (R_5: R_3)
                for (i,j) in combinations(range(6), 2):
                    candidates.append(cyclo_rel(1, terms[i], terms[j]) + \
                                      cyclo_rel(*(1,), *(terms[k] for k in range(6) if k not in (i,j))))
                # Relations of type (R_3) + (R_3)
                for (i,j) in combinations(range(1, 6), 2):
                    candidates.append(cyclo_rel(terms[0], terms[i], terms[j]) + \
                                      cyclo_rel(*(terms[k] for k in range(1,6) if k not in (i,j))))
                # Relations of type (R_2) + (R_2) + (R_2)
                for i in range(1, 6):
                    for j in range(1, 4):
                        tmp = list(k for k in range(1, 6) if k != i)
                        tmp2 = list(k for k in tmp if k not in (tmp[0],tmp[j]))
                        candidates.append((terms[0]-terms[i],
                                           terms[tmp[0]]-terms[tmp[j]],
                                           terms[tmp2[0]]-terms[tmp2[1]]))
#            else:
#                candidates = [(terms[0] + sum(t[i]*terms[i+1] for i in range(m-1)),)
#                              for t in product([-1,1], repeat=m-1)]
            # If the original terms are conjugation-stable, the new relations should be also.
            if m <= 6 and all(x.coefficients()[0] in QQ and ~x in terms for x in terms):
                candidates = [t for t in candidates if
                              all(g(tuple(~x for x in P.gens())) in (t + tuple(-y for y in t)) for g in t)]
            if not any(all(g in I for g in t) for t in candidates):
                return candidates
    return None

## The main recursion

def torsion_closure_inner(I, assume_odd=False):
    """
    Given a Laurent polynomial ideal, return some larger ideals covering the cyclotomic points.

    If ``assume_odd`` is True, we only cover cyclotomic points of odd order.

    The output format is the same as the input format to torsion_closure_recurse,
    except that the directives 'ideal' and 'assume_odd' may be omitted
    (in which case they are assumed to remain unchanged).
    """
    # Define some notations that persist over the whole subroutine.
    P = I.ring()
    Pgens = P.gens()
    n = P.ngens()
    K = P.base_ring() # Assumed to be a cyclotomic field
    z = K.gen()
    N = K.zeta_order()
    Igens = I.gens()
    if any(f.is_unit() for f in Igens):
        return []

    # Recurse using univariate logic if possible.
    # This may enlarge the coefficient field.
    candidates = univariate_logic(I, assume_odd, use_gb=False)
    if candidates is None:
        candidates = univariate_logic(I, assume_odd, use_gb=True)
    if candidates is not None:
        l = []
        for (v, v1, a) in candidates:
            K1 = a.parent()
            P1 = P.change_ring(K1)
            l.append({'transform': lambda g, v=v, v1=v1, a=a, P1=P1:
                          g.toric_substitute(v, v1, a, new_ring=P1),
                      'new_base_ring': K1,
                      'extra_output_gens': [P1.monomial(*v) - a]})
        return l

    # Identify unused polynomial variables, to avoid infinite loops in the recursion.
    Mrows = []
    for f in Igens:
        if f:
            ex = f.exponents()
            Mrows += [v.esub(ex[0]) for v in ex]
    M = Matrix(QQ, Mrows)
    pivots = M.pivots()

    # Compute a family of enlarged ideals with the property that every cyclotomic point
    # of I (of odd order if assume_odd) belongs to one of the enlargements.
    e = (2 if N%4 else 1)
    sg = (-1 if (N%4 and z^(N//2) == -1) else 1)
    h = None if K == QQ else K.hom([sg*(-z)**e])
    if assume_odd:
        ideals = [(lambda g,h=h,n=n:
                   g.toric_coordinate_change(2*identity_matrix(n),h=h), 2, None)]
    else:
        ideals = []
        ranges = [range(2) if i in pivots else (0,) for i in range(n)]
        for t in product(*ranges):
            d = {i: -1 for i in range(n) if t[i]}
            if 1 in t:
                ideals.append((lambda g, d=d: g.rescale_vars(d), 1, t))
            if N%4:
                ideals.append((None, 2, t))
            else:
                ideals.append((lambda g, d=d, h=h: g.rescale_vars(d, h=h), 2, t))

    # Check whether one of the enlarged ideals equals the original ideal.
    for (T,j,t) in ideals:
        if T is None:
            continue
        if all(T(f) in I for f in Igens):
            ideals = [(T,j,t)]
            simplify = True
            break
    else:
        simplify = False

        # Recurse by factoring a reducible polynomial if possible.
        for f in I.groebner_basis():
            if not f.is_zero():
                fac = f.factor()
                if len(fac) > 1 or fac[0][1] > 1:
                    return [{'extra_input_gens': (g,)} for (g, _) in fac]

        # Recurse using mod-2 logic if possible.
        candidates = mod_2_logic(I, assume_odd, use_gb=False)
        if candidates is not None:
            return [{'extra_input_gens': t} for t in candidates]

    # Recurse appropriately using the larger ideals.
    l = []
    for (T,j,t) in ideals:
        if j == 1:
            # Recurse by decimating a variable by 2.
            U, V = row_to_unimodular(vector(t), return_inverse=True)
            V *= diagonal_matrix([2] + [1] * (n-1))
            l.append({'preparse': lambda g, T=T: (g+T(g), g-T(g)),
                      'transform': lambda g, U=U: decimate(g.toric_coordinate_change(U), 0, 2),
                      'untransform': lambda g, V=V: g.toric_coordinate_change(V)})
        elif not N%4:
            # Recurse by reducing the field K.
            K1 = QQ if N == 4 else CyclotomicField(N//4 if (N%8) else N//2)
            l.append({'preparse': lambda g, T=T, z=z: (g+T(g), z*(g-T(g))),
                      'rescale': {i: z for i in range(n) if t[i]},
                      'new_base_ring': K1})
        elif simplify:
            # In this case, I is already a torsion ideal; recurse on its associated primes.
            # We would rather take minimal associated primes, but this runs into a bug in Singular
            # (see trac ticket #29671).
            for J in I.associated_primes():
                l.append({'ideal': J})
        elif not assume_odd:
            # Recurse assuming odd order, after flipping signs to force this.
            l.append({'rescale': {i: -1 for i in range(n) if t[i]},
                      'assume_odd': True})
        else:
            # Recurse by adding extra generators as per Beukers-Smyth.
            l.append({'extra_input_gens': tuple(T(g) for g in Igens)})
    return l

def torsion_closure_recurse(l, verbose=False):
    """
    Execute the recursive computation of torsion closures. 

    The list ``l`` consists of dictionaries, each specifying an ideal
    and some additional directives (applied in this order).

    Directives applied before recursion:

    - ``preparse`` specifies an initial operation to convert generators
       into tuples of generators for the same ideal.
    - ``extra_input_gens`` specifies a tuple of additional generators.
       The same matrix is then used to change coordinates back at the end.
    - ``new_base_ring`` specifies the target base ring.
    - ``rescale`` specifies a dict used to rescale variables.
    - ``transform`` specifies a map to be applied to generators.
      (Cannot be combined with ``rescale``.)
    - ``assume_odd`` is passed to ``torsion_closure_inner``.

    Directives applied after recursion:

    - ``untransform`` specifies a map to be applied to generators. In this case,
      we may not end up with prime ideals, so we recurse again.
    - If ``rescale`` was specified, it is undone at this point. In this case,
      we may need to add Galois conjugates.
    - ``extra_output_gens`` specifies a tuple of additional generators to be 
      added to the ideal.
    """
    ans = []
    for d in l:
        I = d['ideal']
        K0 = I.base_ring()
        R0 = I.ring()

        # Preprocess the input.
        if 'preparse' in d:
            I = R0.ideal([g for f in I.gens() for g in d['preparse'](f) if g],
                         hint=I.hint())
        if 'extra_input_gens' in d:
            I = I + R0.ideal(d['extra_input_gens'])
        if 'new_base_ring' in d:
            K1 = d['new_base_ring']
            R = R0.change_ring(K1)
        else:
            K1 = K0
            R = R0
        if 'rescale' in d:
            sub = d['rescale']
            I = I.apply_map(lambda g, sub=sub: g.rescale_vars(sub), new_ring=R)
        elif 'transform' in d:
            I = I.apply_map(d['transform'], new_ring=R)
        assume_odd = d['assume_odd'] if 'assume_odd' in d else None

        # Perform the recursion.
        if verbose:
            print(I)
        if I.is_zero():
            l2 = [I]
        else:
            l2 = torsion_closure_inner(I, assume_odd)
            for d1 in l2:
                if 'ideal' not in d1:
                    d1['ideal'] = I
                if assume_odd and ('assume_odd' not in d1):
                    d1['assume_odd'] = assume_odd
            l2 = torsion_closure_recurse(l2, verbose=verbose)

        # Postprocess the answers. At this point, l2 consists entirely
        # of torsion prime ideals.
        if 'untransform' in d:
            l2 = [{'ideal': J.apply_map(d['untransform'])} for J in l2]
            # Separate parallel tori.
            l2 = torsion_closure_recurse(l2, verbose=verbose)
        if 'rescale' in d:
            l3 = []
            N0 = K0.zeta_order()
            # When K1 is specified, it is an index-2 subfield of K0, and so 
            # the returned answers are only guaranteed to be complete up to
            # conjugation over K1. In order to get answers complete up to conjugation
            # over K1, we must account for the action of Gal(K0/K1).
            extra_conjugate = ('new_base_ring' in d)
            subd = {i: ~c for i,c in sub.items()}
            for J in l2:
                l4, K2 = extend_ideals_to_cyclotomic([J], K0)
                J2 = l4[0]
                R = R0.change_ring(K2)
                f = lambda g, subd=subd: g.rescale_vars(subd)
                l3.append(J2.apply_map(f))
                if extra_conjugate:
                    # Need an extra Galois conjugate.
                    N2 = K2.zeta_order()
                    m = coprime_factor(N2, N0)
                    m = crt(N0//2+1, 1, N2//m, m)
                    h = K2.hom([K2.gen()**m])
                    J2b = J2.apply_coeff_map(h, forward_hint=False)
                    l3.append(J2b.apply_map(f))
            l2 = l3
        if 'extra_output_gens' in d:
            l2 = [J + J.ring().ideal(d['extra_output_gens']) for J in l2]
        ans += l2
    return ans

def torsion_closure_canonicalize(l, K, all_conjugates=False):
    """
    Canonicalize the presentation of the torsion closure of an ideal.

    This is called by ``torsion_closure`` but typically not directly by the user.
    A case where one might call this directly is if one is breaking a complicated
    problem up manually into subcases (e.g., to account for symmetries).

    EXAMPLES::

        sage: P.<x,y,z> = LaurentPolynomialRing(QQ, 3)
        sage: f = x+y+z+x*y*z
        sage: I = P.ideal([f])
        sage: l = torsion_closure(I, raw=False)
        sage: l2 = torsion_closure(I, raw=True)
        sage: l == l2
        False
        sage: l == torsion_closure_canonicalize(l2, QQ)
        True
    """
    if not l:
        return []
    # Ensure that all primes are defined over the same extension field.
    l, K1 = extend_ideals_to_cyclotomic(l, K)
    Gal = [h for h in K1.automorphisms() if h(K.gen()) == K.gen()]
    # Classify primes by codimension and Galois conjugacy.
    n = l[0].ring().ngens()
    d = {dim: {} for dim in range(n+1)}
    known_gens = {dim: [] for dim in range(n+1)}
    for J in l:
        Jgens = J.gens()
        dim = n - J.dimension()
        if not (Jgens in known_gens[dim]):
            d[dim][Jgens] = [(Jgens, J)]
            known_gens[dim].append(Jgens)
            temp = [Jgens]
            for h in Gal:
                Jh = J.apply_coeff_map(h, forward_hint=False)
                Jhgens = Jh.gens()
                if not (Jhgens in temp):
                    d[dim][Jgens].append((Jhgens, Jh))
                    known_gens[dim].append(Jhgens)
                    temp.append(Jhgens)
    # Eliminate embedded primes. Note that this makes use of the full
    # Galois orbits computed in the previous step.
    d2 = {}
    for dim in range(n+1):
        d2[dim] = {}
        for Jgens in d[dim]:
            J = d[dim][Jgens][0][1]
            if not any(J1 <= J for i in range(dim)
                       for gens in d2[i] for (_, J1) in d[i][gens]):
                d2[dim][Jgens] = J
    if all_conjugates:
        # Return full lists of conjugates.
        l = [J for i in range(n+1) for gens in sorted(d2[i])
             for (_,J) in sorted(d[i][gens])]
    else:
        # Return the first term in each list of conjugates.
        l = [sorted(d[i][gens])[0][1] for i in range(n+1)
             for gens in sorted(d2[i])]
    l, _ = contract_ideals_to_cyclotomic(l, K)
    return l

def torsion_closure(I, raw=False, all_conjugates=False, debug=False, verbose=False):
    """
    Find the torsion closure of a Laurent polynomial ideal over a cyclotomic field.

    The torsion closure of an ideal is the Zariski closure of the set of 
    torsion points (in the ambient torus) contained in the support of the ideal.
    We represent this closure as a family of prime ideals over a possibly
    larger cyclotomic field.
 
    If ``raw`` is True, we only guarantee that:
    - every returned prime is binomial and contains the original ideal;
    - no prime is duplicated, except possibly after a base extension;
    - every minimal prime binomial containing the original ideal is represented
      by at least one Galois conjugate.

    If ``raw`` is False, we further guarantee that:
    - only minimal primes are returned;
    - every minimal prime is represented either exactly once (if 
      ``all_conjugates`` is False) or with all of its Galois conjugates (if 
      ``all_conjugates`` is True);
    - all primes are defined over a single base field, chosen as small as possible.
    These additional features can be enforced on raw output by calling 
    ``torsion_closure_canonicalize``.

    EXAMPLES::

        sage: P.<x> = LaurentPolynomialRing(QQ, 1)
        sage: I = P.ideal([x-1])
        sage: l = torsion_closure(I)
        sage: print([J.gens() for J in l])
        [(x - 1,)]

        sage: I = P.ideal([x^4-1])
        sage: l = torsion_closure(I)
        sage: print([J.gens() for J in l])
        [(x - 1,), (x - zeta4,), (x + 1,)]

        sage: P.<x,y> = LaurentPolynomialRing(QQ, 2)
        sage: I = P.ideal([x+y-1])
        sage: l = torsion_closure(I)
        sage: print([J.gens() for J in l])
        [(x - zeta6, y + zeta6 - 1)]
        sage: print(l[0].ring())
        Multivariate Laurent Polynomial Ring in x, y over Cyclotomic Field of order 6 and degree 2

        sage: K.<z5> = CyclotomicField(5)
        sage: P.<x,y> = LaurentPolynomialRing(K, 2)
        sage: I = P.ideal([x+y+z5])
        sage: l = torsion_closure(I)
        sage: print([J.gens() for J in l])
        [(x + zeta30, y + zeta30^6 - zeta30)]

        sage: P.<x,y,z> = LaurentPolynomialRing(QQ, 3)
        sage: f = x+y+z+x*y*z
        sage: I = P.ideal([f])
        sage: l = torsion_closure(I, raw=True)
        sage: print([J.gens() for J in l])
        [(x + 1, y - 1), (x - 1, y + 1), (x + 1, z - 1), (x - 1, z + 1), (x + 1, y + 1, z - 1), (x - 1, y - 1, z + 1), (y + 1, z - 1), (y - 1, z + 1), (x - 1, y + 1, z - 1), (x + 1, y - 1, z + 1), (x + 1, y - 1, z - 1), (x - 1, y + 1, z + 1)]
        sage: l = torsion_closure(I)
        sage: print([J.gens() for J in l])
        [(y - 1, z + 1), (y + 1, z - 1), (x - 1, z + 1), (x - 1, y + 1), (x + 1, z - 1), (x + 1, y - 1)]

    TESTS::

        sage: P.<x,y> = LaurentPolynomialRing(QQ, 2)
        sage: I = P.ideal([x^8+y^8-1])
        sage: l1 = torsion_closure(I, debug=True)
        sage: l1[0].gens()
        (x + zeta48^15 - zeta48^7, y + zeta48^11 - zeta48^3)
 
    We redo the previous example, this time computing all conjugates, to confirm that:
    - `l1` is irredundant (no entry is Galois conjugate to another);
    - every conjugate of an entry in ``l1`` appears in ``l2``;
    - every ideal in ``l2`` is conjugate to some ideal in ``l1``.

        sage: l2 = torsion_closure(I, all_conjugates=True, debug=True)
        sage: K2 = l2[0].base_ring()
        sage: Gal = K2.automorphisms()
        sage: for J in l1:
        ....:     for h in Gal:
        ....:         Jh = J.apply_coeff_map(h)
        ....:         assert not (Jh in l1 and J != Jh)
        sage: assert all(J.apply_coeff_map(h) in l2 for J in l1 for h in Gal)
        sage: assert all(any(J.apply_coeff_map(h) in l1 for h in Gal) for J in l2)

        sage: K.<z4> = CyclotomicField(4)
        sage: P.<x,y> = LaurentPolynomialRing(K, 2)
        sage: I = P.ideal([x^8+y^8-1])
        sage: l3 = torsion_closure(I, all_conjugates=True, debug=True)
        sage: assert all(J in l2 for J in l3) and all(J in l3 for J in l2)

        sage: K.<z4> = CyclotomicField(4)
        sage: P.<x,y> = LaurentPolynomialRing(K, 2)
        sage: I = P.ideal([x^8+y^8-1])
        sage: l4 = torsion_closure(I, debug=True)
        sage: print(len(l1), len(l2), len(l4))
        8 128 16

        sage: P.<x,y,z> = LaurentPolynomialRing(QQ, 3, order="degrevlex")
        sage: f = x + y + z + ~x + ~y + ~z + 2
        sage: I = P.ideal([f])
        sage: l1 = torsion_closure(I)
        sage: len(l1)
        18
        sage: l2 = torsion_closure(I, all_conjugates=True)
        sage: K = l2[0].base_ring()
        sage: z60 = K.gen()
        sage: J = P.change_ring(K).ideal([x-z60^20, y-z60^12, z-z60^24])
        sage: J in l2
        True

        sage: Gal = K.automorphisms()
        sage: for J in l1:
        ....:     for h in Gal:
        ....:         Jh = J.apply_coeff_map(h)
        ....:         assert not (Jh in l1 and J != Jh)
        sage: assert all(J.apply_coeff_map(h) in l2 for J in l1 for h in Gal)
        sage: assert all(any(J.apply_coeff_map(h) in l1 for h in Gal) for J in l2)

        sage: P.<x,y> = LaurentPolynomialRing(QQ, 2)
        sage: f = (1+(y+~y)^2)*(x+~x)^2 - 4
        sage: I1 = P.ideal([f])
        sage: l1 = torsion_closure(I1)
        sage: I2 = P.ideal([f(y,x)])
        sage: l2 = [J.ring().ideal([g(y,x) for g in J.gens()]) for J in torsion_closure(I2)]
        sage: assert all(J in l2 for J in l1)
        sage: assert all(J in l1 for J in l2)

    This example comes from the classification of Euclidean tetrahedra with
    rational dihedral angles::

        sage: K.<zeta24> = CyclotomicField(24)
        sage: P.<x1,x2,x3,x4,x5,x6> = LaurentPolynomialRing(K, 6)
        sage: M = Matrix([[-2, x1+1/x1, x3+1/x3, x5+1/x5], [x1+1/x1, -2, x6+1/x6, x4+1/x4], [x3+1/x3, x6+1/x6, -2, x2+1/x2], [x5+1/x5, x4+1/x4, x2+1/x2, -2]])
        sage: I = P.ideal([M.det(), x1*x3 + zeta24^3*x6^2, x1*x5 - x6, x5*x6 + (-zeta24^5 + zeta24)*x3, x2 + zeta24^6 - zeta24^2, x4 + zeta24^7])
        sage: l = torsion_closure(I)
        sage: assert all(M.det() in J for J in l)
    """
    P = I.ring()
    n = P.ngens()
    # Run the recursive computation.
    l = torsion_closure_recurse([{'ideal': I}], verbose=verbose)
    # Normalize generators.
    l = [J.normalize_gens() for J in l]
    # Classify primes by generators, eliminating duplicates.
    d = {}
    for J in l:
        if debug:
            assert J.is_prime() and J.is_binomial()
        d[J.gens()] = J
    l = list(d.values())
    if raw:
        return l
    # Further canonicalize the answer.
    K = P.base_ring()
    l = torsion_closure_canonicalize(l, K, all_conjugates)
    if debug:
        assert(I <= J for J in l)
    return l
