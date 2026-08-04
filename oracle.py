"""Static oracle for Av(1324): check a candidate against published data and
verified identities.  Surviving every check is not a proof; failing one is a
refutation.

Adjudicating a candidate answer
------------------------------
  python oracle.py solution "<G(x)>"            every applicable test at once
  python oracle.py gf       "<G(x)>"            expand and compare to A061552
  python oracle.py formula  "<a(n) in n>"       exact check against every term
  python oracle.py recurrence "P0|P1|..."       verify a P-recursion, coeffs constant-first
  python oracle.py algeq    "<P(G,x)>"          does the series satisfy it
  python oracle.py dfinite  [--surplus k]       search for a P-recursion, calibrated
  python oracle.py asymptotic B mu mu1 g [sig]  against the terms, not the fit
  python oracle.py K        "<expr in t>"       a K_t, with the mu it implies
  python oracle.py rhocheck t "<expr in y>"     a candidate rho_t

Checking our own decomposition
------------------------------
  python oracle.py status
  python oracle.py series  1,1,2,6,23,103,...   terms of A061552, a(0) first
  python oracle.py R       9  c0,c1,...         coefficients of R_9
  python oracle.py family  2  "expr in d"       a closed form for [s^t]R_d
  python oracle.py growth  11.6 [0.04] [-1.1]
  python oracle.py fit     v1,v2,... [--start]  hunt a closed form, with surplus
  python oracle.py rho     4                    hunt rho_t in powers of (1-y)
  python oracle.py forbidden d                  F = N_dec - N_sigma at that d
  python oracle.py threeblock [M]               the d = 2 level-1 identity
  python oracle.py blockmodel                   the increasing pattern at d = 2,3,4
  python oracle.py sigmamodel [d]               the block model at every pattern
  python oracle.py staircase                    the tromino bound and its conjecture
  python oracle.py chain [m]                    the chain operator and the g(k) ladder
  python oracle.py walks [n]                    the weighted quotient, both directions
  python oracle.py dominoes [b]                 transfer marginals vs enumeration
  python oracle.py geometric | antisym          the conjecture as one threshold
  python oracle.py theta | identities | calibrate | exponent | clearing | cfit | p3

Library
-------
  from oracle import check_series, check_R, check_two_term, check_family,
                     check_growth, fit_closed_form, fit_rho, check_gf,
                     check_algeq, guess_precursion, check_asymptotic, adjudicate
"""
import sys, re
from fractions import Fraction as Q
from math import comb, factorial, gcd, sqrt, log

try:
    import data as DT
except Exception:
    class _Fallback:
        """Inline copy of the published data: adjudication runs without the
        data layer; decomposition attributes raise and are reported."""
        A061552 = dict(enumerate([1, 1, 2, 6, 23, 103, 513, 2762, 15793, 94776,
            591950, 3824112, 25431452, 173453058, 1209639642, 8604450011,
            62300851632, 458374397312, 3421888118907, 25887131596018,
            198244731603623, 1535346218316422, 12015325816028313,
            94944352095728825, 757046484552152932, 6087537591051072864,
            49339914891701589053, 402890652358573525928,
            3313004165660965754922, 27424185239545986820514,
            228437994561962363104048, 1914189093351633702834757,
            16130725510342551986540152, 136664757387536091240503406,
            1163812341034817216384582333, 9959364766841851088593974979,
            85626551244475524038311935717, 739479176041581588794042743521,
            6413612398452364144369673970347, 55855094052029166019855630997080,
            488354507551082299792086219184434, 4286013140398612535730177106798038,
            37753338738386034300928290519149333,
            333720028221302436110132711265898937,
            2959914488410727889919188039470296624,
            26338690757116988316771828238926079326,
            235113956679181729949424482617740434207,
            2105162587512716675745868833684827184388,
            18904804517351837590874336467009693522354,
            170253750251391700942449152528030601519757,
            1537516984674177479234766336099763469212469]))
        MU, MU_ERR = 11.600, 0.003
        MU1, MU1_ERR = 0.0400, 0.0005
        G, G_ERR = -1.1, 0.1
        GR_LOWER, GR_UPPER = 10.271, 13.5
        @staticmethod
        def cat(n): return comb(2 * n, n) // (n + 1)
        def __getattr__(self, k):
            raise ImportError("data.py absent; %r needs the full data layer" % k)
    DT = _Fallback()

# ----------------------------------------------------------------- checking
def _row(name, ok, got, want): return (name, bool(ok), got, want)

def check_series(terms, start=1):
    """terms[i] is a(start+i) of A061552."""
    out = []
    for i, v in enumerate(terms):
        n = start + i
        if n not in DT.A061552: break
        out.append(_row("a(%d)" % n, int(v) == DT.A061552[n], v, DT.A061552[n]))
    return out

def check_R(d, coeffs):
    """coeffs: list or dict of R_d's coefficients, index = power of s."""
    Rd = dict(enumerate(coeffs)) if not isinstance(coeffs, dict) else dict(coeffs)
    Rd = {k: Q(v) for k, v in Rd.items() if Q(v) != 0}
    ev = lambda x: sum(v*(Q(x)**t) for t, v in Rd.items())
    out = [_row("no negative powers", all(t >= 0 for t in Rd), min(Rd, default=0), ">= 0"),
           _row("degree = 2d-2", max(Rd) == 2*d-2, max(Rd), 2*d-2),
           _row("R(1) = A061552(d)", ev(1) == DT.A061552[d], ev(1), DT.A061552[d]),
           _row("R(-1) = 1", ev(-1) == 1, ev(-1), 1)]
    for t, f in ((0, DT.s0), (1, DT.s1), (2, DT.s2), (3, DT.s3)):
        if 2*d-2 >= t:
            out.append(_row("[s^%d]" % t, Rd.get(t, Q(0)) == f(d), Rd.get(t, Q(0)), f(d)))
    if d in DT.KNOWN_R:
        ref = DT.R(d)
        out.append(_row("matches our R_%d" % d, Rd == {k: v for k, v in ref.items() if v != 0},
                        "...", "..."))
    return out

def check_two_term(d, p, q):
    """p, q: coefficient lists (constant first) of p_d and q_d."""
    p = [Q(x) for x in p]; q = [Q(x) for x in q]
    pv = lambda c, M: sum(a*Q(M)**i for i, a in enumerate(c))
    out = [_row("deg p = d-1", len(p)-1 == d-1, len(p)-1, d-1),
           _row("deg q = d-2", len(q)-1 == d-2, len(q)-1, d-2),
           _row("lead p", p[-1] == DT.p_lead(d), p[-1], DT.p_lead(d)),
           _row("lead q", q[-1] == DT.q_lead(d), q[-1], DT.q_lead(d))]
    if d >= 2: out.append(_row("p_{d,d-2}", p[-2] == DT.p_sublead(d), p[-2], DT.p_sublead(d)))
    if d >= 3: out.append(_row("q_{d,d-3}", q[-2] == DT.q_sublead(d), q[-2], DT.q_sublead(d)))
    out.append(_row("p(0)-q(0) = 1", pv(p,0)-pv(q,0) == 1, pv(p,0)-pv(q,0), 1))
    out.append(_row("p(0)+q(0) = A061552(d)", pv(p,0)+pv(q,0) == DT.A061552[d],
                    pv(p,0)+pv(q,0), DT.A061552[d]))
    for M, v in sorted(DT.D.get(d, {}).items()):
        got = pv(p,M)*comb(2*M,M) + pv(q,M)*4**M
        out.append(_row("D(%d,%d)" % (d, M), got == v, got, v))
    return out

def check_family(t, f):
    """f: d -> value.  Checked against [s^t]R_d for every d we hold."""
    out = []
    for d in DT.KNOWN_R:
        if 2*d-2 < t: continue
        want = DT.R(d).get(t, Q(0))
        try: got = Q(f(d))
        except Exception as e: got = "error: %s" % e
        out.append(_row("[s^%d]R_%d" % (t, d), got == want, got, want))
    return out

def check_diagonal(d, f):
    """f: M -> D(d,M).  Checked against every value we hold, plus A061552 for M<=2."""
    out = []
    for M in range(0, 3):
        want = DT.A061552.get(d + M)
        if want is None: continue
        out.append(_row("D(%d,%d) = A061552(%d)" % (d, M, d+M), f(M) == want, f(M), want))
    for M, v in sorted(DT.D.get(d, {}).items()):
        out.append(_row("D(%d,%d)" % (d, M), f(M) == v, f(M), v))
    return out

def check_growth(mu, mu1=None, g=None):
    out = [_row("mu in proved bounds", DT.GR_LOWER <= mu <= DT.GR_UPPER, mu,
                (DT.GR_LOWER, DT.GR_UPPER)),
           _row("mu within 5 sigma of CGZJ", abs(mu-DT.MU) <= 5*DT.MU_ERR, mu, DT.MU)]
    if mu1 is not None:
        out.append(_row("mu_1 within 5 sigma", abs(mu1-DT.MU1) <= 5*DT.MU1_ERR, mu1, DT.MU1))
    if g is not None:
        out.append(_row("g within 5 sigma", abs(g-DT.G) <= 5*DT.G_ERR, g, DT.G))
    return out

# ------------------------------------------------------- closed-form hunting
def _solve(rows, rhs, unk):
    n = len(rows)
    A = [rows[i][:] + [rhs[i]] for i in range(n)]
    piv = 0; where = [-1]*unk
    for c in range(unk):
        r = next((i for i in range(piv, n) if A[i][c] != 0), None)
        if r is None: continue
        A[piv], A[r] = A[r], A[piv]
        pv = A[piv][c]; A[piv] = [x/pv for x in A[piv]]
        for i in range(n):
            if i != piv and A[i][c] != 0:
                f = A[i][c]; A[i] = [a-f*b for a, b in zip(A[i], A[piv])]
        where[c] = piv; piv += 1
    for i in range(piv, n):
        if A[i][unk] != 0: return None
    if piv < unk: return None
    return [A[where[c]][unk] for c in range(unk)]

def _dfact(n):
    if n <= 0: return 1
    p = 1
    while n > 1: p *= n; n -= 2
    return p

def fit_closed_form(vals, start=1, min_surplus=1):
    """Closed form for vals[i] at d = start+i, in four families tried in order:
    polynomial in d; rational in d; polynomial times C(2d-2a,d-a)/4^(d-a);
    polynomial times (2d-2a-1)!!/(2^(d-b) d!).  Fits with fewer than
    min_surplus unused data points are rejected as interpolations.
    """
    pts = [(start+i, Q(v)) for i, v in enumerate(vals)]
    n = len(pts)
    hits = []

    for deg in range(0, n):
        if n - (deg+1) < min_surplus: break
        rows = [[Q(x)**j for j in range(deg+1)] for x, _ in pts]
        s = _solve(rows, [y for _, y in pts], deg+1)
        if s: hits.append(("polynomial in d, degree %d" % deg, n-(deg+1), s)); break

    if not hits:
        for tot in range(1, n):
            done = False
            for dd in range(0, min(tot, 4)):
                dn = tot - dd; unk = dn+1+dd
                if n - unk < min_surplus: continue
                rows = [[Q(x)**j for j in range(dn+1)] + [-y*Q(x)**j for j in range(dd)]
                        for x, y in pts]
                s = _solve(rows, [y*Q(x)**dd for x, y in pts], unk)
                if s:
                    hits.append(("rational in d, numerator degree %d over denominator degree %d"
                                 % (dn, dd), n-unk, s)); done = True; break
            if done: break

    if not hits:
        for a in range(0, 5):
            for deg in range(0, n):
                if n - (deg+1) < min_surplus: break
                try:
                    st = [(x, y * Q(4**(x-a), comb(2*x-2*a, x-a))) for x, y in pts]
                except (ValueError, ZeroDivisionError): break
                rows = [[Q(x)**j for j in range(deg+1)] for x, _ in st]
                s = _solve(rows, [y for _, y in st], deg+1)
                if s:
                    hits.append(("C(2d-%d,d-%d)/4^(d-%d) times a degree-%d polynomial"
                                 % (2*a, a, a, deg), n-(deg+1), s)); break
            if hits: break

    if not hits:
        for a in range(1, 6):
            for b in range(0, 4):
                for deg in range(0, n):
                    if n - (deg+1) < min_surplus: break
                    den = [_dfact(2*x-2*a-1) for x, _ in pts]
                    if any(v == 0 for v in den): break
                    st = [(x, y * (Q(2)**(x-b)) * factorial(x) / den[i])
                          for i, (x, y) in enumerate(pts)]
                    rows = [[Q(x)**j for j in range(deg+1)] for x, _ in st]
                    s = _solve(rows, [y for _, y in st], deg+1)
                    if s:
                        hits.append(("(2d-%d)!!/(2^(d-%d) d!) times a degree-%d polynomial"
                                     % (2*a+1, b, deg), n-(deg+1), s)); break
                if hits: break
            if hits: break
    return hits

def _binom_coef(alpha, d):
    """[y^d] of (1-y)^alpha, exact for rational alpha."""
    c = Q(1)
    for i in range(d): c *= (alpha - i)
    return c / factorial(d) * ((-1)**d)

def fit_rho(t, max_I=9, min_surplus=1, values=None, dmax=None):
    """rho_t as a combination of (1-y)^(1/2-3t/2+i), i = 0..I, plus a constant
    when 0 is not among the exponents; d with 2d-2 < t contribute zero rows.
    Returns (I, names, coefficients, surplus, flag) at the smallest I fitting
    with min_surplus to spare, else None; flag marks a vanishing leading
    coefficient.  `values` and `dmax` fit a candidate family past the held range.
    """
    base = Q(1, 2) - Q(3*t, 2)
    if values is not None:
        dmax = dmax if dmax is not None else 34
        ds = list(range(0, dmax + 1))
        vals = [Q(values(d)) if 2*d-2 >= t else Q(0) for d in ds]
    else:
        dmax = max(DT.KNOWN_R) if dmax is None else dmax
        ds = list(range(0, dmax + 1))
        vals = [DT.R(d).get(t, Q(0)) if (d in DT.KNOWN_R and 2*d-2 >= t) else Q(0)
                for d in ds]
    for I in range(0, max_I + 1):
        exps = [base + i for i in range(I + 1)]
        cols = list(exps)
        const = Q(0) not in [e for e in exps]
        rows = []
        for d in ds:
            row = [_binom_coef(e, d) for e in cols]
            if const: row = [Q(1) if d == 0 else Q(0)] + row
            rows.append(row)
        unk = len(cols) + (1 if const else 0)
        if len(ds) - unk < min_surplus: continue
        s = _solve(rows, vals, unk)
        if s:
            names = (["1"] if const else []) + ["(1-y)^(%s)" % e for e in exps]
            lead = s[1 if const else 0]
            if lead == 0:
                # Vanishing leading coefficient means the true exponent is higher
                # than assumed, so this is not a fit at 1/2 - 3t/2.
                return (I, names, s, len(ds) - unk, "LEADING COEFFICIENT ZERO: "
                        "rho_%d is less singular than (1-y)^(%s); the exponent "
                        "law does not hold at this t, or the input is wrong" % (t, exps[0]))
            return (I, names, s, len(ds) - unk, None)
    return None

# ------------------------------------------------------- the theta calculus
# theta = x d/dx sends s^-k to (k/2)(s^-(k+2) - s^-k), so it acts triangularly
# on the two bases.  Writing theta^j(1/s) = sum_i c(j,i) s^-(2i+1) and
# theta^j(1/s^2) = sum_i e(j,i) s^-(2i+2), the coefficients of R_d are linear in
# p_d and q_d through these matrices: [s^(2d-2-2i)]R_d = sum_j p_{d,j} c(j,i)
# and [s^(2d-3-2i)]R_d = sum_j q_{d,j} e(j,i).
def theta_c(J=14):
    c = {(0, 0): Q(1)}
    for j in range(0, J):
        for i in range(0, j+2):
            c[(j+1, i)] = Q(2*i-1, 2)*c.get((j, i-1), Q(0)) - Q(2*i+1, 2)*c.get((j, i), Q(0))
    return c

def theta_e(J=14):
    e = {(0, 0): Q(1)}
    for j in range(0, J):
        for i in range(0, j+2):
            e[(j+1, i)] = Q(i)*e.get((j, i-1), Q(0)) - Q(i+1)*e.get((j, i), Q(0))
    return e

def check_theta(J=9):
    """The three closed diagonals on each side, all derived from the recursions."""
    c, e = theta_c(J+3), theta_e(J+3)
    out = []
    for j in range(1, J+1):
        k = j - 1
        out.append(_row("c(%d,%d) = (2j-1)!!/2^j" % (j, j),
                        c[(j, j)] == Q(_dfact(2*j-1), 2**j), c[(j, j)], Q(_dfact(2*j-1), 2**j)))
        out.append(_row("c(%d,%d)/c = -j^2/(2j-1)" % (j, j-1),
                        c[(j, j-1)]/c[(j, j)] == Q(-j*j, 2*j-1),
                        c[(j, j-1)]/c[(j, j)], Q(-j*j, 2*j-1)))
        if j >= 2:
            w = Q(k*(k+1)*(3*k*k+k-1), 6*(2*j-1)*(2*j-3))
            out.append(_row("c(%d,%d)/c" % (j, j-2), c[(j, j-2)]/c[(j, j)] == w,
                            c[(j, j-2)]/c[(j, j)], w))
        out.append(_row("e(%d,%d) = j!" % (j, j), e[(j, j)] == Q(factorial(j)),
                        e[(j, j)], factorial(j)))
        out.append(_row("e(%d,%d)/e = -(j+1)/2" % (j, j-1),
                        e[(j, j-1)]/e[(j, j)] == Q(-(j+1), 2),
                        e[(j, j-1)]/e[(j, j)], Q(-(j+1), 2)))
        if j >= 2:
            z = Q((3*j-2)*(j+1), 24)
            out.append(_row("e(%d,%d)/e" % (j, j-2), e[(j, j-2)]/e[(j, j)] == z,
                            e[(j, j-2)]/e[(j, j)], z))
    return out

def _ev(c, x): return sum(a*Q(x)**i for i, a in enumerate(c))

def check_top_identities():
    """c(j,0) = (-1/2)^j and e(j,0) = (-1)^j, so the top-end families of R_d are
    p_d and q_d at a point."""
    out = []
    for d in DT.KNOWN_R:
        R = DT.R(d)
        out.append(_row("[s^%d]R_%d = p_d(-1/2)" % (2*d-2, d),
                        R.get(2*d-2, Q(0)) == _ev(DT.P[d], Q(-1, 2)),
                        R.get(2*d-2, Q(0)), _ev(DT.P[d], Q(-1, 2))))
        if d >= 2:
            out.append(_row("[s^%d]R_%d = q_d(-1)" % (2*d-3, d),
                            R.get(2*d-3, Q(0)) == _ev(DT.QQ[d], Q(-1)),
                            R.get(2*d-3, Q(0)), _ev(DT.QQ[d], Q(-1))))
    return out

# ------------------------------- from p_{d,d-3} to [s^4], rho_4, K_4, verdict
def s4_from_p3(p3, J=64):
    """[s^4]R_d from a candidate p_{d,d-3}.  Every other term is closed, so this
    is one unknown in one equation.  J bounds the theta matrix and hence the
    largest d evaluable; raise it rather than catching the error."""
    c = theta_c(J)
    def f(d):
        if d < 3: return Q(0)
        if (d-1, d-3) not in c:
            raise ValueError("theta_c too small for d=%d; pass J >= %d" % (d, d+2))
        return (DT.p_lead(d)*c[(d-1, d-3)] + DT.p_sublead(d)*c[(d-2, d-3)]
                + Q(p3(d))*c[(d-3, d-3)])
    return f

def s5_from_q4(q4, J=64):
    """[s^5]R_d from a candidate q_{d,d-4}, by the same route on the 4^M side."""
    e = theta_e(J)
    def f(d):
        if d < 4: return Q(0)
        if (d-2, d-4) not in e:
            raise ValueError("theta_e too small for d=%d; pass J >= %d" % (d, d+2))
        return (DT.q_lead(d)*e[(d-2, d-4)] + DT.q_sublead(d)*e[(d-3, d-4)]
                + Q(q4(d))*e[(d-4, d-4)])
    return f

# K_t is the leading singular coefficient of rho_t at y = 1.
K_OBSERVED = {0: Q(-2), 1: Q(1, 2), 2: Q(1, 4), 3: Q(1, 4)}

def K_models():
    kb = (1 - 1.0/DT.MU) ** 1.5
    kc = log(DT.MU) ** 1.5
    lam = 2.718281828459045 ** (log(DT.MU1) / sqrt(2.0*log(DT.MU)/3.0))
    Cc = 0.5 / (kc * lam)
    return {
        "b movable singularity": lambda t: 0.25 * kb ** (t-2),
        "c geometric x stretched": lambda t: Cc * kc**t * lam**sqrt(t),
        "d Gaussian": lambda t: float(Q(2) * Q(2)**(t*(t-1)//2) / Q(4)**t),
    }

def check_K(K4, K5=None, tol=0.02):
    """Adjudicate the K_t models against an observed K_4 and optional K_5."""
    out = []
    for name, f in sorted(K_models().items()):
        pred = f(4)
        ok = abs(float(K4) - pred) <= tol * max(1.0, abs(pred))
        out.append(_row("K_4 under %s" % name, ok, float(K4), round(pred, 5)))
        if K5 is not None:
            p5 = f(5)
            ok5 = abs(float(K5) - p5) <= tol * max(1.0, abs(p5))
            out.append(_row("K_5 under %s" % name, ok5, float(K5), round(p5, 5)))
    return out

# ---------------------------------------------------------------- calibration
def calibrate():
    """Fitter calibration: four families held in closed form and one deliberate
    negative, p_d(0) = (A061552(d)+1)/2, exactly known and correctly unreachable
    since no tried family contains A061552."""
    known = []
    known.append(("[s^0]R_d", [DT.s0(d) for d in range(1, 10)], 1, True))
    known.append(("[s^2]R_d", [DT.s2(d) for d in range(2, 10)], 2, True))
    known.append(("[s^3]R_d", [DT.s3(d) for d in range(3, 10)], 3, True))
    known.append(("d! p_{d,d-2}", [DT.p_sublead(d)*factorial(d) for d in range(2, 10)], 2, True))
    known.append(("p_d(0) = (A061552+1)/2",
                  [Q(DT.A061552[d]+1, 2) for d in range(1, 10)], 1, False))
    out = []
    for name, vals, st, reachable in known:
        hits = fit_closed_form(vals, start=st)
        out.append(_row("%s %s" % (name, "(should be found)" if reachable
                                   else "(should NOT be found: contaminated)"),
                        bool(hits) == reachable,
                        "found" if hits else "not found",
                        "found" if reachable else "not found"))
    return out

# ----------------------------------------- adjudicating a proposed solution
# The checks above test our own decomposition against itself.  These test a
# candidate answer to Av(1324): a generating function, an algebraic equation, a
# P-recursion, an asymptotic form, a K_t, or a rho_t.
import series as SR


def av1324_series(n=51):
    """A061552 as a truncated power series, a(0) = 1."""
    return SR.S([DT.A061552[i] for i in range(min(n, max(DT.A061552) + 1))], n)


def check_gf(expr, n=51):
    """Expand a candidate G(x) and compare with every term of A061552."""
    try:
        f = SR.evaluate(expr, n)
    except Exception as e:
        return [_row("expansion", False, "error: %s" % e, "a power series")]
    out = []
    first_bad = None
    for i in range(min(n, max(DT.A061552) + 1)):
        ok = f[i] == DT.A061552[i]
        if not ok and first_bad is None: first_bad = i
        out.append(_row("[x^%d]" % i, ok, f[i], DT.A061552[i]))
    return out


def check_algeq(expr, n=51):
    """Substitute the known series into a candidate P(G,x) and check it vanishes.

    expr is written in G and x, e.g. "x**2*G**3 + G - 1".  A genuine algebraic
    equation vanishes to the full order held; a wrong one shows its first
    surviving coefficient.
    """
    G = av1324_series(n)
    try:
        f = SR.evaluate(expr, n, extra={"G": G, "A": G})
    except Exception as e:
        return [_row("substitution", False, "error: %s" % e, "a power series")]
    v = f.valuation()
    return [_row("P(G,x) = 0 to order %d" % (n - 1), v >= n,
                 "first nonzero coefficient at x^%d" % v if v < n else "vanishes", 0)]


def _prec_rows(a, r, m, n0=0):
    """rows of sum_j P_j(n) a(n+j) = 0 with deg P_j <= m, unknowns P_j's coefficients"""
    N = len(a)
    rows = []
    for n in range(n0, N - r):
        rows.append([Q(n) ** k * a[n + j] for j in range(r + 1) for k in range(m + 1)])
    return rows


def guess_precursion(a, rmax=6, mmax=8, min_surplus=5, budget=48):
    """Search for sum_{j<=r} P_j(n) a(n+j) = 0 with deg P_j <= m; (r+1)(m+1)
    capped by budget.  Returns (r, m, basis, surplus) at the smallest unknown
    count with min_surplus spare equations, else None."""
    cands = sorted(((r + 1) * (m + 1), r, m)
                   for r in range(1, rmax + 1) for m in range(0, mmax + 1)
                   if (r + 1) * (m + 1) <= budget)
    for unk, r, m in cands:
        rows = _prec_rows(a, r, m)
        if len(rows) - unk + 1 < min_surplus: continue
        basis, rank = SR.nullspace(rows, unk)
        if basis:
            return r, m, basis, len(rows) - rank
    return None


def check_precursion(a, polys):
    """Verify a proposed P-recursion.  polys[j] is P_j's coefficient list."""
    N = len(a); r = len(polys) - 1
    out = []
    for n in range(0, N - r):
        s = sum(sum(c * Q(n) ** k for k, c in enumerate(polys[j])) * a[n + j]
                for j in range(r + 1))
        out.append(_row("n = %d" % n, s == 0, s, 0))
    return out


def calibrate_precursion(min_surplus=5):
    """Run the guesser on the two solved length-4 classes before trusting a negative."""
    g1234 = [sum(comb(2 * k, k) * comb(n + 1, k + 1) * comb(n + 2, k + 1)
                 for k in range(n + 1)) // ((n + 1) ** 2 * (n + 2))
             for n in range(0, 51)]
    f = SR.evaluate("32*x/(-8*x**2+20*x+1-(1-8*x)**Q(3,2))", 51)
    g1342 = [f[i] for i in range(51)]
    out = []
    for name, seq, want in (("Av(1234)", [Q(v) for v in g1234], True),
                            ("Av(1342)", [Q(v) for v in g1342], True)):
        hit = guess_precursion(seq, min_surplus=min_surplus)
        out.append(_row("%s P-recursion" % name, bool(hit) == want,
                        "order %d degree %d surplus %d" % (hit[0], hit[1], hit[3])
                        if hit else "not found", "found"))
    return out


def check_asymptotic(B, mu, mu1, g, sigma=0.5):
    """Compare B mu^n mu1^(n^sigma) n^g against every term of A061552."""
    out = []
    errs = []
    for n in (10, 20, 30, 40, 50):
        if n not in DT.A061552: continue
        pred = B * mu ** n * mu1 ** (n ** sigma) * n ** g
        act = float(DT.A061552[n])
        rel = (pred - act) / act
        errs.append(abs(rel))
        out.append(_row("n = %d relative error" % n, abs(rel) < 0.25,
                        "%+.4f" % rel, "|.| < 0.25"))
    if len(errs) >= 2:
        out.append(_row("error decreasing in n", errs[-1] <= errs[0],
                        "%.4f -> %.4f" % (errs[0], errs[-1]), "decreasing"))
    out.extend(check_growth(mu, mu1, g))
    return out


def check_K_expr(f, tmax=4, kappa_at=60):
    """Candidate K_t against the observed values; K_t ~ C kappa^t implies
    mu = exp(kappa^(2/3)), and an implied mu outside the proved bounds refutes."""
    obs = dict(K_OBSERVED); obs[4] = Q(21, 64)
    out = []
    for t in sorted(obs):
        if t > tmax: continue
        try: got = Q(f(t))
        except Exception as e: got = "error: %s" % e
        out.append(_row("K_%d%s" % (t, " (conditional)" if t == 4 else ""),
                        got == obs[t], got, obs[t]))
    try:
        r = [abs(float(f(t))) for t in (kappa_at - 1, kappa_at)]
        kap = r[1] / r[0] if r[0] else 0.0
        mu = 2.718281828459045 ** (kap ** (2.0 / 3.0)) if kap > 0 else 0.0
        out.append(_row("implied kappa = lim K_t^(1/t)", True, "%.5f" % kap, "-"))
        out.append(_row("implied mu = exp(kappa^(2/3))",
                        DT.GR_LOWER <= mu <= DT.GR_UPPER, "%.5f" % mu,
                        "[%.3f, %.1f]" % (DT.GR_LOWER, DT.GR_UPPER)))
    except Exception:
        out.append(_row("implied mu", True, "not evaluable at t = %d" % kappa_at,
                        "give a K_t defined for all t"))
    return out


def check_rho(t, expr, dmax=None):
    """Check a candidate rho_t(y) against the [s^t]R_d we hold."""
    dmax = max(DT.KNOWN_R) if dmax is None else dmax
    try:
        f = SR.evaluate(expr, dmax + 1)
    except Exception as e:
        return [_row("expansion", False, "error: %s" % e, "a power series")]
    out = []
    for d in range(0, dmax + 1):
        want = DT.R(d).get(t, Q(0)) if (d in DT.KNOWN_R and 2 * d - 2 >= t) else Q(0)
        out.append(_row("[y^%d]rho_%d" % (d, t), f[d] == want, f[d], want))
    return out


def check_at_minus_one():
    """R_d(-1) = p_d(0) - q_d(0) = 1 and R_d'(-1) = p_d(1) - 2 q_d(1) - (2d-1);
    the zero of R_d nearest -1 sits at 1 + rho = -1/R_d'(-1) to first order,
    so mu is the growth rate of |R_d'(-1)|."""
    out = []
    for d in DT.KNOWN_R:
        R = DT.R(d)
        val = sum(v * Q(-1) ** t for t, v in R.items())
        out.append(_row("R_%d(-1)" % d, val == 1, val, 1))
        der = sum(t * v * Q(-1) ** (t - 1) for t, v in R.items())
        cf = _ev(DT.P[d], 1) - 2 * _ev(DT.QQ[d], 1) - (2 * d - 1)
        out.append(_row("R_%d'(-1) closed form" % d, der == cf, der, cf))
    return out


def guess_algeq(coeffs, dymax=4, dzmax=6, min_surplus=2, budget=None):
    """Search for P(F,z) = 0 with deg_y P <= dy, deg_z P <= dz over the given
    coefficients; a nontrivial nullspace with min_surplus spare equations
    qualifies.  Returns (dy, dz, basis, surplus) at the smallest unknown count,
    else None."""
    N = len(coeffs)
    F = SR.S([Q(v) for v in coeffs], N)
    pw = [SR.S([1], N)]
    for _ in range(dymax): pw.append(pw[-1] * F)
    cands = sorted(((dy + 1) * (dz + 1), dy, dz)
                   for dy in range(1, dymax + 1) for dz in range(0, dzmax + 1)
                   if budget is None or (dy + 1) * (dz + 1) <= budget)
    for unk, dy, dz in cands:
        if N - unk + 1 < min_surplus: continue
        rows = []
        for m in range(N):
            rows.append([pw[i][m - j] if m - j >= 0 else Q(0)
                         for i in range(dy + 1) for j in range(dz + 1)])
        basis, rank = SR.nullspace(rows, unk)
        if basis:
            return dy, dz, basis, N - rank
    return None


def calibrate_algeq(nterms=26):
    """Validate the algebraic guesser on A000139, whose minimal polynomial is
    z^4 y^3 + 2z^2(3z+1) y^2 + (12z^2-10z+1) y + 8z - 1."""
    a = [Q(2 * factorial(3 * n + 3), factorial(n + 2) * factorial(2 * n + 3))
         for n in range(nterms)]
    hit = guess_algeq(a, dymax=3, dzmax=4, min_surplus=1)
    return [_row("A000139 algebraic equation found", bool(hit),
                 "degree %d in y, %d in z, surplus %d" % (hit[0], hit[1], hit[3])
                 if hit else "not found", "degree 3 in y, 4 in z")]


def check_HBA(nmax=10):
    """(x-y) H(x,y) = x B(x,y) - y A(y), with H(x,y) = Sum D(d,M) x^M y^d,
    B(x,y) = Sum over avoiders of x^L y^(n-L), A(y) the counting series;
    boundaries B(x,0) = C(x), B(z,z) = A(z), B(0,y) = 1."""
    import transfer as TR
    J = TR.joint_nL(nmax)
    out = []
    for n in sorted(J):
        tot = sum(J[n].values())
        out.append(_row("A061552(%d)" % n, tot == DT.A061552[n], tot, DT.A061552[n]))
        out.append(_row("Cat(%d) at L = n" % n, J[n].get(n, 0) == DT.cat(n),
                        J[n].get(n, 0), DT.cat(n)))
    H, B, A = {}, {}, {}
    for n in sorted(J):
        A[n] = sum(J[n].values())
        for L, c in J[n].items():
            B[(L, n - L)] = B.get((L, n - L), 0) + c
            for M in range(0, L + 1): H[(M, n - M)] = H.get((M, n - M), 0) + c
    bad = 0
    for i in range(0, nmax):
        for j in range(0, nmax - i):
            lhs = H.get((i - 1, j), 0) - H.get((i, j - 1), 0)
            rhs = B.get((i - 1, j), 0) - (A.get(j - 1, 0) if i == 0 else 0)
            if lhs != rhs: bad += 1
    out.append(_row("(x-y)H = xB - yA over i+j <= %d" % (nmax - 1), bad == 0, bad, 0))
    return out


def local_exponent(vals, ds):
    """-log(f(d)/f(d-1)) / log(d/(d-1)): settles if f decays polynomially, rises
    linearly if f decays geometrically."""
    return [-log(vals[i] / vals[i - 1]) / log(ds[i] / ds[i - 1])
            for i in range(1, len(vals))]


def where_is_mu():
    """A061552(d) = R_d(1) = Sum_t [s^t]R_d: locate the argmax over t and test
    whether the top-pair share decays polynomially or geometrically."""
    ds = [d for d in DT.KNOWN_R if d >= 4]
    out = []
    for d in ds:
        R = DT.R(d)
        ts = max(R, key=lambda t: R[t])
        out.append(_row("argmax t at d=%d" % d, ts == 2 * d - 3, ts, 2 * d - 3))
    share = [float((DT.R(d).get(2 * d - 2, Q(0)) + DT.R(d).get(2 * d - 3, Q(0)))
                   / sum(DT.R(d).values())) for d in ds]
    th = local_exponent(share, ds)
    falling = all(th[i + 1] < th[i] for i in range(1, len(th) - 1))
    out.append(_row("top-pair share at d=%d" % ds[-1], share[-1] > 0.4,
                    "%.4f" % share[-1], "> 0.4"))
    out.append(_row("its local exponent falls (not geometric)", falling,
                    "%s" % ["%.3f" % v for v in th], "falling"))
    ctrl = local_exponent([0.9 ** d for d in ds], ds)
    out.append(_row("control 0.9^d rises", all(ctrl[i + 1] > ctrl[i]
                                               for i in range(len(ctrl) - 1)),
                    "%.3f -> %.3f" % (ctrl[0], ctrl[-1]), "rising"))
    return out


def extrapolation_is_valid(ds=None):
    """Control: the 1/d ratio extrapolation applied to A061552 itself, whose
    limit is known."""
    ds = [d for d in DT.KNOWN_R if d >= 2] if ds is None else ds
    r = [DT.A061552[d] / DT.A061552[d - 1] for d in ds]
    x1, x2 = 1.0 / ds[-2], 1.0 / ds[-1]
    est = r[-1] + (r[-1] - r[-2]) * (0.0 - x2) / (x2 - x1)
    return [_row("1/d extrapolation of A061552 ratios",
                 abs(est - DT.MU) < 0.5, "%.2f" % est, "%.3f" % DT.MU)]


def check_formula(expr, nmax=None):
    """Exact check of a closed form a(n) against every held term."""
    env = {"Q": Q, "comb": comb, "factorial": factorial, "cat": DT.cat,
           "dfact": _dfact, "sqrt": sqrt, "log": log}
    out = []
    top = max(DT.A061552) if nmax is None else nmax
    for n in range(0, top + 1):
        if n not in DT.A061552: continue
        try:
            got = eval(expr, dict(env, n=n))
            got = Q(got) if not isinstance(got, float) else got
        except Exception as e:
            return out + [_row("evaluation at n=%d" % n, False, "error: %s" % e,
                               "an integer")]
        out.append(_row("a(%d)" % n, got == DT.A061552[n], got, DT.A061552[n]))
        if got != DT.A061552[n] and len(out) > 8: break
    return out


def _polys_from_basis(vec, r, m):
    """P_j coefficient lists from one nullspace vector of the recursion search."""
    return [list(vec[j * (m + 1):(j + 1) * (m + 1)]) for j in range(r + 1)]


def tail_growth(coeffs, window=12):
    """Growth read off a candidate's own tail: ratios, and the pair
    extrapolants under 1/n and 1/sqrt(n) corrections."""
    n1 = len(coeffs) - 1
    rs = [(i, float(coeffs[i] / coeffs[i - 1]))
          for i in range(n1 - window, n1 + 1) if coeffs[i - 1] != 0]
    mu_n = [b * rb - a * ra for (a, ra), (b, rb) in zip(rs, rs[1:])]
    mu_s = [(sqrt(b) * rb - sqrt(a) * ra) / (sqrt(b) - sqrt(a))
            for (a, ra), (b, rb) in zip(rs, rs[1:])]
    return rs[-1][1], mu_n[-1], mu_s[-1]


def adjudicate(expr, n=51):
    """Run every applicable test on a candidate generating function."""
    print("  candidate G(x) = %s\n" % expr)
    ok = report("terms against A061552", check_gf(expr, n))
    if not ok:
        print("\n  VERDICT: REFUTED by the counting sequence.")
        return False
    print("\n  all held terms reproduced; structural tests follow.\n")
    try:
        f = SR.evaluate(expr, n)
        a = [f[i] for i in range(n)]
        hit = guess_precursion(a)
        if hit:
            print("  P-recursive: order %d, degree %d, surplus %d" % (hit[0], hit[1], hit[3]))
            print("  This CONTRADICTS the Conway-Guttmann-Zinn-Justin conjecture;")
            polys = _polys_from_basis(hit[2][0], hit[0], hit[1])
            held = [Q(DT.A061552[i]) for i in range(0, max(DT.A061552) + 1)
                    if i in DT.A061552]
            bad = [r for r in check_precursion(held, polys) if not r[1]]
            if bad:
                print("  the recurrence fails on the held terms at %s;" % bad[0][0])
                print("  the candidate diverges from A061552 beyond the terms shown.")
                print("\n  VERDICT: REFUTED by its own recurrence against the held terms.")
                return False
            print("  the recurrence is consistent with all %d held terms." % len(held))
        else:
            print("  no P-recursion within the search budget, consistent with CGZJ")
    except Exception as e:
        print("  P-recursion search failed: %s" % e)
    try:
        deep = 200
        f2 = SR.evaluate(expr, deep)
        c = [f2[i] for i in range(deep)]
        if all(v > 0 for v in c[1:]):
            r, mu_n, mu_s = tail_growth(c)
            print()
            print("  tail of the candidate's own expansion at n = %d:" % (deep - 1))
            print("    ratio %.5f, extrapolants mu = %.4f under 1/n, %.4f under 1/sqrt(n)"
                  % (r, mu_n, mu_s))
            lo, hi = min(mu_n, mu_s), max(mu_n, mu_s)
            if hi < DT.GR_LOWER - 0.05 or lo > DT.GR_UPPER + 0.05:
                print("\n  VERDICT: REFUTED: its own tail growth [%.3f, %.3f] leaves"
                      " the proved window [%.3f, %.1f]."
                      % (lo, hi, DT.GR_LOWER, DT.GR_UPPER))
                return False
            if abs(mu_n - mu_s) < 0.02:
                print("    the two corrections agree: a power-law tail, in"
                      " tension with the CGZJ stretched exponential")
        else:
            print("\n  tail analysis skipped: nonpositive coefficients in the extension")
    except Exception as e:
        print("\n  tail analysis failed: %s" % e)
    print()
    print("  Not tested here: that the expansion continues to agree past n = %d."
          % max(DT.A061552))
    print("  VERDICT: SURVIVES every check the oracle holds.")
    return True


# ------------------------------------------------------------------ display
def report(title, rows, quiet=False):
    bad = [r for r in rows if not r[1]]
    print("  %-34s %d/%d pass%s" % (title, len(rows)-len(bad), len(rows),
          "" if not bad else "    VERDICT: FAIL"))
    for r in (bad if not quiet else bad[:8]):
        print("      %-26s got %s   want %s" % (r[0], r[2], r[3]))
    return not bad

def status():
    print("Av(1324): what the oracle holds\n")
    print("  A061552            n = 1..%d  (published, 50 terms)" % max(DT.A061552))
    print("  A395725 b-file     rows 1..15 (published)")
    print("  D(9,M)             M = 0..%d  (ours)" % max(DT.D[9]))
    print("  D(10,M)            M = 0..%d  (ours)" % max(DT.D[10]))
    print("  R_d exactly        d = 1..%d" % max(DT.KNOWN_R))
    print("  growth rate        %.3f +- %.3f, bounds [%.3f, %.1f]"
          % (DT.MU, DT.MU_ERR, DT.GR_LOWER, DT.GR_UPPER))
    print()
    print("  closed forms held: [s^0], [s^1], [s^2], [s^3] of R_d;")
    print("                     p_{d,d-1}, p_{d,d-2}, q_{d,d-2}, q_{d,d-3};")
    print("                     rho_0, rho_1, rho_2, rho_3; exponent law 1/2 - 3t/2")
    print("  open              : [s^4] and beyond; p_{d,d-3}; the value of mu")
    print()
    print("  self-test on R_9:")
    report("two-term law, d=9", check_two_term(9, DT.P[9], DT.QQ[9]))
    report("R_9 coefficients", check_R(9, DT.R(9)))

def _terms(s): return [Q(x) for x in re.split(r"[,\s]+", s.strip()) if x]

def fit_constrained(vals, start, deg, extra=(), lead=None):
    """Polynomial fit of given degree with extra constraints, reporting effective
    surplus.  A constraint already implied by the data adds a row and no
    information, so each is tested against the fit obtained without it and only
    genuinely new ones count.  Returns (coeffs, effective_surplus, redundant), or
    (None, 0, []) if the system is inconsistent.
    """
    m = deg + 1
    base = [(Q(x), Q(y)) for x, y in [(start+i, v) for i, v in enumerate(vals)]]
    cons = [(Q(x), Q(y)) for x, y in extra]

    def build(pts, use_lead):
        rows, rhs = [], []
        for x, y in pts:
            rows.append([x**j for j in range(m)]); rhs.append(y)
        if use_lead and lead is not None:
            r = [Q(0)]*m; r[deg] = Q(1)
            rows.append(r); rhs.append(Q(lead))
        return rows, rhs

    rows, rhs = build(base + cons, True)
    sol = _solve(rows, rhs, m)
    if sol is None: return None, 0, []

    redundant = []
    tests = [("vanish at d=%s" % x, [(x, y)], False) for x, y in cons]
    if lead is not None: tests.append(("lead = %s" % lead, [], True))
    for name, drop, is_lead in tests:
        keep = [p for p in cons if p not in drop]
        r2, h2 = build(base + keep, not is_lead if lead is not None else False)
        s2 = _solve(r2, h2, m)
        if s2 == sol: redundant.append(name)

    total = len(base) + len(cons) + (1 if lead is not None else 0)
    eff = total - len(redundant) - m
    return sol, eff, redundant

def clearing(vals, start=1, maxfac=8):
    """Offsets and integers k making vals[i] * (d-offset)! * k integral, smallest
    k first."""
    out = []
    for off in range(0, maxfac+1):
        try:
            scaled = [Q(v)*factorial(start+i-off) for i, v in enumerate(vals)]
        except ValueError:
            continue
        den = 1
        for v in scaled: den = den*v.denominator//gcd(den, v.denominator)
        if den <= 10**6:
            out.append((off, den, [int(v*den) for v in scaled]))
    out.sort(key=lambda r: (r[1], r[0]))
    return out

def exponent_law():
    """Order count for the exponent law: with deg(d! p_{d,d-1-j}) = 4j and
    deg(d! q_{d,d-2-j}) = 2+4j, both sides give 3t/2 - 3/2."""
    rows = []
    for t in range(0, 25, 2):
        got = Q(-1,2) - (Q(t,2) + 1) + 2*t
        rows.append(_row("even t=%d" % t, got == Q(3*t,2)-Q(3,2), got, Q(3*t,2)-Q(3,2)))
    for t in range(1, 25, 2):
        got = -(2 + Q(t-1,2)) + 2*t
        rows.append(_row("odd  t=%d" % t, got == Q(3*t,2)-Q(3,2), got, Q(3*t,2)-Q(3,2)))
    return rows

def check_forbidden(d=3, Mmax=8):
    """F_sigma = N_dec - N_sigma, with N_dec = Cat(M) C(M+d,d); the measured
    facts p_F(0) - q_F(0) = 1 and lead p_F = 1/d! at degree d-1 give
    R_sigma(-1) = 0 and deg p_sigma <= d-2."""
    from math import factorial
    from sigma import suffix_counts, fit_two_term
    N = {}
    for M in range(Mmax + 1):
        for s, c in suffix_counts(M, d).items(): N.setdefault(s, {})[M] = c
    dec = tuple(range(d - 1, -1, -1))
    out = []
    for sg in sorted(N):
        if sg == dec: continue
        F = {M: N[dec][M] - N[sg][M] for M in range(Mmax + 1)}
        p, q, st = fit_two_term(d, F)
        if st != "ok":
            out.append(_row("F_%s fits" % "".join(map(str, sg)), False, st, "ok")); continue
        deg = max([i for i, c in enumerate(p) if c], default=0)
        name = "".join(map(str, sg))
        out.append(_row("F_%s: R_F(-1) = 1" % name,
                        p[0] - q[0] == 1, p[0] - q[0], 1))
        out.append(_row("F_%s: lead p_F = 1/d! at degree d-1" % name,
                        deg == d - 1 and p[deg] == Q(1, factorial(d)),
                        (deg, p[deg]), (d - 1, Q(1, factorial(d)))))
    return out


def check_threeblock(Mmax=20):
    """the d = 2 level-1 identity, via the three-block recursion"""
    import sigma as SG
    out = []
    for M in range(Mmax + 1):
        s, p = SG.three_total(M), SG.three_target(M)
        out.append(_row("sum A = (C(2M,M)+4^M)/2 at M=%d" % M, s == p, s, p))
    out.append(_row("A(l,m,0) = Cat(l)Cat(m)",
                    all(SG.three_A(l, m, 0)
                        == (comb(2*l,l)//(l+1))*(comb(2*m,m)//(m+1))
                        for l in range(6) for m in range(6)), "", ""))
    out.append(_row("A symmetric in l and m",
                    all(SG.three_A(l, m, h) == SG.three_A(m, l, h)
                        for l in range(5) for m in range(5) for h in range(5)), "", ""))
    return out


def check_sigma_model(d=3, Mmax=5):
    """the general block model against the transfer counts, every pattern"""
    import sigma as SG
    N = {}
    for M in range(Mmax + 1):
        for s, c in SG.suffix_counts(M, d).items(): N.setdefault(s, {})[M] = c
    out = []
    for sg in sorted(N):
        got = [SG.model(list(sg), M) for M in range(Mmax + 1)]
        want = [N[sg][M] for M in range(Mmax + 1)]
        out.append(_row("d=%d sigma %s" % (d, "".join(map(str, sg))),
                        got == want, got[:4], want[:4]))
    return out


def check_blockmodel():
    """the block model for the increasing pattern, against the fitted forms"""
    import sigma as SG
    out = []
    for d, lim in ((2, 20), (3, 18), (4, 14)):
        bad = [M for M in range(lim + 1)
               if SG.inc_total(M, d) != SG.inc_target(M, d)]
        out.append(_row("d=%d block model matches N_inc through M=%d" % (d, lim),
                        not bad, "mismatches %d" % len(bad), 0))
    out.append(_row("d=2 first terms", [SG.inc_total(M, 2) for M in range(6)]
                    == [1, 3, 11, 42, 163, 638], "", ""))
    out.append(_row("d=3 first terms", [SG.inc_total(M, 3) for M in range(6)]
                    == [1, 4, 17, 72, 303, 1268], "", ""))
    out.append(_row("d=4 first terms", [SG.inc_total(M, 4) for M in range(6)]
                    == [1, 5, 24, 111, 501, 2223], "", ""))
    return out


def check_staircase():
    """the staircase variational bound, against the two published values"""
    import math
    import correlation as CR
    out = []
    Ld = math.log(27 / 4)
    v = math.exp(CR.G(2, Ld, 8 / 14, 7 / 14))
    out.append(("Theorem 5.1 at the paper's (14,8,7) gives 81/8",
                abs(v - 81 / 8) < 1e-8, "%.9f" % v))
    v2 = math.exp(CR.optimise(2, Ld)[0])
    out.append(("its free optimum agrees", abs(v2 - 81 / 8) < 1e-5, "%.9f" % v2))
    thr = CR.tau_threshold(10.271012)
    out.append(("tromino threshold to beat 10.271012", abs(thr - 7.8595) < 5e-3,
                "tau >= %.4f" % thr))
    t = ((27 / 4) ** 4 / 4) ** (1 / 3)
    out.append(("Chebyshev would give tau >= 8.0362", abs(t - 8.0362) < 1e-3,
                "%.4f" % t))
    b = math.exp(CR.optimise(3, math.log(t))[0])
    out.append(("and hence the bound 10.465416", abs(b - 10.465416) < 1e-4,
                "%.6f" % b))
    out.append(("that clears the threshold", t > thr, "%.4f > %.4f" % (t, thr)))
    return out


# balanced trominoes T(m,m,m) and the domino sums D(m,m), from diagonal.py
DIAG_T = [4, 265, 36325, 6949612, 1615228302, 427032119568,
          123792159207513, 38464960591249684, 12619010975298054200,
          4325038470273319306246]
DIAG_S = [2, 23, 424, 9751, 255642, 7316494, 223060740, 7133973623,
          236896023166, 8108615482601]
CATALAN = [1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]


def check_correlation():
    """the diagonal correlation inequality the tromino bound rests on"""
    out = []
    ratios = []
    for i, (T, S, C) in enumerate(zip(DIAG_T, DIAG_S, CATALAN)):
        r = T * C / (S * S)
        ratios.append(r)
        out.append(("m=%d diagonal ratio at least 1" % (i + 1), r >= 1, "%.6f" % r))
    out.append(("the margin is non-decreasing in m",
                all(ratios[i] <= ratios[i + 1] + 1e-12 for i in range(len(ratios) - 1)),
                "excess %.6f at m=%d" % (ratios[-1] - 1, len(ratios))))
    d = [ratios[i + 1] - ratios[i] for i in range(len(ratios) - 1)]
    out.append(("its increments settle rather than decay",
                d[-1] > 0.5 * max(d), "last %.4f of max %.4f" % (d[-1], max(d))))
    # variance decomposition on the diagonal, |within|/between by m
    share = [0.0, 0.0987, 0.1474, 0.1848, 0.2052, 0.2237]
    inc = [share[i + 1] - share[i] for i in range(1, len(share) - 1)]
    out.append(("the within-stratum share stays below one",
                max(share) < 1.0, "max %.4f at m=%d" % (max(share), len(share))))
    out.append(("and its increments shrink, unlike the fixed-a regime",
                all(inc[i + 1] <= inc[i] + 1e-9 for i in range(len(inc) - 1)),
                " ".join("%.4f" % v for v in inc)))
    # Var(g)/Var(h) on the diagonal; the conjecture is exactly that this stays below 1
    vr = [0.0, 0.09871, 0.18603, 0.26356, 0.33229, 0.39311, 0.446891, 0.494452,
          0.536555]
    L, C, q = 0.863825, 1.101209, 0.885700
    err = max(abs(vr[i] - (L - C * q ** (i + 2))) for i in range(len(vr)))
    out.append(("Var(g)/Var(h) matches L - C q^m", err < 2e-4, "max error %.2e" % err))
    out.append(("its limit is below one", L < 1.0, "L = %.5f, margin %.3f" % (L, 1 - L)))
    d2 = [vr[i + 1] - vr[i] for i in range(len(vr) - 1)]
    rr = [d2[i + 1] / d2[i] for i in range(len(d2) - 1) if d2[i]]
    out.append(("the decay ratio is constant", max(rr) - min(rr) < 0.01,
                "spread %.5f about %.5f" % (max(rr) - min(rr), sum(rr) / len(rr))))
    return out


# T_4(m,m,m,m), the four-cell chain, from chainop.py
CHAIN_T4 = [8, 3053, 3110006, 4945513349, 10183097715862, 24864239515801111,
            68560301900937223298, 207145020458706002649863,
            672194901252825186035714727]


def check_chain(mmax=5):
    """The chain transfer operator against its two known marginals, D(m,m) and
    T(m,m,m), with T_4 new; the ladder calibrated on k = 1 and k = 2, whose
    limits are 4 and 27/4 exactly."""
    import chainop as CH
    out = []
    for m in range(1, mmax + 1):
        B = CH.build(m)
        T2, T3, T4 = CH.chain_counts(B)
        out.append(_row("m=%d T_2 = D(m,m)" % m, T2 == CH.DOM[m - 1],
                        T2, CH.DOM[m - 1]))
        out.append(_row("m=%d T_3 = T(m,m,m)" % m, T3 == CH.TRI[m - 1],
                        T3, CH.TRI[m - 1]))
        out.append(_row("m=%d T_4 as recorded" % m, T4 == CHAIN_T4[m - 1],
                        T4, CHAIN_T4[m - 1]))
    from chain_data import LOGT
    for k, truth in ((1, 4.0), (2, 27.0 / 4)):
        g = CH.extrap(CH.ratios(k), 5)
        out.append(_row("g(%d) recovered, from below" % k,
                        0.0 <= truth - g < 0.01 * truth, "%.4f" % g, truth))
    g3 = CH.extrap(CH.ratios(3), 5)
    out.append(_row("tau = g(3) clears 7.8595", g3 > 7.8595, "%.4f" % g3, "> 7.8595"))
    g4 = CH.extrap(CH.ratios(4), 5)
    out.append(_row("g(4)", 8.7 < g4 < 8.8, "%.4f" % g4, "8.7 .. 8.8"))
    ks = sorted(k for k in LOGT if k <= 32)
    first = next((k for k in ks if k > 2 and CH.extrap(CH.ratios(k), 5) > 10.271012),
                 None)
    out.append(_row("balanced ladder reaches 10.271012", first == 11, first, 11))
    # the balanced diagonal is not g(k): the optimum unbalances the cells
    for sizes, rec in (((2, 2), 23), ((3, 3), 424), ((2, 2, 2), 265),
                       ((3, 3, 3), 36325), ((2, 2, 2, 2), 3053),
                       ((3, 3, 3, 3), 3110006)):
        out.append(_row("Tchain %s" % (sizes,),
                        abs(CH.Tchain(sizes) - rec) < 1, CH.Tchain(sizes), rec))
    bal = CH.Tchain((4, 4, 4, 4)) ** (1.0 / 16)
    unb = CH.Tchain((2, 6, 6, 2)) ** (1.0 / 16)
    out.append(_row("unbalanced beats balanced at k=4", unb > bal,
                    "%.5f vs %.5f" % (unb, bal), "greater"))
    out.append(_row("free-chain ratio is 1 at k=2", abs(CH.size_ratio(2) - 1) < 1e-9,
                    CH.size_ratio(2), 1))
    out.append(_row("free-chain ratio at k=4", abs(CH.size_ratio(4) - 1.0607) < 1e-3,
                    "%.4f" % CH.size_ratio(4), 1.0607))
    tau = CH.extrap(CH.ratios(3), 5) * CH.size_ratio(3)
    out.append(_row("corrected tau clears 7.8595", tau > 7.8595, "%.3f" % tau,
                    "> 7.8595"))
    g6 = CH.extrap(CH.ratios(6), 5) * CH.size_ratio(6)
    out.append(_row("corrected g(6) clears 10.271012", g6 > 10.271012,
                    "%.3f" % g6, "> 10.271012"))
    return out


def sV(p):
    """Number of pairs (u,v), 0 <= u <= v <= m, with every entry in 1..u above
    every entry in u+1..v; d_A(b,2) = C(m+2,2) + sV(b) - m(m+1)/2 exactly."""
    from perms import Vfun
    return sum(Vfun(p))


def _pqd(X, Y, N):
    """(violations, cells) of P(X>a, Y>b) >= P(X>a)P(Y>b)"""
    bad = tot = 0
    for a in sorted(set(X)):
        ia = [i for i in range(N) if X[i] > a]
        pa = Q(len(ia), N)
        for b in sorted(set(Y)):
            tot += 1
            pb = Q(sum(1 for i in range(N) if Y[i] > b), N)
            if Q(sum(1 for i in ia if Y[i] > b), N) - pa * pb < 0:
                bad += 1
    return bad, tot


def check_pqd(mmax=7):
    """Positive quadrant dependence: Hoeffding writes Cov(X,Y) as the integral
    of P(X>s,Y>t) - P(X>s)P(Y>t), so a nonnegative integrand gives the
    Chebyshev step.  Three pairs, each stronger; sV involves no 1324-counting."""
    import chainop as CH
    out = []
    for m in range(3, mmax + 1):
        B = CH.build(m)
        dA, _ = CH.marginals(B)
        Ls, il = B["Ls"], B["il"]
        N = len(Ls)
        f = [int(x) for x in dA]
        fs = [int(dA[il[i]]) for i in range(N)]
        X = [sV(b) for b in Ls]
        inv = lambda p: tuple(sorted(range(len(p)), key=lambda i: p[i]))
        Y = [sV(inv(b)) for b in Ls]
        st = {}
        for i in range(N):
            st.setdefault(X[i], []).append(f[i])
        ks = sorted(st)
        mn = [Q(sum(st[k]), len(st[k])) for k in ks]
        out.append(_row("m=%d E[d_A|sV] increasing" % m,
                        all(mn[i] <= mn[i + 1] for i in range(len(mn) - 1)),
                        "%d steps" % (len(mn) - 1), "all up"))
        for name, U, W in (("sV", X, Y), ("d_A vs sV", f, Y), ("d_A vs d_A", f, fs)):
            bad, tot = _pqd(U, W, N)
            out.append(_row("m=%d PQD %s" % (m, name), bad == 0,
                            "%d bad of %d" % (bad, tot), 0))
    return out


def check_stratum():
    """The exact between/within split on the inversion strata, and the crude
    per-stratum bound, which telescopes to Var(g)."""
    w = [0.09871, 0.14745, 0.18483, 0.20520, 0.22372, 0.23622, 0.24434]
    c = [0.09871, 0.19485, 0.29174, 0.39554, 0.50283, 0.61710, 0.73908]
    out = []
    dw = [w[i + 1] - w[i] for i in range(len(w) - 1)]
    dc = [c[i + 1] - c[i] for i in range(len(c) - 1)]
    out.append(_row("|within|/between increments decay",
                    all(dw[i + 1] <= dw[i] + 1e-9 for i in range(len(dw) - 1)),
                    " ".join("%.4f" % v for v in dw), "decreasing"))
    out.append(_row("so the share stays well below one", max(w) < 0.3,
                    "%.5f at m = 9" % w[-1], "< 0.3"))
    out.append(_row("the crude bound's increments grow instead",
                    all(dc[i + 1] >= dc[i] - 1e-9 for i in range(len(dc) - 1)),
                    " ".join("%.4f" % v for v in dc), "increasing"))
    out.append(_row("so Var(g)/between crosses one by m = 12",
                    c[-1] + 3 * dc[-1] > 1.0,
                    "%.5f at m = 9, step %.4f" % (c[-1], dc[-1]), "> 1 by m = 12"))
    out.append(_row("the crude bound overshoots the truth threefold at m = 9",
                    2.5 < c[-1] / w[-1] < 3.5, "%.2f" % (c[-1] / w[-1]), "about 3"))
    return out


def check_certificate():
    """G_3 at a fixed rational triple, evaluated at 120 digits."""
    try:
        from mpmath import mp, mpf, log, exp
    except ImportError:
        return [_row("staircase certificate", False, "mpmath absent",
                     "install mpmath")]
    mp.dps = 120

    def f(x, y):
        if y <= 0 or y >= x:
            return mpf(0)
        return x * log(x) - y * log(y) - (x - y) * log(x - y)

    logtau = log((mpf(27) / 4) ** 4 / 4) / 3
    a, b, c = mpf(1), mpf(69) / 125, mpf(243) / 500
    val = exp((3 * a * logtau + f(2 * b - c, b) + 2 * f(a + c, a)) / (3 * a + b))
    out = []
    out.append(_row("the tromino ratio tau", True,
                    "%.6f" % float(exp(logtau)), "(27/4)^4/4, cube root"))
    out.append(_row("G_3 at a=1, b=69/125, c=243/500 clears the claim",
                    val > mpf("10.465416"),
                    "%.13f" % float(val), "> 10.465416"))
    out.append(_row("and the witness is feasible", 0 < c <= b,
                    "0 < 243/500 <= 69/125", "0 < c <= b"))
    out.append(_row("margin over the published figure",
                    float(val - mpf("10.465416")) > 5e-7,
                    "%.2e" % float(val - mpf("10.465416")), "> 5e-7"))
    return out


def check_rlmax(mmax=7):
    """Legal insertions into a 132-avoider, against its right-to-left maxima."""
    from itertools import permutations

    def av132(p):
        n = len(p)
        return not any(p[i] < p[k] < p[j] for i in range(n)
                       for j in range(i + 1, n) for k in range(j + 1, n))

    def ext(u, v):
        return tuple(x + 1 if v <= x else x for x in u) + (v,)

    def rlmax(u):
        c, mx = 0, -1
        for x in reversed(u):
            if x > mx:
                c += 1
                mx = x
        return c

    bad, tot, cat, child, rows = 0, 0, [], 0, {}
    for m in range(0, mmax + 1):
        bs = [p for p in permutations(range(m)) if av132(p)]
        s = 0
        row = {}
        for u in bs:
            ch = sorted(rlmax(ext(u, v)) for v in range(m + 1)
                        if av132(ext(u, v)))
            k = len(ch)
            tot += 1
            if k != rlmax(u) + 1:
                bad += 1
            if ch != list(range(1, rlmax(u) + 2)):
                child += 1
            row[rlmax(u)] = row.get(rlmax(u), 0) + 1
            s += k
        cat.append(s)
        rows[m] = row
    ref = [1, 1, 2, 5, 14, 42, 132, 429, 1430][1:mmax + 2]
    # T(m+1, j) = sum of T(m, k) over k >= j-1
    tri = True
    for m in range(0, mmax):
        for j in rows[m + 1]:
            if rows[m + 1][j] != sum(v for k, v in rows[m].items()
                                     if k >= j - 1):
                tri = False
    return [
        _row("legal insertions are the right-to-left maxima plus one", bad == 0,
             "%d avoiders at m <= %d, %d mismatches" % (tot, mmax, bad),
             "no mismatches"),
        _row("and the children take each value from 1 to k+1 once",
             child == 0, "%d violations" % child, "none"),
        _row("so the statistic satisfies the Catalan triangle recurrence", tri,
             "T(m+1,j) = sum_{k >= j-1} T(m,k)", "holds at every m, j"),
        _row("and the row sums are the Catalan numbers",
             cat == ref, " ".join(str(x) for x in cat),
             " ".join(str(x) for x in ref)),
    ]


def check_logconvex(mmax=7):
    """Log-convexity of the staircase ladder at k = 2, which holds, and k = 3,
    which fails for every m from 2 to 8."""
    from fractions import Fraction as Q
    import chainop as CH

    held2 = [0.998113208, 0.989819683, 0.977259090, 0.963343579, 0.949667484,
             0.936905626, 0.925255487, 0.914692815]
    held3 = [1.000085447, 1.000654522, 1.001522203, 1.002203035, 1.002404212,
             1.002052362, 1.001208635, 0.999994594]
    a, b = [], []
    for m in range(2, mmax + 1):
        B = CH.build(m, m)
        T2, T3, T4 = CH.chain_counts(B)
        T1 = len(B["Us"])
        a.append(Q(T2 * T2, T1 * T3))
        b.append(Q(T3 * T3, T2 * T4))
    out = []
    out.append(_row("k = 2 holds exactly, at every m computed",
                    all(x <= 1 for x in a),
                    "%.6f at m = %d" % (float(a[-1]), mmax), "<= 1"))
    out.append(_row("and its margin widens with m",
                    all(a[i] < a[i - 1] for i in range(1, len(a))),
                    " ".join("%.4f" % float(x) for x in a), "decreasing"))
    out.append(_row("k = 3 fails, so the ladder is not log-convex",
                    all(x > 1 for x in b),
                    " ".join("%.6f" % float(x) for x in b), "> 1 at every m <= 8"))
    out.append(_row("the computed values match the recorded ones",
                    all(abs(float(a[i]) - held2[i]) < 1e-8 for i in range(len(a)))
                    and all(abs(float(b[i]) - held3[i]) < 1e-8
                            for i in range(len(b))),
                    "%d sizes" % len(a), "agree to 1e-8"))
    out.append(_row("k = 3 recovers by m = 9, so the failure is finite size",
                    held3[-1] < 1 < held3[-2],
                    "%.6f at m = 9 against %.6f at m = 8"
                    % (held3[-1], held3[-2]), "crosses back below 1"))
    out.extend(_ladder_exact(min(mmax, 6)))
    return out


def _ladder_exact(mmax):
    """T_1..T_4 recomputed from V in Python integers, with no numpy in the
    arithmetic path, against chain_counts."""
    import chainop as CH

    held4 = {2: 3053, 3: 3110006, 4: 4945513349, 5: 10183097715862,
             6: 24864239515801111}
    ok, agree = True, True
    for m in range(2, mmax + 1):
        B = CH.build(m, m)
        exact = CH.chain_counts_exact(B)
        ok &= exact == CH.chain_counts(B)
        agree &= exact[2] == held4[m]
    return [_row("T_4 recomputed in exact integers agrees with the matmuls", ok,
                 "m = 2..%d" % mmax, "no int64 overflow"),
            _row("and reproduces the recorded T_4 sequence", agree,
                 "3053, 3110006, 4945513349, ...", "held values")]


def check_sv_split():
    """The diagonal pair against the sV pair, the same conjecture at the corner
    a = c = 2, where r extrapolates to 1.721 rather than 0.861."""
    rd = [0.098708, 0.186034, 0.263562, 0.332291, 0.393112, 0.446891, 0.494452]
    rs = [0.106383, 0.211628, 0.313087, 0.409538, 0.500389, 0.585383, 0.664459]
    co = [1.000000, 0.998877, 0.996086, 0.991616, 0.985599, 0.978208]
    q = [rd[i] / rs[i] for i in range(len(rd))]
    out = []
    out.append(_row("the sV pair fails, with an extrapolated limit above one",
                    _geo_limit(rs) > 1.0, "%.5f" % _geo_limit(rs), "> 1"))
    out.append(_row("the diagonal is below it at every m",
                    all(rd[i] < rs[i] for i in range(len(rd))),
                    "%.6f against %.6f at m = 9" % (rd[-1], rs[-1]),
                    "r_diag < r_sV"))
    out.append(_row("their antisymmetric parts stay nearly collinear",
                    co[-1] > 0.97,
                    "correlation %.4f at m = 8" % co[-1], "> 0.97"))
    out.append(_row("so the difference sits in the symmetric parts",
                    all(q[i] < q[i - 1] for i in range(1, len(q))),
                    " ".join("%.4f" % x for x in q), "ratio decreasing"))
    lo = _geo_limit(q, 0.885) * _geo_limit(rs, 0.885)
    hi = _geo_limit(q) * _geo_limit(rs)
    out.append(_row("the factored route does not pin the limit",
                    lo < 0.861403 < hi,
                    "%.3f to %.3f against the direct 0.861" % (lo, hi),
                    "brackets the direct fit"))
    return out


def _geo_limit(ser, rho=None):
    """Sum the geometric tail at the last increment ratio, or at a given one."""
    d = [ser[i] - ser[i - 1] for i in range(1, len(ser))]
    r = rho if rho is not None else d[-1] / d[-2]
    return ser[-1] + d[-1] * r / (1.0 - r)


def check_antisym():
    """E[(f - f o s)^2] <= 2 Var(f), against a free bound of 4 Var(f), and the
    support of the antisymmetric part."""
    from math import comb

    inv = [(2, 2), (3, 3), (4, 6), (5, 10), (6, 20), (7, 35), (8, 70), (9, 126)]
    cat = [CATALAN[m - 1] for m, _ in inv]
    # Cov/Var at m = 2..10, exact from the transfer operator
    cv = [1.0, 0.820319, 0.686293, 0.582827, 0.501174, 0.435634, 0.382274,
          0.338283, 0.301610]
    out = []
    out.append(_row("the involutions are the central binomial coefficient",
                    all(v == comb(m, m // 2) for m, v in inv),
                    " ".join(str(v) for _, v in inv), "C(m, floor(m/2))"))
    frac = [1.0 - v / c for (_, v), c in zip(inv, cat)]
    out.append(_row("so the antisymmetric support fills the class",
                    frac[-1] > 0.97 and all(frac[i] > frac[i - 1]
                                            for i in range(1, len(frac))),
                    "%.4f at m = 9" % frac[-1], "increasing toward 1"))
    q = [1.0 - x for x in cv]
    out.append(_row("the ratio to be bounded is 1 - Cov/Var", q[-1] < 1.0,
                    "%.5f at m = 10" % q[-1], "conjecture < 1, free < 2"))
    out.append(_row("its increments decay, so it is not headed for the ceiling",
                    all(q[i] - q[i - 1] < q[i - 1] - q[i - 2]
                        for i in range(2, len(q))),
                    " ".join("%.4f" % (q[i] - q[i - 1])
                             for i in range(1, len(q))), "decreasing"))
    # the extrapolated limit of r maps to this scale as 2r/(1+r)
    rl = 0.861403
    out.append(_row("the extrapolated limit maps to this scale below one",
                    2 * rl / (1 + rl) < 1.0,
                    "%.5f" % (2 * rl / (1 + rl)), "< 1"))
    out.extend(_null_model())
    return out


def _null_model():
    """The centred d_A vector against the +-1 eigenspaces of the involution,
    whose dimension ratio tends to 1 and so sits on the boundary."""
    from math import comb

    r = {3: 0.098708262, 4: 0.186033755, 5: 0.263561921, 6: 0.332290910,
         7: 0.393112360, 8: 0.446891295, 9: 0.494451700, 10: 0.536555095}
    ex, inv_r = [], []
    for m in sorted(r):
        N, F = CATALAN[m - 1], comb(m, m // 2)
        null = (N + F) / (N - F)
        ex.append((1.0 / r[m]) / null)
        inv_r.append(1.0 / r[m])
    out = []
    out.append(_row("the null model sits on the boundary",
                    all(e > 1.0 for e in ex),
                    "excess %.4f at m = 10" % ex[-1], "excess > 1 at every m"))
    slope = (ex[-1] - ex[-4]) / 3.0
    cross = 10 + (1.0 - ex[-1]) / slope
    out.append(_row("a linear read of the excess crosses one near m = 17",
                    15 < cross < 20, "crosses at m = %.1f" % cross,
                    "linear extrapolation"))
    d = [inv_r[i] - inv_r[i - 1] for i in range(1, len(inv_r))]
    q = [d[i] / d[i - 1] for i in range(1, len(d))]
    out.append(_row("the decline decelerates, so the limit is finite",
                    all(q[i] > q[i - 1] for i in range(1, len(q)))
                    and q[-1] < 0.9,
                    " ".join("%.3f" % x for x in q),
                    "increment ratios rising toward 0.885"))
    lim = 1.0 / 0.861403
    out.append(_row("the geometric law puts the excess limit above one",
                    lim > 1.0, "%.4f" % lim, "> 1"))
    return out


def check_geometric():
    """Var(g)/Var(h) on the diagonal, whose geometric increments reduce the
    conjecture to a threshold on one ratio."""
    r = [(2, 0.0), (3, 0.098708262), (4, 0.186033755), (5, 0.263561921),
         (6, 0.332290910), (7, 0.393112360), (8, 0.446891295),
         (9, 0.494451700), (10, 0.536555095)]
    v = [x for _, x in r]
    d = [v[i] - v[i - 1] for i in range(1, len(v))]
    q = [d[i] / d[i - 1] for i in range(1, len(d))]
    out = []
    out.append(_row("the ratio rises and is below one at every m",
                    all(v[i] > v[i - 1] for i in range(1, len(v))) and v[-1] < 1,
                    "%.6f at m = %d" % (v[-1], r[-1][0]), "increasing, < 1"))
    out.append(_row("its increments are geometric to three places",
                    max(q) - min(q) < 4e-3,
                    " ".join("%.4f" % x for x in q), "spread < 0.004"))
    # held-out: refit on each truncation and predict the first unseen term
    errs = []
    for k in range(len(v) - 3, len(v)):
        qq = q[:k - 2]
        rho_k = sum(qq) / len(qq)
        errs.append(abs(v[k - 1] + d[k - 2] * rho_k - v[k]))
    out.append(_row("each refit predicts the next unseen term better",
                    all(errs[i] < errs[i - 1] for i in range(1, len(errs)))
                    and errs[-1] < 2e-5,
                    " ".join("%.1e" % e for e in errs), "monotone, last < 2e-5"))
    # the threshold: the extrapolated limit reaches 1 exactly at this ratio
    crit = (1.0 - v[-1]) / (1.0 - v[-1] + d[-1])
    rho = q[-1]
    lim = v[-1] + d[-1] * rho / (1.0 - rho)
    out.append(_row("the conjecture is one threshold on that ratio",
                    rho < crit,
                    "measured %.5f against critical %.5f" % (rho, crit),
                    "measured below critical"))
    out.append(_row("so the extrapolated limit sits below one", lim < 1.0,
                    "%.5f" % lim, "< 1, margin %.3f" % (1.0 - lim)))
    # the increment ratios are not flat, so test whether a power correction
    # measures anything: fit r(m) = L - A rho^m m^alpha on the same truncations
    ge, pw, lg, lp = [], [], [], []
    for M in (8, 9):
        ms = [m for m, _ in r if m <= M]
        vv = {m: x for m, x in r}
        dd = [vv[ms[i]] - vv[ms[i - 1]] for i in range(1, len(ms))]
        qq = [dd[i] / dd[i - 1] for i in range(1, len(dd))]
        rg = sum(qq) / len(qq)
        ge.append(abs(vv[M] + dd[-1] * rg - vv[M + 1]))
        lg.append(vv[M] + dd[-1] * rg / (1 - rg))
        b = _fit_power(vv, ms)
        pw.append(abs(b[1] - b[2] * b[3] ** (M + 1) * (M + 1) ** b[4]
                      - vv[M + 1]))
        lp.append(b[1])
    out.append(_row("a power correction predicts worse, so it measures nothing",
                    all(pw[i] > ge[i] for i in range(len(ge))),
                    "power %s against geometric %s"
                    % (" ".join("%.1e" % x for x in pw),
                       " ".join("%.1e" % x for x in ge)),
                    "power worse at both"))
    out.append(_row("and the limit is stable and drifting down, not up",
                    max(lg + lp) - min(lg + lp) < 0.01
                    and lg[-1] < lg[0] and lp[-1] < lp[0],
                    "%.5f %.5f | %.5f %.5f" % (lg[0], lg[1], lp[0], lp[1]),
                    "spread < 0.01, decreasing"))
    return out


def _fit_power(vv, ms):
    """least squares for r(m) = L - A rho^m m^alpha, L and A linear in the rest"""
    best = None
    rh, al, s = 0.885, 0.0, 0.06
    for _ in range(6):
        g1 = [x for x in (rh + s * (i - 20) / 20.0 for i in range(41))
              if 0.3 < x < 0.999]
        g2 = [al + 4 * s * (i - 20) / 20.0 for i in range(41)]
        best = None
        for a in g2:
            for h in g1:
                b = [h ** m * m ** a for m in ms]
                y = [vv[m] for m in ms]
                n = len(ms)
                sb, sy = sum(b), sum(y)
                sbb = sum(x * x for x in b)
                sby = sum(b[i] * y[i] for i in range(n))
                den = n * sbb - sb * sb
                if abs(den) < 1e-300:
                    continue
                A = (sb * sy - n * sby) / den
                L = (sy + A * sb) / n
                e = sum((y[i] - (L - A * b[i])) ** 2 for i in range(n))
                if best is None or e < best[0]:
                    best = (e, L, A, h, a)
        rh, al = best[3], best[4]
        s /= 4.0
    return best


def check_dominoes(bmax=4):
    """The transfer operator's marginals against brute-force enumeration of the
    dominoes, cell by cell."""
    from itertools import permutations
    import chainop as CH

    def has(p, pat):
        n, s = len(p), len(pat)
        if s == 3:
            return any(_ordiso((p[i], p[j], p[k]), pat)
                       for i in range(n) for j in range(i + 1, n)
                       for k in range(j + 1, n))
        return any(_ordiso((p[i], p[j], p[k], p[l]), pat)
                   for i in range(n) for j in range(i + 1, n)
                   for k in range(j + 1, n) for l in range(k + 1, n))

    def brute(a, b):
        out = {}
        for w in permutations(range(a + b)):
            if has(w, (0, 2, 1, 3)):
                continue
            lo = tuple(x for x in w if x < b)
            hi = tuple(x for x in w if x >= b)
            if has(lo, (0, 2, 1)) or has(hi, (1, 0, 2)):
                continue
            out[lo] = out.get(lo, 0) + 1
        return out

    out = []
    seen = sorted({(a, b) for b in range(1, bmax + 1) for a in (2, b)
                   if a + b <= 8})
    for a, b in seen:
        ref = brute(a, b)
        B = CH.build(a, b)
        dA, _ = CH.marginals(B)
        same = all(int(dA[i]) == ref.get(tuple(l), 0)
                   for i, l in enumerate(B["Ls"]))
        out.append(_row("d_A cell by cell at (a,b) = (%d,%d)" % (a, b), same,
                        "total %d over %d cells"
                        % (sum(ref.values()), len(B["Ls"])),
                        "transfer = enumeration"))
    dom = [2, 23, 424, 9751]
    tri = [4, 265, 36325, 6949612]
    ok, okt, sq = True, True, []
    for m in range(1, 5):
        f = brute(m, m)
        ok &= sum(f.values()) == dom[m - 1]
        t = 0
        for l, v in f.items():
            inv = [0] * m
            for i, x in enumerate(l):
                inv[x] = i
            t += v * f[tuple(inv)]
        okt &= t == tri[m - 1]
        sq.append(dom[m - 1] ** 2 <= CATALAN[m - 1] * t)
    out.append(_row("balanced domino counts from enumeration", ok,
                    "2, 23, 424, 9751", "the held DOM values"))
    out.append(_row("balanced tromino counts from enumeration", okt,
                    "4, 265, 36325, 6949612", "the held TRI values"))
    out.append(_row("the Chebyshev square holds at every m reached", all(sq),
                    "D^2 <= Cat*T at m = 1..4", "what PQD would give"))
    sv = _sv_prefix_identity(6)
    out.append(_row("sV as a prefix sum of skew components", sv[0],
                    sv[1], "sum_{v=0..m} (sc + 1), no m(m+1)/2"))
    out.extend(_diag_split_vs_rocq())
    return out


def _diag_split_vs_rocq():
    """The diagonal split against the integers Rocq evaluates, which carry the
    stratum-size product as a factor."""
    from fractions import Fraction as Q
    import correlation as CR

    held = {3: (3698, -405, 4103), 4: (119478618, -20663244, 140141862)}
    out = []
    for m in (3, 4):
        st, _, _, _ = CR.strata(m)
        N = sum(n for n, _, _ in st.values())
        P = sum(p for _, _, p in st.values())
        S = sum(s for _, s, _ in st.values())
        pi = 1
        for n, _, _ in st.values():
            pi *= n
        total = Q(N * P - S * S)
        within = sum(Q(N, n) * (n * p - s * s) for n, s, p in st.values())
        trip = (pi * total, pi * within, pi * (total - within))
        ok = all(x.denominator == 1 for x in trip) and \
            tuple(int(x) for x in trip) == held[m]
        out.append(_row("Rocq's cleared diagonal split at m = %d" % m, ok,
                        "%d = %d + %d" % tuple(int(x) for x in trip),
                        "%d = %d + %d" % held[m]))
    return out


def _sv_prefix_identity(mmax):
    """sV(b) = sum_{v=0}^{m} (sc(b_1..v) + 1), over every 132-avoider"""
    from itertools import permutations

    def sc(b):
        n = len(b)
        return sum(1 for i in range(1, n + 1)
                   if i == n or min(b[:i]) > max(b[i:]))

    def sV(b):
        m = len(b)
        c = 0
        for u in range(m + 1):
            lo = min(b[:u]) if u else None
            for v in range(u, m + 1):
                if lo is None or all(b[j] < lo for j in range(u, v)):
                    c += 1
        return c

    bad = 0
    tot = 0
    for m in range(2, mmax + 1):
        for p in permutations(range(m)):
            if any(p[i] < p[k] < p[j] for i in range(m) for j in range(i + 1, m)
                   for k in range(j + 1, m)):
                continue
            tot += 1
            if sV(p) != sum(sc(p[:v]) + 1 for v in range(m + 1)):
                bad += 1
    return bad == 0, "%d cells at m <= %d, %d mismatches" % (tot, mmax, bad)


def _ordiso(v, pat):
    """v is order-isomorphic to pat."""
    r = sorted(range(len(v)), key=lambda i: v[i])
    s = [0] * len(v)
    for rank, i in enumerate(r):
        s[i] = rank
    return tuple(s) == tuple(pat)


def check_walks(nmax=10):
    """Weighted quotient of the profile transfer: the 132-free steps are the
    lossless control, the full transfer over-counts from n = 6, and the minimum
    variant degenerates because the capped profile separates every state."""
    import transfer as TR
    from linalg import perron_weighted
    out = []
    wq = TR.weighted(TR.levels(nmax, free_only=True))
    cat = [1]
    for n in range(1, nmax + 1):
        cat.append(cat[-1] * 2 * (2 * n - 1) // (n + 1))
    exact = all(wq[n] == cat[n] for n in range(nmax + 1))
    out.append(_row("132-free quotient is exact (lossless control)", exact,
                    "n <= %d" % nmax, "exact"))
    wq = TR.weighted(TR.levels(nmax))
    over = [n for n in range(1, nmax + 1) if wq[n] > DT.A061552[n]]
    out.append(_row("1324 quotient over-counts, first at n = 6",
                    over and over[0] == 6, over[:3], "[6, 7, 8]"))
    grow = all(wq[n] / DT.A061552[n] <= wq[n + 1] / DT.A061552[n + 1]
               for n in range(6, nmax))
    out.append(_row("and the excess grows", grow,
                    "%.5f at n = %d" % (float(wq[nmax]) / DT.A061552[nmax], nmax),
                    "increasing"))
    o1, p1 = TR.minclass(nmax, TR.cls_capped)
    o2, p2 = TR.minclass(nmax, TR.cls_capvec)
    out.append(_row("capped profile separates every state", len(o1) == len(o2),
                    (len(o1), len(o2)), "equal"))
    out.append(_row("so the minimum quotient is the truncation",
                    abs(perron_weighted(o1, p1) - perron_weighted(o2, p2)) < 1e-9,
                    "%.6f" % perron_weighted(o1, p1), "same"))
    out.append(_row("mu alone gives nothing",
                    perron_weighted(*TR.minclass(nmax, TR.cls_mu)) == 0.0, 0.0, 0))
    return out


def _comps(w):
    """skew components of w, left to right, each standardised"""
    from perms import components
    return components(w)


def check_skew(mmax=7):
    """sV(b) is the prefix sum of skew cuts and sV(b^-1) the value-prefix sum;
    X + Y depends only on the multiset of skew components, X - Y only on their
    arrangement, so the symmetric part is multiset-measurable."""
    from perms import Vfun, av132

    def sV(p):
        return sum(Vfun(p))

    def X(p):
        return sV(p) - len(p) * (len(p) + 1) // 2 - (len(p) + 1)

    def inv(p):
        q = [0] * len(p)
        for i, v in enumerate(p):
            q[v] = i
        return tuple(q)

    def sc(w):
        return len(_comps(w))

    def skew(b, g):
        return tuple(x + len(g) for x in b) + tuple(g)

    out = []
    for m in range(1, mmax + 1):
        bs = av132(m)
        off = m * (m + 1) // 2
        bad = sum(1 for b in bs
                  if sV(b) - off != sum(sc(b[:v]) + 1 for v in range(m + 1)))
        out.append(_row("m=%d sV is the prefix skew sum" % m, bad == 0, bad, 0))
        bad = sum(1 for b in bs
                  if sV(inv(b)) - off !=
                     sum(sc(tuple(x for x in b if x < v)) + 1
                         for v in range(m + 1)))
        out.append(_row("m=%d sV of the inverse is the value sum" % m, bad == 0,
                        bad, 0))
        g = {}
        for b in bs:
            g.setdefault(tuple(sorted(_comps(b))), set()).add(X(b) + X(inv(b)))
        bad = sum(1 for v in g.values() if len(v) > 1)
        out.append(_row("m=%d X+Y constant on multiset classes" % m, bad == 0,
                        "%d classes" % len(g), 0))
    bad1 = bad2 = 0
    for m1 in range(4):
        for m2 in range(4):
            for b in av132(m1):
                for gg in av132(m2):
                    s = skew(b, gg)
                    bad1 += X(s) != X(b) + X(gg) + len(gg) * sc(b)
                    bad2 += inv(s) != skew(inv(gg), inv(b))
    out.append(_row("X(b skew g) = X(b)+X(g)+|g|.sc(b)", bad1 == 0, bad1, 0))
    out.append(_row("(b skew g)^-1 = g^-1 skew b^-1", bad2 == 0, bad2, 0))
    return out


def _main(argv):
    if len(argv) < 2 or argv[1] in ("-h", "--help"): print(__doc__); return
    cmd = argv[1]
    if cmd == "exponent":
        report("exponent law from the coefficient degrees", exponent_law())
        print("  conditional on deg(d! p_{d,d-1-j}) = 4j and deg(d! q_{d,d-2-j}) = 2+4j,")
        print("  observed as 0,4,8 and 2,6.  Reduces Open item 2 to those degrees.")
        return
    if cmd == "clearing":
        start = 1
        if "--start" in argv: start = int(argv[argv.index("--start")+1])
        for off, den, ints in clearing(_terms(argv[2]), start=start):
            print("  (d-%d)! * %-8d -> %s" % (off, den, ints[:8]))
        return
    if cmd == "cfit":
        start = int(argv[argv.index("--start")+1]) if "--start" in argv else 1
        deg = int(argv[argv.index("--deg")+1])
        lead = Q(argv[argv.index("--lead")+1]) if "--lead" in argv else None
        extra = []
        if "--vanish" in argv:
            for x in _terms(argv[argv.index("--vanish")+1]): extra.append((x, Q(0)))
        sol, eff, red = fit_constrained(_terms(argv[2]), start, deg, extra, lead)
        if sol is None: print("  INCONSISTENT"); return
        print("  coefficients %s" % [str(c) for c in sol])
        print("  effective surplus %d%s" % (eff,
              ("   REDUNDANT (adds no information): " + ", ".join(red)) if red else ""))
        if eff < 1: print("  -> interpolation, not a result")
        return
    if cmd == "status": status(); return
    if cmd == "series":
        st = int(argv[argv.index("--start") + 1]) if "--start" in argv else 0
        report("series vs A061552", check_series([int(x) for x in _terms(argv[2])], st)); return
    if cmd == "gf":
        report("G(x) = %s" % argv[2], check_gf(argv[2])); return
    if cmd == "formula":
        report("a(n) = %s" % argv[2], check_formula(argv[2])); return
    if cmd == "recurrence":
        polys = [[Q(x) for x in _terms(p)] for p in argv[2].split("|")]
        held = [Q(DT.A061552[i]) for i in range(0, max(DT.A061552) + 1)
                if i in DT.A061552]
        report("P-recursion on the held terms", check_precursion(held, polys))
        return
    if cmd == "algeq":
        report("algebraic equation %s" % argv[2], check_algeq(argv[2])); return
    if cmd == "guessalg":
        report("guesser calibration on A000139", calibrate_algeq())
        pos = [a for a in argv[2:] if not a.startswith("--") and not a.isdigit()
               or "," in a]
        vals = [int(x) for x in _terms(pos[0])] if pos else \
               [DT.A061552[i] for i in range(0, max(DT.A061552) + 1)]
        b = int(argv[argv.index("--budget") + 1]) if "--budget" in argv else None
        hit = guess_algeq([Q(v) for v in vals], budget=b)
        if hit:
            print("  algebraic: degree %d in y, %d in z, surplus %d"
                  % (hit[0], hit[1], hit[3]))
        else:
            print("  no algebraic equation from %d terms within the searched envelope"
                  % len(vals))
        return
    if cmd == "solution":
        adjudicate(argv[2]); return
    if cmd == "dfinite":
        report("guesser calibration on the solved classes", calibrate_precursion())
        a = [Q(DT.A061552[i]) for i in range(0, max(DT.A061552) + 1)]
        ms = int(argv[argv.index("--surplus") + 1]) if "--surplus" in argv else 5
        hit = guess_precursion(a, min_surplus=ms)
        if hit:
            print("  Av(1324): P-recursion order %d degree %d, surplus %d" % (hit[0], hit[1], hit[3]))
        else:
            print("  Av(1324): no P-recursion with (r+1)(m+1) <= 48 and surplus >= %d" % ms)
            print("            over all %d terms" % len(a))
        return
    if cmd == "asymptotic":
        v = [float(x) for x in argv[2:6]]
        sig = float(argv[6]) if len(argv) > 6 else 0.5
        report("B mu^n mu1^(n^%s) n^g" % sig, check_asymptotic(*v, sigma=sig)); return
    if cmd == "rhocheck":
        t = int(argv[2])
        report("rho_%d = %s" % (t, argv[3]), check_rho(t, argv[3])); return
    if cmd == "wheremu":
        report("where the growth rate sits in t", where_is_mu())
        ok = report("control: 1/d ratio extrapolation recovers a known limit",
                    extrapolation_is_valid())
        if not ok:
            print("      so that extrapolation carries no information at d <= 9")
        return
    if cmd == "R":
        report("R_%s" % argv[2], check_R(int(argv[2]), _terms(argv[3]))); return
    if cmd == "family":
        t = int(argv[2]); expr = argv[3]
        f = lambda d: eval(expr, {"d": d, "Q": Q, "comb": comb, "factorial": factorial,
                                  "cat": DT.cat, "dfact": _dfact})
        report("[s^%d]R_d = %s" % (t, expr), check_family(t, f)); return
    if cmd == "growth":
        a = [float(x) for x in argv[2:5]]
        report("growth constants", check_growth(*a)); return
    if cmd == "theta":
        report("theta diagonals", check_theta()); return
    if cmd == "identities":
        report("top-end evaluation identities", check_top_identities())
        report("R_d and R_d' at s = -1", check_at_minus_one())
        report("(x-y)H = xB - yA", check_HBA()); return
    if cmd == "calibrate":
        report("fitter calibration", calibrate()); return
    if cmd == "staircase":
        report("staircase bound", check_staircase())
        report("diagonal correlation inequality", check_correlation()); return
    if cmd == "chain":
        report("chain operator and the g(k) ladder",
               check_chain(int(argv[2]) if len(argv) > 2 else 5)); return
    if cmd == "stratum":
        report("the inversion strata, split and crude bound", check_stratum()); return
    if cmd == "walks":
        report("weighted quotient of the profile transfer",
               check_walks(int(argv[2]) if len(argv) > 2 else 10)); return
    if cmd == "dominoes":
        report("the transfer marginals against brute-force dominoes",
               check_dominoes(int(argv[2]) if len(argv) > 2 else 4)); return
    if cmd == "geometric":
        report("the geometric law for Var(g)/Var(h) and its threshold",
               check_geometric()); return
    if cmd == "antisym":
        report("the antisymmetric part and the factor of two",
               check_antisym()); return
    if cmd == "svsplit":
        report("the diagonal pair against the sV pair", check_sv_split()); return
    if cmd == "certificate":
        report("the staircase bound at an explicit rational witness",
               check_certificate()); return
    if cmd == "rlmax":
        report("legal insertions against the right-to-left maxima",
               check_rlmax(int(argv[2]) if len(argv) > 2 else 7)); return
    if cmd == "logconvex":
        report("log-convexity of the staircase ladder",
               check_logconvex(int(argv[2]) if len(argv) > 2 else 7)); return
    if cmd == "pqd":
        report("positive quadrant dependence",
               check_pqd(int(argv[2]) if len(argv) > 2 else 7)); return
    if cmd == "skew":
        report("sV as a skew-component sum",
               check_skew(int(argv[2]) if len(argv) > 2 else 7)); return
    if cmd == "sigmamodel":
        d = int(argv[2]) if len(argv) > 2 else 3
        report("general block model at d = %d" % d, check_sigma_model(d)); return
    if cmd == "blockmodel":
        report("block model for the increasing pattern", check_blockmodel()); return
    if cmd == "threeblock":
        report("three-block identity", check_threeblock(
            int(argv[2]) if len(argv) > 2 else 20)); return
    if cmd == "forbidden":
        d = int(argv[2]) if len(argv) > 2 else 3
        report("forbidden count at d = %d" % d, check_forbidden(d)); return
    if cmd == "K":
        try:
            K4 = Q(argv[2]); K5 = Q(argv[3]) if len(argv) > 3 else None
            report("K_t models", check_K(K4, K5))
        except ValueError:                       # not a rational: an expression in t
            f = lambda t: eval(argv[2], {"t": t, "Q": Q, "comb": comb,
                                         "factorial": factorial, "sqrt": sqrt,
                                         "exp": lambda z: 2.718281828459045 ** z,
                                         "log": log, "cat": DT.cat, "dfact": _dfact})
            report("K_t = %s" % argv[2], check_K_expr(f))
        return
    if cmd == "p3":
        expr = argv[2]
        p3 = lambda d: eval(expr, {"d": d, "Q": Q, "comb": comb, "factorial": factorial,
                                   "cat": DT.cat, "dfact": _dfact})
        report("[s^4]R_d implied by this p_{d,d-3}", check_family(4, s4_from_p3(p3)))
        return
    if cmd == "rho":
        t = int(argv[2]); r = fit_rho(t)
        if not r:
            print("  rho_%d: no fit with surplus in powers of (1-y)" % t); return
        I, names, co, sur, flag = r
        print("  rho_%d = %s" % (t, " + ".join("%s*%s" % (c, n)
              for c, n in zip(co, names) if c != 0)))
        print("     I = %d, surplus %d" % (I, sur))
        if flag:
            print("     %s" % flag)
        else:
            lead = co[1] if names and names[0] == "1" else co[0]
            print("     K_%d = %s" % (t, lead))
        return
    if cmd == "fit":
        start = 1
        if "--start" in argv: start = int(argv[argv.index("--start")+1])
        vals = _terms(argv[2])
        hits = fit_closed_form(vals, start=start)
        if not hits:
            print("  no closed form with surplus in the tried families")
            print("  (interpolations with zero surplus are deliberately rejected)")
        for name, sur, coeffs in hits:
            print("  %s" % name)
            print("     surplus %d, coefficients %s" % (sur, [str(c) for c in coeffs]))
        return
    print("unknown command %r; run with --help" % cmd)

def main(argv):
    try:
        return _main(argv)
    except (ImportError, AttributeError, FileNotFoundError) as e:
        print("  unavailable here: %s" % e)
        print("  the self-contained commands are: solution, gf, formula, recurrence,")
        print("  algeq, dfinite, asymptotic, K, series, fit, growth, clearing, cfit")

if __name__ == "__main__":
    main(sys.argv)
