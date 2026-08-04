"""Exact truncated power series over Q, and a safe evaluator for expressions.

A proposed solution to Av(1324) arrives as a generating function, an algebraic
equation, or a recurrence.  All three are decided by expanding to the 51 terms
we hold and comparing, which needs exact series arithmetic and nothing else.
"""
from fractions import Fraction as Q

DEFAULT_N = 51


class S:
    """Power series truncated at x^(n-1), coefficients Fraction."""
    __slots__ = ("c", "n")

    def __init__(self, c=(), n=DEFAULT_N):
        self.n = n
        v = [Q(0)] * n
        for i, a in enumerate(c):
            if i < n: v[i] = Q(a)
        self.c = v

    @staticmethod
    def const(a, n=DEFAULT_N): return S([a], n)

    @staticmethod
    def var(n=DEFAULT_N): return S([0, 1], n)

    def __getitem__(self, i): return self.c[i] if 0 <= i < self.n else Q(0)

    def _lift(self, o):
        return o if isinstance(o, S) else S.const(o, self.n)

    def __add__(self, o):
        o = self._lift(o); return S([a + b for a, b in zip(self.c, o.c)], self.n)
    __radd__ = __add__

    def __neg__(self): return S([-a for a in self.c], self.n)

    def __sub__(self, o): return self + (-self._lift(o))
    def __rsub__(self, o): return self._lift(o) + (-self)

    def __mul__(self, o):
        o = self._lift(o); n = self.n
        r = [Q(0)] * n
        for i, a in enumerate(self.c):
            if a == 0: continue
            for j in range(0, n - i):
                b = o.c[j]
                if b: r[i + j] += a * b
        return S(r, n)
    __rmul__ = __mul__

    def inv(self):
        if self.c[0] == 0: raise ValueError("series has no constant term; cannot invert")
        n = self.n; r = [Q(0)] * n; r[0] = 1 / self.c[0]
        for k in range(1, n):
            s = Q(0)
            for j in range(1, k + 1): s += self.c[j] * r[k - j]
            r[k] = -s / self.c[0]
        return S(r, n)

    def _shift(self, k):
        """multiply by x^-k, discarding nothing (caller guarantees valuation >= k)"""
        return S(self.c[k:], self.n)

    def __truediv__(self, o):
        o = self._lift(o)
        v = o.valuation()
        if v == 0: return self * o.inv()
        if self.valuation() < v:
            raise ValueError("quotient has a pole: valuations %d over %d"
                             % (self.valuation(), v))
        return self._shift(v) * o._shift(v).inv()

    def __rtruediv__(self, o): return self._lift(o) / self

    def __pow__(self, k):
        if isinstance(k, int):
            if k < 0: return (self ** (-k)).inv()
            r = S.const(1, self.n); b = self
            while k:
                if k & 1: r = r * b
                b = b * b; k >>= 1
            return r
        return (self.log() * Q(k)).exp()

    def valuation(self):
        for i, a in enumerate(self.c):
            if a: return i
        return self.n

    def sqrt(self):
        c0 = self.c[0]
        if c0 == 0:
            v = self.valuation()
            if v % 2: raise ValueError("odd valuation; sqrt is not a power series")
            sh = S(self.c[v:], self.n).sqrt()
            return S([Q(0)] * (v // 2) + sh.c[: self.n - v // 2], self.n)
        r0 = _rational_sqrt(c0)
        n = self.n; r = [Q(0)] * n; r[0] = r0
        for k in range(1, n):
            s = Q(0)
            for j in range(1, k): s += r[j] * r[k - j]
            r[k] = (self.c[k] - s) / (2 * r0)
        return S(r, n)

    def exp(self):
        if self.c[0] != 0: raise ValueError("exp needs zero constant term")
        n = self.n; r = [Q(0)] * n; r[0] = Q(1)
        d = [self.c[i] * i for i in range(n)]          # x f'
        for k in range(1, n):
            s = Q(0)
            for j in range(1, k + 1): s += d[j] * r[k - j]
            r[k] = s / k
        return S(r, n)

    def log(self):
        if self.c[0] != 1: raise ValueError("log needs constant term 1")
        return (self.deriv() * self.inv()).integrate()

    def deriv(self):
        return S([self.c[i] * i for i in range(1, self.n)], self.n)

    def integrate(self):
        return S([Q(0)] + [self.c[i] / (i + 1) for i in range(self.n - 1)], self.n)

    def compose(self, o):
        """self(o), requiring o to have zero constant term."""
        if o.c[0] != 0: raise ValueError("composition needs zero constant term")
        r = S.const(0, self.n); p = S.const(1, self.n)
        for a in self.c:
            if a: r = r + p * a
            p = p * o
        return r

    def __repr__(self):
        return " + ".join("%s x^%d" % (a, i) for i, a in enumerate(self.c) if a)[:200]


def _rational_sqrt(q):
    q = Q(q)
    if q < 0: raise ValueError("negative constant term under sqrt")
    a, b = q.numerator, q.denominator
    ra, rb = _isqrt(a), _isqrt(b)
    if ra * ra != a or rb * rb != b:
        raise ValueError("constant term %s is not a rational square" % q)
    return Q(ra, rb)


def _isqrt(m):
    if m < 2: return m
    x = m; y = (x + 1) // 2
    while y < x: x = y; y = (x + m // x) // 2
    return x


def evaluate(expr, n=DEFAULT_N, extra=None):
    """Evaluate an expression in x as a truncated power series.

    Available: x, sqrt, exp, log, Q, integer and Fraction literals, + - * / **.
    """
    x = S.var(n)
    env = {"x": x, "y": x, "z": x, "Q": Q,
           "sqrt": lambda f: (f if isinstance(f, S) else S.const(f, n)).sqrt(),
           "exp": lambda f: (f if isinstance(f, S) else S.const(f, n)).exp(),
           "log": lambda f: (f if isinstance(f, S) else S.const(f, n)).log(),
           "__builtins__": {}}
    if extra: env.update(extra)
    out = eval(expr, env)
    return out if isinstance(out, S) else S.const(out, n)


# ------------------------------------------------------------ linear algebra
def nullspace(rows, unk):
    """Basis of the right nullspace of the exact matrix `rows` with `unk` columns."""
    A = [r[:] for r in rows]
    m = len(A); piv = 0; where = []
    for col in range(unk):
        r = next((i for i in range(piv, m) if A[i][col] != 0), None)
        if r is None: continue
        A[piv], A[r] = A[r], A[piv]
        pv = A[piv][col]; A[piv] = [v / pv for v in A[piv]]
        for i in range(m):
            if i != piv and A[i][col] != 0:
                f = A[i][col]; A[i] = [a - f * b for a, b in zip(A[i], A[piv])]
        where.append(col); piv += 1
    free = [c for c in range(unk) if c not in where]
    basis = []
    for fc in free:
        v = [Q(0)] * unk; v[fc] = Q(1)
        for i, pc in enumerate(where): v[pc] = -A[i][fc]
        basis.append(v)
    return basis, piv
