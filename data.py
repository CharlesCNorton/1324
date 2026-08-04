"""Everything exact that we hold about Av(1324), in one place.

Nothing here is conjectural.  Each item is either published data or an identity
derived and verified against it.  The oracle imports this; so should anything
else that wants to check a claim.
"""
from fractions import Fraction as Q
from math import comb, factorial
import os

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- published
def _load(fn):
    out = {}
    for line in open(os.path.join(HERE, "data", fn)):
        line = line.strip()
        if line and not line.startswith("#"):
            k, v = line.split()
            out[int(k)] = int(v)
    return out

A061552 = _load("b061552.txt")          # |Av_n(1324)|, n = 1..50, Conway-Guttmann-Zinn-Justin
A395725_FLAT = _load("b395725.txt")     # triangle by position of the maximum, rows 1..15

def A395725(n, k):
    """T(n,k), from the OEIS b-file where available."""
    idx = (n - 1) * n // 2 + k
    return A395725_FLAT.get(idx)

# growth rate: fitted constants and proved bounds
MU, MU_ERR   = 11.600, 0.003            # CGZJ 2018
MU1, MU1_ERR = 0.0400, 0.0005
G, G_ERR     = -1.1, 0.1
GR_LOWER     = 10.271                   # Bevan, Brignall, Elvey Price, Pantone
GR_UPPER     = 13.5                     # Bona

# ------------------------------------------------------ staircase sequences
# T_k(m) counts the 1324-avoiding staircase-gridded objects with k cells of m
# points each, the cells alternating Av(213) and Av(132).  T_1 is Catalan and
# T_2 the balanced dominoes; T_3 and T_4 are ours.
CATALAN  = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]
A000139  = [1, 2, 6, 22, 91, 408, 1938, 9614, 49335, 260130, 1402440]
TROMINO  = [1, 3, 11, 47, 224, 1156, 6332, 36312, 215936, 1322455,
            8298878, 53159260, 346555823]

T2 = [2, 23, 424, 9751, 255642, 7316494, 223060740, 7133973623,
      236896023166, 8108615482601]
T3 = [4, 265, 36325, 6949612, 1615228302, 427032119568,
      123792159207513, 38464960591249684, 12619010975298054200,
      4325038470273319306246]
T4 = [8, 3053, 3110006, 4945513349, 10183097715862, 24864239515801111,
      68560301900937223298, 207145020458706002649863,
      672194901252825186035714727]

GR_LOWER_EXACT = 10.271012  # Bevan-Brignall-Elvey Price-Pantone, Theorem 7.1
GR_LOWER_ALG = 10.27101292824530   # their footnote 3: an algebraic number of
                                   # degree 104 from the same refined staircase
TAU_THRESHOLD = 7.8595      # the tromino growth the staircase block needs
TAU_CHEBYSHEV = 8.0362      # ((27/4)^4/4)^(1/3), what the inequality gives
BOUND_TROMINO = 10.465416   # G_3 at that tau

# ------------------------------------------------------------- our diagonals
# D(d,M) = A395725(M+d+1, M+1) = # of (M+d)-permutations avoiding 1324 whose
# length-M prefix avoids 132.  M <= 2 agrees with A061552 by construction.
D = {
 9:  dict(enumerate([94776, 591950, 3824112, 23919834, 144904277, 853457567,
      4905116822, 27594113202, 152329496445, 826923388906, 4422062459254,
      23329711076088, 121582380091678, 626590623709730, 3196402345191860,
      16153387453241372, 80929581281262567, 402228469959568432])),
 10: dict(enumerate([591950, 3824112, 25431452, 163509478, 1017200387,
      6147826607, 36233442968, 208891603183, 1181051010582, 6562598854419,
      35901813608398, 193662530895029, 1031392511940492, 5429190137546380,
      28274786168039316, 145809246550271934, 745103901013533155])),
 11: dict(enumerate([3824112, 25431452, 173453058, 1142454317, 7276041800,
      44995274684, 271203974684, 1598242143927, 9232625528625,
      52392842635425, 292591142125246, 1610471004801912, 8748075190910359,
      46949235882217231, 249187681272850204, 1309121703473547554])),
 12: dict(enumerate([25431452, 173453058, 1209639642, 8139743461,
      52936264558, 334149574221, 2055077483584, 12353191224688,
      72763593507900, 420883902803776, 2394989071822941, 13427641953875866,
      74270889243306318, 405743329772843636, 2191424902028808793])),
 13: dict(enumerate([173453058, 1209639642, 8604450011, 59019298402,
      391111962836, 2514965130801, 15752453055881, 96408220043268,
      578027664706558, 3402356599625872, 19696399105475880,
      112313391955632162, 631658206095799421, 3507768225973524136])),
}

# ------------------------------------------------------- the two-term law
# D(d,M) = p_d(M) C(2M,M) + q_d(M) 4^M, deg p_d = d-1, deg q_d = d-2.
# Coefficient lists are constant-first.
P = {
 1:[Q(1)], 2:[Q(3,2),Q(1,2)], 3:[Q(7,2),Q(11,6),Q(1,6)],
 4:[Q(12),Q(9),Q(35,24),Q(1,24)],
 5:[Q(52),Q(2987,60),Q(447,40),Q(47,60),Q(1,120)],
 6:[Q(257),Q(11437,40),Q(55507,720),Q(5711,720),Q(43,144),Q(1,720)],
 7:[Q(2763,2),Q(1421393,840),Q(2582147,5040),Q(65671,1008),Q(3191,840),
    Q(433,5040),Q(1,5040)],
 8:[Q(7897),Q(8682911,840),Q(34274543,10080),Q(5015329,10080),
    Q(1492493,40320),Q(7837,5760),Q(113,5760),Q(1,40320)],
 9:[Q(94777,2),Q(164178787,2520),Q(76789213,3360),Q(336477719,90720),
    Q(23599361,72576),Q(142673,9072),Q(10049,25920),Q(67,18144),Q(1,362880)],
 10:[Q(591951,2),Q(426134771,1008),Q(47245463303,302400),Q(12469222543,453600),
    Q(1096820519,403200),Q(27364129,172800),Q(3203899,604800),Q(877,9600),
    Q(713,1209600),Q(1,3628800)],
 11:[Q(3824113,2),Q(5576801779,1980),Q(3616161562021,3326400),
    Q(679131756293,3326400),Q(11504724829,518400),Q(787734709,532224),
    Q(808677109,13305600),Q(9759209,6652800),Q(243049,13305600),Q(31,380160),
    Q(1,39916800)],
}
QQ = {
 1:[], 2:[Q(1,2)], 3:[Q(5,2),Q(1,2)], 4:[Q(11),Q(13,4),Q(1,4)],
 5:[Q(51),Q(869,48),Q(35,16),Q(1,12)],
 6:[Q(256),Q(1241,12),Q(191,12),Q(49,48),Q(1,48)],
 7:[Q(2761,2),Q(148309,240),Q(21563,192),Q(1847,192),Q(35,96),Q(1,240)],
 8:[Q(7896),Q(1474253,384),Q(9074837,11520),Q(20895,256),Q(4985,1152),
    Q(5,48),Q(1,1440)],
 9:[Q(94775,2),Q(165558649,6720),Q(3545831,640),Q(3783043,5760),
    Q(4139,96),Q(8743,5760),Q(47,1920),Q(1,10080)],
 10:[Q(591949,2),Q(17477721287,107520),Q(50669971273,1290240),
    Q(42184999,8192),Q(72379187,184320),Q(717569,40960),Q(4961,11520),
    Q(13,2688),Q(1,80640)],
 11:[Q(3824111,2),Q(177266173061,161280),Q(242005240151,860160),
    Q(1854655833743,46448640),Q(69783453,20480),Q(396797953,2211840),
    Q(702407,122880),Q(49237,483840),Q(11,13440),Q(1,725760)],
}

# ------------------------------------------------- Laurent polynomials in s
class L:
    """Laurent polynomial in s = sqrt(1-4x)."""
    __slots__ = ("c",)
    def __init__(self, c=None): self.c = {k: v for k, v in (c or {}).items() if v != 0}
    def __add__(self, o):
        r = dict(self.c)
        for k, v in o.c.items(): r[k] = r.get(k, Q(0)) + v
        return L(r)
    def scale(self, a): return L({k: v*a for k, v in self.c.items()})
    def __mul__(self, o):
        r = {}
        for k1, v1 in self.c.items():
            for k2, v2 in o.c.items(): r[k1+k2] = r.get(k1+k2, Q(0)) + v1*v2
        return L(r)
    def deriv(self): return L({k-1: v*k for k, v in self.c.items() if k != 0})
    def at(self, t): return sum(v*(Q(t)**k) for k, v in self.c.items())

def mono(k, a=1): return L({k: Q(a)})
_ONE, _S2 = mono(0), mono(2)

def theta(f):
    """x d/dx, acting on Laurent polynomials in s."""
    return (_ONE + _S2.scale(Q(-1))).scale(Q(-1, 2)) * mono(-1) * f.deriv()

_basec, _base4 = [mono(-1)], [mono(-2)]
for _ in range(14):
    _basec.append(theta(_basec[-1])); _base4.append(theta(_base4[-1]))

def GF(d):
    """generating function of the d-th diagonal, as a Laurent polynomial in s"""
    F = L()
    for k, c in enumerate(P[d]): F = F + _basec[k].scale(c)
    for k, c in enumerate(QQ[d]): F = F + _base4[k].scale(c)
    return F

def R(d):
    """R_d(s) = GF_d(x) * s^(2d-1); a polynomial of degree 2d-2.  Returns a dict."""
    return (GF(d) * mono(2*d - 1)).c

KNOWN_R = sorted(P)

# ------------------------------------------------------ proved closed forms
def cat(n): return comb(2*n, n)//(n+1)

def s0(d): return Q(cat(d-1), 4**(d-1))
def s1(d): return Q(1, 2) if d >= 2 else Q(0)
def s2(d): return Q(comb(2*d-4, d-2)*(2*d**3 - 7*d**2 + 9*d + 9), 6*4**(d-2)*d)
def s3(d):
    k = d - 3
    return Q(2*k**3 + 3*k**2 + 19*k + 96, 48) if d >= 3 else Q(0)

def p_lead(d):    return Q(1, factorial(d))
def p_sublead(d): return Q(2*d**4 - 9*d**3 + 19*d**2 - 6*d - 6, 6*factorial(d))
def q_lead(d):    return Q(comb(d, 2), factorial(d))
def q_sublead(d):
    k = d - 3
    return (Q(2*k**3+3*k**2+19*k+96, 48) + Q(d-1, 4)) / factorial(d-3)

# leading singular coefficients of rho_t at y = 1: rho_t ~ K_t (1-y)^(1/2-3t/2)
K = {0: Q(-2), 1: Q(1,2), 2: Q(1,4), 3: Q(1,4)}
def rho_exponent(t): return Q(1,2) - Q(3*t, 2)

# rho_t in closed form, as (coefficient, exponent of (1-y), power of y) triples
RHO_CLOSED = {
 0: [(Q(2), None, 0), (Q(-2), Q(1,2), 0)],
 1: [(Q(1,2), Q(-1), 2)],
 2: [(Q(2), None, 0), (Q(-3), Q(1,2), 0), (Q(1), Q(3,2), 0),
     (Q(1,2), Q(-1,2), 2), (Q(1,4), Q(-3,2), 3), (Q(1,4), Q(-5,2), 4)],
 3: None,   # rational: y^3(16-44y+43y^2-13y^3)/(8(1-y)^4)
}
