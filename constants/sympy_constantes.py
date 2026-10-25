#!/usr/bin/env python3
"""
SymPy check of the constants used by the UV fingerprint (variant B) of the Lean statement.

Conventions (Euclidean, d = 4):
  * free Maxwell field, Feynman gauge: <A_mu(x) A_nu(0)> = delta_{mu nu} D(x), D(x) = 1/(4 pi^2 |x|^2)
  * F_{mu nu} = d_mu A_nu - d_nu A_mu
  * F2 = sum_{mu,nu} F_{mu nu} F_{mu nu}
  * T_{mu nu} = sum_a F_{mu a} F_{nu a} - (1/4) delta_{mu nu} F2   (canonical stress tensor, traceless)
  * normal-ordered composites: <:XY:(x) :ZW:(0)> = <XZ><YW> + <XW><YZ>   (Wick)
Results checked:
  (1) T is traceless (algebraic identity).
  (2) <T_{mu nu}(x) T_{rho sigma}(0)> = C_T * I_{mu nu, rho sigma}(x) / |x|^8 with
      I_{mu nu,rho sigma} = 1/2 (I_{mu rho} I_{nu sigma} + I_{mu sigma} I_{nu rho}) - 1/4 delta_{mu nu} delta_{rho sigma},
      I_{mu nu}(x) = delta_{mu nu} - 2 x_mu x_nu / |x|^2,  and C_T = 4/pi^4 = 16 / S_4^2 (S_4 = 2 pi^2).
  (3) <F2(x) F2(0)> = c_F2 / |x|^8, the value of c_F2 is printed.
  (4) Free scalar field: int_0^oo (4 pi s)^(-2) exp(-r^2/(4 s)) ds = 1/(4 pi^2 r^2) ;
      <:phi^k:(x) :phi^l:(0)> = delta_{kl} k! C(x)^k (orthogonality of the Wick powers, checked
      by counting contractions for k, l <= 6).
  (5) b1/b0^2 = 102/121 for pure Yang-Mills (b0 = 11 C_A/3, b1 = 34 C_A^2/3), independent of G.
  (6) Asymptotic expansion: if da/dL = -2 b0 a^2 - 2 b1 a^3 (a = g^2/16pi^2, L = ln(1/(|x| Lambda))),
      then 4 b0^2 L^2 a(L)^2 = 1 - (b1/b0^2) ln L / L + O(1/L) ; numerical check (mpmath).
  (7) kappa = 3 dim G / pi^4 symbolically (b0 cancels), and FP2 with the full two-loop factor
      (beta/2g)^2 for C_A = 2, 3, 5 (numerical, mpmath).
Output: on standard output ONLY; the script writes no file. The expected output is the reference
constantes_verifiees.txt (same folder), which the script never rewrites. Comparison (done by scripts/verify.sh):
  python3 constants/sympy_constantes.py > output.txt && diff constants/constantes_verifiees.txt output.txt
The printed labels are in French; they are kept unchanged so that the reference file stays byte-identical
to the one checked before the translation of the comments (see README.md).
"""
import itertools, math
import sympy as sp

def out(s=""):
    print(s)

x = sp.symbols('x0:4', real=True)
r2 = sum(xi**2 for xi in x)
D = 1/(4*sp.pi**2*r2)

# <F_{mu nu}(x) F_{rho sigma}(0)>: with z = x - y, d^y = -d^z
def dD(m, n):
    return sp.diff(D, x[m], x[n])
def delta(a, b):
    return 1 if a == b else 0

def GFF(mu, nu, rho, sig):
    # <d_mu A_nu(x) d_rho A_sig(y)> = - d_mu d_rho D(z) delta_{nu sig}
    t = lambda a, b, c, e: -dD(a, c)*delta(b, e)
    return t(mu, nu, rho, sig) - t(mu, nu, sig, rho) - t(nu, mu, rho, sig) + t(nu, mu, sig, rho)

idx = range(4)
G = {}
for mu, nu, rho, sig in itertools.product(idx, repeat=4):
    G[(mu, nu, rho, sig)] = sp.simplify(GFF(mu, nu, rho, sig))

# Bilinears in F: dictionary {((mu,nu),(rho,sig)) : coeff} representing sum coeff F_{mu nu} F_{rho sig}
def bil_F2():
    return {((m, n), (m, n)): 1 for m in idx for n in idx}
def bil_T(m, n):
    d = {}
    for a in idx:
        d[((m, a), (n, a))] = d.get(((m, a), (n, a)), 0) + 1
    if m == n:
        for a in idx:
            for b in idx:
                d[((a, b), (a, b))] = d.get(((a, b), (a, b)), 0) - sp.Rational(1, 4)
    return d

def wick2(X, Y):
    s = 0
    for (A, B), cx in X.items():
        for (C, E), cy in Y.items():
            s += cx*cy*(G[A + C]*G[B + E] + G[A + E]*G[B + C])
    return s

# (1) trace of T
trT = {}
for m in idx:
    for k, v in bil_T(m, m).items():
        trT[k] = trT.get(k, 0) + v
trT = {k: v for k, v in trT.items() if v != 0}
out("(1) trace de T (bilinéaire résiduel) : %s" % (trT if trT else "0  [T sans trace : OK]"))

# generic test points to compare the tensor structures
pts = [(1, 2, 3, 5), (sp.Rational(1, 3), -2, sp.Rational(7, 5), 1), (2, 0, 0, 0), (1, 1, 1, 1)]
def Imat(p):
    rr = sum(c**2 for c in p)
    return [[delta(a, b) - 2*sp.Rational(1)*p[a]*p[b]/rr for b in idx] for a in idx]
def Istruct(p, m, n, rho, sig):
    I = Imat(p)
    return sp.Rational(1, 2)*(I[m][rho]*I[n][sig] + I[m][sig]*I[n][rho]) - sp.Rational(1, 4)*delta(m, n)*delta(rho, sig)

# (2) <T T>
CT_vals = set()
ok = True
for p in pts:
    subs = dict(zip(x, p))
    rr = sum(c**2 for c in p)
    for (m, n, rho, sig) in [(0, 0, 0, 0), (0, 1, 0, 1), (1, 2, 1, 2), (0, 0, 1, 1), (0, 1, 2, 3), (2, 3, 2, 3), (0, 2, 0, 2), (3, 3, 3, 3), (1, 1, 2, 2)]:
        val = sp.nsimplify(sp.simplify(wick2(bil_T(m, n), bil_T(rho, sig)).subs(subs)))
        st = sp.simplify(Istruct(p, m, n, rho, sig))
        if st == 0:
            if sp.simplify(val) != 0:
                ok = False
                out("   ECHEC structure nulle mais <TT> != 0 en %s %s : %s" % (p, (m, n, rho, sig), val))
            continue
        CT = sp.simplify(val*rr**4/st)
        CT_vals.add(CT)
out("(2) valeurs de C_T trouvées : %s  (attendu 4/pi^4 = 16/S_4^2) ; structure conforme : %s" % (CT_vals, "OK" if ok and len(CT_vals) == 1 else "ECHEC"))
CT_expected = 4/sp.pi**4
assert CT_vals == {CT_expected}, CT_vals
assert sp.simplify(16/(2*sp.pi**2)**2 - CT_expected) == 0

# (3) <F2 F2>
cF2 = set()
for p in pts:
    subs = dict(zip(x, p))
    rr = sum(c**2 for c in p)
    val = sp.simplify(wick2(bil_F2(), bil_F2()).subs(subs))
    cF2.add(sp.simplify(val*rr**4))
out("(3) c_F2 = |x|^8 <F2(x) F2(0)> : %s" % cF2)
assert len(cF2) == 1

# (4) heat kernel and Wick orthogonality
s, rr_ = sp.symbols('s r', positive=True)
I_heat = sp.integrate((4*sp.pi*s)**-2*sp.exp(-rr_**2/(4*s)), (s, 0, sp.oo))
out("(4a) int_0^oo (4 pi s)^-2 exp(-r^2/4s) ds = %s" % sp.simplify(I_heat))
assert sp.simplify(I_heat - 1/(4*sp.pi**2*rr_**2)) == 0

def wick_count(k, l):
    # number of complete contractions between k copies at x and l copies at 0 without self-contraction:
    # possible only if k == l, and then k!
    if k != l:
        return 0
    return math.factorial(k)
# check by brute-force enumeration of the perfect matchings of k+l points without an internal pair
def brute(k, l):
    pts_ = list(range(k + l))
    def matchings(lst):
        if not lst:
            yield []
            return
        a = lst[0]
        for i in range(1, len(lst)):
            b = lst[i]
            rest = lst[1:i] + lst[i + 1:]
            for m in matchings(rest):
                yield [(a, b)] + m
    c = 0
    for m in matchings(pts_):
        if all((a < k) != (b < k) for a, b in m):
            c += 1
    return c
for k in range(0, 7):
    for l in range(0, 7):
        if (k + l) % 2 == 0:
            assert brute(k, l) == wick_count(k, l), (k, l)
out("(4b) <:phi^k: :phi^l:> = delta_kl k! C^k : vérifié par énumération pour k,l <= 6")

# (5) b1/b0^2
CA = sp.symbols('C_A', positive=True)
b0 = sp.Rational(11, 3)*CA
b1 = sp.Rational(34, 3)*CA**2
ratio = sp.simplify(b1/b0**2)
out("(5) b1/b0^2 = %s" % ratio)
assert ratio == sp.Rational(102, 121)

# (6) numerical check of 4 b0^2 L^2 a^2 = 1 - (b1/b0^2) ln L / L + O(1/L)
import mpmath as mp
mp.mp.dps = 80
B0 = mp.mpf(11)  # C_A = 3
B1 = mp.mpf(102)
# exact implicit solution of da/dL = -2 b0 a^2 - 2 b1 a^3:
#   L = 1/(2 b0 a) + (b1/(2 b0^2)) * ln( b1 a / (b0 + b1 a) ) + const  ; we take const = 0
def L_of_a(a):
    return 1/(2*B0*a) + (B1/(2*B0**2))*mp.log(B1*a/(B0 + B1*a))
def a_of_L(L):
    # L_of_a is decreasing in a on ]0, oo[: bracketing, then bisection
    lo, hi = 1/(8*B0*L), 4/(B0*L)
    assert L_of_a(lo) > L > L_of_a(hi)
    for _ in range(400):           # simple bisection (relative precision ~ 2^-400)
        mid = (lo + hi)/2
        if L_of_a(mid) > L:
            lo = mid
        else:
            hi = mid
    return (lo + hi)/2
out("(6)  L        (4 b0^2 L^2 a^2 - 1) * L / ln L     [limite attendue -b1/b0^2 = %s]" % mp.nstr(-B1/B0**2, 8))
for L in [mp.mpf(10)**k for k in (3, 5, 8, 12, 16)]:
    a = a_of_L(L)
    q = (4*B0**2*L**2*a**2 - 1)*L/mp.log(L)
    out("     1e%-3d  %s" % (int(mp.log10(L)), mp.nstr(q, 12)))

# (7) FP1 coefficient kappa for the Ward-normalised theta (added on 2026-10-25 after the adversarial review).
#     theta = (beta(g)/2g) F^a F^a (canonical normalisation), beta = -b0 g^3/(16 pi^2) - b1 g^5/(16 pi^2)^2,
#     a = g^2/(16 pi^2), beta/(2g) = -(b0 a + b1 a^2)/2 ; one loop: a = 1/(2 b0 L), L = -ln|x| (Lambda = 1) ;
#     <theta theta>_c ~ (beta/2g)^2 * dim G * c_F2 / |x|^8 (free gluons at the scale 1/|x|).
Ls, b0s, dims = sp.symbols('L b_0 dimG', positive=True)
a1 = 1/(2*b0s*Ls)
kappa = sp.simplify((b0s*a1/2)**2 * Ls**2 * dims * list(cF2)[0])
out("(7a) kappa = lim |x|^8 <theta theta>_c (ln|x|)^2 = %s   [b0 s'élimine : kappa ne dépend que de dim G]" % kappa)
assert sp.simplify(kappa - 3*dims/sp.pi**4) == 0
out("(7b) FP2 avec le facteur COMPLET (beta/2g)^2 = (b0 a + b1 a^2)^2/4 à deux boucles :")
out("     C_A   L      (16 L^2 (beta/2g)^2 - 1) * L / ln L   [limite -102/121 = %s, convergence en 1/ln L]"
    % mp.nstr(mp.mpf(-102)/121, 8))
for CAv in (2, 3, 5):
    b0v = mp.mpf(11)*CAv/3
    b1v = mp.mpf(34)*CAv**2/3
    def L_of_a2(a):
        return 1/(2*b0v*a) + (b1v/(2*b0v**2))*mp.log(b1v*a/(b0v + b1v*a))
    def a_of_L2(L):
        lo, hi = 1/(8*b0v*L), 4/(b0v*L)
        assert L_of_a2(lo) > L > L_of_a2(hi)
        for _ in range(400):
            mid = (lo + hi)/2
            if L_of_a2(mid) > L:
                lo = mid
            else:
                hi = mid
        return (lo + hi)/2
    for L in [mp.mpf(10)**k for k in (5, 16, 40)]:
        a = a_of_L2(L)
        q = (4*L**2*(b0v*a + b1v*a**2)**2 - 1)*L/mp.log(L)
        out("     %d     1e%-3d  %s" % (CAv, int(mp.log10(L)), mp.nstr(q, 10)))
