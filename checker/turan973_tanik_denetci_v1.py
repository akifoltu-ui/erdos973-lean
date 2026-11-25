#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""turan973_tanik_denetci_v1.py -- exact checker for explicit configurations in Erdos Problem #973 (n = 3, 4, 5, 6).

Quantity:
    Delta*_n = inf max_{2 <= k <= n+1} |z_1^k + z_2^k + ... + z_n^k|,  over z_1 = 1 and |z_j| >= 1 (j = 2, ..., n).
Data: for each n, the n points z_j = x_j + i*y_j as decimal strings (read as exact rationals) and a number B_n.
The checker verifies, in exact rational arithmetic (Python standard library only):
    (a) z_1 = 1 and x_j^2 + y_j^2 >= 1 for every j;
    (b) |p_k|^2 <= B_n^2 for every k = 2, ..., n+1, where p_k = z_1^k + ... + z_n^k.
Together (a) and (b) give Delta*_n <= B_n. The checker also prints max_k |p_k| and the spread max_k |p_k| - min_k |p_k|.
Negative controls: three corrupted copies of the n = 6 data are checked as well; each must be rejected for its own reason.
Usage: python turan973_tanik_denetci_v1.py      (exit code 0 when every check passes)
Mehmet Akif Oltulu, ORCID 0009-0003-0928-0854, 2026-11-25.
"""
import sys
from fractions import Fraction
from math import isqrt

DATA = {
    3: {"B": "0.467936100887611384260440917836", "z": [
        ("1", "0"),
        ("-0.4259770695665107204310688470304773374725", "-0.9047339587986780582124279649157331072706"),
        ("0.6154865000254697641566267134686468044232", "-0.9700858767691807980395312690737456845659"),
    ]},
    4: {"B": "0.387205517872967112766701799583", "z": [
        ("1", "0"),
        ("-0.8149823616602099053404219396598998528696", "-0.5794857635721060781410175507659931793290"),
        ("-0.1201857156282252116327801013346733625065", "-1.2076432303584561425254468404691385149539"),
        ("0.7977612978274681347217103063485295613680", "-0.9145620207292173966348052853086526878437"),
    ]},
    5: {"B": "0.336586388976032825955813555903", "z": [
        ("1", "0"),
        ("-0.9706397324527208915748757695847865502329", "-0.2405379591335022657258515890449784533343"),
        ("-0.6812584514357044175643602052962833971739", "-1.0410063078932173000627567475270414372500"),
        ("0.1606220175200700033929692713386548977819", "-1.3159175822893259867632438466579198721762"),
        ("0.9116580537784438646620120425571965957282", "-0.8465735666242727214553982378715311032686"),
    ]},
    6: {"B": "0.301768239014820941010637298336", "z": [
        ("1", "0"),
        ("-0.9989561598574452386080209272736209990994", "0.0456792149983590900081227972184183247706"),
        ("-1.0206385398879916244336111512981755504798", "-0.7359623182759746565464700270279405910967"),
        ("-0.4452190860423133780098138085051496813966", "-1.3141987400510828103379278004378911681140"),
        ("0.3847227816907048282030268862365323390565", "-1.3331641850036223676921883055376081418322"),
        ("0.9859549754417990319859386044350246911989", "-0.7818160585639053998381662460324261182604"),
    ]},
}


def check(n, pts, B):
    z = [(Fraction(x), Fraction(y)) for x, y in pts]
    if len(z) != n:
        return False, "wrong number of points", None
    if z[0] != (1, 0):
        return False, "z_1 is not 1", None
    for j, (x, y) in enumerate(z, 1):
        if x * x + y * y < 1:
            return False, "|z_%d| < 1" % j, None
    B2 = Fraction(B) ** 2
    w = list(z)
    mods = []
    for k in range(2, n + 2):
        w = [(a * x - b * y, a * y + b * x) for (a, b), (x, y) in zip(w, z)]
        re = sum(a for a, _ in w)
        im = sum(b for _, b in w)
        m2 = re * re + im * im
        if m2 > B2:
            return False, "|p_%d| > B_%d" % (k, n), None
        mods.append(m2)
    return True, "", mods


def root_decimal(m2, digits=40):
    s = isqrt(m2.numerator * 10 ** (2 * digits) // m2.denominator)
    t = str(s).rjust(digits + 1, "0")
    return t[:-digits] + "." + t[-digits:]


def main():
    ok_all = True
    n_pass = 0
    for n in sorted(DATA):
        pts, B = DATA[n]["z"], DATA[n]["B"]
        ok, why, mods = check(n, pts, B)
        if ok:
            n_pass += 1
            hi, lo = root_decimal(max(mods)), root_decimal(min(mods))
            spread = Fraction(hi) - Fraction(lo)
            print("n = %d | %d points | z_1 = 1, |z_j| >= 1: PASS | max_k |p_k| = %s <= B_%d = %s: PASS | spread < %s | => Delta*_%d <= %s"
                  % (n, len(pts), hi, n, B, "1e-35" if spread < Fraction(1, 10 ** 35) else str(float(spread)), n, B))
        else:
            print("n = %d | FAIL: %s" % (n, why))
            ok_all = False
    pts, B = [list(p) for p in DATA[6]["z"]], DATA[6]["B"]
    lowered = str(Fraction(B) - Fraction(1, 10 ** 20))
    x2, y2 = Fraction(pts[1][0]), Fraction(pts[1][1])
    s = Fraction(10 ** 30 - 1, 10 ** 30)
    inside = [list(p) for p in pts]
    inside[1] = [str(x2 * s), str(y2 * s)]
    flipped = [list(p) for p in pts]
    x3 = flipped[2][0]
    i = x3.index(".") + 12
    flipped[2][0] = x3[:i] + ("0" if x3[i] == "9" else str(int(x3[i]) + 1)) + x3[i + 1:]
    controls = [("bound lowered by 1e-20", pts, lowered, "> B_6"),
                ("z_2 moved inside the unit circle by a factor 1 - 1e-30", inside, B, "|z_2| < 1"),
                ("one digit of x_3 changed (12th decimal)", flipped, B, "> B_6")]
    nk = 0
    for name, p_, b_, expect in controls:
        ok, why, _ = check(6, p_, b_)
        good = (not ok) and expect in why
        nk += good
        print("negative control: %-55s -> %s" % (name, ("rejected (%s): EXPECTED" % why) if good else ("NOT REJECTED AS EXPECTED (%s)" % (why or "passed"))))
    print("SUMMARY: %d/%d configurations PASS, %d/3 negative controls rejected as expected" % (n_pass, len(DATA), nk))
    return 0 if ok_all and nk == 3 else 1


if __name__ == "__main__":
    sys.exit(main())
