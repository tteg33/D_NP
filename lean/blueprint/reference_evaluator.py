#!/usr/bin/env python3
"""Executable reference model for the open obligation `PackedScalarPrograms`.

This file is NOT part of the Lean proof. It is a test bed for the plan in
`blueprint/EVALUATOR_PLAN.md`: every function below mirrors one Lean definition,
and the tests compare the proposed fixed evaluator with brute-force Laurent
expansions on small parameters.

Lean definition                                  Python mirror
-----------------------------------------------  ---------------------------------
LaurentBounds.Expr / Expr.bounds / Expr.expand   Expr classes, bounds, expand
LaurentBounds.Raw.project / tail / geometric     raw_project, raw_tail, raw_geometric
ScalarProjection.exprValue / scalarRecipe        expr_value, scalar_recipe_lean
ScalarProjection.shiftBound                      shift_bound
RadixGrowth.clearFactor / specializedHeight      clear_factor, specialized_height
RadixGrowth.radix                                radix
Extraction.nearest / centered / extractCoeff.    nearest, centered, extract_coefficient
TailRadix.tailNumerator / choose_from_power      tail_numerator, choose_from_power
ScalarDivision.positiveDiv                       Machine.div
ScalarSignedPower.signedPower (a ^ b.toNat)      Machine.pow
ScalarProgram.Term / run / peak                  Term, Term.run (the Machine records the peak)

Proposed (blueprint) definitions                 Python
-----------------------------------------------  ---------------------------------
Expr.evalBounds                                  eval_bounds
Expr.clearedNum                                  cleared_num
Term.Small / Term.Tame                           Term.small, Term.tame

Run:  python blueprint/reference_evaluator.py            (about 80 seconds)
      python blueprint/reference_evaluator.py --quick    (about 8 seconds)
"""

from __future__ import annotations

import random
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from math import comb, floor, prod

# ---------------------------------------------------------------------------
# 0. Bit lengths exactly as in Statement.lean / ScalarProgram.lean
# ---------------------------------------------------------------------------

def bits(x: int) -> int:
    """`bits x = x.log2 + 1` with `Nat.log2 0 = 0`."""
    assert x >= 0
    return max(1, x.bit_length())


def signed_bits(z: int) -> int:
    """`signedBits z = bits z.natAbs + 1`."""
    return bits(abs(z)) + 1


# ---------------------------------------------------------------------------
# 1. The expression syntax of LaurentBounds.lean
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Scalar:
    p: object          # numerator (int, or a Term in symbolic mode)
    q: object          # positive denominator


@dataclass(frozen=True)
class Monomial:
    v: tuple           # fixed integer exponent vector, one entry per coordinate


@dataclass(frozen=True)
class Geometric:
    j: int             # coordinate
    stride: object
    J: object


@dataclass(frozen=True)
class Add:
    f: object
    g: object


@dataclass(frozen=True)
class Neg:
    f: object


@dataclass(frozen=True)
class Mul:
    f: object
    g: object


@dataclass(frozen=True)
class Pow:
    f: object
    n: object


@dataclass(frozen=True)
class Threshold:
    f: object
    n: object
    k: object


@dataclass(frozen=True)
class Project:
    f: object
    j: int
    m: object          # positive period


def bounds(e):
    """`Expr.bounds` : (denominator, height, radius), verbatim."""
    if isinstance(e, Scalar):
        return (e.q, max(1, abs(e.p)), 0)
    if isinstance(e, Monomial):
        return (1, 1, max([abs(a) for a in e.v], default=0))
    if isinstance(e, Geometric):
        return (1, max(1, 2 ** e.J - 1), max(e.J - 1, 0) * e.stride)
    if isinstance(e, (Neg, Project)):
        return bounds(e.f)
    if isinstance(e, Add):
        (df, hf, gf), (dg, hg, gg) = bounds(e.f), bounds(e.g)
        return (df * dg, dg * hf + df * hg, max(gf, gg))
    if isinstance(e, Mul):
        (df, hf, gf), (dg, hg, gg) = bounds(e.f), bounds(e.g)
        return (df * dg, hf * hg, gf + gg)
    if isinstance(e, Pow):
        d, h, g = bounds(e.f)
        return (d ** e.n, h ** e.n, e.n * g)
    if isinstance(e, Threshold):
        d, h, g = bounds(e.f)
        return ((2 * d) ** e.n, (2 * (d + h)) ** e.n, e.n * g)
    raise TypeError(e)


# Raw numerators. Lean keeps repeated exponents as separate summands; combining
# them here changes neither the value nor the validity of the bounds.

def raw_add(P, Q):
    R = dict(P)
    for v, c in Q.items():
        R[v] = R.get(v, 0) + c
    return {v: c for v, c in R.items() if c}


def raw_scale(a, P):
    return {v: a * c for v, c in P.items() if a * c}


def raw_mul(P, Q):
    R = {}
    for v, c in P.items():
        for w, c2 in Q.items():
            u = tuple(a + b for a, b in zip(v, w))
            R[u] = R.get(u, 0) + c * c2
    return {v: c for v, c in R.items() if c}


def raw_pow(P, n, d):
    R = {tuple([0] * d): 1}
    for _ in range(n):
        R = raw_mul(R, P)
    return R


def raw_tail(P, D, n, k, d):
    """`Raw.tail`: sum over i >= k of C(n,i) (D+P)^i (D-P)^(n-i)."""
    zero = tuple([0] * d)
    A = raw_add({zero: D}, P)
    B = raw_add({zero: D}, raw_scale(-1, P))
    R = {}
    for i in range(k, n + 1):
        R = raw_add(R, raw_scale(comb(n, i), raw_mul(raw_pow(A, i, d), raw_pow(B, n - i, d))))
    return R


def raw_geometric(j, stride, J, d):
    R = {}
    for i in range(J):
        v = tuple((-stride * i if t == j else 0) for t in range(d))
        R[v] = R.get(v, 0) + 2 ** i
    return R


def raw_project(P, j, m):
    R = {}
    for v, c in P.items():
        if v[j] % m == 0:
            u = tuple((0 if t == j else a) for t, a in enumerate(v))
            R[u] = R.get(u, 0) + c
    return {v: c for v, c in R.items() if c}


def expand(e, d):
    """`Expr.expand`, with like terms combined."""
    if isinstance(e, Scalar):
        return {tuple([0] * d): e.p} if e.p else {}
    if isinstance(e, Monomial):
        return {tuple(e.v): 1}
    if isinstance(e, Geometric):
        return raw_geometric(e.j, e.stride, e.J, d)
    if isinstance(e, Neg):
        return raw_scale(-1, expand(e.f, d))
    if isinstance(e, Project):
        return raw_project(expand(e.f, d), e.j, e.m)
    if isinstance(e, Add):
        return raw_add(raw_scale(bounds(e.g)[0], expand(e.f, d)),
                       raw_scale(bounds(e.f)[0], expand(e.g, d)))
    if isinstance(e, Mul):
        return raw_mul(expand(e.f, d), expand(e.g, d))
    if isinstance(e, Pow):
        return raw_pow(expand(e.f, d), e.n, d)
    if isinstance(e, Threshold):
        return raw_tail(expand(e.f, d), bounds(e.f)[0], e.n, e.k, d)
    raise TypeError(e)


def raw_value(P, x):
    """`rawValue P x` for rational coordinates x."""
    total = Fraction(0)
    for v, c in P.items():
        term = Fraction(c)
        for xi, a in zip(x, v):
            term *= Fraction(xi) ** a
        total += term
    return total


def expr_value(e, x):
    """`exprValue e x = rawValue e.expand x / e.bounds.denominator`."""
    return raw_value(expand(e, len(x)), x) / bounds(e)[0]


# ---------------------------------------------------------------------------
# 2. Lean's scalar recipe, transcribed with rationals (ground truth for §3)
# ---------------------------------------------------------------------------

def shift_bound(G, m):
    """`shiftBound G m = m*((max G 1 - 1)/m + 1)`."""
    return m * ((max(G, 1) - 1) // m + 1)


def clear_factor(p, q, G):
    return prod((pi * qi) ** G for pi, qi in zip(p, q))


def specialized_height(p, q, H, G):
    return H * prod(max(pi, qi) ** (2 * G) for pi, qi in zip(p, q))


def radix(p, q, H, G, b):
    return 4 * (specialized_height(p, q, H, G) * (2 * b + 1)) + 5


def nearest_int(v, d):
    return (2 * v + d) // (2 * d)


def centered_int(v, z):
    return v - z * nearest_int(v, z)


def extract_coefficient_int(value, z, k):
    return centered_int(nearest_int(value, z ** k), z)


def scalar_recipe_lean(p, q, D, H, G, m, child):
    """`ScalarProjection.scalarRecipe`, verbatim (child : ℕ → ℚ)."""
    b = shift_bound(G, m)
    z = radix(p, q, H, G, b)
    C = clear_factor(p, q, G)
    n = 2 * b // m + 1
    v = floor(Fraction(C) * Fraction(z) ** b * (D * child(z)))
    return Fraction(extract_coefficient_int(v * ((z ** (m * n) - 1) // (z ** m - 1)), z, 2 * b), C * D)


# ---------------------------------------------------------------------------
# 3. Machines: the only operations a fixed scalar program may use
# ---------------------------------------------------------------------------

class Machine:
    """Integer semantics of the certified operations, recording `Term.peak`."""

    def __init__(self):
        self.peak = 0
        self.ops = 0

    def _see(self, v):
        self.peak = max(self.peak, signed_bits(v))
        self.ops += 1
        return v

    def lit(self, z):
        self.peak = max(self.peak, signed_bits(z))
        return z

    def add(self, a, b):
        return self._see(a + b)

    def sub(self, a, b):
        return self._see(a - b)

    def mul(self, a, b):
        return self._see(a * b)

    def div(self, a, b):
        """`positiveDiv a b = if 0 < b then a / b else 0` (floor division)."""
        return self._see(a // b if b > 0 else 0)

    def pow(self, a, b):
        """`signedPower`: `a ^ b.toNat`."""
        return self._see(a ** max(b, 0))

    def log2(self, a):
        """Proposed new operation: `Nat.log2 a.toNat` (0 for a <= 1)."""
        return self._see(max(a, 0).bit_length() - 1 if a >= 1 else 0)


class Term:
    """`ScalarProgram.Term`: a fixed tree of binary integer operations.

    `size` is the number of nodes of the tree (Lean's `Term` has no sharing; subterms are
    shared here only to save memory). `small` and `tame` are the two syntactic classes of
    the blueprint, computed when the node is built:

      Small: inputs, literals, and value-tame operations (+, -, *, positive division, log2)
             applied to Small terms.  Their values stay polynomial in the inputs.
      Tame:  Small terms; bit-tame operations (+, -, *, positive division) applied to Tame
             terms; and powers with a Tame base and a Small exponent.  Their bit lengths
             stay polynomial in the inputs.
    """
    __slots__ = ("kind", "op", "l", "r", "payload", "size", "small", "tame")

    VALUE_TAME = ("add", "sub", "mul", "div", "log2")
    BIT_TAME = ("add", "sub", "mul", "div")

    def __init__(self, kind, op=None, l=None, r=None, payload=None):
        self.kind, self.op, self.l, self.r, self.payload = kind, op, l, r, payload
        if kind != "app":
            self.size, self.small, self.tame = 1, True, True
        else:
            self.size = 1 + l.size + r.size
            self.small = op in Term.VALUE_TAME and l.small and r.small
            self.tame = self.small or (op in Term.BIT_TAME and l.tame and r.tame) or (
                op == "pow" and l.tame and r.small)

    def run(self, env, machine, memo):
        """Returns `Term.run`; `machine.peak` accumulates `Term.peak`."""
        key = id(self)
        if key in memo:
            return memo[key]
        if self.kind == "in":
            val = machine.lit(env[self.payload])
        elif self.kind == "lit":
            val = machine.lit(self.payload)
        else:
            a = self.l.run(env, machine, memo)
            b = self.r.run(env, machine, memo)
            val = machine.log2(a) if self.op == "log2" else getattr(machine, self.op)(a, b)
        memo[key] = val
        return val


class Builder:
    """Same interface as `Machine`, but builds a `Term` instead of computing."""

    def __init__(self):
        self._lits = {}
        self._inputs = {}
        self.created = 0          # operation nodes created (a program with sharing)

    def inp(self, name):
        if name not in self._inputs:
            self._inputs[name] = Term("in", payload=name)
        return self._inputs[name]

    def lit(self, z):
        if z not in self._lits:
            self._lits[z] = Term("lit", payload=z)
        return self._lits[z]

    def _app(self, op, a, b):
        self.created += 1
        return Term("app", op, a, b)

    def add(self, a, b):
        return self._app("add", a, b)

    def sub(self, a, b):
        return self._app("sub", a, b)

    def mul(self, a, b):
        return self._app("mul", a, b)

    def div(self, a, b):
        return self._app("div", a, b)

    def pow(self, a, b):
        return self._app("pow", a, b)

    def log2(self, a):
        return self._app("log2", a, a)


# ---------------------------------------------------------------------------
# 4. Derived operations, written once for both machines
# ---------------------------------------------------------------------------

def positive(M, a):
    """[a > 0] as 0/1:  positiveDiv a a."""
    return M.div(a, a)


def absolute(M, a):
    """|a| = a * (2*[a>0] - 1)."""
    return M.mul(a, M.sub(M.mul(M.lit(2), positive(M, a)), M.lit(1)))


def nearest(M, v, d):
    """`Extraction.nearest v d = (2*v+d)/(2*d)` (d > 0 wherever it is used)."""
    return M.div(M.add(M.mul(M.lit(2), v), d), M.mul(M.lit(2), d))


def centered(M, v, z):
    """`Extraction.centered v z = v - z * nearest v z`."""
    return M.sub(v, M.mul(z, nearest(M, v, z)))


def extract_coefficient(M, value, z, k):
    """`Extraction.extractCoefficient value z k`."""
    return centered(M, nearest(M, value, M.pow(z, k)), z)


def tail_numerator(M, a, b, d, k):
    """`TailRadix.tailNumerator a b d k`, verbatim:
    H = (2+|a|+|b|)^d, z = 8H+3, centered (nearest ((b+a z)^d) (z^k)) (z-1)."""
    H = M.pow(M.add(M.add(M.lit(2), absolute(M, a)), absolute(M, b)), d)
    z = M.add(M.mul(M.lit(8), H), M.lit(3))
    return centered(M, nearest(M, M.pow(M.add(b, M.mul(a, z)), d), M.pow(z, k)), M.sub(z, M.lit(1)))


def geom_sum(M, y, J):
    """sum_{i<J} 2^i y^(J-i), for every integer y and J >= 0, without branching:
    y*(y^J-2^J)/(y-2) when y != 2, and J*2^J when y = 2."""
    s = M.sub(y, M.lit(2))
    s2 = M.mul(s, s)
    nonzero = positive(M, s2)                                   # [y != 2]
    main = M.div(M.mul(M.mul(M.sub(M.pow(y, J), M.pow(M.lit(2), J)), y), s), s2)
    special = M.mul(M.sub(M.lit(1), nonzero), M.mul(J, M.pow(M.lit(2), J)))
    return M.add(main, special)


def choose_from_power(M, n, k):
    """`TailRadix.choose_from_power`: C(n,k) = ((1+R)^n / R^k) % R with R = 2^(n+1)."""
    R = M.pow(M.lit(2), M.add(n, M.lit(1)))
    t = M.div(M.pow(M.add(M.lit(1), R), n), M.pow(R, k))
    return M.sub(t, M.mul(R, M.div(t, R)))


# ---------------------------------------------------------------------------
# 5. The proposed evaluator
# ---------------------------------------------------------------------------

def eval_bounds(M, e):
    """`Expr.evalBounds` (blueprint): the exact denominator of `Expr.bounds`, and
    over-estimates of height and radius that need only +, * and ^."""
    cache = M.__dict__.setdefault("_bounds_cache", {})
    hit = cache.get(id(e))
    if hit is None:
        hit = (e, _eval_bounds(M, e))          # keep `e` alive so that its id stays unique
        cache[id(e)] = hit
    return hit[1]


def _eval_bounds(M, e):
    if isinstance(e, Scalar):
        return (e.q, M.add(M.mul(e.p, e.p), M.lit(1)), M.lit(0))
    if isinstance(e, Monomial):
        return (M.lit(1), M.lit(1), M.lit(sum(abs(a) for a in e.v)))
    if isinstance(e, Geometric):
        return (M.lit(1), M.pow(M.lit(2), e.J), M.mul(e.J, e.stride))
    if isinstance(e, (Neg, Project)):
        return eval_bounds(M, e.f)
    if isinstance(e, Add):
        (df, hf, gf), (dg, hg, gg) = eval_bounds(M, e.f), eval_bounds(M, e.g)
        return (M.mul(df, dg), M.add(M.mul(dg, hf), M.mul(df, hg)), M.add(gf, gg))
    if isinstance(e, Mul):
        (df, hf, gf), (dg, hg, gg) = eval_bounds(M, e.f), eval_bounds(M, e.g)
        return (M.mul(df, dg), M.mul(hf, hg), M.add(gf, gg))
    if isinstance(e, Pow):
        d, h, g = eval_bounds(M, e.f)
        return (M.pow(d, e.n), M.pow(h, e.n), M.mul(e.n, g))
    if isinstance(e, Threshold):
        d, h, g = eval_bounds(M, e.f)
        two = M.lit(2)
        return (M.pow(M.mul(two, d), e.n), M.pow(M.mul(two, M.add(d, h)), e.n), M.mul(e.n, g))
    raise TypeError(e)


def product(M, xs):
    acc = M.lit(1)
    for a in xs:
        acc = M.mul(acc, a)
    return acc


def cleared_num(M, e, x):
    """`Expr.clearedNum e x` (blueprint).  For positive integer coordinates x,

        clearedNum e x = (prod x)^G~ * rawValue e.expand x,     G~ = (evalBounds e).radius,

    so that  exprValue e x = clearedNum e x / ((prod x)^G~ * e.bounds.denominator).
    Only ring operations, floor division by positive integers and natural powers occur."""
    if isinstance(e, Scalar):
        return e.p
    if isinstance(e, Monomial):
        G = sum(abs(a) for a in e.v)
        return product(M, [M.pow(xi, M.lit(G + a)) for xi, a in zip(x, e.v)])
    if isinstance(e, Geometric):
        G = M.mul(e.J, e.stride)
        others = product(M, [M.pow(xi, G) for i, xi in enumerate(x) if i != e.j])
        return M.mul(others, geom_sum(M, M.pow(x[e.j], e.stride), e.J))
    if isinstance(e, Neg):
        return M.sub(M.lit(0), cleared_num(M, e.f, x))
    if isinstance(e, Mul):
        return M.mul(cleared_num(M, e.f, x), cleared_num(M, e.g, x))
    if isinstance(e, Pow):
        return M.pow(cleared_num(M, e.f, x), e.n)
    X = product(M, x)
    if isinstance(e, Add):
        (df, _, gf), (dg, _, gg) = eval_bounds(M, e.f), eval_bounds(M, e.g)
        left = M.mul(M.mul(dg, M.pow(X, gg)), cleared_num(M, e.f, x))
        right = M.mul(M.mul(df, M.pow(X, gf)), cleared_num(M, e.g, x))
        return M.add(left, right)
    if isinstance(e, Threshold):
        d, _, g = eval_bounds(M, e.f)
        A = M.mul(M.pow(X, g), d)
        N = cleared_num(M, e.f, x)
        return tail_numerator(M, M.add(A, N), M.sub(A, N), e.n, e.k)
    if isinstance(e, Project):
        _, H, G = eval_bounds(M, e.f)
        m = e.m
        one, two = M.lit(1), M.lit(2)
        # b = shiftBound G m = m*((max G 1 - 1)/m + 1);   max G 1 - 1 = G - [G > 0]
        b = M.mul(m, M.add(M.div(M.sub(G, positive(M, G)), m), one))
        # z = radix x 1 H G b = 4*(H * X^(2G) * (2b+1)) + 5
        z = M.add(M.mul(M.lit(4), M.mul(M.mul(H, M.pow(X, M.mul(two, G))),
                                        M.add(M.mul(two, b), one))), M.lit(5))
        child = cleared_num(M, e.f, [z if i == e.j else xi for i, xi in enumerate(x)])
        # v = clearFactor * z^b * D * child(z) = x_j^G * z^(b-G) * clearedNum f x[j:=z]
        v = M.mul(M.mul(M.pow(x[e.j], G), M.pow(z, M.sub(b, G))), child)
        n = M.add(M.div(M.mul(two, b), m), one)
        kernel = M.div(M.sub(M.pow(z, M.mul(m, n)), one), M.sub(M.pow(z, m), one))
        return extract_coefficient(M, M.mul(v, kernel), z, M.mul(two, b))
    raise TypeError(e)


def evaluate_at_one(M, e, d):
    """Numerator and denominator of `scalarAtOne e`: clearedNum e 1 and bounds.denominator."""
    ones = [M.lit(1)] * d
    return cleared_num(M, e, ones), eval_bounds(M, e)[0]


# ---------------------------------------------------------------------------
# 6. Tests
# ---------------------------------------------------------------------------

class TooBig(Exception):
    """A random draw whose brute-force expansion would be too expensive."""


def random_leaf(rng, d):
    r = rng.random()
    if r < 0.5:
        return Monomial(tuple(rng.randint(-2, 2) for _ in range(d)))
    if r < 0.75:
        return Scalar(rng.choice([-3, -2, -1, 1, 2, 3, 0]), rng.randint(1, 3))
    return Geometric(rng.randrange(d), rng.choice([1, 1, 2, 0]), rng.choice([1, 2, 3, 3, 0]))


def random_sum(rng, d):
    """A few weighted leaves, so that expansions start with several distinct exponents."""
    e = random_leaf(rng, d)
    for _ in range(rng.randint(1, 3)):
        t = random_leaf(rng, d)
        if rng.random() < 0.5:
            t = Mul(Scalar(rng.choice([-2, -1, 1, 2, 3]), rng.randint(1, 2)), t)
        e = Add(e, t)
    return e


def random_expr(rng, d, depth, allow_project=True):
    """A random expression over all nine constructors. Degenerate parameters (degree 0,
    empty threshold, empty geometric sum, zero scalar) occur with small probability."""
    if depth <= 0:
        return random_sum(rng, d) if rng.random() < 0.8 else random_leaf(rng, d)
    kinds = ["add"] * 3 + ["mul"] * 2 + ["neg", "pow", "sum"] + ["threshold"] * 2
    if allow_project:
        kinds += ["project"] * 3
    kind = rng.choice(kinds)

    def sub():
        return random_expr(rng, d, depth - 1, allow_project)

    if kind == "sum":
        return random_sum(rng, d)
    if kind == "add":
        return Add(sub(), sub())
    if kind == "mul":
        return Mul(sub(), sub())
    if kind == "neg":
        return Neg(sub())
    if kind == "pow":
        return Pow(sub(), rng.choice([1, 2, 2, 3, 0]))
    if kind == "threshold":
        n = rng.choice([1, 2, 2, 3, 0])
        return Threshold(sub(), n, n + 1 if rng.random() < 0.1 else rng.randint(0, n))
    return Project(sub(), rng.randrange(d), rng.choice([1, 2, 2, 3, 4]))


def checked_expand(e, d, limit=1500, trace=None):
    """`expand`, refusing draws whose intermediate expansions exceed `limit` terms.
    `trace` collects the size of every sub-expansion, and for projections how many
    terms went in and how many survived."""
    if isinstance(e, (Scalar, Monomial, Geometric)):
        return expand(e, d)
    if isinstance(e, Neg):
        P = raw_scale(-1, checked_expand(e.f, d, limit, trace))
    elif isinstance(e, Project):
        A = checked_expand(e.f, d, limit, trace)
        P = raw_project(A, e.j, e.m)
        if trace is not None:
            trace.append(("project", len(A), len(P)))
    elif isinstance(e, Add):
        P = raw_add(raw_scale(bounds(e.g)[0], checked_expand(e.f, d, limit, trace)),
                    raw_scale(bounds(e.f)[0], checked_expand(e.g, d, limit, trace)))
    elif isinstance(e, Mul):
        A, B = checked_expand(e.f, d, limit, trace), checked_expand(e.g, d, limit, trace)
        if len(A) * len(B) > 40 * limit:
            raise TooBig
        P = raw_mul(A, B)
    elif isinstance(e, Pow):
        A = checked_expand(e.f, d, limit, trace)
        if len(A) ** max(e.n, 1) > 40 * limit:
            raise TooBig
        P = raw_pow(A, e.n, d)
    else:
        A = checked_expand(e.f, d, limit, trace)
        if (len(A) + 1) ** max(e.n, 1) > 40 * limit:
            raise TooBig
        P = raw_tail(A, bounds(e.f)[0], e.n, e.k, d)
    if len(P) > limit:
        raise TooBig
    if trace is not None:
        trace.append(("node", len(P), len(P)))
    return P


def estimated_bits(e, coordinate_bits):
    """Rough bit length of the largest number the evaluator forms for `e` when the
    coordinates have `coordinate_bits` bits in total. Used only to keep the random
    tests fast: nested projections multiply the size by about twice the radius."""
    if isinstance(e, (Scalar, Monomial, Geometric)):
        return 0
    if isinstance(e, Project):
        D, H, G = eval_bounds(Machine(), e.f)
        z_bits = H.bit_length() + 2 * G * coordinate_bits + 16
        here = (4 * G + 2 * e.m + 2) * z_bits
        return max(here, estimated_bits(e.f, coordinate_bits + z_bits))
    if isinstance(e, Threshold):
        D, H, G = eval_bounds(Machine(), e.f)
        a_bits = H.bit_length() + D.bit_length() + 2 * G * coordinate_bits + 2
        return max(e.n * (e.n * a_bits + 8), estimated_bits(e.f, coordinate_bits))
    if isinstance(e, (Neg, Pow)):
        return estimated_bits(e.f, coordinate_bits)
    return max(estimated_bits(e.f, coordinate_bits), estimated_bits(e.g, coordinate_bits))


def draw(rng, depth, budget_bits=3_000_000, max_nesting=2, allow_project=True):
    """Draw expressions until one is small enough for brute force. Returns
    (d, e, expansion, evalBounds, trace of sub-expansions, number of rejected draws)."""
    rejected = 0
    while True:
        d = rng.randint(1, 3)
        e = random_expr(rng, d, depth, allow_project)
        if count_projects(e) <= max_nesting and estimated_bits(e, 3 * d) <= budget_bits:
            try:
                trace = []
                P = checked_expand(e, d, trace=trace)
                return d, e, P, eval_bounds(Machine(), e), trace, rejected
            except TooBig:
                pass
        rejected += 1


def expr_nodes(e):
    if isinstance(e, (Scalar, Monomial, Geometric)):
        return 1
    if isinstance(e, (Neg, Pow, Threshold, Project)):
        return 1 + expr_nodes(e.f)
    return 1 + expr_nodes(e.f) + expr_nodes(e.g)


def count_projects(e):
    """Largest number of nested projections."""
    if isinstance(e, (Scalar, Monomial, Geometric)):
        return 0
    if isinstance(e, Project):
        return 1 + count_projects(e.f)
    if isinstance(e, (Neg, Pow, Threshold)):
        return count_projects(e.f)
    return max(count_projects(e.f), count_projects(e.g))


def median(values):
    return sorted(values)[len(values) // 2]


def test_bounds_dominate(trials, seed):
    """evalBounds: same denominator, larger height and radius than Expr.bounds."""
    rng = random.Random(seed)
    M = Machine()
    for _ in range(trials):
        d = rng.randint(1, 3)
        e = random_expr(rng, d, 3)
        D, H, G = bounds(e)
        D2, H2, G2 = eval_bounds(M, e)
        assert D2 == D and H2 >= H and G2 >= G, e
    return trials


def test_cleared_num(trials, seed, depths=(2, 3, 3, 4)):
    """clearedNum e x = (prod x)^G~ * rawValue e.expand x, and |clearedNum| <= H~ (prod x)^(2G~)."""
    rng = random.Random(seed)
    st = dict(trials=trials, rejected=0, with_projection=0, nested=0, filtering=0, nodes=[],
              widest=[], peak=0, nonzero=0)
    for _ in range(trials):
        d, e, P, (D, H, G), trace, rejected = draw(rng, rng.choice(depths))
        x = [rng.choice([1, 1, 2, 3, 5]) for _ in range(d)]
        M = Machine()
        N = cleared_num(M, e, x)
        X = prod(x)
        truth = Fraction(X) ** G * raw_value(P, x)
        assert truth.denominator == 1, (e, x)
        assert N == truth.numerator, (e, x, N, truth)
        assert abs(N) <= H * X ** (2 * G), (e, x)
        assert Fraction(N, X ** G * D) == raw_value(P, x) / bounds(e)[0], (e, x)
        st["rejected"] += rejected
        st["with_projection"] += count_projects(e) > 0
        st["nested"] += count_projects(e) > 1
        st["filtering"] += any(kind == "project" and 0 < kept < before for kind, before, kept in trace)
        st["nodes"].append(expr_nodes(e))
        st["widest"].append(max([before for _, before, _ in trace], default=len(P)))
        st["peak"] = max(st["peak"], M.peak)
        st["nonzero"] += N != 0
    return st


def test_recipe_transcription(trials, seed):
    """Lean's `scalarRecipe` (rational, with floor) agrees with the projection, both with the
    bounds of `Expr.bounds` (theorem `scalarRecipe_expr`) and with the over-estimates."""
    rng = random.Random(seed)
    terms = []
    for _ in range(trials):
        d, f, P, (D2, H2, G2), _, _ = draw(rng, rng.choice((2, 3)), budget_bits=400_000, allow_project=False)
        D, H, G = bounds(f)
        j, m = rng.randrange(d), rng.randint(1, 5)
        p = [rng.choice([1, 2, 3, 4]) for _ in range(d)]
        q = [rng.choice([1, 1, 2, 3]) for _ in range(d)]
        pt = [Fraction(a, b) for a, b in zip(p, q)]

        def child(z):
            return raw_value(P, [Fraction(z) if i == j else t for i, t in enumerate(pt)]) / D

        target = raw_value(raw_project(P, j, m), pt) / D
        assert scalar_recipe_lean(p, q, D, H, G, m, child) == target, (f, j, m, p, q)
        assert scalar_recipe_lean(p, q, D2, H2, G2, m, child) == target, (f, j, m, p, q)
        terms.append(len(P))
    return trials, median(terms), max(terms)


def test_small_helpers():
    M = Machine()
    for a in range(-6, 7):
        assert positive(M, a) == (1 if a > 0 else 0)
        assert absolute(M, a) == abs(a)
    for y in range(-4, 9):
        for J in range(0, 7):
            assert geom_sum(M, y, J) == sum(2 ** i * y ** (J - i) for i in range(J)), (y, J)
    for n in range(0, 14):
        for k in range(0, n + 1):
            assert choose_from_power(M, n, k) == comb(n, k)
    for a in range(-5, 6):
        for b in range(-5, 6):
            for d in range(0, 5):
                for k in range(0, d + 2):
                    want = sum(a ** i * b ** (d - i) * comb(d, i) for i in range(k, d + 1))
                    assert tail_numerator(M, a, b, d, k) == want, (a, b, d, k)
    for G in range(0, 12):
        for m in range(1, 7):
            b = m * ((G - (1 if G > 0 else 0)) // m + 1)
            assert b == shift_bound(G, m) and b >= G and b % m == 0
    return True


# --- parameters of the actual construction (ConcreteGrid / GridLogic / FormulaOperations) ---

def lean_radius(U):
    return max(2, U)


def lean_size(U):
    B = lean_radius(U)
    return 4 * (2 * B + 1) * (2 * B + 2) ** 30


def lean_J(U):
    return 2 * lean_radius(U) + 1


def lean_stride(U):
    return 4 * (2 * lean_radius(U) + 2) ** 30


def lean_precision(U):
    s = lean_size(U)
    return 100 * ((2 * lean_radius(U) + 1) + 10 * ((s.bit_length() - 1) + 1) + 20)


def lean_half_degree(U):
    s = lean_size(U)
    return 2 ** 15 * s ** 8 * (lean_precision(U) + 20 * ((s.bit_length() - 1) + 1) + 100)


def parameter_terms(M, U):
    """The numerical parameters as fixed terms in the input U (valid for U >= 1)."""
    lit = M.lit

    def power_literal(a, n):          # a^n for a fixed n, by repeated multiplication (stays Small)
        acc = lit(1)
        for _ in range(n):
            acc = M.mul(acc, a)
        return acc

    radius = M.add(U, M.div(lit(1), U))                       # max 2 U = U + [U = 1]
    twoB2 = M.add(M.mul(lit(2), radius), lit(2))
    J = M.add(M.mul(lit(2), radius), lit(1))
    stride = M.mul(lit(4), power_literal(twoB2, 30))
    size = M.mul(J, stride)                                   # 4*(2B+1)*(2B+2)^30
    logsize1 = M.add(M.log2(size), lit(1))
    precision = M.mul(lit(100), M.add(M.add(J, M.mul(lit(10), logsize1)), lit(20)))
    half = M.mul(M.mul(lit(2 ** 15), power_literal(size, 8)),
                 M.add(M.add(precision, M.mul(lit(20), logsize1)), lit(100)))
    return dict(U=U, radius=radius, J=J, stride=stride, size=size, precision=precision, halfDegree=half)


def pi_rational_terms(M, n):
    """Numerator and denominator (not reduced) of `piRational n = 16^n / (n * C(2n,n)^2)`."""
    c = choose_from_power(M, M.mul(M.lit(2), n), n)
    return M.pow(M.lit(16), n), M.mul(n, M.mul(c, c))


def test_parameter_terms():
    B = Builder()
    terms = parameter_terms(B, B.inp("U"))
    lean = dict(radius=lean_radius, J=lean_J, stride=lean_stride, size=lean_size,
                precision=lean_precision, halfDegree=lean_half_degree)
    values = list(range(1, 40)) + [100, 1000, 12345, 10 ** 6]
    for U in values:
        for name, f in lean.items():
            got = terms[name].run({"U": U}, Machine(), {})
            assert got == f(U), (name, U)
    for name in lean:
        assert terms[name].small, name                      # usable as exponents
    # Wallis constant: correct for small arguments, and Tame when the argument is size^4
    for n in range(1, 25):
        num, den = pi_rational_terms(Machine(), n)
        assert Fraction(num, den) == Fraction(16 ** n, n * comb(2 * n, n) ** 2)
    n_term = B.mul(B.mul(terms["size"], terms["size"]), B.mul(terms["size"], terms["size"]))
    num, den = pi_rational_terms(B, n_term)
    assert n_term.small and num.tame and den.tame
    assert not num.small                                    # a power, so not an index term
    return len(values), {k: v.size for k, v in terms.items() if k != "U"}


# --- a fixed program for a family of expressions, as in PackedScalarPrograms ---

def toy_family(Mx, U, t):
    """A small expression with the same ingredients as `packedExpr`: U- and t-dependent
    scalars, exponents, threshold degrees, a geometric kernel and two nested cyclic
    projections. `Mx` is a Machine (U, t integers) or a Builder (U, t input terms)."""
    lit = Mx.lit
    m = Mx.add(U, lit(2))                                   # period
    n = Mx.add(Mx.mul(lit(2), U), lit(1))                   # threshold degree 2U+1
    k = Mx.add(U, lit(1))
    cos0 = Mul(Scalar(lit(1), lit(2)), Add(Monomial((1, 0)), Monomial((-1, 0))))
    x0 = Add(Scalar(t, lit(1)), Mul(Scalar(lit(-1), Mx.add(U, lit(3))), cos0))
    gate = Threshold(Mul(x0, Scalar(lit(1), Mx.add(Mx.mul(lit(2), U), lit(4)))), n, k)
    inner = Project(Mul(gate, Pow(Monomial((1, 1)), lit(2))), 0, m)
    carrier = Mul(Pow(Monomial((0, 1)), Mx.add(U, lit(1))), Geometric(1, lit(1), Mx.add(U, lit(1))))
    return Project(Mul(Add(inner, Scalar(lit(1), lit(3))), carrier), 1, m)


def test_fixed_program(schedule, brute_force_up_to, cross_check_up_to):
    """`schedule` is a list of (U, list of t). One pair of terms is built once and then run."""
    B = Builder()
    num_t, den_t = evaluate_at_one(B, toy_family(B, B.inp("U"), B.inp("t")), 2)
    assert num_t.tame and den_t.tame, "the fixed program must be Tame"
    rows = []
    for U, ts in schedule:
        peak_U = 0
        for t in ts:
            Mrun = Machine()
            memo = {}
            num = num_t.run({"U": U, "t": t}, Mrun, memo)
            den = den_t.run({"U": U, "t": t}, Mrun, memo)
            assert den > 0
            if U <= cross_check_up_to:
                # the same expression with integer parameters, evaluated without terms
                Mi = Machine()
                e = toy_family(Mi, U, t)
                assert (num, den) == evaluate_at_one(Mi, e, 2)
                if U <= brute_force_up_to:
                    assert Fraction(num, den) == expr_value(e, [Fraction(1), Fraction(1)]), (U, t)
            peak_U = max(peak_U, Mrun.peak)
        rows.append((U, peak_U))
    return num_t.size + den_t.size, B.created, rows


# --- the same leaves replaced by unreduced fractions (plan, step R5) ---

def unreduce(rng, e):
    if isinstance(e, Scalar):
        c = rng.randint(1, 4)
        return Scalar(e.p * c, e.q * c)
    if isinstance(e, (Monomial, Geometric)):
        return e
    if isinstance(e, Neg):
        return Neg(unreduce(rng, e.f))
    if isinstance(e, Pow):
        return Pow(unreduce(rng, e.f), e.n)
    if isinstance(e, Threshold):
        return Threshold(unreduce(rng, e.f), e.n, e.k)
    if isinstance(e, Project):
        return Project(unreduce(rng, e.f), e.j, e.m)
    return type(e)(unreduce(rng, e.f), unreduce(rng, e.g))


def test_scalar_equivalence(trials, seed):
    """Replacing scalar leaves by equal, unreduced fractions never changes `exprValue`
    (it does change `Expr.bounds`). This is what lets the evaluator skip gcds."""
    rng = random.Random(seed)
    changed = 0
    for _ in range(trials):
        d, e, P, _, _, _ = draw(rng, rng.choice((3, 4)), budget_bits=10 ** 12, max_nesting=4)
        e2 = unreduce(rng, e)
        x = [Fraction(rng.randint(1, 5), rng.randint(1, 3)) for _ in range(d)]
        assert raw_value(P, x) / bounds(e)[0] == expr_value(e2, x), (e, x)
        changed += bounds(e) != bounds(e2)
    return trials, changed


# ---------------------------------------------------------------------------
# 7. The actual expression `packedExpr φ t`, built symbolically
# ---------------------------------------------------------------------------

class RQ:
    """A rational constant kept as an unreduced pair of terms with positive denominator."""
    __slots__ = ("M", "num", "den")

    def __init__(self, M, num, den):
        self.M, self.num, self.den = M, num, den

    def __mul__(self, o):
        return RQ(self.M, self.M.mul(self.num, o.num), self.M.mul(self.den, o.den))

    def __truediv__(self, o):                 # only used with o > 0
        return RQ(self.M, self.M.mul(self.num, o.den), self.M.mul(self.den, o.num))

    def __add__(self, o):
        M = self.M
        return RQ(M, M.add(M.mul(self.num, o.den), M.mul(o.num, self.den)), M.mul(self.den, o.den))

    def __neg__(self):
        return RQ(self.M, self.M.sub(self.M.lit(0), self.num), self.den)

    def scalar(self):
        return Scalar(self.num, self.den)


def formula_depth(phi):
    """`FormulaLaurent.depth`."""
    tag = phi[0]
    if tag == "atom":
        return 0
    if tag == "neg":
        return formula_depth(phi[1])
    if tag in ("conj", "disj"):
        return max(formula_depth(phi[1]), formula_depth(phi[2]))
    return formula_depth(phi[1]) + 1          # ex, maj


def packed_expr(M, U, t, phi):
    """Mirror of FormulaLeaves, FormulaOperations, FormulaCompiler, KernelExpressions and
    KernelEvaluation: the expression `packedExpr φ t`, with every numerical parameter a
    value of the machine M (terms in U and t when M is a Builder) and every rational leaf
    an unreduced fraction. Returns (expression, number of coordinates)."""
    par = parameter_terms(M, U)
    radius, size, J, stride, half = par["radius"], par["size"], par["J"], par["stride"], par["halfDegree"]
    d = 4 + formula_depth(phi)
    lit = M.lit

    def qi(term):
        return RQ(M, term, lit(1))

    def ql(a, b=1):
        return RQ(M, lit(a), lit(b))

    size4 = M.mul(M.mul(size, size), M.mul(size, size))
    pi = RQ(M, *pi_rational_terms(M, size4))                 # piRational (size^4)

    def sub(a, b):
        return Add(a, Neg(b))

    def mono(j, s):
        return Monomial(tuple(s if i == j else 0 for i in range(d)))

    def cosine(j):
        return Mul(ql(1, 2).scalar(), Add(mono(j, 1), mono(j, -1)))

    leaf_cache = {}

    def x_leaf(j):
        if ("x", j) not in leaf_cache:
            leaf_cache[("x", j)] = Add(qi(radius).scalar(),
                                       Mul(((-qi(size)) / (ql(2) * pi)).scalar(), cosine(j)))
        return leaf_cache[("x", j)]

    def y_leaf(j):
        if ("y", j) not in leaf_cache:
            w = pi * (ql(2) * qi(radius) + ql(1)) / qi(size)
            leaf_cache[("y", j)] = Add((w * w / ql(4)).scalar(),
                                       Mul(ql(-1, 4).scalar(), Pow(cosine(j), lit(2))))
        return leaf_cache[("y", j)]

    n_thr, k_thr = M.add(M.mul(lit(2), half), lit(1)), M.add(half, lit(1))

    def tail(e):
        return Threshold(e, n_thr, k_thr)

    def and_expr(f, g):
        return tail(Mul(sub(Add(f, g), ql(3, 2).scalar()), ql(1, 4).scalar()))

    def or_expr(f, g):
        return tail(Mul(sub(Add(f, g), ql(1, 2).scalar()), ql(1, 4).scalar()))

    def normalize(x):
        return Mul(x, (ql(1) / (ql(8) * qi(size4))).scalar())

    def guard(x):
        return tail(normalize(Add(sub(sub(qi(U).scalar(), ql(1).scalar()), x), ql(1, 2).scalar())))

    def atom_expr(a, z):
        kind = a[0]
        if kind == "eqv":
            r = sub(z[a[1]], z[a[2]])
        elif kind == "leq":
            r = sub(z[a[2]], z[a[1]])
        elif kind == "add":
            r = sub(Add(z[a[1]], z[a[2]]), z[a[3]])
        else:
            r = sub(Mul(z[a[1]], z[a[2]]), z[a[3]])
        inner = Add(r, ql(1, 2).scalar()) if kind == "leq" else sub(ql(1, 4).scalar(), Pow(r, lit(2)))
        return tail(normalize(inner))

    def quant(j, k_term, child):
        guarded = and_expr(child, guard(x_leaf(j)))
        avg = Project(Mul(tail(y_leaf(j)), guarded), j, size)
        C = Mul((qi(size) / ql(2)).scalar(), avg)
        return tail(Mul(sub(sub(C, qi(k_term).scalar()), ql(1, 2).scalar()),
                        (ql(1) / (qi(size) + qi(U) + ql(2))).scalar()))

    def address(a):
        return qi(a[1]).scalar() if a[0] == "param" else x_leaf(a[1])

    def compile_formula(phi, r, s):
        tag = phi[0]
        if tag == "atom":
            return atom_expr(phi[1], [address(a) for a in r])
        if tag == "neg":
            return sub(ql(1).scalar(), compile_formula(phi[1], r, s))
        if tag == "conj":
            return and_expr(compile_formula(phi[1], r, s), compile_formula(phi[2], r, s))
        if tag == "disj":
            return or_expr(compile_formula(phi[1], r, s), compile_formula(phi[2], r, s))
        k_term = lit(0) if tag == "ex" else M.div(U, lit(2))
        return quant(s, k_term, compile_formula(phi[1], [("coord", s)] + r, s + 1))

    truth = and_expr(compile_formula(phi, [("coord", 0)] + [("param", ti) for ti in t], 4), guard(x_leaf(0)))

    def centered_expr(j):
        return sub(x_leaf(j), qi(radius).scalar())

    eq_residual = sub(sub(Mul(x_leaf(0), centered_expr(1)), Mul(qi(J).scalar(), centered_expr(2))),
                      centered_expr(3))
    L = tail(normalize(sub(ql(1, 4).scalar(), Pow(eq_residual, lit(2)))))

    def diff(j):
        return sub(mono(j, 1), mono(j, -1))

    S = tail(Mul(Mul(diff(1), diff(3)), ql(-1, 16).scalar()))
    carrier = Mul(Pow(mono(3, 1), stride), Geometric(1, stride, J))
    mask = truth
    for j in range(4):
        mask = Mul(mask, tail(y_leaf(j)))
    kernel = Mul(Mul(Mul(mask, L), S), carrier)
    avg = Project(Project(Project(Project(kernel, 3, size), 2, size), 1, size), 0, size)
    return Mul((qi(size4) / (ql(8) * qi(J))).scalar(), avg), d


SAMPLE_FORMULAS = {
    # the bound variable is slot 0; outer variables shift by one under each quantifier
    "MAJ x (x < j)": (0, ("maj", ("neg", ("atom", ("leq", 1, 0))))),
    "MAJ x EX y (y < x and y = j)": (0, ("maj", ("ex", ("conj", ("neg", ("atom", ("leq", 1, 0))),
                                                         ("atom", ("eqv", 0, 2)))))),
    "EX x (x + t = j or x * x = t)": (1, ("ex", ("disj", ("atom", ("add", 0, 2, 1)),
                                                 ("atom", ("mul", 0, 0, 2))))),
}


def test_real_programs():
    """Build the fixed numerator/denominator programs for the real `packedExpr` and check,
    syntactically, that they are Tame. (They cannot be run: 16^(size^4) is far too large.)"""
    rows = []
    for name, (k, phi) in SAMPLE_FORMULAS.items():
        B = Builder()
        U = B.inp("U")
        t = [B.inp(f"t{i}") for i in range(k)]
        e, d = packed_expr(B, U, t, phi)
        num, den = evaluate_at_one(B, e, d)
        assert num.tame and den.tame, name
        assert not num.small
        rows.append((name, d, expr_nodes(e), B.created, len(str(num.size + den.size))))
    return rows


def main(argv):
    quick = "--quick" in argv
    t0 = time.time()
    print("reference evaluator: tests of the plan for PackedScalarPrograms")
    test_small_helpers()
    print("  helpers (sign, |.|, geometric sum, binomial coefficient, tail numerator, shift): ok")
    print(f"  evalBounds dominates Expr.bounds on {test_bounds_dominate(400 if quick else 3000, 1)} "
          f"random expressions: ok")
    n, mid, top = test_recipe_transcription(40 if quick else 300, 2)
    print(f"  Lean scalarRecipe transcription = cyclic projection on {n} random cases "
          f"(median {mid}, up to {top} Laurent terms): ok")
    st = test_cleared_num(150 if quick else 1500, 3)
    print(f"  clearedNum = cleared Laurent value on {st['trials']} random expressions "
          f"({st['nonzero']} with a nonzero value): ok")
    print(f"    {st['with_projection']} with projections ({st['nested']} nested, {st['filtering']} where a "
          f"projection removes some terms and keeps others);")
    wide = sorted(st["widest"])
    print(f"    median {median(st['nodes'])} nodes (up to {max(st['nodes'])}); widest sub-expansion: median "
          f"{median(wide)}, 90th percentile {wide[(9 * len(wide)) // 10]}, largest {wide[-1]} Laurent terms;")
    print(f"    largest intermediate value {st['peak']} bits; {st['rejected']} oversized draws rejected")
    done, changed = test_scalar_equivalence(100 if quick else 600, 4)
    print(f"  unreduced scalar leaves leave exprValue unchanged on {done} random expressions "
          f"({changed} with different Expr.bounds): ok")
    count, sizes = test_parameter_terms()
    print(f"  parameter terms match the Lean definitions for {count} values of U: ok")
    print(f"    tree sizes: {sizes}")
    if quick:
        schedule = [(U, list(range(U))) for U in (1, 2, 3, 4, 5)]
    else:
        schedule = [(U, list(range(U))) for U in (1, 2, 3, 4, 5, 6)] + [(8, [0, 7]), (10, [9])]
    size, shared, rows = test_fixed_program(schedule, brute_force_up_to=3 if quick else 4,
                                            cross_check_up_to=6)
    print(f"  one fixed program evaluates the toy family for every (U, t) tested: ok")
    print(f"    {shared} operations with sharing, {size} nodes as a tree, Tame")
    print("    U:peak signed bits  " + "  ".join(f"{U}:{p}" for U, p in rows))
    if len(rows) >= 4:
        from math import log
        (U1, p1), (U2, p2) = rows[len(rows) // 2], rows[-1]
        print(f"    growth exponent between U={U1} and U={U2}: "
              f"{log(p2 / p1) / log((1 + U2) / (1 + U1)):.2f}  (polynomial, as the Tame lemma predicts)")
    for name, d, nodes, shared, digits in test_real_programs():
        print(f"  packedExpr for  {name}:  {d} coordinates, {nodes} expression nodes;")
        print(f"    fixed program: {shared} operations with sharing, a {digits}-digit number of tree nodes, Tame")
    print(f"all checks passed in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main(sys.argv[1:])
