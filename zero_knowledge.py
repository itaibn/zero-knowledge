"""
An implementation of a general zero-knowledge proof protocl for claims in NP

WARNING::
    DO NOT USE THIS IN ANY SECURITY-CRITICAL CODE. This code has not been tested
    and probably has many security vulnerabilities. In particular, it use sage's
    default random number generator, which probably is not suitable for
    cryptographic use.

Example Usage:

Generate a random set of quadratic equations over `F_2` and a prover for them::

    sage: instance, prover = make_random_instance(20, 10)

(This creates a set of 10 quadratic equations over 20 variables.)

Create an agent to interact with the prover::

    sage: verifier = Verifier(instance)

Conduct the verification protocol once (1/4 chance of catching cheaters).

    sage: verifier.interact_once(prover)
    True

Repeat the testing protocol 100 times (if the prover is not genuine, it would a
chance of less than 10^(-12) of getting away):

    sage: verifier.interact(prover, 100)
    True
"""

import hashlib
import random
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.modules.free_module import VectorSpace
from sage.quadratic_forms.quadratic_form import QuadraticForm
from sage.structure.sage_object import dumps

ZZ2 = IntegerModRing(2)

def hash_sage_object(x):
    return hashlib.sha512(dumps(x)).digest()

class Instance(object):
    def __init__(self, n, quad_forms, results):
        self.quad_forms = quad_forms
        self.domain_space = VectorSpace(ZZ2, n)
        self.range_space = VectorSpace(ZZ2, len(results))
        self.results = self.range_space(results)

    def __call__(self, vector):
        result = []
        for q in self.quad_forms:
            result.append(q(vector))
        return self.range_space(result)

    def partial_map(self, x, y):
        result = []
        for q in self.quad_forms:
            result.append(q(x + y) - q(x))
        return self.range_space(result)

    def check(self, solution):
        return self(solution) == self.results

class Prover(object):
    def __init__(self, instance, solution):
        if not instance.check(solution):
            raise ValueError, "The prover must be given a valid solution"
        self.instance = instance
        self.quad_forms = instance.quad_forms
        self.domain_space = instance.domain_space
        self.range_space = instance.range_space
        self.results = instance.results
        self.solution = self.domain_space(solution)
        self.step = 0

    def step0(self):
        if self.step != 0:
            raise Exception, "Wrong step"

        self.step = self.step + 1

        random = self.domain_space.random_element
        x = []
        x.append(random())
        x.append(random())
        x.append(self.solution - x[0] - x[1])
        self.x = x
        
        random = self.range_space.random_element
        c = []
        c.append(random())
        c.append(random())
        c.append(-c[0] - c[1])
        self.c = tuple(c)

        self.r = []
        for i in range(3):
            self.r.append(c[i] + self.instance.partial_map(x[i], x[i-1]))

        result = []
        result.append(hash_sage_object(self.c))
        for i in range(3):
            result.append(hash_sage_object(self.x[i]))
            result.append(hash_sage_object(self.r[i]))

        return result

    def step1(self, i):
        if self.step != 1:
            raise Exception, "Wrong step"
        self.step = 0

        if i < 3:
            return (self.x[i], self.x[i-1], self.c, self.r[i])
        elif i == 3:
            return self.r
        else:
            raise ValueError, "Challenge %d mus be a number from 0 to 3" % i

    def bilinear_map(self, x, y):
        result = []
        for q in self.quad_forms:
            result.append(q(x + y) - q(x))
        return self.range_space(result)

class Verifier(object):
    def __init__(self, instance):
        self.instance = instance

    def interact(self, prover, ntimes):
        for _ in range(ntimes):
            if not self.interact_once(prover):
                return False
        return True

    def interact_once(self, prover):
        h = prover.step0()
        hc = h[0]
        hx = h[1:7:2]
        hr = h[2:8:2]

        i = random.randint(0,3)
        if i < 3:
            xi, xim, c, ri = prover.step1(i)
            return hash_sage_object(xi) == hx[i] and \
                hash_sage_object(xim) == hx[i-1] and \
                hash_sage_object(c) == hc and \
                hash_sage_object(ri) == hr[i] and \
                xi in self.instance.domain_space and \
                xim in self.instance.domain_space and \
                c[0] in self.instance.range_space and \
                c[0] + c[1] + c[2] == 0 and \
                self.instance.partial_map(xi, xim) + c[i] == ri
        else:
            r = prover.step1(i)
            l = 0
            for j in range(3):
                if hash_sage_object(r[j]) != hr[j] or \
                    r[j] not in self.instance.range_space:
                    return False
                l = l + r[j]
            return l == self.instance.results

def make_random_instance(n, m):
    solution = VectorSpace(ZZ2, n).random_element()
    results = []
    quad_forms = []
    for _ in range(m):
        e = []
        for _ in range(n*(n+1)/2):
            e.append(ZZ2.random_element())
        quad_form = QuadraticForm(ZZ2, n, e)
        quad_forms.append(quad_form)
        results.append(quad_form(solution))
    instance = Instance(n, quad_forms, results)
    prover = Prover(instance, solution)
    return (instance, prover)
