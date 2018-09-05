'''
Created on Sep 5, 2018

Module for measuring LTL formulas.

@author: Marten Lohstroh
'''

from spec_space.parser.parser import LTL_PARSER
from spec_space.formula import Next, VarNext, Disjunction, Conjunction, UnaryFormula, Literal, BinaryFormula, Globally, Eventually;
from copy import deepcopy

#f = LTL_PARSER.parse("G(tom & maso)")
f = LTL_PARSER.parse("F(G(tom & X(maso)))")

N = 3

''' Turn a formula into a conjunction with itself and a shifted copy of itself.'''
def conj(f, n):
    c = f
    while (n < N):
        n += 1
        c = Conjunction(c, shift(deepcopy(f), n), True)

    return c

def disj(f, n):
    d = f
    while (n < N):
        n += 1
        d = Disjunction(d, shift(deepcopy(f), n), True)

    return d

''' Shift all variable indices by one and return the formula. '''
def shift(f, n):
    if isinstance(f, Literal):
        f.index = f.index + n # FIXME: what if index is greater than N?
    if isinstance(f, BinaryFormula):
        shift(f.left_formula, n)
        shift(f.right_formula, n)
    if isinstance(f, UnaryFormula):
        shift(f.right_formula, n)
    return f    

''' Expand LTL formula into a Boolean expression, observing time bound N. '''
def expand(f):
    if isinstance(f, BinaryFormula):
        f.left_formula = expand(f.left_formula)
        f.right_formula = expand(f.right_formula)
    else:
        if isinstance(f, Globally):
            f = conj(expand(f.right_formula), 0)

        if isinstance(f, Eventually):
            f = disj(expand(f.right_formula), 0)

        if isinstance(f, Next) or isinstance(f, VarNext):
            f = expand(shift(f.right_formula, 1))
        # FIXME: add more temporal operators here

    return f

f = expand(f)
print(f.generate(with_base_names=False, ignore_precedence=True))
# print(f.deps.assigned);
# print(f.update_deps())
