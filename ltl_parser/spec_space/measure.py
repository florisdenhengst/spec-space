'''
Created on Sep 5, 2018

Module for measuring LTL formulas.

@author: Marten Lohstroh
'''

from sys import argv
from copy import deepcopy
from spec_space.parser.parser import LTL_PARSER
from spec_space.formula import TrueFormula, FalseFormula, Constant, Next, \
        VarNext, Disjunction, Conjunction, UnaryFormula, Literal, \
        BinaryFormula, Globally, Eventually;
from pyeda.boolalg.expr import expr, expr2dimacscnf
from subprocess import call, check_output


expr1 = None
expr2 = None
N = None

#def deepcopy(o):
#    return o

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
        f.index = f.index + n
        if (f.index > N):
             return FalseFormula() # FIXME: alternatively, leave this out and have a "soft" bound
    if isinstance(f, BinaryFormula):
        f.left_formula = shift(f.left_formula, n)
        f.right_formula = shift(f.right_formula, n)

    if isinstance(f, UnaryFormula):
        f.right_formula = shift(f.right_formula, n)

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

''' Apply Boolean reduction rules to formula. '''
def reduce(f):
    if isinstance(f, BinaryFormula):
        f.left_formula = reduce(f.left_formula)
        f.right_formula = reduce(f.right_formula)

        if isinstance(f, Conjunction):
            if isinstance(f.left_formula, FalseFormula) \
            or isinstance(f.right_formula, FalseFormula):
                return FalseFormula()
            if isinstance(f.left_formula, TrueFormula):
                return f.right_formula
            if isinstance(f.right_formula, TrueFormula):
                return f.left_formula
            if f.left_formula == f.right_formula: # FIXME: this won't work. NuSVM?
                return f.left_formula
            # FIXME:
            # A and ~A = 0
        if isinstance(f, Disjunction):
            if isinstance(f.left_formula, FalseFormula):
                if isinstance(f.right_formula, FalseFormula):
                    return FalseFormula()
                else:
                    return f.right_formula
            else:
                if isinstance(f.right_formula, FalseFormula):
                    return f.left_formula
            if (isinstance(f.left_formula, TrueFormula) \
            or isinstance(f.right_formula, TrueFormula)):
                return TrueFormula()
            if f.left_formula == f.right_formula: # FIXME: this won't work. NuSVM?
                return f.left_formula
            # FIXME:
            # A or ~A = 1

    #FIXME:
    # ~~A = A
    # A or ~AB = A or B
    if isinstance(f, UnaryFormula):
        reduce(f.right_formula)

    return f

''' Print a help message and exit. '''
def help_exit():
    print("Usage: python measure.py [TIME_BOUND] LTL_EXPR1 [LTL_EXPR2]")
    exit(1)

''' Read commandline arguments. '''
try:
    N = int(argv[1])
except Exception as e:
     help_exit()

try:
    expr1 = LTL_PARSER.parse(argv[2])
    if len(argv) > 3:
        expr2 = LTL_PARSER.parse(argv[3])
except Exception as e:
    help_exit()

if N == None or expr1 == None:
    help_exit()

f1 = expand(expr1)
#print(f1)
# f = expand(f)
# print(f)
print(f1.generate(with_base_names=False, ignore_precedence=True))
#print(f.generate(with_base_names=False, ignore_precedence=True))

#x = ""
x = expr("((tom0) & (maso1)) | (tom1)")
cnf = expr2dimacscnf(x.to_cnf())
print(cnf[1])
file = open('input.cnf', 'w')
file.write(str(cnf[1]))
file.close()

output = check_output(["bin/sharpSAT", "input.cnf"])
print(output.decode('UTF-8'))
# FIXME: peel out the number
# print(f.deps.assigned);
# print(f.update_deps())


#f = LTL_PARSER.parse("G(tom & maso)")
#f = LTL_PARSER.parse("F(G(tom & maso))")
#f = LTL_PARSER.parse("((tom | maso) & (tom | maso))") # FIXME: this exposes the renaming issue. It should not all be considered the same vars.
#f = LTL_PARSER.parse("G(tom & X tom)")
#f = LTL_PARSER.parse("G(tom & X tom)")
#f = LTL_PARSER.parse("F(G(tom & X(maso)))")
#f = LTL_PARSER.parse("a & false")
#f = LTL_PARSER.parse("a & XXXXa")