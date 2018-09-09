'''
Created on Sep 5, 2018

Module for measuring LTL formulas.

@author: Marten Lohstroh
'''

from sys import argv, setrecursionlimit
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

setrecursionlimit(100000)

# ''' Turn a formula into a conjunction with itself and a shifted copy of itself.'''
# def conj(f, n):
#     c = f
#     while (n < N):
#         n += 1
#         c = Conjunction(c, shift(deepcopy(f), n), True)

#     return c

# def disj(f, n):
#     d = f
#     while (n < N):
#         n += 1
#         d = Disjunction(d, shift(deepcopy(f), n), True)

#     return d

# ''' Shift all variable indices by one and return the formula. '''
# def shift(f, n):
#     if isinstance(f, Literal):
        
#         if (f.index + n > N):
#              return FalseFormula() # FIXME: alternatively, leave this out and have a "soft" bound
#     if isinstance(f, BinaryFormula):
#         f.left_formula = shift(f.left_formula, n)
#         f.right_formula = shift(f.right_formula, n)

#     if isinstance(f, UnaryFormula):
#         f.right_formula = shift(f.right_formula, n)

#     return f

''' Expand LTL formula into a Boolean expression, observing time bound N. 
This function returns a tuple holding a string representation of the expansion
and a set containing all the atomic propositions featured in the expression. '''
def expand(f, n):

    if isinstance(f, Literal):
        if (n > N):
            return ["false", set([])]
            
        else:
            name = f.generate(with_base_names=True) + "_" + str(n)
            return [name, set([name])]

    if isinstance(f, BinaryFormula):
        
        l, ldeps = expand(f.left_formula, n)
        r, rdeps = expand(f.right_formula, n)
        f.info['ldeps'] = ldeps
        f.info['rdeps'] = rdeps

        if isinstance(f, Conjunction):    
            if (l == "false" or r == "false"):
                f.info['expr'] = "false"
                return [f.info['expr'], set([])]    
            else:
                f.info['expr'] = "(" + l + " & " + r + ")"
                return [f.info['expr'], set(ldeps.union(rdeps))]
        elif isinstance(f, Disjunction):
            if (l == "false" and r == "false"):
                f.info['expr'] = "false"
                return [f.info['expr'], set([])]
            elif (l == "false"):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]    
            elif (r == "false"):
                f.info['expr'] = l
                return [f.info['expr'], ldeps]
            else:
                f.info['expr'] = "(" + l + " | " + r + ")"
                return [f.info['expr'], set(ldeps.union(rdeps))]
        elif isinstance(f, Implication):
            if (l == "false" or r == "true"):
                f.info['expr'] = "true"
                return [f.info['expr'], set([])]
            if (l == "true"):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]
            if (r == "false"):
                f.info['expr'] = "not " + l
                return [f.info['expr'], ldeps]
            else:
                f.info['expr'] = "(not" + l + " | " + r + ")"
                return [f.info['expr'], set(ldeps.union(rdeps))]
        else:
            throw("Error: cannot expand unsupported BinaryFormula!")
    else:
        if isinstance(f, Globally):
            conj = "true"
            deps = set([])
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e == "false":
                    return ["false", set([])]
                else:
                    conj += " & " + e
                    deps = deps.union(d)
                n += 1
                
            return [conj, deps]  
        elif isinstance(f, Eventually):
            disj = "false"
            deps = set([])
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e != "false":
                    disj += " | " + e 
                    deps = deps.union(d)
                n += 1
            return [disj, deps]
        elif isinstance(f, Next) or isinstance(f, VarNext):
            return expand(f.right_formula, n+1)
        else:
            return expand(f.right_formula, n)

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

f1, d1 = expand(expr1, 0)
print(d1)
print(f1)
exit()
#print(f1)
# f = expand(f)
# print(f)
#print(f1) # .generate(with_base_names=False, ignore_precedence=True)
#exit()
#print(f.generate(with_base_names=False, ignore_precedence=True))

#x = ""
cnf = expr2dimacscnf(expr(f1).to_cnf())
#print(cnf[1])
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