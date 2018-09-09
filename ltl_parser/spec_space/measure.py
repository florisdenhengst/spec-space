'''
Created on Sep 5, 2018

Module for measuring LTL formulas.

@author: Marten Lohstroh
'''
import re
from sys import argv, setrecursionlimit
from copy import deepcopy
from spec_space.parser.parser import LTL_PARSER
from spec_space.formula import TrueFormula, FalseFormula, Constant, Next, \
        VarNext, Disjunction, Conjunction, UnaryFormula, Literal, \
        BinaryFormula, Globally, Eventually, DoubleImplication, Implication, \
        Negation;
from pyeda.boolalg.expr import expr, expr2dimacscnf
from subprocess import call, check_output
from spec_space.symbol_sets import PyEDASymbolSet

expr1 = None
expr2 = None
N = None

target = PyEDASymbolSet()

fls = target.symbols['FALSE']
tru = target.symbols['TRUE']
lor = target.symbols['OR']
lnd = target.symbols['AND']
neg = target.symbols['NOT']

setrecursionlimit(100000)

''' Expand a given LTL formula into a Boolean expression, observing time bound N. 
    This function returns a tuple. The first item in the returned tuple is a 
    string representation of the expansion; the second is a set containing all 
    the atomic propositions featured in the expression. As a side effect, this
    traversal will decorate all BinaryFormula nodes in the AST. In particular, 
    it sets the nodes' info['expr'], info['ldeps'], and info['rdeps'] fields. 
    Some basic constant folding is done to eradicate trivial bloat in the 
    generated expression. '''
def expand(f, n=0):

    if isinstance(f, Literal):
        if (n > N):
            return ["false", set([])]
            
        else:
            name = "(" + f.generate(with_base_names=True) + str(n) + ")"
            return [name, set([name])]

    if isinstance(f, BinaryFormula):
        
        l, ldeps = expand(f.left_formula, n)
        r, rdeps = expand(f.right_formula, n)
        f.info['ldeps'] = ldeps
        f.info['rdeps'] = rdeps
        
        if isinstance(f, Conjunction):    
            if (l == fls or r == fls):
                f.info['expr'] = fls
                return [f.info['expr'], set([])]
            elif (l == tru):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]
            elif (r == tru):
                f.info['expr'] = l
                return [f.info['expr'], ldeps]
            elif (r == tru and l == tru):
                f.info['expr'] = true
                return [f.info['expr'], set([])]
            else:
                f.info['expr'] = "(" + l + " " + lnd + " " + r + ")"
                return [f.info['expr'], set(ldeps.union(rdeps))]
        elif isinstance(f, Disjunction):
            if (l == fls and r == fls):
                f.info['expr'] = fls
                return [f.info['expr'], set([])]
            elif (l == fls):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]    
            elif (r == fls):
                f.info['expr'] = l
                return [f.info['expr'], ldeps]
            else:
                f.info['expr'] = "(" + l + " | " + r + ")"
                return [f.info['expr'], set(ldeps.union(rdeps))]
        else:
            throw("Error: cannot expand unsupported BinaryFormula!")
    else:
        if isinstance(f, Globally):
            conj = tru
            deps = set([])
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e == fls:
                    return [fls, set([])]
                else:
                    conj += " " + lnd + " " + e
                    deps = deps.union(d)
                n += 1
                
            return [conj, deps]  
        elif isinstance(f, Eventually):
            disj = fls
            deps = set([])
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e != fls:
                    disj += " " + lor + " " + e 
                    deps = deps.union(d)
                n += 1
            return [disj, deps]
        elif isinstance(f, Next) or isinstance(f, VarNext):
            return expand(f.right_formula, n+1)
        elif isinstance(f, Negation):
            e, d = expand(f.right_formula, n)
            if e == fls:
                return [tru, set([])]
            elif e == fls:
                return [fls, set([])]
            else:
                return [neg + e, d]
        else:
            return expand(f.right_formula, n)

''' Print a help message and exit. '''
def help_exit():
    print("Usage: python measure.py [TIME_BOUND] LTL_EXPR1 [LTL_EXPR2]")
    exit(1)

''' Read commandline arguments. '''
def init():
    global N, expr1, expr2
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

''' Pass the given Boolean formula to SharpSAT. 
    Return the number of satisfying models. '''
def count(formula):
    cnf = expr(formula).to_cnf()
    '''false'''
    if str(cnf) == "0":
        return 0
    '''true'''
    if str(cnf) == "1":
        return 1
    else:
        '''sat?'''
        file = open('input.cnf', 'w')
        file.write(str(expr2dimacscnf(cnf)[1]))
        file.close()

        output = check_output(["bin/sharpSAT", "input.cnf"])
        m = re.search(r"# solutions \n([0-9]+)\n# END", output.decode('UTF-8'))
        return m.group(1)


def simplify(f):

    if isinstance(f, BinaryFormula):
        l = f.left_formula
        r = f.right_formula
        if isinstance(f, Implication):
            if (l == FalseFormula or r == TrueFormula):
                return TrueFormula()
            if (l == TrueFormula):
                return r
            if (r == FalseFormula):
                return Negation(l)
            else:
                return Disjunction(Negation(l),r)
        elif isinstance(f, DoubleImplication):
            # ((l and r) or (not l and not r))
            # FIXME: add reductions here
            return Disjunction(Conjunction(l, r), Conjunction(Negation(l), Negation(r)))
    return f

''' Recursively apply given function to each node in the AST. '''
def traverse(form, func):
    
    if isinstance(form, BinaryFormula):
        form.left_formula = traverse(form.left_formula, func)
        form.right_formula = traverse(form.right_formula, func)
    elif isinstance(form, UnaryFormula):
        form.right_formula = traverse(form.right_formula, func)

    return func(form)

def measure(e1, e2=None):
    e1 = traverse(e1, simplify)
    print(e1.generate(with_base_names=False, ignore_precedence=True))
    
    #traverse(e1, )...
    print(expand(e1)[0])



''' Main '''
init()
measure(expr1, expr2)

# f1, d1 = expand(expr1, 0)
# print(expr1.right_formula.info['ldeps'].isdisjoint(expr1.right_formula.info['rdeps']))
# print(f1)
# exit()


#print(count(expr1.generate(PyEDASymbolSet)))
#print(expr("x & 1"))
#f = LTL_PARSER.parse("G(tom & maso)")
#f = LTL_PARSER.parse("F(G(tom & maso))")
#f = LTL_PARSER.parse("((tom | maso) & (tom | maso))") # FIXME: this exposes the renaming issue. It should not all be considered the same vars.
#f = LTL_PARSER.parse("G(tom & X tom)")
#f = LTL_PARSER.parse("G(tom & X tom)")
#f = LTL_PARSER.parse("F(G(tom & X(maso)))")
#f = LTL_PARSER.parse("a & false")
#f = LTL_PARSER.parse("a & XXXXa")