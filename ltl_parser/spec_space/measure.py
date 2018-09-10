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

''' Maps atomic propositions to sets of time indexes. '''
class DepTracker:

    def __init__(self, lit=None, n=None):
        self.literals = {}
        if lit != None and n != None:
            self.add(lit, n)

    def add(self, literal, indexes):
        if self.literals.get(literal) == None:
            self.literals[literal] = indexes
        else:
            self.literals[literal] = self.literals[literal].union(indexes)

    def union(self, other):
        new = DepTracker()
        if other == None:
            return new
        for k,v in other.literals.items():
            if self.literals.get(k) == None:
                new.add(k, v)
            else:
                new.add(k, self.literals[k].union(v))
        for k,v in self.literals.items():
            if other.literals.get(k) == None:
                new.add(k, v)

        return new

    def isdisjoint(self, other):
        if len(self.literals) <= len(other.literals):
            mine = self.literals
            their = other.literals
        else:
            mine = other.literals
            their = self.literals

        for k,v in mine.items():
            if their.get(k) != None:
                return False
        return True

    def count(self):
        cnt = 0
        for v in self.literals.values():
            for t in v:
                cnt += 1
        return cnt

    def timeindependent(self):
        for v in self.literals.values():
            if len(v) > 1:
                return False
        return True

    def shift(self, n):
        for k, v in self.literals.items():
            shifted = set([])
            for t in v.values():
                shifted.add(v+n)    
            self.literals[k] = shifted
        return self

    def saturate(self):
        for k, v in self.literals.items():
            self.literals[k] = set(range(min(v), N))
        return self

''' Expand a given LTL formula into a Boolean expression, observing time bound N. 
    This function returns a tuple. The first item in the returned tuple is a 
    string representation of the expansion; the second is a set containing all 
    the atomic propositions featured in the expression. As a side effect, this
    traversal will decorate all BinaryFormula nodes in the AST. In particular, 
    it sets the nodes' info['expr'], info['ldeps'], and info['rdeps'] fields. 
    Some basic constant folding is done to eradicate trivial bloat in the 
    generated expression. '''
def expand(f, n=0): # FIXME: separate the dependency analysis from the expansion

    if isinstance(f, Literal):
        if (n > N):
            return ["false", None]
            
        else:
            name = f.generate(with_base_names=True)
            f.info['deps'] = DepTracker(name, set([n]))
            return [name + str(n), f.info['deps']]

    if isinstance(f, BinaryFormula):
        
        l, ldeps = expand(f.left_formula, n)
        r, rdeps = expand(f.right_formula, n)
        f.info['ldeps'] = ldeps
        f.info['rdeps'] = rdeps
        
        if isinstance(f, Conjunction):    
            if (l == fls or r == fls):
                f.info['expr'] = fls
                return [f.info['expr'], None]
            elif (l == tru):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]
            elif (r == tru):
                f.info['expr'] = l
                return [f.info['expr'], ldeps]
            elif (r == tru and l == tru):
                f.info['expr'] = true
                return [f.info['expr'], None]
            else:
                f.info['expr'] = "(" + l + " " + lnd + " " + r + ")"
                return [f.info['expr'], ldeps.union(rdeps)] # FIXME: could ldeps be None?
        elif isinstance(f, Disjunction):
            if (l == fls and r == fls):
                f.info['expr'] = fls
                return [f.info['expr'], None]
            elif (l == fls):
                f.info['expr'] = r
                return [f.info['expr'], rdeps]    
            elif (r == fls):
                f.info['expr'] = l
                return [f.info['expr'], ldeps]
            else:
                f.info['expr'] = "(" + l + " | " + r + ")"
                return [f.info['expr'], ldeps.union(rdeps)]
        else:
            raise Exception("Error: cannot expand unsupported BinaryFormula!")
    else:
        if isinstance(f, Globally):
            conj = tru
            deps = DepTracker()
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e == fls:
                    return [fls, None]
                else:
                    conj += " " + lnd + " " + e
                    deps = deps.union(d)
                n += 1
            f.info['deps'] = deps
            return [conj, deps]  
        elif isinstance(f, Eventually):
            disj = fls
            deps = DepTracker()
            while (n <= N):
                e, d = expand(f.right_formula, n)
                if e != fls:
                    disj += " " + lor + " " + e 
                    deps = deps.union(d)
                n += 1
            f.info['deps'] = deps
            return [disj, deps]
        elif isinstance(f, Next) or isinstance(f, VarNext):
            return expand(f.right_formula, n+1)
        elif isinstance(f, Negation):
            e, d = expand(f.right_formula, n)
            if e == fls:
                return [tru, None]
            elif e == fls:
                return [fls, None]
            else:
                return [neg + e, d]
        else:
            pass
            #return expand(f.right_formula, n)


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
    print(cnf)
    ''' False '''
    if str(cnf) == "0":
        return 0
    ''' True '''
    if str(cnf) == "1":
        return 1
    else:
        ''' Sat? '''
        file = open('input.cnf', 'w')
        file.write(str(expr2dimacscnf(cnf)[1]))
        file.close()

        output = check_output(["bin/sharpSAT", "input.cnf"])
        m = re.search(r"# solutions \n([0-9]+)\n# END", output.decode('UTF-8'))
        return int(m.group(1))

''' Traversal function that reduces implications, double implications. '''
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

''' Traversal function that computes AST nodes' dependencies. 
    Updates the info['deps'] field for all nodes, and the 
    info['lrdisjoint'] for bifurcating nodes. '''
def compute_deps(f):

    if isinstance(f, Literal):
        name = f.generate(with_base_names=True)
        f.info['deps'] = DepTracker(name, set([0]))
    elif isinstance(f, BinaryFormula):
        ldeps = f.left_formula['deps']
        rdeps = f.right_formula['deps']
        f.info['deps'] = ldeps.union(rdeps)
        f.info['lrdisjoint'] = ldeps.isdisjoint(rdeps)
    else:
        if isinstance(f, Globally) or isinstance(f, Eventually):
            f.info['deps'] = f.right_formula.info['deps'].saturate()
            print("HERE!!")
        elif isinstance(f, Next) or isinstance(f, VarNext):
            f.info['deps'] = f.right_formula.info['deps'].shift(1)
        else:
            raise Exception("Unsupported AST node: " + type(f).__name__)
    
    return f

''' Measure the given formula. '''
def measure(f, n=0):
    print(f.generate(with_base_names=False))
    
    if isinstance(f, TrueFormula):
        return 1

    if isinstance(f, FalseFormula):
        return 0

    if isinstance(f, Literal):
        if (n <= N):
            return 0.5
        else:
            return 0

    if isinstance(f, Negation):
        return 1 - measure(f.right_formula, n)

    if isinstance(f, Conjunction):
        if f.info['lrdisjoint']:
            print("disjoint")
            return measure(f.right_formula, n) * measure(f.left_formula, n)
        else:
            print("overlapping")
            num_vars = f.info['deps'].count()   # FIXME: could ldeps or rdeps be None?
            num_asrs = count(f.info['expr']) # using a cached version; should probably do this on the fly...?
            return num_asrs / 2**num_vars

    if isinstance(f, Disjunction):
        if f.info['lrdisjoint']:
            print("disjoint")
            return 1 - (1-measure(f.right_formula, n)) * (1-measure(f.left_formula, n))
        else:
            print("overlapping")
            num_vars = f.info['deps'].count()   # FIXME: could ldeps or rdeps be None?
            num_asrs = count(f.info['expr']) # using a cached version; should probably do this on the fly...?
            return num_asrs / 2**num_vars

    if isinstance(f, Next):
        return measure(f, n+1)

    if isinstance(f, Globally):
        deps = f.right_formula.info['deps']

        if deps.timeindependent():
            print("here")
            m = 1
            for i in range(0, N):
                m *= measure(f.right_formula, n+i) # we will easily move past N here.
            return m
        else:
            print(f.info['deps'].literals)
            # FIXME: go to the model counter
            pass

    if isinstance(f, Eventually):
        deps = f.right_formula.info['deps']
        
        if deps.timeindependent():
            print("here")
            m = 1
            for i in range(0, N):
                m *= 1 - measure(f.right_formula, n+i) # we will easily move past N here.
            return 1-m
        else:
            print(f.info['deps'].literals)
            # FIXME: go to the model counter
            pass

''' Main '''
init()
#FIXME: run input expression through PyEDA for simplification first
# 
traverse(expr1, simplify)
traverse(expr1, compute_deps)
print(measure(expr1))

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