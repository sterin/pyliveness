from gi.overrides.keysyms import implies
from pyzz import *
from liveness_to_safety import extract_liveness_as_safety

values = ['UNDEF', 'ERROR', 'UNSAT', 'SAT']

def extract(N, candidates, p, k=0):

    def is_stabilizing(x):
        if S.solve(U[x, k], U[~x, k+1]) == solver.UNSAT:
            return True
        if S.solve(U[~x,k], U[x, k+1]) == solver.UNSAT:
            return True
        return False

    def add_stabilizing(x):
        stabilizing_constraints.add(x)
        for i in xrange(k+1):
            S.equivalence(U[x, k], U[x, k+1])

    def implies_prop(x):
        return S.solve( U[x, k], ~U[p, k] ) == solver.UNSAT

    def add_polarity(x):
        polarity_constraints.add(x)
        S.cube( U[x,i] for i in xrange(k+2) )

    U = unroll(N, init=False)
    S = solver(U.F)

    stabilizing_constraints = set()
    polarity_constraints = set()

    while True:

        new_facts = False
        to_remove = []

        for ff in candidates:

            if ff not in stabilizing_constraints:

                if is_stabilizing(ff):
                    add_stabilizing(ff)
                    new_facts = True

            if ff in stabilizing_constraints:

                if implies_prop(ff):
                    add_polarity(~ff)
                    new_facts = True
                    to_remove.append(ff)

                elif implies_prop(~ff):
                    add_polarity(ff)
                    new_facts = True
                    to_remove.append(ff)

        if not new_facts:
            break

        for ff in to_remove:
            candidates.remove(ff)

    return stabilizing_constraints, polarity_constraints

def fold_fairness_constraints(N, fairness_constraints):

    if len(fairness_constraints) == 1:
        return fairness_constraints[0]

    flops = [ N.add_Flop() for _ in fairness_constraints ]
    fair = conjunction(N, flops)

    for fc, ff in zip(fairness_constraints, flops):
        ff[0] = fair.ite(fc, ff|fc )

    return fair

    N = netlist()

    ffs = [ N.add_Flop() for _ in xrange(10) ]

    for i, ff in enumerate(ffs):
        N.flop_init[ff] = solver.l_True if i==0 else solver.l_False
        ff[0] = ffs[(i-1) if i>0 else (len(ffs)-1)]

    xx = N.add_Flop(init=solver.l_Undef)
    xx[0] = xx

    po = N.add_PO(fanin=ffs[-1]&xx)
    N.add_fair_property([po])

    print sc, pc
if __name__=="__main__":
    sc, pc = extract(N, list(N.get_Flops()), ~po)

    orig_symbols = utils.make_symbols(N)

    M, xlat, loop_start = extract_liveness_as_safety(N)

    symbols= { "_LIVENESS_LOOP_START":loop_start }
    symbols.update( (n,xlat[s]) for n,s in orig_symbols.iteritems() if s in xlat )

