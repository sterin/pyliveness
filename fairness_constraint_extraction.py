from gi.overrides.keysyms import implies
from pyzz import *
from liveness_to_safety import extract_liveness_as_safety

values = ['UNDEF', 'ERROR', 'UNSAT', 'SAT']

def extract(N, p, k=0):

    def is_stabilizing(x):
        if S.solve(U[x, k], U[~x, k+1]) == solver.UNSAT:
            return True
        if S.solve(U[~x,k], U[x, k+1]) == solver.UNSAT:
            return True
        return False

    def add_stabilizing(x):
        stabilizing_constraints.add(x)
        new_facts = True
        for i in xrange(k+1):
            w1, w2 = U[x, k], U[x, k+1]
            S.equivalence(w1, w2)

    def implies_prop(x):
        return S.solve( U[x, k], ~U[p, k] ) == solver.UNSAT

    def add_polarity(x):
        polarity_constraints.add(x)
        S.cube( U[x,i] for i in xrange(k+2) )

    U = unroll(N, init=False)
    S = solver(U.F)

    stabilizing_constraints = set()
    polarity_constraints = set()

    candidate_flops = set(N.get_Flops())

    while True:

        new_facts = False
        to_remove = []

        for ff in candidate_flops:

            if ff not in stabilizing_constraints:

                if is_stabilizing(ff):
                    add_stabilizing(ff)

            if ff in stabilizing_constraints:

                if implies_prop(ff):
                    add_polarity(~ff)
                    to_remove.append(ff)

                elif implies_prop(~ff):
                    add_polarity(ff)
                    to_remove.append(ff)

        if not new_facts:
            break

        for ff in to_remove:
            candidate_flops.remove(ff)

    return stabilizing_constraints, polarity_constraints

if __name__=="__main__":

    N = netlist()

    ffs = [ N.add_Flop() for _ in xrange(10) ]

    for i, ff in enumerate(ffs):
        N.flop_init[ff] = solver.l_True if i==0 else solver.l_False
        ff[0] = ffs[(i-1) if i>0 else (len(ffs)-1)]

    po = N.add_PO(fanin=ffs[-1]&xx)
    N.add_fair_property([po])

    print extract(N, po)

    orig_symbols = utils.make_symbols(N)

    M, xlat, loop_start = extract_liveness_as_safety(N)

    symbols= { "_LIVENESS_LOOP_START":loop_start }
    symbols.update( (n,xlat[s]) for n,s in orig_symbols.iteritems() if s in xlat )

