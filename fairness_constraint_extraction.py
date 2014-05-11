from pyzz import *
from liveness_to_safety import extract_liveness_as_safety

import itertools

values = ['UNDEF', 'ERROR', 'UNSAT', 'SAT']

from pyaig import AIG, read_aiger, write_aiger

def extract_stabilizing_constraints(N, candidates, fg_prop, k=0, conflict_limit=None):

    """

    :type N: pyzz.netlist
    :type candidates: list
    :type fg_prop: pyzz._pyzz.wire
    :type k: int
    :type conflict_limit: int
    :return:
    """

    U = unroll(N, init=False)
    S = solver(U.F, conflict_limit=conflict_limit)

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
        return S.solve( U[x, k], ~U[fg_prop, k] ) == solver.UNSAT

    def add_polarity(x):
        polarity_constraints.add(x)
        S.cube( U[x,i] for i in xrange(k+2) )

    for i in xrange(k+2):
        S.cube( U[N.get_constraints(), i] )

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

if __name__=="__main__":

    from optparse import OptionParser

    parser = OptionParser()

    parser.add_option( "--aiger", dest="aiger", help="input file")
    parser.add_option( "--outfile", dest="outfile", default="/dev/stdout", help="list of constraints extracted")
    parser.add_option( "--K", dest="K", type="int", default=0, help="K")
    parser.add_option( "--conflict_limit", dest="conflict_limit", type="int", default=None, help="conflict limit for each SAT call")

    options, args = parser.parse_args()

    if not options.aiger:
        parser.error('--aiger argument missing')

    if not options.outfile:
        parser.error('--outfile argument missing')

    N = netlist.read_aiger(options.aiger)

    original_flops = list(N.get_Flops())

    assert len(N.get_fair_properties()) == 1

    all_fcs = list(itertools.chain(N.get_fair_properties()[0], N.get_fair_constraints()))
    all_fcs = [ w[0]^w.sign() for w in all_fcs]

    fg_prop = ~fold_fairness_constraints(N, all_fcs)

    sc, pc = extract_stabilizing_constraints(N, list(N.get_Flops()), fg_prop, options.K, options.conflict_limit)

    with open(options.outfile, 'w') as f:

        for i, flop in enumerate(original_flops):
            if flop in pc:
                print >> f, '+%d'%i
            elif ~flop in pc:
                print >> f, '-%d'%i
            elif flop in sc or ~flop in sc:
                print >> f, '%d'%i
