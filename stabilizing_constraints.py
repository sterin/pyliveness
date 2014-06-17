import sys
import itertools

from pyzz import *

from utils import fold_fairness_constraints
from liveness_to_safety import extract_liveness_as_safety

def compute_stabilizing_constraints(N, candidates, fg_prop, k=0, conflict_limit=None):

    candidates = set(candidates)

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


def extract_stabilizing_constraints(N0, fair_po_no, candidates, K=0, conflict_limit=None):

    N, xlat = N0.copy()

    all_fcs = [ w[0]^w.sign() for w in all_fcs_for_fair_po(N, fair_po_no)]

    fc_prop = fold_fairness_constraints(N, all_fcs)

    sc, pc = compute_stabilizing_constraints(N, [xlat[w] for w in candidates], ~fc_prop, K, conflict_limit)

    new_fgs = []

    for c in candidates:

        nc = xlat[c]

        if nc in pc:
            new_fgs.append(c)
        elif ~nc in pc:
            new_fgs.append(~c)
        elif nc.is_Flop() and ( nc in sc or ~nc in sc ):
            new_fgs.append( c.equals( c[0]^c.sign()) )

    new_fg = conjunction(N0, new_fgs)

    for fc in all_fcs_for_fair_po(N0, fair_po_no):
        assert not fc.sign()
        fc[0] = fc[0]&new_fg

    return N0, new_fg

if __name__=="__main__":

    from optparse import OptionParser

    parser = OptionParser()

    parser.add_option( "--aiger", dest="aiger", help="input file")
    parser.add_option( "--outfile", dest="outfile", default=None, help="output aiger file with extracted fairness constraints")

    parser.add_option( "--fair_po_no", dest="fair_po_no", type="int", default=None, help="Liveness PO number")

    parser.add_option( "--K", dest="K", type="int", default=0, help="K")
    parser.add_option( "--conflict_limit", dest="conflict_limit", type="int", default=None, help="conflict limit for each SAT call")

    parser.add_option( "--l2s", dest="l2s", action="store_true", default=False, help="liveness to safety")

    options, args = parser.parse_args()

    if not options.aiger:
        parser.error('--aiger argument missing')

    if not options.outfile:
        parser.error('--outfile argument missing')

    N = netlist.read_aiger(options.aiger)

    if N.n_fair_properties() == 0:
        parser.error('not justice properties in AIGER file')

    if options.fair_po_no is None:
        if N.n_fair_properties() == 1:
            options.fair_po_no = 0
        else:
            parser.error("--fair_po_no is required when there are more than one justice property")

    if N.n_fair_properties() <= options.fair_po_no:
        parser.error('too few justice properties in AIGER file')

    candidates = list(N.get_Flops())

    N, new_fg = extract_stabilizing_constraints(N, options.fair_po_no, candidates, options.K, options.conflict_limit)

    if options.l2s:
        N, xlat, _ = extract_liveness_as_safety(N, new_fg)

    N.write_aiger(options.outfile)
