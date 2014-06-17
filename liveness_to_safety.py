import itertools

from pyzz import *

from utils import fold_fairness_constraints

def liveness_to_safety(N, new_fg=None):

    flops = list(N.get_Flops())
    shadows = [ rigid(N) for _ in flops ]

    eq = equal(N, flops, shadows)
    loop_start, prev_loop_start = somepast(N, eq)

    bad = []

    for i in xrange(N.n_fair_properties()):

        all_fcs = [ fc[0]^fc.sign() for fc in all_fcs_for_fair_po(N, 0) ]
        fair = conjunction(N, (somepast(N, fc&loop_start)[1] for fc in all_fcs))

        fail = fair & eq & ( new_fg if new_fg is not None else N.get_True() )
        bad.append( N.add_PO(fanin=fail) )

    return bad, loop_start


def extract_liveness_as_safety(N, new_fg=None):

    constraints = list(N.get_constraints())

    bad, loop_start = liveness_to_safety(N, new_fg)

    M, xlat = copy_coi(N, bad+constraints+[loop_start])

    for b in bad:
        M.add_property( ~xlat[b] )

    for c in constraints:
        M.add_constraint( xlat[c] )

    return M, xlat, xlat[loop_start]


if __name__=="__main__":

    N = netlist()

    ffs = [ N.add_Flop() for _ in xrange(10) ]

    for i, ff in enumerate(ffs):
        N.flop_init[ff] = solver.l_True if i==0 else solver.l_False
        ff[0] = ffs[(i-1) if i>0 else (len(ffs)-1)]

    po = N.add_PO(fanin=ffs[-1])
    N.add_property(~po)

    print "BMC(safe):\n"
    bmc.safety_bmc(N, 50)

    N.add_fair_property([po])
    orig_symbols = utils.make_symbols(N)

    M, xlat, loop_start = extract_liveness_as_safety(N)

    symbols= { "_LIVENESS_LOOP_START":loop_start }
    symbols.update( (n,xlat[s]) for n,s in orig_symbols.iteritems() if s in xlat )

    print
    print "BMC(live):\n"
    bmc.safety_bmc(M, 50, symbols)
