import itertools

from pyzz import *

def liveness_to_safety(N):

    flops = list(N.get_Flops())
    shadows = [ rigid(N) for _ in flops ]

    eq = equal(N, flops, shadows)
    loop_start, prev_loop_start = somepast(N, eq)

    fair_constraints = [ fc[0]^fc.sign() for fc in N.get_fair_constraints() ]

    bad = []

    for fair_property in N.get_fair_properties():

        fair_property = ( fc[0]^fc.sign() for fc in fair_property )
        all_fcs = itertools.chain(fair_constraints, fair_property)

        fair = conjunction(N, ( somepast(N, fc&loop_start)[0] for fc in all_fcs ) )
        fail = fair & eq & prev_loop_start

        bad.append( N.add_PO(fanin=fail) )

    return bad, loop_start

def extract_liveness_as_safety(N):

    bad, loop_start = liveness_to_safety(N)
    M, xlat = copy_coi(N, bad+[loop_start])

    for b in bad:
        M.add_property(~xlat[b])

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

    M, xlat, loop = extract_liveness_as_safety(N)

    symbols= { "_LIVENESS_LOOP_START":loop }
    symbols.update( (n,xlat[s]) for n,s in orig_symbols.iteritems() if s in xlat )

    print
    print "BMC(live):\n"
    bmc.safety_bmc(M, 50, symbols)
