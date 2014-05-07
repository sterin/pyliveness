from gi.overrides.keysyms import implies
from pyzz import *
from liveness_to_safety import extract_liveness_as_safety

values = ['UNDEF', 'ERROR', 'UNSAT', 'SAT']

from pyaig import AIG, write_aiger, read_aiger

def pyzz_to_pyaig(N):

    aig = AIG()
    xlat = utils.fmap()

    xlat[N.get_True()] = AIG.get_const1()

    for pi in N.get_PIs():
        xlat[pi] = aig.create_pi()

    flop_init = N.flop_init
    lbool_to_init = [AIG.INIT_NONDET, AIG.INIT_NONDET, AIG.INIT_ZERO, AIG.INIT_ONE]

    for ff in N.get_Flops():
        xlat[ff] = aig.create_latch(init=lbool_to_init[flop_init[ff]])

    for a in N.get_Ands():
        xlat[a] = aig.create_and( xlat[a[0]], xlat[a[1]])

    for ff in N.get_Flops():
        aig.set_next(xlat[ff], xlat[ff[0]])

    def xlat_po(po):
        return xlat[ po[0]^po.sign() ]

    for p in N.get_properties():
        aig.create_po( xlat_po(~p), po_type=AIG.BAD_STATES)

    for c in N.get_constraints():
        aig.create_po(xlat_po(c), po_type=AIG.CONSTRAINT)

    for fp in N.get_fair_properties():
        j_pos = [ aig.create_po(xlat_po(f), po_type=AIG.JUSTICE) for f in fp ]
        aig.create_justice(j_pos)

    for fc in N.get_fair_constraints():
        aig.create_po(xlat_po(fc), po_type=AIG.FAIRNESS)

    print [+f for fp in N.get_fair_properties() for f in fp]

    all_prop_pos = set( itertools.chain(
        (+p for p in N.get_properties()),
        (+c for c in N.get_constraints()),
        (+fc for fc in N.get_fair_constraints()),
        (+f for fp in N.get_fair_properties() for f in fp)
    ))

    for po in N.get_POs():
        if po not in all_prop_pos:
            aig.create_po(xlat_po(po), po_type=AIG.OUTPUT)

    return aig

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

def build_aig1():
    N = netlist()

    ffs = [ N.add_Flop() for _ in xrange(10) ]

    for i, ff in enumerate(ffs):
        N.flop_init[ff] = solver.l_True if i==0 else solver.l_False
        ff[0] = ffs[(i-1) if i>0 else (len(ffs)-1)]

    xx = N.add_Flop(init=solver.l_Undef)
    xx[0] = xx

    po = N.add_PO(fanin=ffs[-1]&xx)
    N.add_fair_property([po])

    return N, po

def build_aig2():

    N = netlist()

    b0, b1 = [ N.add_Flop(init=solver.l_False) for _ in xrange(2) ]
    b0[0] = ~b0 | b1
    b1[0] = b0 | b1

    print "b0=", b0, ", b1=", b1

    po = N.add_PO(fanin=~b1)
    N.add_fair_property([po])

    return N, po

if __name__=="__main__":

    #N, po = build_aig2()

    N = netlist.read_aiger('/home/sterin/Desktop/hwmcc12-live/cucnt10.aig')

    with open('cucnt_pyzz_to_pyaig.aig', 'w') as f:
        aig = pyzz_to_pyaig(N)
        write_aiger(aig, f)

    for fp in N.get_fair_properties():
        for pp in fp:
            po = pp

    print pp

    sc, pc = extract(N, list(N.get_Flops()), ~po)

    flops= list(N.get_Flops())
    print len(flops), flops

    print len(sc), sc, set(flops)-set(sc)
    print len(pc), pc, set(flops)-set(+x for x in pc)

    orig_symbols = utils.make_symbols(N)

    M, xlat, loop_start = extract_liveness_as_safety(N)

    symbols= { "_LIVENESS_LOOP_START":loop_start }
    symbols.update( (n,xlat[s]) for n,s in orig_symbols.iteritems() if s in xlat )
