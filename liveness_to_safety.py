import itertools

from pyzz import *


def init_bmc_netlist_common(N, props):

    props = [p[0] ^ p.sign() for p in props]
    constraints = [c[0] ^ c.sign() for c in N.get_constraints()]

    M, xlat = copy_coi(N, props + constraints)

    props = [ xlat[p] for p in props]
    constraints = [ xlat[c] for c in constraints]

    failed = somepast(M, ~conjunction(M, constraints))[0]

    return M, xlat, props, failed


def init_bmc_netlist_safety(N, props):

    M, xlat, props, failed = init_bmc_netlist_common(N, props)

    bad = M.add_PO( ~conjunction( N, props ) & ~failed)
    M.add_property(~bad)

    return M, xlat, bad


def init_bmc_netlist_liveness(N, fairness_constraints):

    M, xlat, fairness_constraints, failed = init_bmc_netlist_common(N, fairness_constraints)

    monitor = M.add_Buf()
    N.add_PO(fanin=monitor)

    flops = [ M.add_Flop() for _ in fairness_constraints ]
    seen = [ monitor&(ff|fc) for ff, fc in zip(flops, fairness_constraints) ]

    toggle = conjunction(M, seen)

    for ff, s in zip(flops, seen):
        ff[0] = ~toggle & s

    fair = toggle & ~failed
    return M, xlat, fair, monitor

def add_stabilizing_constraints_to_netlist(N, candidates, pc, sc):

    new_fgs = []

    for c in candidates:

        if c in pc:
            new_fgs.append(c)
        elif ~c in pc:
            new_fgs.append(~c)
        elif c.is_Flop() and ( c in sc or ~c in sc ):
            new_fgs.append(c.equals(c[0] ^ c.sign()))

    fair = N.get_property(0)
    fair = fair[0]^fair

    N.add_fair_property([ fair & conjunction(N, new_fgs) ])


def init_stabilizing_constraints_netlist(N0, fair_prop_no):

    fairs = [ fc[0]^fc.sign() for fc in Ntmp.get_fair_constraints() ]
    fairs.extend( fp[0]^fp.sign() for fp in N.get_fair_properties()[fair_prop_no])

    Ntmp, xlat, fc_prop, monitor = init_bmc_netlist_liveness(N0, fairs)
    monitor[0] = Ntmp.True()
    Ntmp.remove_buffers()

    candidates = [ff for ff in Ntmp.get_Flops()]
    sc, pc = extract_stabilizing_constraints(M, candidates, fc_prop)

    N, xlat, bad = init_bmc_netlist_safety(Ntmp, [fc_prop])
    add_stabilizing_constraints_to_netlist(candidates, [xlat[c] for c in pc], [xlat[c] for c in sc])

    return N

def live3(N0, fair_prop_no):
    N = init_stabilizing_constraints_netlist(N0, fair_prop_no)

def xxx2(N, fair_po_no, candidates, K, conflict_limit):
    print "xxx2:"
    print "\t N:", N
    print "\t fair_po_no:", fair_po_no
    print "\t candidates:", candidates, type(candidates)
    print "\t K:", K
    print "\t conflict_limit:", conflict_limit

    all_fcs = list(itertools.chain(N.get_fair_properties()[fair_po_no], N.get_fair_constraints()))
    all_fcs = [ w[0]^w.sign() for w in all_fcs]

    fc_prop = fold_fairness_constraints(N, all_fcs)
    fg_prop = ~fc_prop

    print "candidates:", candidates

    sc, pc = extract_stabilizing_constraints(N, candidates, fg_prop, K, conflict_limit)
    print "2:", sc, pc, candidates

    new_fgs = []

    print 'candidates:', candidates
    for c in candidates:

        if c in pc:
            print 1
            new_fgs.append(c)
        elif ~c in pc:
            print 2
            new_fgs.append(~c)
        elif c.is_Flop() and ( c in sc or ~c in sc ):
            print 3
            new_fgs.append( c.equals( c[0]^c.sign()) )

    fair = N.add_PO( fanin=conjunction(N, new_fgs) & fc_prop )

    M, xlat = copy_coi(N, [fair])
    M.add_fair_property([xlat[fair]])

    def add(f):
        M.add_property(M.add_PO(fanin=xlat[f]))

    add( fc_prop )
    print "YYY"

    for f in new_fgs:
        print "XXX"
        add(f)

    add( conjunction(N, new_fgs) )

    print list(N.get_properties())

    M.write_aiger('zzz.aig')




def liveness_to_safety(N, new_fgs):

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
        fail = fair & eq & prev_loop_start & new_fgs

        bad.append( N.add_PO(fanin=fail) )

    return bad, loop_start

def extract_liveness_as_safety(N, new_fgs):

    constraints = list(N.get_constraints())
    bad, loop_start = liveness_to_safety(N, new_fgs)
    M, xlat = copy_coi(N, bad+[loop_start, new_fgs]+constraints)

    for b in bad:
        M.add_property(~(xlat[b]))

    for c in constraints:
        M.add_constraint(xlat[c])

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
