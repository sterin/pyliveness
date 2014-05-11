import itertools

from pyzz import *

def cec(N1, N2):

    """
    Combinational Equivalence Checking of N1 and N2
    :type N1: pyzz.netlist
    :type N2: pyzz.netlist
    :return:
    :raise RuntimeError:
    """

    if N1.n_PIs() != N2.n_PIs():
        raise RuntimeError("cec: number of PIs in both circuits doesn't match")

    if N1.n_Flops() != N2.n_Flops():
        raise RuntimeError("cec: number of Flops in both circuits doesn't match")

    flop_init1 = N1.flop_init
    flop_init2 = N2.flop_init

    for ff1, ff2 in zip(N1.get_Flops(), N2.get_Flops()):
        if flop_init1[ff1] != flop_init2[ff2]:
            raise RuntimeError("")

    M = netlist()

    def cis(N):
        return itertools.chain( N.get_PIs(), N.get_Flops() )

    def cos(N):
        return ( w[0]^w.sign() for w in itertools.chain( N.get_POs(), N.get_Flops() ) )

    pis = [ M.add_PI() for _ in xrange(N1.n_PIs() + N1.n_Flops()) ]

    stop_at1 = { w1:pi for w1, pi in zip(cis(N1), M.get_PIs())}
    xlat1 = utils.copy_cone(N1, M, cos(N1), stop_at=stop_at1)

    stop_at2 = { w2:pi for w2, pi in zip(cis(N2), M.get_PIs())}
    xlat2 = utils.copy_cone(N2, M, cos(N2), stop_at=stop_at2)


    S = solver(M)

    # for i1, po1 in enumerate(cos(N1)):
    #     for i2, po2 in enumerate(cos(N2)):

    # for i1, po1 in enumerate(w[0] for w in N1.get_POs()):
    #     for i2, po2 in enumerate(w[0] for w in N2.get_POs()):

    for i, (po1, po2) in enumerate(zip(cos(N1), cos(N2))):

            i1 = i
            i2 = i

            def sign_text(sign):
                return '~' if sign else ''

            def check(sign):

                rc = S.solve( xlat1[po1]^sign, ~xlat2[po2] )

                if rc == solver.SAT:

                    return False, '1: %sPO %d != PO %d'%( sign_text(sign),  i1, i2)

                else:

                    rc = S.solve( ~xlat1[po1]^sign, xlat2[po2] )

                    if rc == solver.SAT:
                        return False, '2: %sPO %d != PO %d'%( sign_text(sign), i1, i2)

                    else:
                        return True, '%sPO %d == PO %d'%( sign_text(sign), i1, i2)


            res1, msg1 = check(False)
            res2, msg2 = check(True)

            if not res1 and not res2:
                print msg1
                print msg2

            else:
                print "                     ", msg1
                print "                     ", msg2

    M.write_aiger('miter.aig')

if __name__=="__main__":

    import sys
    cec( netlist.read_aiger(sys.argv[1]), netlist.read_aiger(sys.argv[2]))
