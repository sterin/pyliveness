from pyzz import *


def fold_fairness_constraints(N, all_fcs):

    if len(all_fcs) == 1:
        return all_fcs[0]

    flops = [ N.add_Flop() for _ in all_fcs ]
    fair = conjunction(N, flops)

    for fc, ff in zip(all_fcs, flops):
        ff[0] = fair.ite(fc, ff|fc )

    return fair
