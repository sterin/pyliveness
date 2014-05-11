from pyaig import *

def strip(aig_in, aig_out, po):

    with open(aig_in, 'r') as f:
        aig = read_aiger(f)

    utils.po_info.remove(aig)

    with open(aig_out, 'w') as f:
        write_aiger(aig, f)

import sys

strip(sys.argv[1], sys.argv[2], int(sys.argv[3]))
