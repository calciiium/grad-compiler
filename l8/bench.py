import json
import sys

from dom import *
from df import *
from cfg import *

if __name__ == '__main__':
	bril = json.load(sys.stdin)

	for j in range(len(bril['functions'])):
		func = bril['functions'][j]
		blocks = block_map(form_blocks(func['instrs']))
		add_entry(blocks)
		add_terminators(blocks)
		bril['functions'][j]['instrs'] = reassemble(blocks)
	json.dump(bril, sys.stdout, indent=2, sort_keys=True)