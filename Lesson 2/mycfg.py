import json
import sys
from collections import OrderedDict

TERMINATORS = 'jmp', 'br', 'ret'

def form_blocks(body):
	cur_block = []

	for instr in body:
		if 'op' in instr:  # actual instr
			cur_block.append(instr)

			if instr['op'] in TERMINATORS:
				# call is not a terminator
				#print(cur_block)
				if cur_block:
					print("x")
					blocks.append(cur_block)
					print(blocks)

				cur_block = []
		else:
			if cur_block:
				#print(cur_block)
				blocks.append(cur_block)
			cur_block = [instr]
	
	if cur_block:
		blocks.append(cur_block)


def mycfg():
	prog = json.load(sys.stdin)
	cfgs = {}
	func_to_blocks = {}

	for func in prog['functions']:
		print(func['name'])
		blocks = []
		m = OrderedDict()
		cur_block = []

		def add_block(block):
			if block:
				if 'label' in block[0]:
					name = block[0]['label']
					block = block[1:]
				else:
					name = '{}_b{}'.format(func['name'], len(m))
				blocks.append(block)
				m[name] = block

		for instr in func['instrs']:
			if 'op' in instr:  # actual instr
				cur_block.append(instr)

				if instr['op'] in TERMINATORS:
					# call is not a terminator

					add_block(cur_block)
					cur_block = []
			else:
				add_block(cur_block)
				cur_block = [instr]
		
		add_block(cur_block)

		# for block in blocks:
			# print(block)
		
		# print()
		# print(m)
		cfg = {}
		for i, (name, block) in enumerate(m.items()):
			if block:
				last = block[-1]

				if last['op'] in ('jmp', 'br'):
					succ = last['labels']
				elif last['op'] == 'ret':
					succ = []
				else:
					if i == len(m) - 1:
						succ = []
					else: 
						succ = [list(m.keys())[i + 1]]
			else:
				if i == len(m) - 1:
					succ = []
				else: 
					succ = [list(m.keys())[i + 1]]
			cfg[name] = succ
			# print(name)
			# print(succ)
		
		cfgs[func['name']] = cfg
		func_to_blocks [func['name']] = m
	
	return cfgs, func_to_blocks

if __name__ == '__main__':
	print(mycfg())