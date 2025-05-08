import json
import sys
from collections import OrderedDict
import subprocess

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
					# print("x")
					blocks.append(cur_block)
					# print(blocks)

				cur_block = []
		else:
			if cur_block:
				#print(cur_block)
				blocks.append(cur_block)
			cur_block = [instr]
	
	if cur_block:
		blocks.append(cur_block)


def mycfg(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	cfgs = {}
	func_to_blocks = {}

	for func in prog['functions']:
		# print(func['name'])
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

def DCE(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)

	for j in range(len(prog['functions'])):
		func = prog['functions'][j]
		flag = True

		while flag:

			flag = False

			used = set()

			for instr in func['instrs']:
				if 'args' in instr:
					for a in instr['args']:
						used.add(a)
			sol = []
			
			for instr in func['instrs']:
				if 'dest' in instr and instr['dest'] not in used:
					flag = True
				else:
					sol.append(instr)
		
			func['instrs'] = sol

			last_def = {} # vars that has been defined but never used

			for i in range(len(func['instrs'])):
				instrs = func['instrs']
				instr = instrs[i]
				if 'args' in instr:
					for v in instr['args']:
						if v in last_def:
							del last_def[v]

				if 'dest' in instr:
					if instr['dest'] in last_def:
						func['instrs'][last_def[instr['dest']]] = ""

					last_def[instr['dest']] = i
			
			sol = []

			for instr in func['instrs']:
				if instr != "":
					sol.append(instr)
				else:
					flag = True

			func['instrs'] = sol
		
		prog['functions'][j] = func
	
	print(json.dumps(prog))
	
	return prog


# why not directly replace everything w canonicl form, including the dest
# what if the same variable get reassigned to another val

"""
EST_OP( "phi",    PHI);
TEST_OP( "alloc",  ALLOC);
TEST_OP( "free",   FREE);
TEST_OP( "store",  STORE);
TEST_OP( "load",   LOAD);
TEST_OP( "ptradd", PTRADD);
TEST_OP( "fadd",   FADD);
TEST_OP( "fmul",   FMUL);
TEST_OP( "fsub",   FSUB);
TEST_OP( "fdiv",   FDIV);
TEST_OP( "feq",    FEQ);
TEST_OP( "flt",    FLT);
TEST_OP( "fle",    FLE);
TEST_OP( "fgt",    FGT);
TEST_OP( "fge",    FGE);
"""
def LCV(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	cfgs, func_to_blocks = mycfg(prog)

	for j in range(len(prog['functions'])):
		var2num = {} # var |-> numbering
		val2num = {} # function args: (name, type) || others (op, args list / value, optional type) || unknown (var)
		num2can = {} # numbering |-> canonical var
		num = 0

		# preload function arguments 
		if 'args' in prog['functions'][j]:
			args = prog['functions'][j]['args']
			for arg in args:
				name = arg['name']
				typ = arg['type']
				var2num[name] = num
				val2num[(name, typ)] = num
				num2can[num] = name
				num += 1
		
		cfg = cfgs[prog['functions'][j]['name']]
		blocks = func_to_blocks[prog['functions'][j]['name']]

		sol = []

		for block_name, block in blocks.items(): # order of blocks is preserved
			for i in range(len(block)):
				instr = block[i]
				op = instr['op']

				if 'dest' not in instr:
					continue

				def find_num_or_add_var(var):
					"""for right side of assign
					"""
					nonlocal num
					if var in var2num:
						return var2num[var]
					
					var2num[var] = num
					val2num[(var)] = num
					num2can[num] = var
					num += 1
					return num - 1

				def update(dest, val): 
					nonlocal num
					n = -1
					# val2num and num2can
					if val in val2num:
						n = val2num[val]
					else:
						n = num
						val2num[val] = n
						num2can[n] = dest
						num += 1

					# var2num
					if dest not in var2num:
						var2num[dest] = n
					else:
						prev_num = var2num[dest]
						del var2num[dest]
						alter_can = next((key for key, value in var2num.items() if value == prev_num), None)
						if alter_can:
							num2can[prev_num] = alter_can
						else:
							del num2can[prev_num]
							for key in [key for key, value in val2num.items() if value == prev_num]:
								del val2num[key]
						
						var2num[dest] = n

				match op:
					case "const":
						# print(num)
						t = ("const", instr['value'], instr['type'])
						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							pass
						update(instr['dest'], t)

					case "add" | "mul" | "eq" | "and" | "or": # ascending order
						assert len(instr['args']) == 2, "incorrect number of args"

						args = [find_num_or_add_var(arg) for arg in instr['args']]
						if args[0] > args[1]:
							tem = args[0]
							args[0] = args[1]
							args[1] = tem

						t = (op, ) + tuple(args)
						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							block[i]['args'] = [num2can[a] for a in args]
						update(instr['dest'], t)
							
					case "sub" | "div":
						assert len(instr['args']) == 2, "incorrect number of args"

						args = [find_num_or_add_var(arg) for arg in instr['args']]
						t = (op, ) + tuple(args)
						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							block[i]['args'] = [num2can[a] for a in args]
						update(instr['dest'], t)

					case "lt" | "le":
						assert len(instr['args']) == 2, "incorrect number of args"
						args = [find_num_or_add_var(arg) for arg in instr['args']]
						t = (op, ) + tuple(args)
						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							block[i]['args'] = [num2can[a] for a in args]
						update(instr['dest'], t)

					case "gt" | "ge":
						assert len(instr['args']) == 2, "incorrect number of args"
						args = [find_num_or_add_var(arg) for arg in instr['args']]

						tem = args[0]
						args[0] = args[1]
						args[1] = tem
						t = ("lt" if op == "gt" else "le", ) + tuple(args)

						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							block[i]['args'] = [num2can[a] for a in args]
							block[i]['op'] = "lt" if op == "gt" else "le"
						update(instr['dest'], t)

					case "not":
						assert len(instr['args']) == 1, "incorrect number of args"
						args = [find_num_or_add_var(arg) for arg in instr['args']]
						t = (op, ) + tuple(args)
						if t in val2num:
							block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						else:
							block[i]['args'] = [num2can[a] for a in args]
						update(instr['dest'], t)
						
					case "call":
						pass
					case "jmp" | "br" | "ret":
						assert False, "no dest"
					case "id":
						assert len(instr['args']) == 1, "incorrect number of args"

						arg_num = find_num_or_add_var(instr['args'][0])
						block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[arg_num]], 'type': instr['type']}
						update(instr['dest'], next((key for key, value in val2num.items() if value == arg_num), None))

						# args = [find_num_or_add_var(arg) for arg in instr['args']]
						# t = (op, ) + tuple(args)
						# if t in val2num:
						# 	block[i] = {'dest': instr['dest'], 'op': 'id', 'args': [num2can[val2num[t]]], 'type': instr['type']}
						# else:
						# 	block[i]['args'] = [num2can[a] for a in args]
						# update(instr['dest'], t)
					case "nop":
						pass
					case "print":
						assert False, "no dest"
					case _:
						pass
				
			sol.append({"label": block_name})
			sol.extend(block)

			# empty tables
			var2num = {} # var |-> numbering
			val2num = {} # function args: (name, type) || others (op, args list / value, optional type)
			num2can = {} # numbering |-> canonical var
			num = 0
		prog['functions'][j]['instrs'] = sol
	
	# print(json.dumps(prog))
	prog = DCE(prog)
	return prog

def tracing(trace_file="trace.out"):
	prog = json.load(sys.stdin)

	cmd = ["deno", "run", "--allow-write", "brili.ts"]
	subprocess.run(cmd, input=json.dumps(prog), text=True, stdout=subprocess.DEVNULL, stderr = subprocess.DEVNULL)

	instrs = []
	jmp_cnt = -1 # index
	with open(trace_file, "r") as f:
		for line in f:
			line = line.strip()
			if not line:
				continue
			instr = json.loads(line)
			if 'op' in instr and instr['op'] == 'jmp':
				jmp_cnt = len(instrs)
			instrs.append(instr)
	# print(instrs)
	
	if (jmp_cnt == -1):
		print(json.dumps(prog))
		return

	jmp = instrs[jmp_cnt]
	instrs = instrs[:jmp_cnt]

	speculate = []
	for instr in instrs:
		op = instr['op']
		match op:
			case "br":
				new_instr = {
					'op': 'guard',
					'args': instr['args'],
					'labels': ['main__b0'],
				}
				speculate.append(new_instr)
			case "jmp":
				pass
			case _:
				speculate.append(instr)

	cmt = {
		'op': 'commit',
	}

	failed_lbl = {
		'label': 'main__b0',
	}
	
	spec = {
		'op': 'speculate',
	}

	speculate.insert(0, spec)
	speculate.append(cmt)
	speculate.append(jmp)
	speculate.append(failed_lbl)

	for j in range(len(prog['functions'])):
		func = prog['functions'][j]
		funcname = func['name']
		if funcname != "main":
			continue
		main_instrs = func['instrs']
		# prog['functions'][j]['instrs'].extend(speculate)
		prog['functions'][j]['instrs'] = speculate + main_instrs
	
	print(json.dumps(prog))
	return instrs


if __name__ == '__main__':
	# LCV()
	# DCE()
	tracing()