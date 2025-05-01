import json
import sys
from collections import OrderedDict

TERMINATORS = 'jmp', 'br', 'ret'

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
						block.append({'op': 'jmp', 'labels': succ})
			else:
				if i == len(m) - 1:
					succ = []
				else: 
					succ = [list(m.keys())[i + 1]]
			cfg[name] = succ
		
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




def data_flow(analysis, prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	
	cfgs, func_to_blocks = mycfg(prog)

	def pred(blockname, cfg, blocks):
		""" return a list of block names * block body
		"""
		pred_lst = []
		for (name, succ) in cfg.items():
			if blockname in succ:
				pred_lst.append((name, blocks[name]))
		return pred_lst


	def succ(blockname, cfg, blocks):
		""" return a list of block names * block body
		"""
		succ_lst = []
		for name in cfg[blockname]:
			succ_lst.append((name, blocks[name]))
		return succ_lst


	def forward(cfg, blocks, transfer, merge, init, changed):
		worklist = list(blocks.items())
		imap = {}
		omap = {}
		for i, (blockname, block) in enumerate(blocks.items()):
			omap[blockname] = init
			if i == 0:
				imap[blockname] = init

		while len(worklist) > 0:
			blockname, block = worklist.pop()
			imap[blockname] = merge([omap[p] for p in pred(blockname, cfg, blocks)])
			ans = transfer(blockname, block, imap[blockname])
			if changed(ans, omap[blockname]):
				omap[blockname] = ans
				worklist.extend(succ(blockname, cfg, blocks))
		
		return imap, omap
	
	
	def backward(cfg, blocks, transfer, merge, init, changed):
		worklist = list(blocks.items())
		imap = {}
		omap = {}
		for i, (blockname, block) in enumerate(blocks.items()):
			imap[blockname] = init
			if i == 0:
				omap[blockname] = init

		while len(worklist) > 0:
			blockname, block = worklist.pop()
			# print(blockname)
			# print(cfg)
			# print(succ(blockname, cfg))
			omap[blockname] = merge([imap[p] for p in succ(blockname, cfg, blocks)])
			ans = transfer(blockname, block, omap[blockname])
			# print(ans)
			if changed(ans, imap[blockname]):
				imap[blockname] = ans
				worklist.extend(pred(blockname, cfg, blocks))
			
		return imap, omap
		
	def live_analysis():
		func_to_iomap = {}
		for j in range(len(prog['functions'])):
			cfg = cfgs[prog['functions'][j]['name']]
			blocks = func_to_blocks[prog['functions'][j]['name']]

			def transfer(blockname, block, out):
				
				used = set()
				defed = set()

				for instr in block:
					if 'args' in instr:
						for a in instr['args']:
							used.add(a)
					if 'dest' in instr:
						defed.add(instr['dest'])
				return (used | (out - defed))
			
			def merge(lst):
				if len(lst) == 0:
					return set()
				ans = set()
				for item in lst:
					ans |= item
				return ans
			
			def changed(a, b):
				return a != b

			init = set()

			imap, omap = backward(cfg, blocks, transfer, merge, init, changed)
			for k, v in imap.items():
				imap[k] = sorted(list(v))
			for k, v in omap.items():
				omap[k] = sorted(list(v))
			
			func_to_iomap[prog['functions'][j]['name']] = (imap, omap)
		return func_to_iomap

				
	if analysis == "live analysis":
		return live_analysis()

def dominators(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	
	cfgs, func_to_blocks = mycfg(prog)

	def pred(blockname, cfg, blocks):
		""" return a list of block names * block body
		"""
		pred_lst = []
		for (name, succ) in cfg.items():
			if blockname in succ:
				pred_lst.append((name, blocks[name]))
		return pred_lst


	def succ(blockname, cfg, blocks):
		""" return a list of block names * block body
		"""
		succ_lst = []
		for name in cfg[blockname]:
			succ_lst.append((name, blocks[name]))
		return succ_lst

	domed_map = {} # domed[a] = {b} means b dominates a: E-B-A
	dom_frontier_map = {}
	dom_tree_map = {}

	for j in range(len(prog['functions'])):
		cfg = cfgs[prog['functions'][j]['name']]
		blocks = func_to_blocks[prog['functions'][j]['name']]
		# print("cfg", blocks)

		domed = {} # blockname -> [blockname]
		val = set(blocks.keys())
		for blockname, _ in blocks.items():
			domed[blockname] = val

		entry_name, _ = next(iter(blocks.items()))
		domed[entry_name] = {entry_name}
		
		flag = True

		while flag:
			flag = False

			for block_name, _ in blocks.items():
				if block_name == entry_name:
					continue
				
				ans = set()

				p = pred(block_name, cfg, blocks)
				if len(p) == 0:
					ans = set()
				else:
					p_name, _ = p[0]
					ans = set(domed[p_name])
				for p_name, _ in p:
					ans &= domed[p_name]
				ans |= {block_name}
				# if j == 3 and block_name == "then.7":
				# 	print("====", ans)

				if domed[block_name] != ans:
					domed[block_name] = ans
					flag = True
		dom = {} # dom[a] = set(b) means a dominates b: E-A-B
		for key, lst in domed.items():
			for name in lst:
				if (name in dom) == False:
					dom[name] = set()
				dom[name].add(key)

		dom_frontier = {} # succ(A's dominators) - A's dominators
		for block_name, _ in blocks.items():
			dom_frontier[block_name] = set()
			for dom_name in dom[block_name]:
				dom_frontier[block_name] |= set(cfg[dom_name])
			dom_frontier[block_name] -= dom[block_name]

		# tree
		dom_tree = {} # name -> succ
		# for name, s in dom.items():
		# 	print("tree ", name)
		# 	print(s)
		# 	print(cfg[name])
		# 	dom_tree[name] = s & set(cfg[name])
		dom_inv_strict = {a: {b for b in bs if b != a}
                      for a, bs in dom.items()}
		dom_inv_strict_2x = {a: set().union(*(dom_inv_strict[b] for b in bs))
							for a, bs in dom_inv_strict.items()}
		dom_tree = {
			a: {b for b in bs if b not in dom_inv_strict_2x[a]}
			for a, bs in dom_inv_strict.items()
    	}

		domed_ans = {}
		dom_tree_ans = {}
		dom_frontier_ans = {}
		for block_name, block_dom in domed.items():
			domed_ans[block_name] = sorted(list(block_dom))
		for block_name, dom_succ in dom_tree.items():
			dom_tree_ans[block_name] = sorted(list(dom_succ))
		for block_name, block_frontier in dom_frontier.items():
			dom_frontier_ans[block_name] = sorted(list(block_frontier))
				
		domed_map[prog['functions'][j]['name']] = domed_ans
		dom_tree_map[prog['functions'][j]['name']] = dom_tree_ans
		dom_frontier_map[prog['functions'][j]['name']] = dom_frontier_ans
		# how to verify?
	# return domed_map			
	return domed_map, dom_tree_map, dom_frontier_map			
	
def into_ssa(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	
	cfgs, func_to_blocks = mycfg(prog)
	domed_map, dom_tree_map, dom_frontier_map = dominators(prog)

	for j in range(len(prog['functions'])):
		cfg = cfgs[prog['functions'][j]['name']]
		blocks = func_to_blocks[prog['functions'][j]['name']]
		df = dom_frontier_map[prog['functions'][j]['name']] # blockname -> [frontiers]
		dom_tree = dom_tree_map[prog['functions'][j]['name']] # blockname -> [blockname]

		types = {} # old var name -> type, ignore undefined?
		vars = set()
		func = prog['functions'][j]
		for instr in func['instrs']:
			if 'args' in instr:
				for a in instr['args']:
					vars.add(a)
			if 'dest' in instr:
				vars.add(instr['dest'])
				if 'type' in instr:
					types[instr['dest']] = instr['type']
		
		defs = {} # var -> set(blocks)
		for block_name, block_body in blocks.items():
			for instr in block_body:
				if 'dest' in instr:
					if instr['dest'] not in defs:
						defs[instr['dest']] = set()
					defs[instr['dest']].add(block_name)
		
		# phi node insertion
		phi_map = {name: [] for name, _ in blocks.items()} # blockname -> [vars]
		for v, v_def in defs.items():
			def_lst = list(v_def)

			while def_lst:
				d = def_lst.pop()
				for fr_name in df[d]:
					if fr_name not in phi_map:
						phi_map[fr_name] = []
					if v not in phi_map[fr_name]:
						phi_map[fr_name].append(v)
						if fr_name not in def_lst:
							def_lst.append(fr_name)
		# print()
		# print(dom_tree)
		# print(defs)
		# print(df)
		# print(phi_map)
		# renaming
		sts = {} # var -> a stack list
		undefs = {} 
		gets = {} # block_name -> [(old_var_name, new name)]
		sets = {} # block_name -> [(get_block, old_var_name, value)]
		cnts = {} # var -> cnt

		for v in vars:
			sts[v] = []
			cnts[v] = 0

		if 'args' in func:
			for item in func['args']:
				n = item['name']
				sts[n] = [n]
				types[n] = item['type']

		def fresh_name(old):
			# print(old)
			cnt = cnts[old]
			new_name = f"{old}_{cnt}"
			cnts[old] += 1
			sts[old].append(new_name)
			return new_name
		
		def get_name(old):
			if old in sts and sts[old]:
				return sts[old][-1]
			sts[old] = [f"{old}.undef"]
			# undefs.add((old, sts[old][-1]))
			undefs[old] = sts[old][-1]
			cnts[old] = 1
			return sts[old][-1]

		def rename(block_name, block_body, sts):
			# print(block_name)
			gets[block_name] = {}
			saved_sts = dict(sts)
			if block_name in phi_map:
				# print(phi_map[block_name])
				for var in phi_map[block_name]:
					# print(var)
					new_name = fresh_name(var)
					# gets[block_name].append((var, new_name))
					gets[block_name][var] = new_name

			for instr in block_body:
				# print(instr)
				if 'args' in instr:
					for i in range(len(instr['args'])):
						arg = instr['args'][i]
						instr['args'][i] = get_name(arg)

				if 'dest' in instr:
					dest = instr['dest']
					new_name = fresh_name(dest)
					instr['dest'] = new_name
				# print(instr)
				# print()

			for s in cfg[block_name]:
				if block_name not in sets:
					sets[block_name] = []
				for p in phi_map[s]:
					sets[block_name].append((s, p, get_name(p)))

			for dom_name in dom_tree[block_name]:
				if dom_name != block_name:
					rename(dom_name, blocks[dom_name], sts)

			sts = dict(saved_sts)
		
		entry_name, entry_body = next(iter(blocks.items()))
		rename(entry_name, entry_body, sts)
		
		# add gets and sets and undefs
		for var, undef in undefs.items():
			instr = {
				'op': 'undef',
				'type': types[var],
				'dest': undef
			}
			entry_body.insert(0, instr)
		
		for block_name, m in gets.items():
			block = blocks[block_name]
			for old_var, new_var in m.items():
				instr = {
					'op': 'get',
					'type': types[old_var],
					'dest': new_var
				}
				block.insert(0, instr)

		# print(gets)
		for block_name, lst in sets.items():
			block = blocks[block_name]
			for get_block, old_var, value in lst:
				new_name = gets[get_block][old_var]
				instr = {
					'op': 'set', 
					'args': [new_name, value]
				}
				block.insert(-1, instr)
		
		sol = []
		for block_name, block in blocks.items():
			sol.append({'label': block_name})
			sol.extend(block)
		prog['functions'][j]['instrs'] = sol
	
	return prog


def out_of_ssa(prog = ""):
	if prog == "":
		prog = json.load(sys.stdin)
	for j in range(len(prog['functions'])):
		instrs = prog['functions'][j]['instrs']
		func = prog['functions'][j]

		types = {} # old var name -> type, ignore undefined?
		if 'args' in func:
			for item in func['args']:
				n = item['name']
				types[n] = item['type']
		for instr in instrs:
			if 'dest' in instr:
				if 'type' in instr:
					types[instr['dest']] = instr['type']

		ans = []
		for instr in instrs:
			if 'op' in instr:
				match instr['op']:
					case 'set':
						new_instr = {
							'op': 'id',
							'type': types[instr['args'][1]],
							'dest': instr['args'][0],
							'args': [instr['args'][1]]
						}
						ans.append(new_instr)
					case 'get':
						pass
					case 'undef': # workaround, don't know why undef is not a valid opcode
						value = 0
						match instr['type']:
							case 'int':
								t = 0
							case 'bool':
								t = True
						
						new_instr = {
							'op': 'const',
							'type': instr['type'],
							'dest': instr['dest'],
							'value': value
						}
						ans.append(new_instr)
					case _:
						ans.append(instr)
			else:
				ans.append(instr)
		
		prog['functions'][j]['instrs'] = ans
	
	return prog
			

if __name__ == '__main__':
	# DCE()
	# LCV()
	# print(data_flow("live analysis"))
	# print(dominators())
	# print(json.dumps((into_ssa()), indent=2, sort_keys=True))
	print(json.dumps(out_of_ssa(into_ssa()), indent=2, sort_keys=True))