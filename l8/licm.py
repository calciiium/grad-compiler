import json
import sys

from dom import *
from df import *
from cfg import *


def find_back_edges(blocks, entry):
	def dfs(u, adj, visited, inStack, discovery, finish, timeStamp, edges):
		visited[u] = True
		inStack[u] = True
		discovery[u] = timeStamp[0] = timeStamp[0] + 1
		
		for v in adj[u]:
			if not visited[v]:
				# Tree Edge
				edges[0].append([u, v])
				dfs(v, adj, visited, inStack, discovery, finish, timeStamp, edges)
			else:
				if inStack[v]:
					# Back Edge
					edges[2].append([u, v])
				elif discovery[u] < discovery[v]:
					# Forward Edge
					edges[1].append([u, v])
				else:
					# Cross Edge
					edges[3].append([u, v])
		
		inStack[u] = False
		finish[u] = timeStamp[0] = timeStamp[0] + 1

	def classifyEdges(adj):
		n = len(adj)
		
		discovery = {node : 0 for node in adj.keys()} 
		finish = {node : 0 for node in adj.keys()} 
		visited = {node : False for node in adj.keys()} 
		inStack = {node : False for node in adj.keys()} 
		timeStamp = [0]
		
		edges = [[] for _ in range(4)]
		
		for node in adj.keys():
			if not visited[node]:
				dfs(node, adj, visited, inStack, discovery, finish, timeStamp, edges)
		
		return edges[2]
	
	return classifyEdges(blocks)

def is_invariant(instr, loop, blocks, reaching_defs, invariants):
	# print(instr)
	if 'args' not in instr:
		return True  

	for arg in instr['args']:
		defs = reaching_defs.get(arg, set())
		# print(arg, defs)
		if not defs:
			continue

		defs_in_loop = [d for d in defs if any(d == block_name for block_name in loop)]
		if len(defs_in_loop) > 1:
			return False

		if len(defs_in_loop) == 1:
			def_instr = defs_in_loop[0]
			if not any(def_instr == inv[1] for inv in invariants):
				return False 

	return True

def is_safe_instr(instr):
	return instr.get("op", "") not in ["print", "store", "load", "call", "div"] and "labels" not in instr

def create_preheader(header, blocks, succ, loop):
	preheader = f"{header}_preheader"
	blocks[preheader] = []

	for pred in list(blocks.keys()):
		if pred != preheader and header in succ[pred] and pred not in loop:
			succ[pred].remove(header)
			succ[pred].append(preheader)
			blocks[pred][-1]["labels"] = [preheader if label == header else label for label in blocks[pred][-1]["labels"]]

	succ[preheader] = [header]
	blocks[preheader].append({"op": "jmp", "labels": [header]})

	return preheader

def def_dom_all_uses(instr, succ, block_name, loop, blocks, dom):
	# print(instr)
	if "dest" not in instr:
		return True

	dest = instr["dest"]
	for block in loop:
		for i in blocks[block]:
			if "args" in i and dest in i["args"]:
				if block_name not in dom[block]:
					return False
	return True

def no_other_def_in_loop(instr, succ, block_name, loop, blocks):
	# print(instr)
	# print(loop)
	if "dest" not in instr:
		return True

	dest = instr["dest"]
	for block in loop:
		cnt = 0
		for i in blocks[block]:
			if "dest" in i and i["dest"] == dest:
				cnt += 1
		if (block == block_name and cnt > 1) or (block != block_name and cnt > 0):
			# print(cnt, block, block_name)
			return False
	return True

def dom_loop_exits(instr, succ, block_name, loop, blocks, dom):
	# print(instr)
	# print(loop)
	# print(dom)
	if "dest" not in instr:
		return True

	dest = instr["dest"]
	for block in loop:
		for succ_block in succ[block]:
			if succ_block not in loop:
				if block_name not in dom[succ_block]:
					return False
	return True

if __name__ == '__main__':
	bril = json.load(sys.stdin)

	for j in range(len(bril['functions'])):
		func = bril['functions'][j]
		blocks = block_map(form_blocks(func['instrs']))
		add_entry(blocks)
		add_terminators(blocks)

		entry = next(iter(blocks.keys()))

		succ = {name: successors(block[-1]) for name, block in blocks.items()}
		dom = get_dom(succ, list(blocks.keys())[0])
		# print(blocks)
		# print(json.dumps((blocks), indent=2, sort_keys=True))
		# print(succ)
		# print(entry)
		# print(find_back_edges(succ, entry))
		_, reaching_defs = df_worklist(blocks, ANALYSES["reaching"])
		# print(reaching_defs)

		back_edges = find_back_edges(succ, entry)
		natural_loops = []
		for u, v in back_edges:
			loop = set()
			stack = [u]
			while stack:
				node = stack.pop()
				if node not in loop:
					loop.add(node)
					if node != v:
						stack.extend(pred for pred in blocks if node in succ[pred])
			natural_loops.append((v, loop))

		# print(natural_loops)

		for header, loop in natural_loops:
			invariants = []
			while True:
				flag = False
				for block_name in loop:
					block = blocks[block_name]
					for instr in block[:-1]:  
						if (block_name, instr) not in invariants and is_invariant(instr, loop, blocks, reaching_defs[block_name], invariants):
							invariants.append((block_name, instr))
							flag = True
				if not flag:
					break
			# print((invariants))

			preheader_created = False
			preheader = ""
			for block_name, instr in invariants:
				if is_safe_instr(instr) and def_dom_all_uses(instr, succ, block_name, loop, blocks, dom) and no_other_def_in_loop(instr, succ, block_name, loop, blocks) and dom_loop_exits(instr, succ, block_name, loop, blocks, dom):
					if not preheader_created:
						preheader = create_preheader(header, blocks, succ, loop)
						preheader_created = True
					# print(instr)
					blocks[block_name].remove(instr)
					blocks[preheader].insert(-1, instr)
		bril['functions'][j]['instrs'] = reassemble(blocks)
	json.dump(bril, sys.stdout, indent=2, sort_keys=True)