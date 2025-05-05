import sys
import json
from collections import namedtuple

from form_blocks import form_blocks
import cfg

# A single dataflow analysis consists of these part:
# - forward: True for forward, False for backward.
# - init: An initial value (bottom or top of the latice).
# - merge: Take a list of values and produce a single value.
# - transfer: The transfer function.
Analysis = namedtuple('Analysis', ['forward', 'init', 'merge', 'transfer'])


def union(sets):
    out = set()
    for s in sets:
        out.update(s)
    return out


def df_worklist(blocks, analysis):
    """The worklist algorithm for iterating a data flow analysis to a
    fixed point.
    """
    preds, succs = cfg.edges(blocks)

    # Switch between directions.
    if analysis.forward:
        first_block = list(blocks.keys())[0]  # Entry.
        in_edges = preds
        out_edges = succs
    else:
        first_block = list(blocks.keys())[-1]  # Exit.
        in_edges = succs
        out_edges = preds

    # Initialize.
    in_ = {first_block: analysis.init}
    out = {node: analysis.init for node in blocks}

    # Iterate.
    worklist = list(blocks.keys())
    while worklist:
        node = worklist.pop(0)

        inval = analysis.merge(out[n] for n in in_edges[node])
        in_[node] = inval

        outval = analysis.transfer(node, blocks[node], inval)

        if outval != out[node]:
            out[node] = outval
            # print(node, outval)
            worklist += out_edges[node]

    if analysis.forward:
        return in_, out
    else:
        return out, in_


def fmt(val):
    """Guess a good way to format a data flow value. (Works for sets and
    dicts, at least.)
    """
    if isinstance(val, set):
        if val:
            return ', '.join(v for v in sorted(val))
        else:
            return '∅'
    elif isinstance(val, dict):
        if val:
            return ', '.join('{}: {}'.format(k, v)
                             for k, v in sorted(val.items()))
        else:
            return '∅'
    else:
        return str(val)


def run_df(bril, analysis):
    for func in bril['functions']:
        # Form the CFG.
        blocks = cfg.block_map(form_blocks(func['instrs']))
        cfg.add_terminators(blocks)

        in_, out = df_worklist(blocks, analysis)
        for block in blocks:
            print('{}:'.format(block))
            print('  in: ', fmt(in_[block]))
            print('  out:', fmt(out[block]))


def gen(block):
    """Variables that are written in the block.
    """
    return {i['dest'] for i in block if 'dest' in i}


def use(block):
    """Variables that are read before they are written in the block.
    """
    defined = set()  # Locally defined.
    used = set()
    for i in block:
        used.update(v for v in i.get('args', []) if v not in defined)
        if 'dest' in i:
            defined.add(i['dest'])
    return used


def cprop_transfer(node, block, in_vals):
    out_vals = dict(in_vals)
    for instr in block:
        if 'dest' in instr:
            if instr['op'] == 'const':
                out_vals[instr['dest']] = instr['value']
            else:
                out_vals[instr['dest']] = '?'
    return out_vals


def cprop_merge(vals_list):
    out_vals = {}
    for vals in vals_list:
        for name, val in vals.items():
            if val == '?':
                out_vals[name] = '?'
            else:
                if name in out_vals:
                    if out_vals[name] != val:
                        out_vals[name] = '?'
                else:
                    out_vals[name] = val
    return out_vals

def reach_union(lst):
    inp = []
    for s in lst:
        inp.append(s)
    # print(inp)
    ans = {}
    keys = set()
    for m in inp:
        keys.update(m.keys())
    
    for k in keys:
        ans[k] = set()
        for m in inp:
            if k in m:
                ans[k].update(m[k])
    # print(ans)
    # print()
    return ans

def reach_transfer(node, block, in_vals):
    """ var |-> set(node)
    """
    # print((block))
    # print(node, in_vals)
    ans = dict(in_vals)
    # print(block)
    defs = {instr['dest'] for instr in block if 'dest' in instr}
    # print(defs)
    for var, _ in ans.items():
        if var in defs:
            ans[var] = {node}
    for var in defs:
        if var not in ans:
            ans[var] = set()
        ans[var].add(node)
    # print(ans)
    # print()
    return ans

ANALYSES = {
    # A really really basic analysis that just accumulates all the
    # currently-defined variables.
    'defined': Analysis(
        True,
        init=set(),
        merge=union,
        transfer=lambda _, block, in_: in_.union(gen(block)),
    ),

    # Live variable analysis: the variables that are both defined at a
    # given point and might be read along some path in the future.
    'live': Analysis(
        False,
        init=set(),
        merge=union,
        transfer=lambda _, block, out: use(block).union(out - gen(block)),
    ),

    # A simple constant propagation pass.
    'cprop': Analysis(
        True,
        init={},
        merge=cprop_merge,
        transfer=cprop_transfer,
    ),

    # reaching definition
    'reaching': Analysis(
        True, 
        init={},
        merge=reach_union,
        transfer=reach_transfer,
    ),
}

if __name__ == '__main__':
    bril = json.load(sys.stdin)
    run_df(bril, ANALYSES[sys.argv[1]])
