import algorithm
import deques
import strutils
import sequtils
import sets
import tables
import strformat

type
  # Instructions parsed directly from input as expected
  InstructionKind = enum
    ikInp,
    ikAdd,
    ikMul,
    ikDiv,
    ikMod,
    ikEql
  Register = enum
    rW, rX, rY, rZ

  # for binary operations; the second argument can be a register or literal
  SlotKind = enum
    skReg, skLit
  Slot = object
    case kind: SlotKind
    of skReg:
      reg: Register
    of skLit:
      lit: int

  # An instruction can either be a binary operator or unary
  # (the only unary operator is inp)
  Instruction = object
    case kind: InstructionKind
    of ikInp:
      reg: Register
      idx: Natural
    of ikAdd .. ikEql:
      reg1 : Register
      slot2: Slot

func parseReg(regstr: string): Register =
  case regstr
  of "w": return rW
  of "x": return rX
  of "y": return rY
  of "z": return rZ

func parseSlot(slotstr: string): Slot =
  if slotstr[0] == '-' or slotstr[0] in Digits:
    result = Slot(kind: skLit, lit: slotstr.parseInt)
  else:
    result = Slot(kind: skReg, reg: slotstr.parseReg)

proc parseInput(fname: string): seq[Instruction] =
  result = @[]
  var inp_idx = 0
  for line in fname.lines:
    let spt = line.split " "
    case spt[0]
    of "inp":
      result.add Instruction(kind: ikInp, reg: parseReg(spt[1]), idx: inp_idx)
      inc inp_idx
    of "add":
      result.add Instruction(kind: ikAdd, reg1: parseReg(spt[1]), slot2: parseSlot(spt[2]))
    of "mul":
      result.add Instruction(kind: ikMul, reg1: parseReg(spt[1]), slot2: parseSlot(spt[2]))
    of "div":
      result.add Instruction(kind: ikDiv, reg1: parseReg(spt[1]), slot2: parseSlot(spt[2]))
    of "mod":
      result.add Instruction(kind: ikMod, reg1: parseReg(spt[1]), slot2: parseSlot(spt[2]))
    of "eql":
      result.add Instruction(kind: ikEql, reg1: parseReg(spt[1]), slot2: parseSlot(spt[2]))
    else:
      discard

# ALU originally implemented as an attempt to brute-force the problem
# Now used to verify that any optimizations that I do still work
type
  ALU = object
    regs: array[Register, int]
func `[]`(self: ALU; idx: Register): int {.inline.} =
  self.regs[idx]
proc `[]=`(self: var ALU; idx: Register; val: int) {.inline.} =
  self.regs[idx] = val

func execBinop(op: range[ikAdd..ikEql]; a, b: int): int =
  case op
  of ikAdd: return a + b
  of ikMul: return a * b
  of ikDiv: return a div b
  of ikMod: return a mod b
  of ikEql: return (if a == b: 1 else: 0)

func execProgram(prog: openarray[Instruction]; input: openarray[int]): ALU =
  # result defaults initialized to 0
  var inp_ptr = 0
  for inst in prog:
    case inst.kind
    of ikInp:
      result[inst.reg] = input[inp_ptr]
      inc inp_ptr
    of ikAdd .. ikEql:
      let v1 = result[inst.reg1]
      let v2 = case inst.slot2.kind
      of skReg:
        result[inst.slot2.reg]
      of skLit:
        inst.slot2.lit
      result[inst.reg1] = execBinop(inst.kind, v1, v2)

# Types used for attempting to apply some optimizations to remove
# some useless instructions. I did not examine my input too closely except
# for the first few lines, where there were instances of i.e., modifying a
# register and then just setting it to 0. My initial thought was therefore
# that the main challenge here would be to eliminate dead code, leading to
# a simple program that I could examine. There was also a lot of, "I've always
# wanted to try doing a compiler/interpreter/whatever, anyway", though I
# certainly know very little of how to go about that.
# If I had looked a little more closely at my input, I would have seen
# that there really aren't that many optimizations to be done
type
  # Types for a syntax graph (called a ParseTree here)
  NodeKind = enum
    nkInp,
    nkLit,
    nkBinOp,
  # I'd have like to use a ref object here, but the built-in hashtables
  # don't work on references. They do work on pointers, though, because pointers
  # don't get moved around
  # So, fun fact: this entire program leaks memory because I couldn't be bothered
  # to clean up after myself
  ParseTreePtr = ptr ParseTree
  ParseTree = object
    case kind: NodeKind
    of nkInp:
      reg: Register
      idx: Natural
    of nkLit:
      n: int
    of nkBinOp:
      inst_kind: range[ikAdd .. ikEql]
      left, right: ParseTreePtr

# whether an instruction modifies the given register
func setsReg(inst: Instruction; reg: Register): bool =
  case inst.kind
  of ikInp:
    return inst.reg == reg
  else:
    return inst.reg1 == reg

# wrapper around initialization
proc newParseTree: ParseTreePtr =
  result = cast[ParseTreePtr](alloc0(sizeof ParseTree))

# stringify for debugging
# does not recurse
proc `$`(p: ParseTreePtr): string =
  case p.kind
  of nkBinOp:
    result = "<" & $p.inst_kind & ">"
  else:
    result = $p[]

# Generates an instruction dependency tree for the given register
# takes the reversed input. I could have written it in the forwards direction,
# but conceptually this was simpler for me
# ids are unique for each instruction and help develop the edges in the tree
# visited makes sure that we aren't recursing into oblivion
# next_id is for generating nodes that don't correspond to instructions (i.e., literals)
# nullrec is just a dummy node because we need to return something
proc makeDepTreeHelper(rev_input: openarray[Instruction];
                       ids: openarray[int];
                       reg: Register;
                       visited: var Table[int, ParseTreePtr] = initTable[int, ParseTreePtr]();
                       next_id: var int;
                       nullrec: ParseTreePtr): ParseTreePtr =
  # shave off all irrelevant instructions (i.e., those that don't modify reg)
  let (remaining_input, remaining_ids) = block:
    var p = 0
    while p < rev_input.len and not rev_input[p].setsReg(reg):
      inc p
    (rev_input[p .. rev_input.high], ids[p .. ids.high])

  assert remaining_input.len == remaining_ids.len

  if remaining_input.len == 0:
    return nullrec

  let inst = remaining_input[remaining_input.low]
  let id = remaining_ids[remaining_ids.low]
  if id in visited:
    return visited[id]

  result = newParseTree()
  case inst.kind
  of ikInp:
    result[] = ParseTree(kind: nkInp, reg: inst.reg, idx: inst.idx)
  of ikAdd .. ikEql:
    # all binary operator instructions set the register in their first argument,
    # so we chase the dependency chain through that argument
    let left = makeDepTreeHelper(remaining_input[remaining_input.low+1..remaining_input.high],
                                 remaining_ids[remaining_ids.low+1..remaining_ids.high],
                                 reg, visited, next_id, nullrec)
    # the right side of the binary operator might recurse, or it might not
    let right = block:
      case inst.slot2.kind
      of skLit:
        var res = newParseTree()
        res[] = ParseTree(kind: nkLit, n: inst.slot2.lit)
        visited[next_id] = res
        inc next_id
        res
      of skReg:
        makeDepTreeHelper(remaining_input[remaining_input.low+1..remaining_input.high],
                          remaining_ids[remaining_ids.low+1..remaining_ids.high],
                          inst.slot2.reg, visited, next_id, nullrec)
    result[] = ParseTree(kind: nkBinOp, inst_kind: inst.kind, left: left, right: right)
  visited[id] = result


# topological sort (DFS method). helper function to incorporate the `visited` graph
proc topSortHelper(tree: ParseTreePtr; visited: var HashSet[ParseTreePtr];
                   res: var seq[ParseTreePtr]) =
  if tree in visited:
    return
  if tree.kind == nkBinOp:
    topSortHelper(tree.left, visited, res)
    topSortHelper(tree.right, visited, res)

  visited.incl tree
  res.add tree

# topologically sort the dependency tree
# this returns a list such that, for every node in the list, any instructions
# that that node depends on appear after that node
proc topSort(tree: ParseTreePtr): seq[ParseTreePtr] =
  var visited = initHashSet[ParseTreePtr]()
  result = @[]
  topSortHelper(tree, visited, result)
  reverse(result)

# returns a topologically sorted sequence of ParseTreePtrs; see the helper
# function above
proc makeDepTree(input: openarray[Instruction];
                 reg: Register): seq[ParseTreePtr] =

  var rev_input = toSeq(input)
  reverse(rev_input)
  # assign IDs to each instruction in a parallel list
  var ids = newSeq[int](rev_input.len)
  for i in 0 .. ids.high:
    ids[i] = i
  var next_id = ids.high+1
  # ht maps ids to generated ParseTrees
  var ht = initTable[int, ParseTreePtr]()
  let nullrec = newParseTree()
  nullrec[] = ParseTree(kind: nkLit, n: 0)
  ht[-1] = nullrec
  let root = makeDepTreeHelper(rev_input, ids, reg, ht, next_id, nullrec)
  result = topSort(root)


# OPTIMIZATION: fold together any binary operation that operates on two constants
# While AOC input doesn't contain any such operations, any register that is not
# set in an input operation reduces to a constant literal (0), leading to some
# nodes containing operations on two constants
# The algorithm operates on the topologically-sorted instruction dependency graph
proc foldConstants(sorted_tree: openarray[ParseTreePtr]) =
  # go backwards through the tree to make sure that we don't encounter any nodes
  # before we encounter their dependencies
  for idx in countdown(sorted_tree.high, sorted_tree.low):
    let node = sorted_tree[idx]
    if node.kind == nkBinOp:
      if node.left.kind == nkLit and node.right.kind == nkLit:
        node[] = ParseTree(kind: nkLit, n: execBinop(node.inst_kind, node.left.n, node.right.n))

# OPTIMIZATION: fold together nodes when an operation has a guaranteed result (nop
# is a misnomer). For example, adding 0 to something returns that something,
# multiplying by 0 always returns 0, etc.
proc foldNops(sorted_tree: openarray[ParseTreePtr]) =
  for idx in countdown(sorted_tree.high, sorted_tree.low):
    # make sure that we've removed as many constants as possible
    foldConstants(sorted_tree[idx..^1])
    let node = sorted_tree[idx]
    if node.kind == nkBinOp:
      case node.inst_kind
      # if either branch of add is 0, return the other branch
      of ikAdd:
        if node.left.kind == nkLit and node.left.n == 0:
          node[] = node.right[]
        elif node.right.kind == nkLit and node.right.n == 0:
          node[] = node.left[]
      # if either branch of mul is 0, return 0
      # if either branch of mul is 1, return the other branch
      of ikMul:
        if node.left.kind == nkLit:
          if node.left.n == 1:
            node[] = node.right[]
          elif node.left.n == 0:
            node[] = ParseTree(kind: nkLit, n: 0)
        elif node.right.kind == nkLit:
          if node.right.n == 1:
            node[] = node.left[]
          elif node.right.n == 0:
            node[] = ParseTree(kind: nkLit, n: 0)
      # if the right branch is 1, return the left branch
      of ikDiv:
        if node.right.kind == nkLit and node.right.n == 1:
          node[] = node.left[]
        elif node.left.kind == nkLit and node.left.n == 0:
          node[] = ParseTree(kind: nkLit, n: 0)
      # if the right branch is 1, return 0
      # if the left branch is 0, return 0
      of ikMod:
        if node.right.kind == nkLit and node.right.n == 1 or
            node.left.kind == nkLit and node.left.n == 0:
          node[] = ParseTree(kind: nkLit, n: 0)
      # if the two nodes are the same, return 1
      # NOTE: SPECIAL CASE:
      # The problem statement says that each inp will be a single digit (i.e.,
      # 0 .. 9). This means that any eql operatino on an inp and some constant
      # will necessarily return 0 if the constant is not in the range 0 .. 9.
      # This is NOT a general optimization, and is problem-specific
      of ikEql:
        if node.left == node.right:
          node[] = ParseTree(kind: nkLit, n: 1)
        # special case if one of the leaves is input; we know 0 <= inp < 10
        elif node.left.kind == nkInp and node.right.kind == nkLit and not (node.right.n in 0..9):
          node[] = ParseTree(kind: nkLit, n: 0)
        elif node.right.kind == nkInp and node.left.kind == nkLit and not (node.left.n in 0..9):
          node[] = ParseTree(kind: nkLit, n: 0)

# for debugging
proc displayParseTreePtr(self: ParseTreePtr; indent: string = "") =
  case self.kind
  of nkInp..nkLit:
    stdout.write indent
    echo self[]
  else:
    stdout.write indent
    echo self.inst_kind
    displayParseTreePtr(self.left, indent & " |")
    displayParseTreePtr(self.right, indent & " |")

# equality function for ParseTrees, because Nim does not automatically implement
# `==` for variant records records
proc hasSameContents(a, b: ParseTreePtr): bool =
  if a.kind != b.kind:
    return false
  case a.kind
  of nkLit:
    return a.n == b.n
  of nkInp:
    return a.idx == b.idx
  of nkBinOp:
    return a.inst_kind == b.inst_kind and a.left == b.left and a.right == b.right

# Because I was not especially careful with my tree traversal when generating
# the dependency graph, and because each literal is assigned its own node,
# we end up with a lot of duplicate nodes. This removes those duplicates.
#
# Operates on a topologically sorted list of nodes
#
# It's also O(n^2) in nodes
proc dedupTree(sorted_tree: openarray[ParseTreePtr]) =
  var seen_ptrs = newSeq[ParseTreePtr]()

  # loop the tree bottom up
  for idx in countdown(sorted_tree.high, sorted_tree.low):
    let node = sorted_tree[idx]
    var seen : ParseTreePtr = nil
    # check if a node with identical contents has been seen already
    for p in seen_ptrs:
      if hasSameContents(node, p):
        seen = p
        break
    # if not, add it to our "seen" list
    if seen.isNil:
      seen_ptrs.add node
    else:
      # if one has been seen, update all nodes that depend on the current node
      # to depend instead on the version of the current node that has been seen
      for i in 0 ..< idx:
        let other_node = sorted_tree[i]
        if other_node.kind == nkBinOp:
          if other_node.left == node:
            other_node.left = seen
          if other_node.right == node:
            other_node.right = seen

# Determine the number of nodes that directly depend on each node in the graph.
# This is uesful later for working out whether to assign a node to a variable,
# or whether we can compile the node into an in-line expression
# BFS starting from the root
proc findIntersections(tree: ParseTreePtr): Table[ParseTreePtr, int] =
  result = initTable[ParseTreePtr, int]()
  var node_queue = initDeque[ParseTreePtr]()
  node_queue.addLast tree
  while node_queue.len > 0:
    let cur = node_queue.popFirst

    if cur notin result and cur.kind == nkBinOp:
      node_queue.addLast cur.left
      node_queue.addLast cur.right

    result.mgetOrPut(cur, 0) += 1

# for representing operations
func translateBinOp(op: range[ikAdd .. ikEql]): string =
  case op
  of ikAdd: return "+"
  of ikMul: return "*"
  of ikDiv: return "div"
  of ikMod: return "mod"
  of ikEql: return "=="

# Recursively an expression that's a bit easier to look at than the ParseTree
# Starts from the current node in the ParseTree
# The idents table contains labels for specific parse tree nodes; if we encounter
# a parse tree that has a label, substitute that label instead of expanding further
proc genExpr(tree: ParseTreePtr; idents: Table[ParseTreePtr, string]): string =
  case tree.kind
  of nkInp:
    fmt"result[{tree.idx}]"
  of nkLit:
    $tree.n
  of nkBinOp:
    if tree in idents:
      idents[tree]
    # search for the pattern where ((x == literal) == 0); this is equivalent to `!=`,
    # and makes reading the output easier
    elif tree.inst_kind == ikEql and tree.right.kind == nkLit and tree.right.n == 0 and
        tree.left.kind == nkBinOp and tree.left.inst_kind == ikEql:
      let left = tree.left.left
      let right = tree.left.right
      fmt"({genExpr(left, idents)} != {genExpr(right, idents)}"
    else:
      fmt"({genExpr(tree.left, idents)} {translateBinOp(tree.inst_kind)} {genExpr(tree.right, idents)})"

# Generate a list of `let x = ...` expressions, storing any values that multiple
# nodes depend on. The final "let" will be the result of the program
proc translateTree(tree: ParseTreePtr) =
  let intersections = tree.findIntersections
  var sorted = topSort(tree)
  var n_ints = 0
  for node in sorted:
    if node.kind == nkBinOp and intersections[node] > 1:
      inc n_ints
  echo "Number of intersections: ", n_ints

  # FIXME: if there are too many nodes, this will run out of identifiers
  var idents = toSeq("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
  reverse(idents)
  var ident_table = initTable[ParseTreePtr, string]()

  for idx in countdown(sorted.high, sorted.low):
    let node = sorted[idx]
    # node guaranteed to not be in ident_table
    if node.kind == nkBinOp and intersections[node] > 1:
      let cur_ident = idents.pop
      echo "let ", cur_ident, " = ", genExpr(node, ident_table)
      ident_table[node] = $cur_ident
  echo "let ", idents.pop, " = ", genExpr(tree, ident_table)

# evaluate the parse tree with the given input
proc evalTree(sorted_nodes: seq[ParseTreePtr]; input: openarray[int]): int =
  var results = initTable[ParseTreePtr, int]()
  for idx in countdown(sorted_nodes.high, sorted_nodes.low):
    let node = sorted_nodes[idx]
    case node.kind
    of nkLit:
      results[node] = node.n
    of nkInp:
      results[node] = input[node.idx]
    of nkBinOp:
      results[node] = execBinop(node.inst_kind, results[node.left], results[node.right])
  return results[sorted_nodes[0]]

when isMainModule:
  proc main =
    let ex_inp = "ex.inp".parseInput
    let real_inp = "real.inp".parseInput
    let test_inp = "test1.inp".parseInput
    # example model number
    let model_num : seq[int] = @[9,9,9,9,9,9,9,9,9,9,9,9,9,9]
    echo "Program output: ", execProgram(real_inp, model_num)

    var sorted_nodes = makeDepTree(real_inp, rZ)
    echo "Number of nodes in tree: ", sorted_nodes.len
    echo "Tree eval: ", evalTree(sorted_nodes, model_num)

    sorted_nodes.dedupTree
    sorted_nodes = topSort(sorted_nodes[0])
    echo "Number of nodes in deduped tree: ", sorted_nodes.len
    echo "Tree eval: ", evalTree(sorted_nodes, model_num)

    echo "Folding constants..."
    sorted_nodes.foldConstants
    echo "Number of remaining nodes: ", topSort(sorted_nodes[0]).len
    echo "Tree eval: ", evalTree(sorted_nodes, model_num)

    echo "Folding nops..."
    sorted_nodes.foldNops
    echo "Tree eval: ", evalTree(sorted_nodes, model_num)
    echo "Number of items in tree: ", topSort(sorted_nodes[0]).len

    sorted_nodes.dedupTree
    sorted_nodes = topSort(sorted_nodes[0])
    echo "Number of nodes in deduped tree: ", sorted_nodes.len
    echo "Tree eval: ", evalTree(sorted_nodes, model_num)
    sorted_nodes[0].translateTree

  main()
