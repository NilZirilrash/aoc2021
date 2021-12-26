import threadpool
{.experimental.}
import options

# Manually translated from output of decompiler
# Not a great effort on my part; I was exhausted from the
# dealing with the decompiler

# Two functions defined (the div 1 was both elided by my decompiler
# and consciously by me) to reason about them a little better
# (don't judge)
proc mix(a: var int64; b, c, i: int64) =
  if (a mod 26) + b != i:
    a = a * 26 + i + c

proc crunch(a: var int64; b, c, i: int64) =
  if (a mod 26) + b != i:
    a = (a div 26) * 26 + i + c
  else:
    a = a div 26

type Input = array[0..13, int64]

type
  InstructionKind = enum ikMix, ikCrunch
  Instruction = object
    kind: InstructionKind
    b, c: int64
const
  HASH_INSTS : array[1..13, Instruction] = [
    Instruction(kind: ikMix, b: 10, c: 16),
    Instruction(kind: ikMix, b: 12, c: 2),
    Instruction(kind: ikMix, b: 10, c: 8),
    Instruction(kind: ikMix, b: 14, c: 11),
    Instruction(kind: ikCrunch, b: -11, c: 6),
    Instruction(kind: ikMix, b: 10, c: 12),
    Instruction(kind: ikCrunch, b: -16, c: 2),
    Instruction(kind: ikCrunch, b: -9, c: 2),
    Instruction(kind: ikMix, b: 11, c: 15),
    Instruction(kind: ikCrunch, b: -8, c: 1),
    Instruction(kind: ikCrunch, b: -8, c: 10),
    Instruction(kind: ikCrunch, b: -10, c: 14),
    Instruction(kind: ikCrunch, b: -9, c: 10)
  ]

# hard-coded version of the output of the decompiler
proc hash(inp: Input): int64 =
  result = inp[0]+13
  mix(result, 10, 16, inp[1])
  mix(result, 12, 2, inp[2])
  mix(result, 10, 8, inp[3])
  mix(result, 14, 11, inp[4])
  crunch(result, -11, 6, inp[5])
  mix(result, 10, 12, inp[6])
  crunch(result, -16, 2, inp[7])
  crunch(result, -9, 2, inp[8])
  mix(result, 11, 15, inp[9])
  crunch(result, -8, 1, inp[10])
  crunch(result, -8, 10, inp[11])
  crunch(result, -10, 14, inp[12])
  crunch(result, -9, 10, inp[13])


# separated out for parallel brute force below
proc runInstruction(inst: Instruction; cur: var int64; inp: int64) {.inline.} =
  case inst.kind
  of ikMix:
    mix(cur, inst.b, inst.c, inp)
  of ikCrunch:
    crunch(cur, inst.b, inst.c, inp)

func hash2(inp: Input): int64 =
  result = inp[0] + 13
  for i in HASH_INSTS.low .. HASH_INSTS.high:
    runInstruction(HASH_INSTS[i], result, inp[i])

proc intpow(a, b: int64): int64 =
  result = 1
  for i in 1..b:
    result *= a

# recursively search valid digits for each position in the input;
# depth corresponds to the index of the input
proc hashSearch(a: int64; depth: int): Option[int64] =
  case depth
  of 13:
    # for max instead of minimum number:
    # for i in countdown(9, 1):
    for i in 1..9:
      var tmp = a
      runInstruction(HASH_INSTS[depth], tmp, i)
      if tmp == 0:
        return some(i.int64)
    return none(int64)
  else:
    # the last four instructions are all crunch, which
    # either divides the input by 26 or potentially subtracts by at most 25
    # (if the div26/*26 truncates 25). Thus, the current value has to be less
    # than the constant below on the fourth-to-last iteration in order for
    # the program to have a chance of outputting 0
    if depth == 10 and a > 26*26*26*26+26*4:
      return none(int64)
    # for max instead of minimum number:
    # for i in countdown(9, 1):
    for i in 1..9:
      var tmp = a
      runInstruction(HASH_INSTS[depth], tmp, i)
      let res = hashSearch(tmp, depth+1)
      if res.isSome:
        return some(res.get+i*intpow(10, 13-depth))
    return none(int64)


when isMainModule:
  proc main =
    # quick check to make sure I implemented everything correctly
    # (comparing to output from decompiler)
    var test : Input
    for i in test.low .. test.high:
      test[i] = 9'i64
    echo "Hash: ", test.hash
    echo "New hash: ", test.hash2
    var res : array[1..9, Option[int64]]
    # when brute force doesn't work, use more brute force
    parallel:
      # process each possible first input in parallel
      for i in 1..9:
        # The first input is incremented by 13 by the AOC program, so
        # do that here
        res[i] = spawn hashSearch(i+13, 1)
    echo "Possible values:"
    for i, r in res:
      if r.isSome:
        echo $i, r.get

  main()
