#!/usr/bin/python
""" A parameterizable division routine builder for 6502 """

##################################################################################
#
# A parameterizable division routine builder for 6502.
#
# The division routines produced use a table of divide-by-constant routines, falling back
# to repeated subtraction for higher denominator values.
# The repeated subtraction may use a loop (smaller) or unrolled code (faster).
# To limit the size of the divide-by-constant routines, they share code when possible -
# multiples of powers of two are handled by one or more leading shift-rights for the power
# of two, so for example a divide-by-5 routine also handles 10, 20 and 40.
# Factoring (e.g. replacing "x/9" with "(x/3)/3") is used when it saves time, when asked for
# (it adds some size) which is for 9 (22-62 cycles saved) or 15 (4-17 cycles saved) only
# (and their multiples of powers of two), when the custom routines for those denominators are
# not used.
# The routines also by default share trailing code, so to save space will branch between routines.
#
# For complete documentation, see the README.md:
# 	https://github.com/msearle5/makedivide/blob/main/README.md
#

import argparse
import concurrent.futures
import copy
import math
import os
import random
import subprocess
import sys
import tempfile
import time

has_tqdm = True
try:
	import tqdm
except ModuleNotFoundError:
	print("Warning: unable to find tqdm")
	has_tqdm = False

# Maximum length of a command line output in stats
MAX_COMMAND = 40

# Longer than any actual code, the timeout
BAD_CYCLES = 4000

REG_MEM_SOURCES = ( "x", "y", "a", "memory" )

# Available constants to divide by
CUSTOMS = {
	0, 1, 2, 3, 4,
	5, 6, 7, 8, 9,
	10, 11, 12, 13, 14,
	15, 16, 17, 18,
	19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
	29, 30, 31, 32, 34, 36,
	38, 40, 42, 44, 46, 48, 50, 52, 54, 56,
	58, 60, 62, 64, 68, 72, 76
}

# Prime numbers including 1, below 100.
PRIMES = {
	1,
	2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
	37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
	79, 83, 89, 97
}

# Fast tests use this denominator and numerator only
FAST_TEST = (
	0, 1, 2, 3,
	4, 6, 8, 10,
	12, 16, 20, 24,
	28, 36, 44, 52,
	60, 76, 82, 98,
	112, 127, 128, 129,
	144, 176, 224, 255
)

# Case lists: filled only when requested
FAST_CASES = []
FULL_CASES = []

# Has a tail branch
TAIL = {
	7, 11, 13, 15, 19, 23, 25, 27, 29, 31, 32
}

# Cycles taken for the unbranching-tail variant of each routine
CYCLES = {
	3: 27,
	5: 27,
	7: 24,
	9: 27,
	11: 32,
	13: 34,
	15: 21,
	17: 27,
	19: 27,
	21: 33,
	23: 31,
	25: 26,
	27: 24,
	29: 33,
	31: 23
}

# Time taken to dispatch through a choice tree (max custom which is 1+ number of choices includig 0)
CHOICE_CYCLES = {
	2: (5+7+9) / 3,
	3: (8+11+7+9) / 4,
	4: (10+12+14+7+9) / 5,
	5: (7+11+13+10+12+14) / 6,
}

CYCLES12 = copy.deepcopy(CYCLES)
CYCLES12[1] = 0

NOT_POSS = ": !warn: Half pointer not possible"


class Divider:
	""" A class containing a set of parameters which can be used to build a divider """ 
	def __init__(self, args, *, max_custom = None, max_full = None, numerator = None, denominator = None, prefix = None, \
		insn = None, label = None, equb = None, comment = None, style=None, emulate=False, \
		fallback_unrolled_subtraction = False, \
		high_bit_check = False, early_high_bit = False, divide_by_0=None, \
		use_factoring=False, inlining=False, use_choice_tree=False, with_stats=False, \
		half_table=False, use_smc=False, fast_stats=False, assemble=False, first=False, with_65c02 = False, \
		error_vector=False, max_shifting_divider=0, denominator_from=None, numerator_from=None, result_to=None, \
		random_stats=0, known_denominator=0, skip_custom=0):
		""" Create a Divider from command line args ("args") and separate args for test modes, etc. """

		if max_custom is None:
			max_custom = args.max_custom
		if max_full is None:
			max_full = args.max_full

		if args.numerator is not None:
			numerator = args.numerator
		assert numerator is not None
		if args.denominator is not None:
			denominator = args.denominator
		assert denominator is not None
		if args.prefix is not None:
			prefix = args.prefix
		assert prefix is not None
		if args.instruction is not None:
			insn = args.instruction
		assert insn is not None
		if args.label is not None:
			label = args.label
		assert label is not None
		if args.equb is not None:
			equb = args.equb
		assert equb is not None
		if args.comment is not None:
			comment = args.comment
		assert comment is not None

		if args.divide_by_zero is not None:
			divide_by_0 = args.divide_by_zero

		if args.error_vector is not None:
			error_vector |= args.error_vector
		assert error_vector is not None
		if args.fast_stats is not None:
			fast_stats |= args.fast_stats
		assert fast_stats is not None
		if args.assemble is not None:
			assemble |= args.assemble
		assert assemble is not None
		if args.with_65c02 is not None:
			with_65c02 |= args.with_65c02
		assert with_65c02 is not None
		if args.emulate is not None:
			emulate |= args.emulate
		assert emulate is not None
		if args.unroll is not None:
			fallback_unrolled_subtraction |= args.unroll
		assert fallback_unrolled_subtraction is not None
		if args.high_bit is not None:
			high_bit_check |= args.high_bit
		assert high_bit_check is not None
		if args.early_high_bit is not None:
			early_high_bit |= args.early_high_bit
		assert early_high_bit is not None
		if args.factoring is not None:
			use_factoring |= args.factoring
		assert use_factoring is not None
		if args.inlining is not None:
			inlining |= args.inlining
		assert inlining is not None
		if args.choice_tree is not None:
			use_choice_tree |= args.choice_tree
		assert use_choice_tree is not None
		if args.stats is not None:
			with_stats |= args.stats
		assert with_stats is not None
		if args.half_table is not None:
			half_table |= args.half_table
		assert half_table is not None
		if args.self_modifying is not None:
			use_smc |= args.self_modifying
		assert use_smc is not None

		if args.denominator_from is not None:
			denominator_from=args.denominator_from
		assert denominator_from is not None
		if args.numerator_from is not None:
			numerator_from=args.numerator_from
		assert numerator_from is not None
		if args.result_to is not None:
			result_to=args.result_to
		assert result_to is not None
		if args.random_stats != 0:
			random_stats = args.random_stats
		if args.skip_custom != 0:
			skip_custom = args.skip_custom
		# First is not from args
		if args.known_denominator is not None:
			known_denominator=args.known_denominator

		self.emulate = emulate
		self.assemble = assemble
		self.first = first
		self.skip_custom = skip_custom
		self.max_custom = max_custom
		self.max_full = max_full
		self.numerator = numerator
		self.denominator = denominator
		self.prefix = prefix
		self.insn = insn
		self.label = label
		self.style = style
		self.equb = equb
		self.comment = comment
		self.fallback_unrolled_subtraction = fallback_unrolled_subtraction
		self.high_bit_check = high_bit_check
		self.early_high_bit = early_high_bit
		self.divide_by_0 = divide_by_0
		self.error_vector = error_vector
		self.use_factoring = use_factoring
		self.inlining = inlining
		self.use_choice_tree = use_choice_tree
		self.max_shifting_divider = max_shifting_divider
		self.with_stats = with_stats
		self.half_table = half_table
		self.use_smc = use_smc
		self.denominator_from = denominator_from
		self.numerator_from = numerator_from
		self.result_to = result_to
		self.fast_stats = fast_stats
		self.random_stats = random_stats
		self.known_denominator = known_denominator
		self.with_65c02 = with_65c02
		self.result = None


	# Cycles needed to check the high bit, and if set return 1 or 0.
	def cycles_by_high_bit(self, numerator, denominator):
		""" Cycles needed to check the high bit, and if set return 1 or 0. """
		cycles = 0
		if self.high_bit_check is True:
			if numerator < 128:
				cycles += 2
			else:
				if numerator < denominator:
					cycles += 12
				else:
					cycles += 10
		return cycles

	# Cycles needed to find the quotient by repeated subtraction
	def cycles_by_subtraction(self, numerator, denominator):
		""" Cycles needed to find the quotient by repeated subtraction """
		quotient = 1+(numerator // denominator)

		cycles = self.cycles_by_high_bit(numerator, denominator)
		if self.high_bit_check is True:
			if numerator < 128:
				cycles += 2
			else:
				if numerator < denominator:
					cycles += 12
				else:
					cycles += 10

		if not self.fallback_unrolled_subtraction:
			cycles += 1 # emu
			cycles += 7	# leading loop
			cycles += 8 * quotient # per iter
			cycles += 1 # exiting loop, not including RTS as all must do that. Minus 1 as branch not taken
		else:
			cycles += 5 # before unrolled loop
			cycles += 6 * quotient # per iter
			cycles += 3 # end
			if quotient == 255 // denominator:
				cycles -= 1
		return cycles


	# Cycles needed to find the quotient by repeated subtraction averaged over all numerators
	def mean_cycles_by_subtraction(self, denominator):
		""" Cycles needed to find the quotient by repeated subtraction averaged over all numerators """
		total = 0
		for num in range(0,256):
			total += self.cycles_by_subtraction(num, denominator)
		return total / 256

	# Cycles needed to find the quotient by a custom routine
	def cycles_by_custom(self, numerator, denominator, powers_of_2=False):
		""" Cycles needed to find the quotient by a custom routine """
		cycles = self.cycles_by_high_bit(numerator, denominator)
		inline_mod = 0
		if self.inlining is False and denominator in TAIL:
			inline_mod = 3
		cyc = CYCLES
		if powers_of_2 is True:
			cyc = CYCLES12
		if denominator in cyc:
			return cyc[denominator]+inline_mod+cycles
		if denominator//2 in cyc:
			return cyc[denominator//2]+2+inline_mod+cycles
		if denominator//4 in cyc:
			return cyc[denominator//4]+4+inline_mod+cycles
		if denominator//8 in cyc:
			return cyc[denominator//8]+6+inline_mod+cycles
		if denominator//16 in cyc:
			return cyc[denominator//16]+8+inline_mod+cycles
		if denominator//32 in cyc:
			return cyc[denominator//32]+10+inline_mod+cycles
		if denominator//64 in cyc:
			return cyc[denominator//64]+12+inline_mod+cycles
		return None

	# Cycles needed to find the quotient by a combination of two custom routines
	def cycles_by_factor(self, factor0, factor1):
		""" Cycles needed to find the quotient by a combination of two custom routines """
		c1 = self.cycles_by_custom(0, factor0, False)
		c2 = self.cycles_by_custom(0, factor1, False)
		if c1 is None or c2 is None:
			return None
		return 15 + c1 + c2	# jsr, rts, bpl

	# Find the set of two factors which is fastest
	def cheapest_factors(self, denominator):
		""" Find the set of two factors which is fastest """
		# Use a single factor if possible
		if denominator <= self.max_custom:
			result = self.cycles_by_custom(0, denominator, False)
			if result is not None:
				return (result, denominator, 1)

		# Search for all possible pairs
		factors = []
		maxf = math.ceil(math.sqrt(denominator))
		maxf = min(maxf, self.max_custom)
		for f in range(3, maxf+1):
			for g in range(3, maxf+1):
				if f*g == denominator:
					cfg = self.cycles_by_factor(f, g)
					if cfg is not None:
						factors.append((cfg, f, g))
		if len(factors) == 0:
			return (None, denominator, 1)
		if len(factors) == 1:
			return factors[0]

		# Find the best
		factors.sort()
		return factors[-1]

	# Returns (True, X, Y) if factoring is possible and improves average performance
	# where X and Y are the best factors to use.
	# Otherwise returns (False, X, 1).
	def factoring_is_good(self, denominator):
		""" Is factoring possible and an improvement to average performance? """
		fac_cycles, factor1, factor2 = self.cheapest_factors(denominator)
		if factor2 == 1:
			# factoring not needed, or not possible
			return (False, factor1, factor2)
		sub_cycles = self.mean_cycles_by_subtraction(denominator)
		return (fac_cycles < sub_cycles, factor1, factor2)

	def cycles_by_generic(self, numerator, denominator):
		""" Cycles needed for shifting or subtraction """
		cycles = 0
		if self.max_shifting_divider not in {0, 256}:
			cycles += 5
		if denominator <= self.max_shifting_divider:
			return cycles + 158 # this isn't accurate for all cases
		return cycles + self.cycles_by_subtraction(numerator, denominator)

	def mean_cycles_numerator(self, numerator, denominator, jumps):
		""" Estimate cycles needed for the given numerator and denominator """
		cycles = 12 # JSR-RTS

		# Early high bit test
		if self.high_bit_check is True and self.early_high_bit is True:
			cycles += self.cycles_by_high_bit(numerator, denominator)
			cycles += 3 # match emu
			if denominator >= 128:
				return cycles

		# Jump table test
		if denominator <= self.max_custom:
			cycles += 4
			# and dispatch (RTS trick, etc)
			if denominator not in CHOICE_CYCLES or self.use_choice_tree is False:
				if self.half_table is True:
					if self.use_smc is True:
						cycles += 11	# lda abs+x; sta abs; jmp
					else:
						cycles += 21
				else:
					if self.use_smc is True:
						cycles += 19	# lda abs+x; sta abs; lda abs+x; sta abs; jmp
					else:
						cycles += 23
			else:
				cycles += CHOICE_CYCLES[denominator]
			# Custom?
			if denominator in jumps:#CUSTOMS and (denominator in PRIMES or denominator <= self.max_full):
				cc = self.cycles_by_custom(numerator, denominator, True)
				if cc is None:
					cycles += self.cycles_by_generic(numerator, denominator)
				else:
					cycles += cc
			else:
				factor1 = 1
				factor2 = 1
				if self.use_factoring is True:
					is_good, factor1, factor2 = self.factoring_is_good(denominator)
				else:
					is_good = False
				if is_good is True:
					cycles += self.cycles_by_factor(factor1, factor2)
				else:
					cycles += self.cycles_by_generic(numerator, denominator)
		else:
			cycles += 5

			if self.high_bit_check is True and self.early_high_bit is False:
				cycles += self.cycles_by_high_bit(numerator, denominator)
				if denominator >= 128:
					return cycles

			cycles += self.cycles_by_generic(numerator, denominator)
		return cycles

	def stats_cycles(self, jumps):
		""" Estimate cycles needed for all numerators and denominators, or a fixed or random subset """
		fast_stats = self.fast_stats
		cycles = 0
		clist=[]
		cycles64 = 0
		cycles16 = 0
		if fast_stats:
			total = 0
			total64 = 0
			total16 = 0
			for numerator in FAST_TEST:
				for denominator in FAST_TEST[1:]:
					c = self.mean_cycles_numerator(numerator, denominator, jumps)
					clist.append(c)
					cycles += c
					total += 1
					if denominator <= 64:
						cycles64 += c
						total64 += 1
					if denominator <= 16:
						cycles16 += c
						total16 += 1
		else:
			total = 255*256
			total64 = 63*256
			total16 = 15*256
			for numerator in range(0,256):
				for denominator in range(1,256):
					c = self.mean_cycles_numerator(numerator, denominator, jumps)
					clist.append(c)
					cycles += c
					if denominator <= 64:
						cycles64 += c
					if denominator <= 16:
						cycles16 += c
		cycles /= total
		cycles64 /= total64
		cycles16 /= total16
		clist.sort()
		median = clist[len(clist)//2]
		worst = clist[-1]
		return cycles, cycles64, cycles16, median, worst

	def make_customs(self, jumps):
		""" Emit a division routine for all fixed denominators in the 'jumps' set except 0,1, powers of 2 and 17 """
		label = self.label
		prefix = self.prefix
		insn = self.insn
		numerator = self.numerator

		text = []

		if 48 in jumps:
			text.append(f"{label}{prefix}divide_by_48")
			text.append(f"{insn}lsr")
		if 24 in jumps:
			text.append(f"{label}{prefix}divide_by_24")
			text.append(f"{insn}lsr")
		if 12 in jumps:
			text.append(f"{label}{prefix}divide_by_12")
			text.append(f"{insn}lsr")
		if 6 in jumps:
			text.append(f"{label}{prefix}divide_by_6")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 3 in jumps:
			text.append(f"{label}{prefix}divide_by_3")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #21")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}rts")

		if 40 in jumps:
			text.append(f"{label}{prefix}divide_by_40")
			text.append(f"{insn}lsr")
		if 20 in jumps:
			text.append(f"{label}{prefix}divide_by_20")
			text.append(f"{insn}lsr")
		if 10 in jumps:
			text.append(f"{label}{prefix}divide_by_10")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 5 in jumps:
			text.append(f"{label}{prefix}divide_by_5")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #13")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_5_end")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}rts")

		if 56 in jumps:
			text.append(f"{label}{prefix}divide_by_56")
			text.append(f"{insn}lsr")
		if 28 in jumps:
			text.append(f"{label}{prefix}divide_by_28")
			text.append(f"{insn}lsr")
		if 14 in jumps:
			text.append(f"{label}{prefix}divide_by_14")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 7 in jumps:
			text.append(f"{label}{prefix}divide_by_7")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")

				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_5_end")

		if 72 in jumps:
			text.append(f"{label}{prefix}divide_by_72")
			text.append(f"{insn}lsr")
		if 36 in jumps:
			text.append(f"{label}{prefix}divide_by_36")
			text.append(f"{insn}lsr")
		if 18 in jumps:
			text.append(f"{label}{prefix}divide_by_18")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 9 in jumps:
			#lsr; lsr; lsr; adc {numerator}; ror; adc {numerator}; ror; adc {numerator}; ror; lsr; lsr; lsr;
			text.append(f"{label}{prefix}divide_by_9")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_9_end")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}rts")
		elif (36 in jumps or 18 in jumps) and 3 in jumps:
			text.append(f"{label}{prefix}divide_by_9")
			text.append(f"{insn}jsr {prefix}divide_by_3")
			text.append(f"{insn}bpl {prefix}divide_by_3")

		if 44 in jumps:
			text.append(f"{label}{prefix}divide_by_44")
			text.append(f"{insn}lsr")
		if 22 in jumps:
			text.append(f"{label}{prefix}divide_by_22")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 11 in jumps:
			text.append(f"{label}{prefix}divide_by_11")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_9_end")

		if 52 in jumps:
			text.append(f"{label}{prefix}divide_by_52")
			text.append(f"{insn}lsr")
		if 26 in jumps:
			text.append(f"{label}{prefix}divide_by_26")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 13 in jumps:
			text.append(f"{label}{prefix}divide_by_13")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}clc")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_9_end")

		if 60 in jumps:
			text.append(f"{label}{prefix}divide_by_60")
			text.append(f"{insn}lsr")
		if 30 in jumps:
			text.append(f"{label}{prefix}divide_by_30")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 15 in jumps:
			text.append(f"{label}{prefix}divide_by_15")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #4")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				if self.with_65c02 is True:
					text.append(f"{insn}bra {prefix}divide_by_9_end")
				else:
					text.append(f"{insn}jmp {prefix}divide_by_9_end")
		elif (30 in jumps or 60 in jumps) and 3 in jumps and 5 in jumps:
			text.append(f"{label}{prefix}divide_by_15")
			text.append(f"{insn}jsr {prefix}divide_by_3")
			text.append(f"{insn}bpl {prefix}divide_by_5")

		if 76 in jumps:
			text.append(f"{label}{prefix}divide_by_76")
			text.append(f"{insn}lsr")
		if 38 in jumps:
			text.append(f"{label}{prefix}divide_by_38")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 19 in jumps:
			text.append(f"{label}{prefix}divide_by_19")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			if self.inlining is True or 21 not in jumps:
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bne {prefix}divide_by_21_end_ror")
				# Falls through when num in 0, but the result is the same.

		if 42 in jumps:
			text.append(f"{label}{prefix}divide_by_42")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 21 in jumps:
			text.append(f"{label}{prefix}divide_by_21")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_21_end_adc")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{label}{prefix}divide_by_21_end_ror")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_21_end")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}rts")

		if 46 in jumps:
			text.append(f"{label}{prefix}divide_by_46")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 23 in jumps:
			text.append(f"{label}{prefix}divide_by_23")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")

		if 50 in jumps:
			text.append(f"{label}{prefix}divide_by_50")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 25 in jumps:
			text.append(f"{label}{prefix}divide_by_25")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")

		if 54 in jumps:
			text.append(f"{label}{prefix}divide_by_54")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 27 in jumps:
			text.append(f"{label}{prefix}divide_by_27")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")

		if 58 in jumps:
			text.append(f"{label}{prefix}divide_by_58")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 29 in jumps:
			text.append(f"{label}{prefix}divide_by_29")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")

		if 62 in jumps:
			text.append(f"{label}{prefix}divide_by_62")
			text.append(f"{insn}lsr")
			text.append(f"{insn}sta {numerator}")
		if 31 in jumps:
			text.append(f"{label}{prefix}divide_by_31")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if self.inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")
		return text

	def make_powers_of_2(self, jumps, internal_div_by_0, divide_by_0):
		""" Emit a division routine for denominators 0,1, powers of 2 and 17 """
		label = self.label
		prefix = self.prefix
		insn = self.insn
		numerator = self.numerator

		powers_of_2 = []
		# Custom dividers
		if 64 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_64")
			powers_of_2.append(f"{insn}lsr")
		if 32 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_32")
			powers_of_2.append(f"{insn}lsr")
			if self.inlining is True:
				powers_of_2.append(f"{insn}lsr")
				powers_of_2.append(f"{insn}lsr")
				powers_of_2.append(f"{insn}lsr")
				powers_of_2.append(f"{insn}lsr")
				powers_of_2.append(f"{insn}rts")
			else:
				powers_of_2.append(f"{insn}bpl {prefix}divide_by_16")

		if 68 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_68")
			powers_of_2.append(f"{insn}lsr")
		if 34 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_34")
			powers_of_2.append(f"{insn}lsr")
			powers_of_2.append(f"{insn}sta {numerator}")
		if 17 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_17")
			powers_of_2.append(f"{insn}lsr")
			powers_of_2.append(f"{insn}adc {numerator}")
			powers_of_2.append(f"{insn}ror")
			powers_of_2.append(f"{insn}adc {numerator}")
			powers_of_2.append(f"{insn}ror")
			powers_of_2.append(f"{insn}adc {numerator}")
			powers_of_2.append(f"{insn}ror")
			powers_of_2.append(f"{insn}adc #0")

		if 16 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_16")
			powers_of_2.append(f"{insn}lsr")
		if 8 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_8")
			powers_of_2.append(f"{insn}lsr")
		if 4 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_4")
			powers_of_2.append(f"{insn}lsr")
		if 2 in jumps:
			powers_of_2.append(f"{label}{prefix}divide_by_2")
			powers_of_2.append(f"{insn}lsr")
		powers_of_2.append(f"{label}{prefix}divide_by_1")
		if internal_div_by_0 is True:
			powers_of_2.append(f"{label}{prefix}divide_by_0")
			powers_of_2.append(f"{insn}rts")
		else:
			powers_of_2.append(f"{insn}rts")
			powers_of_2.append(f"{label}{prefix}divide_by_0")
			if self.error_vector is True:
				powers_of_2.append(f"{insn}jmp ({divide_by_0})")
			else:
				powers_of_2.append(f"{insn}jmp {divide_by_0}")
		return powers_of_2

	# Make a constant denominator divider.
	# This uses a custom routine if available, otherwise a subtraction loop.
	# This doesn't accept any variations and always goes from numerator A, return A
	#
	def make_constant_divider(self, denom):
		""" Make a constant denominator divider. """
		assert denom > 0
		assert denom < 256
		jumps = set()
		for i in range(0,8):
			jumps.add(denom >> i)
			if (denom >> i) & 1 == 1:
				break
		self.inlining = True
		self.use_factoring = False
		text = []
		if denom in (0, 1, 2, 4, 8, 16, 17, 32, 34, 64, 68):
			text = self.make_powers_of_2(jumps, True, "divide_by_0")
		else:
			if denom <= 76:
				text = self.make_customs(jumps)

		# No custom? Use a subtract loop
		if len(text) == 0:
			label = self.label
			prefix = self.prefix
			insn = self.insn
			text.append(f"{label}{prefix}divide_by_{denom}")
			text.append(f"{insn}ldx #255")
			text.append(f"{insn}sec")
			text.append(f"{label}{prefix}use_sub_loop")
			text.append(f"{insn}sbc #{denom}")
			text.append(f"{insn}inx")
			text.append(f"{insn}bcs {prefix}use_sub_loop")
			text.append(f"{insn}txa")
			text.append(f"{insn}rts")

		return self.get_size_and_stats(text, jumps, True)

	# The main entry point: see top of file for documentation
	def make_divide(self, dry_run=False):
		""" The main entry point: make a division routine, or if dry_run is set test whether it is possible to do so. """
		available = True
		max_custom = self.max_custom
		early_high_bit = self.early_high_bit

		if dry_run:
			if (self.max_full > self.max_custom) or (self.early_high_bit and not self.high_bit_check) or (self.max_full < 0):
				return False
		else:
			assert self.max_full <= max_custom
			assert (self.high_bit_check or not early_high_bit)

		if max_custom < 2 and self.high_bit_check is True and early_high_bit is False:
			if dry_run is True:
				return False
			early_high_bit = True
			print("WARNING: late high bit not available for max_custom < 2")

		choice_tree = self.use_choice_tree

		if max_custom >= 5 and choice_tree is True:
			if dry_run is True:
				return False
			choice_tree = False
			available = False
			print("WARNING: choice_tree not available for max_custom >= 5")

		low_iters_max = 0
		if self.high_bit_check is True and self.fallback_unrolled_subtraction is True:
			low_iters_max = 2

		if (self.skip_custom > 0 and self.skip_custom < 3) or self.skip_custom >= self.max_custom or self.skip_custom in (2,4,8,16):
			if dry_run is True:
				return False
			available = False
			self.skip_custom = 0
			print("WARNING: skip_custom out of range. disabled")

		if self.skip_custom > 0 and self.inlining is False:
			if dry_run is True:
				return False
			available = False
			self.inlining = True
			print("WARNING: skip_custom requires inlining, enabled")

		if self.skip_custom > 0 and self.use_choice_tree is True:
			if dry_run is True:
				return False
			available = False
			self.skip_custom = 0
			print("WARNING: skip_custom and choice_tree are incompatible, skip_custom disabled")

		# Reduce if there is wasted space at the top of the table
		while max_custom not in CUSTOMS:
			max_custom -= 1

		# Build a table of jumps - determine which are available
		jumps = set()
		for i in range(0, max_custom+1):
			if i in CUSTOMS:
				jumps.add(i)
				if i > 1:
					for j in range(1, 7):
						if (i*(1<<j)) <= self.max_full:
							jumps.add(i*(1<<j))

		if self.skip_custom != 0:
			for j in range(0, 7):
				if self.skip_custom*(1<<j) in jumps:
					jumps.remove(self.skip_custom*(1<<j))

		fallback_unrolled_subtraction = self.fallback_unrolled_subtraction
		divide_by_0 = self.divide_by_0
		prefix = self.prefix

		# Determine the divide by 0 address
		internal_div_by_0 = False
		if divide_by_0 is None:
			internal_div_by_0 = True
			divide_by_0 = f"{prefix}divide_by_0"

		# Jump table - make entries
		factors = set()
		jumpentries = []
		jumpentries.append(f"{prefix}divide_by_0")
		max_custom_avail = max_custom
		has_jump_to_sub = False
		ijumps = set(jumps)

		for i in range(1, max_custom+1):
			if i in ijumps:#CUSTOMS and (i in PRIMES or i <= self.max_full) and not (i == self.skip_custom):
				jumpentries.append(f"{prefix}divide_by_{i}")
			else:
				if self.use_factoring is True:
					is_good, _, _ = self.factoring_is_good(i)
				else:
					is_good = False
				if is_good is True:
					assert(i in {9,15})
					factors.add(i)
					jumps.add(i)
					jumps.add(i*2)
					jumps.add(i*4)
					jumps.add(i*8)
					jumpentries.append(f"{prefix}divide_by_{i}")
				else:
					max_custom_avail = min(max_custom_avail, i-1)
					has_jump_to_sub = True
					jumpentries.append(f"{prefix}use_sub_bounce")

		# Find highest point which can be handled without the generic function
		max_custom_avail = max(1, max_custom_avail)

		max_iters = max(255 // max_custom_avail, low_iters_max)

		with_shifting = False
		with_subtraction = False

		# Repeated subtraction, unrolled
		if self.max_shifting_divider > 0:
			with_shifting = True
		if self.max_shifting_divider < 256:
			with_subtraction = True

		# Half tables limit the targets to the first page
		# That's always OK if not inlining and there are no non-custom jumps
		# Otherwise have limits
		use_sub_bounce = False
		if self.half_table is True:
			if self.inlining is True:
				max_limit = 30
				if has_jump_to_sub is True:
					max_limit = 28
					if (with_shifting and with_subtraction):
						max_limit = 25
				if self.use_smc is True:
					max_limit -= 1
			else:
				max_limit = 64
				if has_jump_to_sub is True:
					max_limit = 34
					if (with_shifting and with_subtraction):
						max_limit = 29
					if self.use_smc is True:
						max_limit -= 1
			if fallback_unrolled_subtraction is True:
				max_limit -= 1
			if max_custom > max_limit:
				if dry_run is True:
					return False
				print(f"WARNING: max custom denominator exceeds the limit of {max_limit} for half-tables with these args (inlining, " \
					"shifting vs subtraction as fallback and whether there are gaps in the table all affect it.", file=sys.stderr)
				max_custom = max_limit
				available=False
			table_limit = 0
			# Account for the extra size of the JMP to external divide by 0
			if internal_div_by_0 is False:
				table_limit = 7
			if (max_limit - max_custom) - ((table_limit + max_iters) // 4) < 0:
				use_sub_bounce = True

		# Limited by branch range to 62
		if fallback_unrolled_subtraction is True and max_iters > 62:
			if dry_run is True:
				return False
			print("WARNING: unrolled subtraction not available - branch range limited", file=sys.stderr)
			fallback_unrolled_subtraction = False
			available=False

		denominator_from = self.denominator_from
		numerator_from = self.numerator_from
		assert denominator_from != numerator_from or denominator_from == "memory"
		assert denominator_from in REG_MEM_SOURCES
		assert numerator_from in REG_MEM_SOURCES
		denominator_from = self.denominator_from.lower()
		if denominator_from == "x" and early_high_bit is True:
			if dry_run is True:
				return False
			print("WARNING: early_high_bit not available with denominator in X", file=sys.stderr)
			early_high_bit = False
			available=False

		if dry_run is True:
			return True

		label = self.label
		prefix = self.prefix
		insn = self.insn
		equb = self.equb
		comment = self.comment
		denominator = self.denominator
		numerator = self.numerator

		nonp2_customs = self.make_customs(jumps)

		# Transfer denominator to X on entry and/or X to denominator if needed later
		if denominator_from == "x":
			denominator_to_x = []
			x_to_denominator = [f"{insn}stx {denominator}"]
		elif denominator_from == "a":
			denominator_to_x = [f"{insn}tax"]
			x_to_denominator = [f"{insn}stx {denominator}"]
		elif denominator_from == "y":
			denominator_to_x = [f"{insn}tya", f"{insn}tax"]
			x_to_denominator = [f"{insn}stx {denominator}"]
		else:
			denominator_to_x = [f"{insn}ldx {denominator}"]
			x_to_denominator = []

		# Transfer numerator to memory on entry
		numerator_to_mem = []
		if numerator_from == "x":
			numerator_to_mem = [f"{insn}stx {numerator}"]
		elif numerator_from == "a":
			numerator_to_mem = [f"{insn}sta {numerator}"]
		elif numerator_from == "y":
			numerator_to_mem = [f"{insn}sty {numerator}"]

		# Use a wrapper if not returning in A
		# The wrapper calls _wrapped_entry, then does something (from the wrapper[] list) and then returns.
		wrapper = []
		if self.result_to == 'x':
			wrapper.append(f"{insn}tax")
		elif self.result_to == 'y':
			wrapper.append(f"{insn}tay")
		elif self.result_to == 'denominator':
			wrapper.append(f"{insn}sta {denominator}")
		elif self.result_to == 'numerator':
			wrapper.append(f"{insn}sta {numerator}")
		elif self.result_to == 'a':
			pass
		else:
			print("WARNING: unrecognized return location, defaulting to A")

		text = []
		text.append(f"{comment}Division, 8 / 8 bits.")
		text.append(f"{comment}Generated by makedivide.py {self.command_words()[0]}")
		if self.half_table is True:
			text.append(f"{comment}This code must be page aligned!")
		if self.use_smc is True:
			text.append(f"{comment}This code is self-modifying, and so cannot run from ROM.")
		text.append(f"{comment}Entry point is at {prefix}entry")

		powers_of_2 = self.make_powers_of_2(jumps, internal_div_by_0, divide_by_0)

		if self.half_table is True:
			if self.use_smc is False:
				text.append(f"{insn}nop") # Prevent a ff in the table

			text.extend(powers_of_2)
			text.extend(nonp2_customs)

		cpx_branch = []
		if max_custom == 0:
			if denominator_from == "x":
				cpx_branch.append(f"{insn}cpx #0")
			cpx_branch.append(f"{insn}bne {prefix}use_sub")
		else:
			cpx_branch.append(f"{insn}cpx #{max_custom+1}")
			cpx_branch.append(f"{insn}bcs {prefix}use_sub")

		if use_sub_bounce is True:
			text.append(f"{label}{prefix}use_sub_bounce")
			text.append(f"{insn}bcc {prefix}use_sub_unchecked")

		if not choice_tree:
			if len(wrapper) > 0:
				text.append(f"{label}{prefix}wrapped_entry")
			else:
				text.append(f"{label}{prefix}entry")
			text.extend(numerator_to_mem)
			text.extend(denominator_to_x)
			# Early high jump
			if early_high_bit is True and denominator_from != "x":
				text.append(f"{insn}bmi {prefix}high_bit_denom")

			# Check jump vs. subtract
			text.extend(cpx_branch)

			if self.half_table is True:
				if self.use_smc is True:
					text.append(f"{comment}Half SMC jump table")
					text.append(f"{insn}lda {prefix}lowtable, x")
					text.append(f"{insn}sta {prefix}table_jump+1")
					text.append(f"{insn}lda {numerator}")
					text.append(f"{label}{prefix}table_jump")
					text.append(f"{insn}jmp {jumpentries[0]}")
				else:
					text.append(f"{comment}Half RTS-trick jump table")
					text.append(f"{insn}lda #(>({jumpentries[0]}))")
					text.append(f"{insn}pha")
					text.append(f"{insn}lda {prefix}lowtable, x")
					text.append(f"{insn}pha")
					text.append(f"{insn}lda {numerator}")
					text.append(f"{insn}rts")
			else:
				if self.use_smc is True:
					text.append(f"{comment}SMC jump table")
					text.append(f"{insn}lda {prefix}hightable, x")
					text.append(f"{insn}sta {prefix}table_jump+2")
					text.append(f"{insn}lda {prefix}lowtable, x")
					text.append(f"{insn}sta {prefix}table_jump+1")
					text.append(f"{insn}lda {numerator}")
					text.append(f"{label}{prefix}table_jump")
					text.append(f"{insn}jmp 0x8000")
				else:
					text.append(f"{comment}RTS-trick jump table")
					text.append(f"{insn}lda {prefix}hightable, x")
					text.append(f"{insn}pha")
					text.append(f"{insn}lda {prefix}lowtable, x")
					text.append(f"{insn}pha")
					text.append(f"{insn}lda {numerator}")
					text.append(f"{insn}rts")

		high_check = []
		high_check.append(f"{label}{prefix}high_bit_denom")
		high_check.append(f"{insn}cpx {numerator}")
		high_check.append(f"{insn}bcc {prefix}return_1")
		high_check.append(f"{insn}beq {prefix}return_1")
		# Fall thru to return 0 if unrolled
		if fallback_unrolled_subtraction is False or with_subtraction is False or max_custom < 2:
			high_check.append(f"{insn}lda #0")
			high_check.append(f"{insn}rts")
			high_check.append(f"{label}{prefix}return_1")
			high_check.append(f"{insn}lda #1")
			high_check.append(f"{insn}rts")

		high_bit_early = False
		# Check high bit
		if self.high_bit_check is True and max_custom < 2:
			text.extend(high_check)
			high_bit_early = True

		if with_shifting and with_subtraction:
			text.append(f"{label}{prefix}use_sub")
			text.append(f"{insn}cpx #{self.max_shifting_divider}+1")
			# Branch to subtraction...
			text.append(f"{insn}bcs {prefix}use_sub_unchecked")
			# or fall through to shifting

		if with_shifting:
			if not with_subtraction:
				text.append(f"{label}{prefix}use_sub")
				if self.high_bit_check is True:
					text.append(f"{insn}bmi {prefix}high_bit_denom")
				if use_sub_bounce is False:
					text.append(f"{label}{prefix}use_sub_bounce")
				text.append(f"{label}{prefix}use_sub_unchecked")
			text.append(f"{label}{prefix}use_shift")
			text.extend(x_to_denominator)
			text.append(f"{insn}lda #0")
			text.append(f"{insn}ldx #8")
			text.append(f"{insn}asl {numerator}")
			text.append(f"{label}{prefix}divide_l1")
			text.append(f"{insn}rol")
			text.append(f"{insn}cmp {denominator}")
			text.append(f"{insn}bcc {prefix}divide_l2")
			text.append(f"{insn}sbc {denominator}")
			text.append(f"{label}{prefix}divide_l2")
			text.append(f"{insn}rol {numerator}")
			text.append(f"{insn}dex")
			text.append(f"{insn}bne {prefix}divide_l1")
			text.append(f"{insn}lda {numerator}")
			text.append(f"{insn}rts")

		# Check high bit
		if self.high_bit_check is True and (self.use_choice_tree is False or max_custom >= 2) and high_bit_early is False:
			text.extend(high_check)
			high_bit_early = True

		if with_subtraction:
			if fallback_unrolled_subtraction is True:
				midpoint = max(low_iters_max, (max_iters - 4) // 2) # offset because for very large tables the limit is the bcs use_sub
				if choice_tree:
					midpoint = min(max_iters, 30)
				for i in range(0, midpoint):
					text.append(f"{label}{prefix}return_{i}")
					text.append(f"{insn}lda #{i}")
					text.append(f"{insn}rts")
				if not with_shifting:
					text.append(f"{label}{prefix}use_sub")
					if self.high_bit_check is True and self.early_high_bit is False:
						text.append(f"{insn}bmi {prefix}high_bit_denom")
				if use_sub_bounce is False:
					text.append(f"{label}{prefix}use_sub_bounce")
				text.append(f"{label}{prefix}use_sub_unchecked")
				text.extend(x_to_denominator)
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}sec")
				for i in range(0, max_iters):
					text.append(f"{insn}sbc {denominator}")
					text.append(f"{insn}bcc {prefix}return_{i}")
				text.append(f"{insn}lda #{max_iters}")
				text.append(f"{insn}rts")
				for i in range(midpoint, max_iters):
					text.append(f"{label}{prefix}return_{i}")
					text.append(f"{insn}lda #{i}")
					text.append(f"{insn}rts")
			else:
				# Repeated subtraction, rolled
				if not with_shifting:
					text.append(f"{label}{prefix}use_sub")
				if self.high_bit_check is True and self.early_high_bit is False:
					text.append(f"{insn}bmi {prefix}high_bit_denom")
				if use_sub_bounce is False:
					text.append(f"{label}{prefix}use_sub_bounce")
				text.append(f"{label}{prefix}use_sub_unchecked")
				text.extend(x_to_denominator)
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}ldx #255")
				text.append(f"{insn}sec")
				text.append(f"{label}{prefix}use_sub_loop")
				text.append(f"{insn}sbc {denominator}")
				text.append(f"{insn}inx")
				text.append(f"{insn}bcs {prefix}use_sub_loop")
				text.append(f"{insn}txa")
				text.append(f"{insn}rts")

		if self.half_table is False:
			if max_custom >= 2:
				text.extend(powers_of_2)

		if choice_tree is True:
			if len(wrapper) > 0:
				text.append(f"{label}{prefix}wrapped_entry")
			else:
				text.append(f"{label}{prefix}entry")
			text.extend(numerator_to_mem)
			text.extend(denominator_to_x)

			# Early high jump
			if early_high_bit is True and denominator_from != "x":
				text.append(f"{insn}bmi {prefix}high_bit_denom")

			# Check jump vs. subtract
			text.extend(cpx_branch)

			# Jump table (or choice tree) dispatch
			# Jumps to use_sub will always bypass high bit check
			if max_custom <= 1:
				text.append(f"{insn}lda {numerator}")
			elif max_custom == 2:
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}cpx #1")
				text.append(f"{insn}beq {prefix}divide_by_1")
				text.append(f"{insn}bcs {prefix}divide_by_2")
				if internal_div_by_0:
					text.append(f"{insn}rts")
				else:
					text.append(f"{insn}bcc {prefix}divide_by_0")
			elif max_custom == 3:
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}cpx #2")
				text.append(f"{insn}bcc {prefix}divide_by_1_0")
				text.append(f"{insn}beq {prefix}divide_by_2")
				text.append(f"{insn}bne {prefix}divide_by_3")
				text.append(f"{label}{prefix}divide_by_1_0")
				text.append(f"{insn}cpx #1")
				text.append(f"{insn}beq {prefix}divide_by_1")
				if internal_div_by_0:
					text.append(f"{insn}rts")
				else:
					text.append(f"{insn}bne {prefix}divide_by_0")
			elif max_custom == 4:
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}cpx #3")
				text.append(f"{insn}bcc {prefix}divide_by_2_0")
				text.append(f"{insn}beq {prefix}divide_by_3")
				text.append(f"{insn}bne {prefix}divide_by_4")
				text.append(f"{label}{prefix}divide_by_2_0")
				text.append(f"{insn}cpx #1")
				text.append(f"{insn}beq {prefix}divide_by_1")
				text.append(f"{insn}bcs {prefix}divide_by_2")
				if internal_div_by_0:
					text.append(f"{insn}rts")
				else:
					text.append(f"{insn}bcc {prefix}divide_by_0")
			elif max_custom == 5:
				text.append(f"{insn}lda {numerator}")
				text.append(f"{insn}cpx #3")
				text.append(f"{insn}bcc {prefix}divide_by_2_0")
				text.append(f"{insn}beq {prefix}divide_by_3")
				text.append(f"{insn}cpx #4")
				text.append(f"{insn}beq {prefix}divide_by_4")
				text.append(f"{insn}bne {prefix}divide_by_5")
				text.append(f"{label}{prefix}divide_by_2_0")
				text.append(f"{insn}cpx #1")
				text.append(f"{insn}beq {prefix}divide_by_1")
				text.append(f"{insn}bcs {prefix}divide_by_2")
				if internal_div_by_0:
					text.append(f"{insn}rts")
				else:
					text.append(f"{insn}bcc {prefix}divide_by_0")
			else:
				print("WARNING: choice tree not available with this size table", file=sys.stderr)
				choice_tree = False
				available = False
			# Check high bit
			if self.high_bit_check is True and high_bit_early is False:
				text.extend(high_check)
				high_bit_early = True

		else:
			if self.half_table:
				# Align text.append(f"!do while >( * + {len(jumpentries)} ) != >* {{ nop }}")
				low, lb = ("low", "<")
				text.append(f"{label}{prefix}{low}table")
				for entry in jumpentries:
					if self.use_smc:
						text.append(f"{equb} {lb}({entry})")
					else:
						text.append(f"{equb} {lb}({entry}-1)")
			else:
				for lh in ( ("low", "<"), ("high", ">") ):
					low, lb = lh
					text.append(f"{label}{prefix}{low}table")
					for entry in jumpentries:
						if self.use_smc:
							text.append(f"{equb} {lb}({entry})")
						else:
							text.append(f"{equb} {lb}({entry}-1)")

		if self.half_table is False:
			if max_custom < 2:
				text.extend(powers_of_2)
			text.extend(nonp2_customs)

		if self.half_table is True:
			for entry in jumpentries[1:]:
				if self.use_smc:
					text.append('!if (>('+f"{jumpentries[0]})) != (>({entry})) {{ !warn "+
						f'"Half pointer not possible for SMC with these parameters ({jumpentries[0]} vs {entry})" }}')
				else:
					text.append('!if (>('+f"{jumpentries[0]}-1)) != (>({entry}-1)) {{ !warn "+
						f'"Half pointer not possible for RTS with these parameters ({jumpentries[0]} vs {entry})" }}')

		if len(wrapper) > 0:
			text.append(f"{label}{prefix}entry")
			text.append(f"{insn}jsr wrapped_entry")
			text.extend(wrapper)
			text.append(f"{insn}rts")

		return self.get_size_and_stats(text, jumps, available)

	def get_size_and_stats(self, text, jumps, available):
		""" Find the size of code generated, and optionally the estimated time taken """
		insn = self.insn
		# Analyze size
		size=0
		sizes = [
			(f"{insn}lsr", 1),
			(f"{insn}asl", 1),
			(f"{insn}clc", 1),
			(f"{insn}sec", 1),
			(f"{insn}txa", 1),
			(f"{insn}tax", 1),
			(f"{insn}in", 1),
			(f"{insn}de", 1),
			(f"{insn}ror", 1),
			(f"{insn}rol", 1),
			(f"{insn}pha", 1),
			(f"{insn}rts", 1),
			(f"{insn}adc", 2),
			(f"{insn}sbc", 2),
			(f"{insn}b", 2),
			(f"{insn}j", 3),
			(f"{self.equb}", 1),
			(f"{insn}ld", 2),
			(f"{insn}st", 2),
			(f"{insn}cp", 2),
			(f"{insn}cmp", 2),
			(f"{self.comment}", 0),
			(f"{self.label}", 0),
		]
		for line in text:
			ok=False
			for match in sizes:
				string, ilen = match
				if line[:len(string)] == string:
					size += ilen
					ok=True
					break
			if not ok:
				print(f"Instruction not recognized, {line}", file=sys.stderr)

		if self.with_stats is True:
			stat = self.stats_cycles(jumps)
		else:
			stat = (0,0,0,0,0)
		text.append("")
		return (available, "\n".join(text), stat[0], stat[1], stat[2], stat[3], stat[4], size)

	# Return true if the set of args is acceptable
	def try_make_divide(self):
		""" Return true if the set of args is acceptable """
		return self.make_divide(dry_run=True)

	def do_make_divide(self):
		""" Make a divider,  optionally assemble and emulate """ 
		num, denom = self.numerator, self.denominator

		avail, string, cycles, m64, m16, median, worst, size = self.make_divide()

		result = None
		binary = None
		emulation_result = None
		ecycles = BAD_CYCLES
		em64 = BAD_CYCLES
		em16 = BAD_CYCLES
		emedian = BAD_CYCLES
		eworst = BAD_CYCLES
		if self.assemble is True:
			prolog=f"{num}=0\n{denom}=1\n* = $200\n"
			if self.emulate is True:
				prolog = prolog + f"jsr {self.prefix}entry\njmp $bcde\n"
			if self.divide_by_0 is not None:
				prolog = prolog + f"{self.divide_by_0}\n\tjmp $cdef\n"
			if self.emulate is True:
				prolog = prolog + "* = $300"
			with tempfile.NamedTemporaryFile('w') as infile:
				src = "\n\n".join([prolog, string])
				infile.write(src)
				infilename = infile.name
				infile.flush()
				filesize = 0
				with tempfile.NamedTemporaryFile('rb') as outfile:
					with tempfile.NamedTemporaryFile('r') as reportfile:
						acme = ["acme", "-v2"]
						if self.with_65c02 is True:
							acme.extend(["--cpu", "65c02"])
						acme.extend(["-o", outfile.name, "-r", reportfile.name, infilename])
						result = subprocess.run(acme, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False).stdout
						filesize =os.path.getsize(outfile.name)
						report = reportfile.read()
						binary = f"Binary output {filesize} bytes\n" + "Source:\n" + src + "\n\nReport:\n" + report
						if self.emulate is True:
							error = "Error" in result
							notposs = NOT_POSS in result
							if filesize > 0 and not (error or notposs):
								emulation_result = run_emulator(outfile.name, filesize, denominator_from=self.denominator_from,
									numerator_from=self.numerator_from, result_to=self.result_to, fast_stats=self.fast_stats,
									random_stats=self.random_stats)
								if isinstance(emulation_result, tuple) and isinstance(emulation_result[3], tuple):
									ecycles, em64, em16, emedian, eworst = emulation_result[3]
							elif filesize > 0 and (error or notposs):
								if error is True:
									emulation_result = "Asm Err"
								else:
									emulation_result = "HalfTab"
							else:
								emulation_result = "No File"
		self.result = (result, binary, avail, string, cycles, m64, m16, median, worst,
						ecycles, em64, em16, emedian, eworst, size, emulation_result)
		return self

	def command_words(self):
		""" Returns a command line which could be used to produce the same result, and components of a line of stats output """
		style = self.style
		if style is None:
			style = ""
		com_words = []
		com_words.append(f"-c{self.max_custom}")
		com_words.append(f"-f{self.max_full}")

		cwith = "No"
		if self.use_choice_tree is True:
			com_words.append("-T")
			cwith = "Yes"
			style = style + "_c"
		fwith = "No"
		if self.use_factoring is True:
			com_words.append("-F")
			fwith = "Yes"
			style = style + "_f"
		iwith = "No"
		if self.inlining is True:
			com_words.append("-I")
			iwith = "Yes"
			style = style + "_i"
		style = style + f"_s{self.max_shifting_divider}"
		uwith = "No"
		if self.fallback_unrolled_subtraction is True:
			com_words.append("-u")
			uwith = "Yes"
			style = style + "_u"
		hwith = "No"
		if self.high_bit_check is True:
			hwith = "Late"
			if self.early_high_bit is True:
				hwith = "Early"
				style = style + "_e"
				com_words.append("-V")
			else:
				style = style + "_l"
				com_words.append("-B")

		if self.max_shifting_divider != 0:
			com_words.append(f"-S {self.max_shifting_divider}")

		twith="No"
		if self.half_table is True:
			com_words.append("-H")
			twith="Yes"

		swith="No"
		if self.use_smc is True:
			com_words.append("-M")
			swith="Yes"

		if self.divide_by_0 is not None:
			com_words.append("-0 d")

		if self.skip_custom != 0:
			com_words.append(f"-K {self.skip_custom}")

		command = " ".join(com_words)
		return command, cwith, fwith, iwith, style, uwith, hwith, twith, swith

	def add_line(self, stat):
		""" Add a line of results to stats output lists """
		_, _, _, _, mean, mean64, mean16, median, worst, emean, emean64, emean16, emedian, eworst, size, emulation_result = self.result
		emulate = self.emulate

		command, cwith, fwith, iwith, _, uwith, hwith, twith, swith = self.command_words()

		line = f"|{self.max_custom:6}|{self.max_full:6}|{self.skip_custom:6}|{fwith:6}|{iwith:6}|{uwith:6}|{hwith:6}|{cwith:6}|" + \
				f"{self.max_shifting_divider:6}|{twith:6}|{swith:6}|{size:6}|{command.ljust(MAX_COMMAND)}|"
		bad = False
		if self.with_stats is True:
			line = f"{line[:-(1+MAX_COMMAND)]}{float(mean):7.5}|{float(mean64):7.5}|{float(mean16):7.5}|" + \
					f"{median:6}|{float(worst):7.5}|{command.ljust(MAX_COMMAND)}|"

		emtext = ""
		trace=None
		if emulate is True:
			if emulation_result is None:
				emtext="Failed!"
			else:
				if isinstance(emulation_result, str):
					emtext=emulation_result
				else:
					mismatch, divisor, dividend, cycles, trace = emulation_result
					if mismatch is True:
						emtext=f"{divisor}/{dividend}"
					elif divisor == -1:
						emtext=f"{float(cycles[0]):7.5}"
					else:
						emtext=f"{divisor}!{dividend}"

			bad = True
			if emtext == "":
				emtext = f"{float(emean):7.5}"
			line = f"{line[:-(1+MAX_COMMAND)]}{emtext}|{float(emean64):7.5}|{float(emean16):7.5}|{emedian:6}|" + \
					f"{float(eworst):7.5}|{command.ljust(MAX_COMMAND)}|"

			if isinstance(emulation_result, tuple):
				if isinstance(emulation_result[3], tuple):
					emean, emean64, emean16, emedian, eworst = emulation_result[3]
					stat["emean"].append((emean, emean64, emean16, eworst, emedian, size, line))
					stat["emean64"].append((emean64, emean16, emean, eworst, emedian, size, line))
					stat["emean16"].append((emean16, emean64, emean, eworst, emedian, size, line))
					stat["emedian"].append((emedian, eworst, emean, mean64, emean16, size, line))
					stat["eworst"].append((eworst, emean, emean64, emean, emedian, size, line))
					bad = False

		if not bad:
			stat["mean"].append((mean, mean64, mean16, worst, median, size, line))
			stat["mean64"].append((mean64, mean16, mean, worst, median, size, line))
			stat["mean16"].append((mean16, mean64, mean, worst, median, size, line))
			stat["median"].append((median, worst, mean, mean64, mean16, size, line))
			stat["worst"].append((worst, mean, mean64, mean, median, size, line))


		stat["full"].append(line)
		return trace

def add_title(name, slist, args):
	""" Add a title block to the output """
	dbar=    "+===================================================================================+"
	title1 = "|Max   |Max   |Skip  |With  |With  |Unroll|Hi Bit|Choice|Max   |Half  |Self  |Size  |"
	title2 = "|Custom|Full  |Custom|Factor|Inline|Subtrc|Check |Tree  |Shift |Table |Modify|bytes |"
	if args.stats:
		dbar=  dbar[:-1] + "=======================================+"
		title1 = title1  + "Estimat|Mea<=64|Mea<=16|Median|Worst  |"
		title2 = title2  + "Mean C |cycles |cycles |cycles|cycles |"
	if args.emulate:
		dbar = dbar[:-1] + "=======================================+"
		title1= title1   + "Emulate|Mea<=64|Mea<=16|Median|Worst  |"
		title2= title2   + "Mea/Err|cycles |cycles |cycles|cycles |"
	dbar = dbar[:-1] + f"{'='*(MAX_COMMAND+1)}+"
	title1= title1   + f"{'Command line to generate'.center(MAX_COMMAND)}|"
	title2= title2   + f"{' '*(MAX_COMMAND)}|"

	slist.append(dbar)
	slist.append(f"|{name.center(len(dbar)-2)}|")
	slist.append(dbar)
	slist.append(title1)
	slist.append(title2)
	slist.append(dbar)

# Sort the list of lines, and output the first of each length
def best_time(lines):
	""" Sort the list of lines, and output the first of each length """
	out = []
	lines.sort()
	besti = 1000000
	for maxsize in range(0, 1000):
		for sizelinei, sizeline in enumerate(lines):
			_, _, _, _, _, size, line = sizeline
			if size == maxsize:
				if sizelinei < besti:
					out.append(line)
					besti = sizelinei
				break
	return out

# Blended score
# This is the average index into all 5 lists (which must already be sorted)
def blended_best_time(lists, weights):
	""" Calculate the weighted average of indices into all 5 lists (which must already be sorted) """
	index = {}
	for item in lists[0]:
		index[item[6]] = []
	for listi, l in enumerate(lists):
		for itemi, item in enumerate(l):
			index[item[6]].append((item[5], itemi * weights[listi]))
	indexl = []
	for k, v in index.items():
		vsum = 0
		for ve in v:
			size, value = ve
			vsum += value
		indexl.append((vsum, 0, 0, 0, 0, size, k))
	return best_time(indexl)

# Run the emulator on the given file and size.
# Load, repeatedly call it and verify correctness and time taken.
def run_emulator(filename, size, tracy=False, numin=0, denomin=0, denominator_from="memory", numerator_from="memory",
	result_to="a", fast_stats=False, random_stats=0):
	""" Run the emulator on the given file and size. """
	from py65emu.cpu import CPU
	from py65emu.mmu import MMU, ReadOnlyError

	global FULL_CASES, FAST_CASES

	trace = None
	if tracy is True:
		trace = []

	total_cycles = 0
	total_64_cycles = 0
	total_16_cycles = 0
	cycle_list=[]

	total_64_cases = 0
	total_16_cases = 0
	if fast_stats is False and random_stats == 0:
		total_64_cases = 63*256
		total_16_cases = 15*256

	# Each tuple is (start_address, length, readOnly=True, value=None, valueOffset=0)
	# Value is a file pointer, binary value or list of unsigned integers (*not* a single integer)
	# May not overlap
	load_address = 0x200
	num_addr = 0
	denom_addr=1
	with open(filename, "rb") as file:
		mmu = MMU([
			(0, 				load_address,					False,	[0] * load_address),						# ZP and Stack, zero fill
			(load_address,		size,							False,	file),										# Exe, modifiable
			(load_address+size,	0x10000-(load_address+size),	True, 	[0x60] * (0x10000-(load_address+size)))		# Not modifiable, RTS fill
		])

		# Start the CPU at the entry point
		cpu = CPU(mmu, load_address)

		# For all numerator, denominator pairs:
		numrange = range(numin, 256)
		denomrange = range(denomin, 256)
		if len(FULL_CASES) == 0:
			FULL_CASES = []
			for num in numrange:
				for denom in denomrange:
					FULL_CASES.append((denom, num))
		cases = FULL_CASES
		if fast_stats is True:
			numrange = FAST_TEST
			denomrange = FAST_TEST[1:]
			if len(FAST_CASES) == 0:
				FAST_CASES = []
				for num in numrange:
					for denom in denomrange:
						FAST_CASES.append((denom, num))
			cases = FAST_CASES
		elif isinstance(random_stats, int):
			if random_stats > 0:
				samples = random.sample(range(256,256*256), random_stats)
				random_stats = []
				for case in samples:
					random_stats.append((case // 256, case % 256))
		if not isinstance(random_stats, int):
			cases = random_stats
		for case in cases:
			denominator, numerator = case
			# Set up - write params
			cpu.r.a = 0
			cpu.r.y = 0
			cpu.r.x = 0
			if numerator_from == "x":
				cpu.r.x = numerator
				mmu.write(num_addr, 0)
			elif numerator_from == "y":
				cpu.r.y = numerator
				mmu.write(num_addr, 0)
			elif numerator_from == "a":
				cpu.r.a = numerator
				mmu.write(num_addr, 0)
			else:
				mmu.write(num_addr, numerator)
			if denominator_from == "x":
				cpu.r.x = denominator
				mmu.write(denom_addr, 0)
			elif denominator_from == "y":
				cpu.r.y = denominator
				mmu.write(denom_addr, 0)
			elif denominator_from == "a":
				cpu.r.a = denominator
				mmu.write(denom_addr, 0)
			else:
				mmu.write(denom_addr, denominator)
			if tracy is True:
				trace = [ f"{numerator} / {denominator}" ]

			# Main emulation loop
			cycles = 0
			cpu.r.pc = load_address
			try:
				if tracy is True:
					while cycles < BAD_CYCLES and cpu.r.pc < 0x8000:
						cpu.step()
						cycles += cpu.cc
						trace.append((copy.deepcopy(cpu.r), mmu.read(0), mmu.read(1)))
				else:
					while cycles < BAD_CYCLES and cpu.r.pc < 0x8000:
						cpu.step()
						cycles += cpu.cc
			except ReadOnlyError:
				# Like a timeout, but can be distinguished by the cycle count
				return (False, numerator, denominator, cycles, None)

			# Left loop - timeout?
			if cycles >= BAD_CYCLES:
				return (False, numerator, denominator, cycles, None)

			# Not timeout
			# Div by zero?
			if cpu.r.pc == 0xcdef and denominator == 0:
				# Expected
				pass
			else:

				# Value is in A etc. Is it correct?
				if result_to == "a":
					result = cpu.r.a
				elif result_to == "x":
					result = cpu.r.x
				elif result_to == "y":
					result = cpu.r.y
				elif result_to == "denominator":
					result = mmu.read(denom_addr)
				elif result_to == "numerator":
					result = mmu.read(num_addr)
				else:
					print(f"Unrecognized result_to {result_to}, using a")
					result = cpu.r.a

				if denominator <= 1:
					wanted = numerator
				else:
					wanted = numerator // denominator

				# No, fail early
				if result != wanted:
					if tracy is False:
						df, nf = denominator_from, numerator_from
						return run_emulator(filename, size, True, numerator, denominator, df, nf, result_to, fast_stats, random_stats)
					strace = str(trace)
					last = 0
					start = 0
					newtrace = []
					# Convert "F: 01010101" to "NVC" format
					while True:
						last = start
						start = strace.find("P: ", start)
						if start == -1:
							newtrace.append(strace[last:])
							break
						newtrace.append(strace[last:start])
						flags = strace[start+3:start+11]
						start += 11
						neg = "-"
						if flags[0] == "1":
							neg = "N"
						over = "-"
						if flags[1] == "1":
							over = "V"
						zero = "-"
						if flags[6] == "1":
							zero = "Z"
						carry = "-"
						if flags[7] == "1":
							carry = "C"
						newtrace.append(f"F: {neg}{over}{zero}{carry}")
					return (True, numerator, denominator, cycles, "".join(newtrace))

			# OK
			if denominator > 0:
				total_cycles += cycles
				if denominator <= 64:
					total_64_cycles += cycles
					if denominator <= 16:
						total_16_cycles += cycles
			if fast_stats is True or random_stats != 0:
				if denominator <= 64:
					total_64_cases += 1
					if denominator <= 16:
						total_16_cases += 1
			cycle_list.append(cycles)

		# All successful - return mean, mean64, mean16, median, worstcase
		offset = 3	# 3 cycles overhead, for JMP to exit. (JSR-RTS is included with estimate)
		cycle_list.sort()
		try:
			stats = (	(total_cycles / (len(cycle_list))) - offset,
						(total_64_cycles / (total_64_cases)) - offset,
						(total_16_cycles / (total_16_cases)) - offset,
						cycle_list[len(cycle_list)//2] - offset,
						cycle_list[-1] - offset )
		except (ZeroDivisionError, IndexError):
			print(f"Warning: bad emulated stats ({len(cycle_list)} total, {total_64_cases} <=64, {total_16_cases} <=16 - all must be > 0)")
			stats = ( BAD_CYCLES, BAD_CYCLES, BAD_CYCLES, BAD_CYCLES, BAD_CYCLES )
		return (False, -1, -1, stats, None)


def single(args):
	""" Generate a single divider routine """
	divi = Divider(args)
	if args.known_denominator is not None:
		_, string, m256, m64, m16, median, worst, size = divi.make_constant_divider(args.known_denominator)
	else:
		_, string, m256, m64, m16, median, worst, size = divi.make_divide()
	# Report stats
	print(f"Divider generated. Size {size} bytes.", file=sys.stderr)
	if args.stats is True:
		p = "Estimated Cycles: "
		p += f"{m256:.5} mean, {m64:.5} for denominators <=64, {m16:.5} for <=16, {median} median, {float(worst):.5} worst case."
		print(p, file=sys.stderr)
	if args.assemble is True:
		result = divi.do_make_divide().result
		_, asmout, _, _, _, _, _, _, _, _, _, _, _, _, _, emulation_result = result
		if args.emulate is True:
			if isinstance(emulation_result, tuple):
				if isinstance(emulation_result[3], tuple):
					m256, m64, m16, median, worst = emulation_result[3]
					p = "Emulated Cycles: "
					p += f"{m256:.5} mean, {m64:.5} for denominators <=64, {m16:.5} for <=16, {median} median, {float(worst):.5} worst case."
				else:
					p = f"Emulator Error: {emulation_result}"
			else:
				p = "Emulator Error: No Asm"
			print(p, file=sys.stderr)
		print(asmout)

	if isinstance(args.output, str):
		with open(args.output,"w", encoding="utf-8") as file:
			file.write(string)
	else:
		args.output.write(string)

def build_format(parser):
	""" Formatting """
	format_group = parser.add_argument_group("Formatting", \
		"Formatting parameters, for compatibility with different assemblers. The defaults are for ACME.")
	format_group.add_argument('-C', '--comment', default=';', help='prefix to comments (e.g. "#")')
	format_group.add_argument('-e', '--equb', default="!byte", help="prefix to assemble a literal byte")
	format_group.add_argument('-i', '--instruction', default='\t', help='prefix to instructions (e.g. \\t)')
	format_group.add_argument('-l', '--label', default='', help='prefix to labels (e.g. ".")')
	format_group.add_argument('-p', '--prefix', default='divide_', help='prefix to labels and calls (e.g. "divi_")')

def build_env(parser):
	""" Environment """
	env_group = parser.add_argument_group("Environment", "Parameters controlling the calling convention.")
	env_group.add_argument('-0', '--divide-by-zero', help="set the external divide by zero handler.")
	env_group.add_argument('-9', '--error-vector', action='store_true',
		help="if set, the division by zero handler is a vector (pointer to call indirectly), not a target to call directly.")
	env_group.add_argument('-D', '--denominator-from', default="x",
		help="take the denominator from this reg ('x', 'y' or 'a'), or 'memory' (the 'denominator' location).")
	env_group.add_argument('-d', '--denominator', default="muldiv_temp_u",
		help="label of the zero page location containing the denominator")
	env_group.add_argument('-N', '--numerator-from', default="memory",
		help="take the numerator from this reg ('x', 'y' or 'a'), or 'memory' (the 'numerator' location).")
	env_group.add_argument('-n', '--numerator', default="muldiv_temp_t",
		help="label of the zero page location containing the numerator")
	env_group.add_argument('-W', '--result-to', default="a",
		help="return the result in this reg ('x', 'y' or 'a'), or 'denominator' or 'numerator' to put it in memory.")

def build_single(parser):
	""" Parameters for producing a single instance """
	single_group = parser.add_argument_group("Parameters", \
		"Parameters defining a single divider routine, or the subset of routines which a test will consider.")
	single_group.add_argument('-6', '--with-65c02', action="store_true", help="generate code for the 65c02. This cannot be emulated.")
	single_group.add_argument('-B',	'--high-bit', action='store_true',
		help="test the high bit of the denominator: over 128 the result is either 0 or 1, which is fast to test.")
	single_group.add_argument('-~B','--no-high-bit', action='store_true')
	single_group.add_argument('-c', '--max-custom', type=int, default=None,
		help="maximum denominator to use a custom routine (higher is faster but larger)")
	single_group.add_argument('-F', '--factoring', action='store_true', help="use factoring (faster for a few cases, but bigger)")
	single_group.add_argument('-~F','--no-factoring', action='store_true')
	single_group.add_argument('-f', '--max-full', type=int, default=None,
		help="maximum denominator to use a custom routine that is not just a prefix to another")
	single_group.add_argument('-H', '--half-table', action="store_true",
		help="use a half-width (8, not 16 bit) table. Faster and smaller, but is sensitive to alignment")
	single_group.add_argument('-~H','--no-half-table', action='store_true')
	single_group.add_argument('-I', '--inlining', action='store_true', help="use inlining (less space, but slower)")
	single_group.add_argument('-~I','--no-inlining', action='store_true')
	single_group.add_argument('-K', '--skip-custom', type=int, default=0, help="avoid producing a routine for this denominator")
	single_group.add_argument('-k',	'--known-denominator', type=int, help="produce code to divide by a known constant denominator")
	single_group.add_argument('-M', '--self-modifying', action="store_true",
		help="use self modifying code. Faster and smaller, but won't run from ROM")
	single_group.add_argument('-~M','--no-self-modifying', action='store_true')
	single_group.add_argument('-S', '--max-shifting', type=int, default=0,
		help="maximum denominator to use the shifting divider as a fallback when over max-custom. 0 = never use it, 256=always.")
	single_group.add_argument('-T', '--choice-tree', action='store_true',
		help="use a choice tree if possible (faster and usually smaller, for low --max-custom)")
	single_group.add_argument('-~T','--no-choice-tree', action='store_true')
	single_group.add_argument('-u', '--unroll', action='store_true', help="unroll the subtraction loop (bigger, faster)")
	single_group.add_argument('-~u','--no-unroll', action='store_true')
	single_group.add_argument('-V',	'--early-high-bit', action='store_true',
		help="do that test before checking whether it's in the table - faster if high bit set values are common.")
	single_group.add_argument('-~V','--no-early-high-bit', action='store_true')

def build_test(parser):
	""" Test / Stats (multiple run) modes """
	test_group = parser.add_argument_group("Test modes", \
		"Test modes: run multiple cases to check correctness and obtain comparative stats.")
	test_group.add_argument('-1', '--one-error', action="store_true", help="when testing, exit at the first error")
	test_group.add_argument('-A', '--report', help="generate a report of errors to this file")
	test_group.add_argument('-a', '--assemble', action="store_true",
		help="when testing, run the ACME assembler to test correctness of each output")
	test_group.add_argument('-E', '--emulate', action="store_true",
		help="when testing, run a 6502 emulator to check correctness and time taken (this makes the test much slower)")
	test_group.add_argument('-m', '--mix', nargs=5, type=float,
		help="takes 5 floats: <mean 16> <mean 64> <mean> <median> <worst>, setting the weights used in the mixed table")
	test_group.add_argument('-O', '--old-file', default=None, help="read an old output file and regenerate stats from it")
	test_group.add_argument('-Q', '--quickest', action="store_true", help="when testing, run a much smaller set of cases")
	test_group.add_argument('-q', '--quick', action="store_true",
		help="when testing, run a smaller set of cases")
	test_group.add_argument('-R', '--random-seed', type=int, default=0,
		help="when testing with --random, use a repeatable set of cases generated from this number")
	test_group.add_argument('-r', '--random', type=int, help="when testing, run this many randomly generated test cases")
	test_group.add_argument('-s', '--stats', action="store_true", help="generate statistics (this makes the test slower)")
	test_group.add_argument('-t', '--test', action="store_true",
		help="produce all possibilities, save stats and a command line to repeat it")
	test_group.add_argument('-v', '--verbose', action="store_true",
		help="when testing, include all (not just failing) cases in the report")
	test_group.add_argument('-X', '--fast-stats', action="store_true",
		help="generate estimated or emulated statistics from a limited set of numerator/denominators (faster, less accurate)")
	test_group.add_argument('-Y', '--random-stats', type=int, default=0,
		help="generate estimated or emulated statistics from randomized numerator/denominators (faster, less accurate)")

def build_parser():
	""" build an argparser parser """
	parser = argparse.ArgumentParser(
			prog='makedivide',
			description='A parameterizable division routine builder for 6502',
			epilog='For full documentation, see https://github.com/msearle5/makedivide/blob/main/README.md')

	parser.add_argument('-o', '--output', default=sys.stdout, help="file to output to (stats from a test mode, otherwise code)")
	parser.add_argument('-P', '--no-progress', help="disable the progress bar")

	build_format(parser)
	build_env(parser)
	build_single(parser)
	build_test(parser)

	return parser

def main():
	""" Main command line entry. Parse, check consistency, and run. """
	parser = build_parser()

	args = parser.parse_args()

	if args.with_65c02 is True and args.emulate is True:
		args.emulate = False
		print("Warning: the emulator supports 6502 only, not 65c02. Emulation has been disabled.")

	if args.skip_custom is not None and args.max_custom is not None and args.skip_custom > args.max_custom:
		print("Turning off --skip-custom, as it must be <= max custom")
		args.skip_custom = 0

	if args.skip_custom is not None and args.choice_tree is True:
		print("Turning off --skip-custom, as it is incompatible with --choice-tree")
		args.skip_custom = 0

	if args.max_custom is None and args.test is False:
		print("Using default max_custom (18)")
		args.max_custom = 18

	if args.max_custom is not None and args.max_full is None and args.test is False:
		print("Assuming max_full = max_custom")
		args.max_full = args.max_custom

	if args.assemble is False and args.emulate is True:
		print("Using --assemble, as it is required for emulation")
		args.assemble = True

	# Seed the RNG if it's going to be used
	if (args.random is not None and args.random > 0) or (args.random_stats is not None and args.random_stats > 0):
		if args.random_seed == 0:
			seed = time.time_ns()
			print(f"Using random seed {seed}", file=sys.stderr)
		else:
			seed = args.random_seed
		random.seed(seed)

	if args.random is None and args.random_stats is None and args.random_seed != 0:
		print("Random seed was given, without either --random or --random-stats: this will have no effect by itself")

	if args.early_high_bit is True:
		args.high_bit = True

	if args.quickest is True:
		args.quick = True

	# Take 5 floats for mixer or use a default
	if args.mix is None:
		args.mix = (1, 1, 1, 1, 1)

	if args.old_file is not None:
		test_from_old(args)
	elif args.test is True:
		test(args)
	else:
		single(args)

# True if the given parameters match command line limits on test modes
def args_are_ok(args, factoring, inlining, choice_tree, half_table, self_modifying, unroll, high_bit, early_high_bit):
	""" True if the given parameters match command line limits on test modes """
	if (early_high_bit is False and args.early_high_bit is True) or (early_high_bit is True and args.no_early_high_bit is True):
		return False
	if (high_bit is False and args.high_bit is True) or (high_bit is True and args.no_high_bit is True):
		return False
	if (unroll is False and args.unroll is True) or (unroll is True and args.no_unroll is True):
		return False
	if (self_modifying is False and args.self_modifying is True) or (self_modifying is True and args.no_self_modifying is True):
		return False
	if (half_table is False and args.half_table is True) or (half_table is True and args.no_half_table is True):
		return False
	if (choice_tree is False and args.choice_tree is True) or (choice_tree is True and args.no_choice_tree is True):
		return False
	if (inlining is False and args.inlining is True) or (inlining is True and args.no_inlining is True):
		return False
	if (factoring is False and args.factoring is True) or (factoring is True and args.no_factoring is True):
		return False

	return True

def test_random_futures(args, executor):
	""" Random testing: generate parameters at random and run test cases, returning futures """
	futures = []
	i_max = 64
	j_max = 64
	factoring_max = 2
	inlining_max = 2
	choice_tree_max = 2
	half_table_max = 2
	use_smc_max = 2
	unrolled_max = 2
	high_bit_max = 2
	early_high_bit_max = 2

	shift_cases_max = 66
	sample_max = i_max * j_max * shift_cases_max * factoring_max * inlining_max * choice_tree_max * use_smc_max
	sample_max *= half_table_max * high_bit_max * early_high_bit_max * j_max
	print(f"Taking {args.random} samples randomly from {sample_max} possibilities", file=sys.stderr)

	poss = int(args.random * 1.2)
	pargsl = []
	while len(pargsl) < args.random:
		print(f"Trying {poss} possibilities...", file=sys.stderr)
		rnl = random.sample(range(sample_max), poss)
		rnl_idx = 0
		pargsl = []
		assert poss < (sample_max // 2)
		while len(pargsl) < args.random and rnl_idx < poss:
			sample = rnl[rnl_idx]
			rnl_idx += 1
			i = sample % i_max
			sample //= i_max
			j = sample % j_max
			sample //= j_max
			if i < j:
				i, j = j, i
			max_shifting_divider = sample % shift_cases_max
			if max_shifting_divider == shift_cases_max-1:
				max_shifting_divider = 256
			sample //= shift_cases_max
			factoring = (sample % factoring_max) == 0
			sample //= factoring_max
			inlining = (sample % inlining_max) == 0
			sample //= inlining_max
			choice_tree = (sample % choice_tree_max) == 0
			sample //= choice_tree_max
			half_table = (sample % half_table_max) == 0
			sample //= half_table_max
			use_smc = (sample % use_smc_max) == 0
			sample //= use_smc_max
			unrolled = (sample % unrolled_max) == 0
			sample //= unrolled_max
			high_bit = (sample % high_bit_max) == 0
			sample //= high_bit_max
			early_high_bit = (sample % early_high_bit_max) == 0
			sample //= early_high_bit_max
			skip_custom = 0
			if j > 1:
				skip_custom = sample % j

			if args_are_ok(args, factoring, inlining, choice_tree, half_table, use_smc, unrolled, high_bit, early_high_bit):
				divi = Divider(args, max_custom=i, max_full=j, prefix="", use_factoring=factoring, inlining=inlining, style="", \
										use_choice_tree=choice_tree, max_shifting_divider=max_shifting_divider, half_table=half_table, \
										use_smc=use_smc, fallback_unrolled_subtraction=unrolled, \
										high_bit_check=high_bit, early_high_bit=early_high_bit, skip_custom=skip_custom, first=False)
				if divi.try_make_divide() is True:
					pargsl.append(divi)
		if len(pargsl) < args.random:
			if len(pargsl) <= 100:
				poss *= 10
			else:
				poss *= 1 + ((1.05 * args.random) // (1 + len(pargsl)))
			poss += 100
			poss = int(poss)
	print(f"Found {len(pargsl)} possibilities...", file=sys.stderr)
	for pargs in pargsl:
		futures.append(executor.submit(pargs.do_make_divide))

	return futures

def test_futures(args, executor):
	""" With all possible combinations of args, run test cases and return a list of futures """
	if args.random is not None:
		return test_random_futures(args, executor)

	futures, max_cases, shift_cases = [], list(CUSTOMS), (0, 4, 8, 12, 16, 24, 32, 48, 64, 256)
	hs_table = ( (False, True), (False, False), (True, False), (True, True) )
	skips = (0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28)
	if args.quick is True:
		max_cases = (
			0, 1, 2, 3, 4,
			6, 8, 10, 12,
			15, 18, 23, 28,
			34, 40, 52, 64
			)
		shift_cases = (0, 4, 12, 48, 256)
		skips = (0, 1, 2, 4, 6, 8)
		hs_table = ( (True, False), (True, True) )
		if args.quickest is True:
			shift_cases = (0, 12, 256)
			max_cases = (
				0, 1, 2, 3, 4,
				6, 8, 10, 12,
				15, 18, 23, 64
				)
			skips = (0, 4)
			hs_table = ( (True, True), )
	full_cases = max_cases

	# Over 15: ignore factoring, allow inlining, ignore choice
	# 7 to 15: allow factoring, allow inlining, ignore choice
	# 5 to 7:  allow factoring, ignore inlining, ignore choice
	# <5:      allow factoring, ignore inlining, allow choice
	fic_table_over_15	= ( (False, False, False), (False, True, False) )
	fic_table_7_15		= ( (False, False, False), (False, True, False), (True, False, False), (True, True, False) )
	fic_table_5_7		= ( (False, False, False), (True, False, False) )
	fic_table_under_5	= ( (False, False, False), (True, False, False), (False, False, True), (True, False, True) )

	tags = (	(False, False, False, "_rn"), (True, False, False, "_rl",), (True, True, False, "_re"),
				(False, False, True, "_un"), (True, False, True, "_ul",), (True, True, True, "_ue") )

	def test_one_future(args, i):
		""" Run one of the list of futures """
		offset_cases = []
		for m in shift_cases:
			if m not in {0,256}:
				offset_cases.append(m + i)
			else:
				offset_cases.append(m)
		fic_table = fic_table_over_15
		if i <= 15:
			fic_table = fic_table_7_15
			if i < 7:
				fic_table = fic_table_5_7
				if i <= 5:
					fic_table = fic_table_under_5
		for j in full_cases:
			if j <= i:
				for factoring, inlining, choice_tree in fic_table:
					if (j != i) and ((args.quickest is True) or (choice_tree is True)):
						continue
					for k in skips:
						if k == 0:
							skip_custom = 0
						else:
							if choice_tree is True or inlining is False:
								continue
							skip_custom = j-k
							if skip_custom <= 2:
								continue
						for half_table, use_smc in hs_table:
							for max_shifting_divider in offset_cases:
								first = True
								for high_bit, early_high_bit, unrolled, _ in tags:
									if args_are_ok(args, factoring, inlining, choice_tree, half_table, use_smc, unrolled, high_bit, early_high_bit):
										divi = Divider(args, max_custom=i, max_full=j, prefix="", use_factoring=factoring, inlining=inlining, style="", \
											use_choice_tree=choice_tree, max_shifting_divider=max_shifting_divider, half_table=half_table, \
											use_smc=use_smc, fallback_unrolled_subtraction=unrolled, \
											high_bit_check=high_bit, early_high_bit=early_high_bit, skip_custom=skip_custom, first=first)
										if divi.try_make_divide() is True:
											futures.append(executor.submit(divi.do_make_divide))
											first = False
			else:
				break

	for i in max_cases:
		test_one_future(args, i)

	return futures

def write_stats(args, out):
	""" Join and write to output """
	if isinstance(args.output, str):
		with open(args.output, "w", encoding="utf-8") as file:
			print("\n".join(out), file=file)
	else:
		print("\n".join(out), file=args.output)

def print_stats(args, stat_lists):
	""" Calculate and print stats (best per size, for different measures of merit) """
	# Add stats
	out = []
	est=""
	if args.emulate is True:
		best_worst  	= best_time(stat_lists["eworst"])
		best_median 	= best_time(stat_lists["emedian"])
		best_mean   	= best_time(stat_lists["emean"])
		best_mean_64   	= best_time(stat_lists["emean64"])
		best_mean_16   	= best_time(stat_lists["emean16"])
		best_blended   	= blended_best_time([stat_lists["emean16"], stat_lists["emean64"], stat_lists["emean"], \
											stat_lists["emedian"], stat_lists["eworst"]], args.mix)
		add_title("Emulated: Best by a mixed score, smallest to fastest", out, args)
		out.extend(best_blended)
		add_title("Emulated: Best by mean cycles, from smallest to fastest", out, args)
		out.extend(best_mean)
		add_title("Emulated: Best by mean cycles for denominators <= 64, from smallest to fastest", out, args)
		out.extend(best_mean_64)
		add_title("Emulated: Best by mean cycles for denominators <= 16, from smallest to fastest", out, args)
		out.extend(best_mean_16)
		add_title("Emulated: Best by median cycles, from smallest to fastest", out, args)
		out.extend(best_median)
		add_title("Emulated: Best by worst case cycles, from smallest to fastest", out, args)
		out.extend(best_worst)
		est = "Estimated: "
	if args.stats is True:
		best_worst  	= best_time(stat_lists["worst"])
		best_median 	= best_time(stat_lists["median"])
		best_mean   	= best_time(stat_lists["mean"])
		best_mean_64   	= best_time(stat_lists["mean64"])
		best_mean_16   	= best_time(stat_lists["mean16"])
		best_blended   	= blended_best_time([stat_lists["mean16"], stat_lists["mean64"], stat_lists["mean"], \
											stat_lists["median"], stat_lists["worst"]], args.mix)
		add_title(f"{est}Best by a mixed score (mean <256,64,16 + median + worst), smallest to fastest", out, args)
		out.extend(best_blended)
		add_title(f"{est}Best by mean cycles, from smallest to fastest", out, args)
		out.extend(best_mean)
		add_title(f"{est}Best by mean cycles for denominators <= 64, from smallest to fastest", out, args)
		out.extend(best_mean_64)
		add_title(f"{est}Best by mean cycles for denominators <= 16, from smallest to fastest", out, args)
		out.extend(best_mean_16)
		add_title(f"{est}Best by median cycles, from smallest to fastest", out, args)
		out.extend(best_median)
		add_title(f"{est}Best by worst case cycles, from smallest to fastest", out, args)
		out.extend(best_worst)
	add_title("All cases, sorted by table length", out, args)
	if args.random is not None:
		stat_lists["full"].sort()
	out.extend(stat_lists["full"])
	write_stats(args, out)
	print("Statistics complete.", file=sys.stderr)

def new_stat_lines():
	""" Return an empty stats structure (dict of lists) """
	stat_lists = {}
	for name in (	"full",
					"mean", "mean64", "mean16", "median", "worst", "mix",
					"emean", "emean64", "emean16", "emedian", "eworst", "emix"):
		stat_lists[name] = []
	return stat_lists

def do_test(args, futures, executor):
	""" Run a list of futures, report errors and stats """

	errors = 0
	badparams = 0
	emu_errors = 0
	emu_traces = 0
	success = 0

	cases = len(futures)
	sbar = "+------" * 12
	if args.stats:
		sbar = f"{sbar}+-------+-------+-------+------+-------"
	if args.emulate:
		sbar = f"{sbar}+-------+-------+-------+------+-------"
	sbar = f"{sbar}+{'-' * MAX_COMMAND}"

	sbar = sbar + "+"
	stat_lists = new_stat_lines()

	# Run them all
	emulation_results = {}
	asmout = []

	def do_one_test(args, returned):
		""" Run one of a list of futures """
		nonlocal errors, badparams, emu_errors, emu_traces, success, sbar, asmout, stat_lists
		result, binary, avail, _, _, _, _, _, _, _, _, _, _, _, _, emulation_result = returned.result

		factoring = returned.use_factoring
		inlining = returned.inlining
		choice_tree = returned.use_choice_tree
		max_shifting_divider = returned.max_shifting_divider
		unrolled = returned.fallback_unrolled_subtraction

		if avail:
			if returned.first:
				stat_lists["full"].append(sbar)
			returned.add_line(stat_lists)

		error = (binary is None or result is None or "Error" in result)
		if error is True:
			errors += 1
		badparam = result and NOT_POSS in result
		if badparam is True:
			badparams += 1
		if error is False and badparam is False:
			success += 1
		emu_trace = None
		if emulation_result is not None:
			if isinstance(emulation_result, str):
				emu_errors += 1
			else:
				mismatch, divisor, _, _, trace = emulation_result
				if mismatch is True or divisor != -1:
					emu_errors += 1
					if trace is not None:
						emu_traces += 1
						emu_trace = str(trace)
		eib = (emulation_result is not None and isinstance(emulation_result, str) and badparam is not True)
		if args.verbose or error is True or emu_trace is not None or eib:
			asmout.append(f"Results for max_custom {returned.max_custom}, max_full {returned.max_full}, factoring {factoring}, " + \
							f"inlining {inlining}, unrolled {unrolled}, choice {choice_tree}, max_shifting {max_shifting_divider}," + \
							f" skip_custom {returned.skip_custom}:")
			asmout.append(f"(equivalent to command: {returned.command_words()[0]})")
			if result is None:
				asmout.append("(no result)")
			else:
				asmout.append(str(result))
			if isinstance(emulation_result, str):
				if emulation_result not in emulation_results:
					emulation_results[emulation_result] = 0
				emulation_results[emulation_result] += 1
			if (emulation_result is not None and isinstance(emulation_result, str) and badparam is not True):
				asmout.append(f"Emulation error: {emulation_result}")
			if emu_trace is not None:
				asmout.append("Trace follows:")
				asmout.append(")\n".join(emu_trace.split("),")))
				asmout.append("")
			if binary is None:
				asmout.append("(no binary output)")
			else:
				asmout.append(str(binary))
			asmout.append("")
		if args.one_error and (error is True or emu_trace is not None or eib):
			print(f"Error, exiting after {success} successful cases...", file=sys.stderr)
			return False
		return True

	print(f"Running {cases} test cases...", file=sys.stderr)

	tqdm_range = range(len(futures))
	if has_tqdm is True and args.no_progress is False:
		tqdm_range = tqdm.tqdm(range(len(futures)), delay=3, total=len(futures), miniters=1, smoothing=0.05)
	for futurei in tqdm_range:
		future = futures[futurei]
		returned = future.result()
		futures[futurei] = None
		if do_one_test(args, returned) is False:
			executor.shutdown(cancel_futures=True, wait=True)
			break
	stat_lists["full"].append(sbar)

	print("All test cases complete.", file=sys.stderr)
	if args.emulate is True or args.stats is True:
		asmoutname = args.report
		print("Computing statistics...", file=sys.stderr)
		if asmoutname is not None:
			with open(asmoutname, "w", encoding="utf-8") as file:
				header = f"Ran {errors+success} test cases, {errors} errors, {success} successfully assembled.\n"
				if args.emulate:
					header = header[:-2] + f", {emu_errors - badparams} emulation errors, {badparams} bad parameters, {emu_traces} with trace.\n"
					if len(emulation_results) > 0:
						header = f"{header}Emulation errors reported: {emulation_results}"
				file.write(header)
				for entry in asmout:
					file.write("\n")
					file.write(entry)
				file.write("\n")

		print_stats(args, stat_lists)

def test_from_old(args):
	""" Parse old test output, use it to re-run statistics """
	# Parse output. Skip lines until "All cases is found", then skip 4 more.
	# Until the end of file, read lines, skipping ones starting with + and reading ones starting with |.
	# |-lines are parsed by replacing | with space and reading space-delimited, converting to a Divider
	#	and setting its result.
	name = args.old_file
	all_cases = False
	print(f"Reading old results from {name}...", file=sys.stderr)

	stat_lists = new_stat_lines()
	with open(name, "r", encoding="utf-8") as filep:
		file = filep.read()
		lines = file.splitlines()
		for line in lines:
			if len(line) > 1 and line[:2] == '| ':
				if all_cases is False:
					if "All cases" in line:
						all_cases = True
				else:
					words = line.split('|')
					if len(words) != 25:
						print(f"Bad line (wrong field count): {line}", file=sys.stderr)
						return
					words = words[1:-2] # strip leading and trailing '', and command line
					stripped = []
					# remove whitespace
					for word in words:
						stripped.append(word.strip())
					conv = []
					for s in stripped:
						if len(s) < 1:
							print(f"Bad line (empty field): {line}", file=sys.stderr)
							return
						if s == "Yes":
							conv.append(True)
						elif s == "No":
							conv.append(False)
						elif s == "Early":
							conv.append((True, True))
						elif s == "Late":
							conv.append((True, False))
						elif (s[0].isdigit() or s[0] == '-') and '.' in s:
							conv.append(float(s))
						elif (s[0].isdigit() or s[0] == '-'):
							conv.append(int(s))
						else:
							conv.append(s)
					if conv[6] is False:
						check_high_bit=False
						early_high_check=False
					else:
						check_high_bit, early_high_check=conv[6]
					divi = Divider(args, max_custom=conv[0], max_full=conv[1], prefix="", style="", skip_custom=conv[2], use_factoring=conv[3], \
						inlining=conv[4], fallback_unrolled_subtraction=conv[5], high_bit_check=check_high_bit, \
						early_high_bit=early_high_check, use_choice_tree=conv[7], max_shifting_divider=conv[8], half_table=conv[9], \
						use_smc=conv[10], first=False)

					size, mean, mean64, mean16, median, worst, emean, emean64, emean16, emedian, eworst = conv[11:22]
					divi.result = ("", "", True, "",	mean, mean64, mean16, median, worst,
														emean, emean64, emean16, emedian, eworst,
														size, (False, -1, -1, (emean, emean64, emean16, emedian, eworst), None))
					divi.add_line(stat_lists)

	print_stats(args, stat_lists)

def test(args):
	""" Set up futures for all possibilities, and run them """
	with concurrent.futures.ProcessPoolExecutor() as executor:
		futures=test_futures(args, executor)
		do_test(args, futures, executor)

if __name__ == '__main__':
	main()
