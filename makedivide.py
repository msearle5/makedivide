#!/usr/bin/python

##################################################################################
#
# A parameterizable division routine builder for 6502.
#
# The division routines produced use a table of divide-by-constant routines, falling back to repeated subtraction for higher denominator values.
# The repeated subtraction may use a loop (smaller) or unrolled code (faster).
# To limit the size of the divide-by-constant routines, they share code when possible - multiples of powers of two are handled by one or more
# leading shift-rights for the power of two, so for example a divide-by-5 routine also handles 10, 20 and 40.
# Factoring (e.g. replacing "x/9" with "(x/3)/3") is used when it saves time, when asked for (it adds some size) which is for 9 (22-62 cycles
# saved) or 15 (4-17 cycles saved) only (and their multiples of powers of two), when the custom routine for those denominators is not used.
# The routines also by default share trailing code, so to save space will branch between routines.
#
# Options:
# def make_divide(max_custom, max_full, numerator, denominator, prefix, insn, label, equb, comment, *, fallback_unrolled_subtraction = True, high_bit_check = False, early_high_bit = False, divide_by_0=None, use_factoring=False, inlining=False):
#
###################################################################################
# Formatting options:
# These don't change the effect of the code, but change the prefixes used for compatibility with different assemblers and to allow multiplecopies to be used.
#
# "fallback_unrolled_subtraction" if true, will use straight line code instead of a loop for repeated subtraction (faster, but longer - how much
#            longer depends on the maximum possible result, which increases for smaller jump table sizes. The result of that it that there is a
#            minimum-size table length point where reducing the size further produces larger (and slower) code.
#
###################################################################################
# Options determining what divider will be produced:
#
# "max_custom" is the highest value for which a custom routine (as opposed to repeated subtraction) is used.
#
# "max_full" (which must be no more than max_custom) is the highest value for which a custom routine that is not just a divide-by-2 or 4 in front
#            of another is used.
#
# "inlining" if true, will make every divide-by-constant separate, rather than sharing parts (branching between them). This uses more space but
#            is a little faster (saving 3 cycles for a branch in the affected denominators)
#
# "high_bit_check" if true adds a check for high bit set (128+) denominators. These can be handled simply (the result is either 0 or 1, depending
#            on whether the numerator is less than the denominator or not) so this improves performance if high denominators are expected. The
#            check occurs by default only if the denominator is known to not use the jump table, so those routines won't be slowed by the check
#            - only ones using the generic divider.
#
# "early_high_bit" if true (and if high_bit_check is also true) it will check for denominators >= 128 before the check for denominators in the jump
#            table. No effect on size, it makes high denominators faster and low ones slower. On average it's an improvement (there are 128
#            high-bit-set denominators and no more than 64 entries in the jump table), although that only matters if you are expecting evenly
#            distributed arguments.
#

# TODO is the loop always smaller?
# TODO - option to use dedicated routines for 64, 12 etc.
# TODO - find more routines? (they are made moslty from ror, lsr and adc numerator)
# TODO- replace RTS trick with num denom jump? Optionally, because time vs space, + it required the nom denom to be sequential zero page:
#		- RTS: lda hightable, x; pha; lda lowtable, x; pha; lda numerator; rts => 23 cycles, 9 bytes
#		- NDJ: ldy hightable, x; sty denominator; lda numerator; ldy lowtable, x; sty numerator; jmp (denominator) => 22 cycles, 12 bytes
#			- **NOT compaitble with shifting
# TODO estimate based on average # of iters
# TODO buildability check (for all, invoking acme) => extend or reduce some limits?
# TODO real cli, including request for one spec
# TODO reg in-out?
# TODO simplify (inline etc) small choice, allow the size 1 case
# TODO levels of completeness of search for test
# TODO use more cores?
# TODO short unrolls are notthe best?
# TODO make TOML output us external files so as to be non-Imogoly?
# TODO process chunks


import argparse
import concurrent.futures
import copy
import math
import os
import subprocess
import sys
import tempfile

# Available constants to divide by
CUSTOMS = {
	0, 1, 2, 3, 4,
	5, 6, 7, 8, 9,
	10, 11, 12, 13, 14,
	15, 16, 17, 18,
	19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
	29, 30, 31, 32, 34, 36,
	40, 44, 48, 52, 56,
	60, 64
}

# Prime numbers including 1, below 100.
PRIMES = {
	1,
	2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
	37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
	79, 83, 89, 97
}

# Has a tail branch
TAIL = {
	7, 11, 13, 15, 19, 23, 25, 27, 29, 31
}

# Cycles taken for the branching-tail variant of each routine
CYCLES = {
	3: 9+16+2,
	5: 9+16+2,
	7: 3+12+3+3+6,
	9: 9+18,
	11: 9+12+3+3+8,
	13: 9+14+3+3+8,
	15: 0+8+2+3+3+8,
	17: 9+8+2+8,
	19: 9+8+3+8,
	21: 3+22,
	23: 3+8+3+3+10,
	25: 3+8+3+3+12,
	27: 3+8+3+3+12,
	29: 6+12+3+3+12,
	31: 0+8+3+3+12
}

# Time taken to dispatch through a choice tree (max custom which is 1+ number of choices includig 0)
CHOICE_CYCLES = {
	2: (5+7+9) / 3,
	3: (8+11+7+9) / 4,
	4: (10+12+14+7+9) / 5,
	5: (7+11+13+10+12+14) / 6,
	6: (7+13+15+17+10+12+14) / 7,
	7: (7+11+13+15+10+12+16+17) / 8,
}

CYCLES12 = copy.deepcopy(CYCLES)
CYCLES12[1] = 0

# Cycles needed to check the high bit, and if set return 1 or 0.
def cycles_by_high_bit(numerator, denominator, high_bit):
	cycles = 0
	if high_bit is True:
		if numerator < 128:
			cycles += 2
		else:
			if numerator < denominator:
				cycles += 12
			else:
				cycles += 10
	return cycles

# Cycles needed to find the quotient by repeated subtraction
def cycles_by_subtraction(numerator, denominator, unrolled, high_bit):
	quotient = numerator // denominator

	cycles = cycles_by_high_bit(numerator, denominator, high_bit)
	if high_bit is True:
		if numerator < 128:
			cycles += 2
		else:
			if numerator < denominator:
				cycles += 12
			else:
				cycles += 10

	if not unrolled:
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
def mean_cycles_by_subtraction(denominator, unrolled, high_bit):
	total = 0
	for num in range(0,256):
		total += cycles_by_subtraction(num, denominator, unrolled, high_bit)
	return total / 256

# Cycles needed to find the quotient by a custom routine
def cycles_by_custom(numerator, denominator, high_bit, inlining, powers_of_2=False):
	cycles = cycles_by_high_bit(numerator, denominator, high_bit)
	inline_mod = 0
	if inlining is True and denominator in TAIL:
		inline_mod = -3
	cyc = CYCLES
	if powers_of_2 is True:
		cyc = CYCLES12
	if denominator in cyc:
		return cyc[denominator]+inline_mod
	elif denominator//2 in cyc:
		return cyc[denominator//2]+2+inline_mod
	elif denominator//4 in cyc:
		return cyc[denominator//4]+4+inline_mod
	elif denominator//8 in cyc:
		return cyc[denominator//8]+6+inline_mod
	elif denominator//16 in cyc:
		return cyc[denominator//16]+8+inline_mod
	elif denominator//32 in cyc:
		return cyc[denominator//32]+10+inline_mod
	elif denominator//64 in cyc:
		return cyc[denominator//64]+12+inline_mod
	return None

# Cycles needed to find the quotient by a combination of two custom routines
def cycles_by_factor(factor0, factor1, inlining):
	c1 = cycles_by_custom(0, factor0, False, inlining)
	c2 = cycles_by_custom(0, factor1, False, inlining)
	if c1 is None or c2 is None:
		return None
	return 8 + c1 + c2	# jsr, rts, bpl

# Find the set of two factors which is fastest
def cheapest_factors(max_custom, denominator, inlining):
	# Use a single factor if possible
	if denominator <= max_custom:
		result = cycles_by_custom(0, denominator, False, inlining)
		if result is not None:
			return (result, denominator, 1)
 
	# Search for all possible pairs
	factors = []
	maxf = math.ceil(math.sqrt(denominator))
	maxf = min(maxf, max_custom)
	for f in range(3, maxf+1):
		for g in range(3, maxf+1):
			if f*g == denominator:
				cfg = cycles_by_factor(f, g, inlining)
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
def factoring_is_good(max_custom, denominator, unrolled, high_bit, inlining):
	fac_cycles, factor1, factor2 = cheapest_factors(max_custom, denominator, inlining)
	if factor2 == 1:
		# factoring not needed, or not possible
		return (False, factor1, factor2)
	sub_cycles = mean_cycles_by_subtraction(denominator, unrolled, high_bit)
	return (fac_cycles < sub_cycles, factor1, factor2)

def cycles_by_generic(numerator, denominator, unrolled, high_bit, max_shifting_divider):
	if denominator <= max_shifting_divider:
		return 210	# FIXME get a more accurate average from the test mode, reduced because preamble, or a trace of execution
	return cycles_by_subtraction(numerator, denominator, unrolled, high_bit)

def mean_cycles_numerator(numerator, denominator, max_custom, max_full, unrolled, high_bit, early_high_bit, inlining, factoring, choice_tree, max_shifting_divider):
	cycles = 0

	# Early hi bit test
	if high_bit is True and early_high_bit is True:
		cycles += cycles_by_high_bit(numerator, denominator, high_bit)
		if denominator >= 128:
			return cycles

	# Jump table test
	if denominator <= max_custom:
		cycles += 4
		# and dispatch (RTS trick)
		if denominator not in CHOICE_CYCLES or choice_tree is False:
			cycles += 23
		else:
			cycles = CHOICE_CYCLES[denominator]
		# Custom?
		if denominator in CUSTOMS and (denominator in PRIMES or denominator <= max_full):
			cc = cycles_by_custom(numerator, denominator, high_bit, inlining, True)
			if cc is None:
				cycles += cycles_by_generic(numerator, denominator, unrolled, False, max_shifting_divider)
			else:
				cycles += cc
		else:
			if factoring is True:
				is_good, factor1, factor2 = factoring_is_good(max_full, denominator, unrolled, high_bit, inlining)
			else:
				is_good = False
			if is_good is True:
				cycles += cycles_by_factor(factor1, factor2, inlining)
			else:
				cycles += cycles_by_generic(numerator, denominator, unrolled, False, max_shifting_divider)
	else:
		cycles += 5

		if high_bit is True and early_high_bit is False:
			cycles += cycles_by_high_bit(numerator, denominator, high_bit)
			if denominator >= 128:
				return cycles

		cycles += cycles_by_generic(numerator, denominator, unrolled, False, max_shifting_divider)
	return cycles

def stats_cycles(max_custom, max_full, unrolled, high_bit, early_high_bit, inlining, factoring, choice_tree, max_shifting_divider):
	cycles = 0
	clist=[]
	cycles64 = 0
	cycles16 = 0
	for numerator in range(0,256):
		for denominator in range(1,256):
			c = mean_cycles_numerator(numerator, denominator, max_custom, max_full, unrolled, high_bit, early_high_bit, inlining, factoring, choice_tree, max_shifting_divider)
			clist.append(c)
			cycles += c
			if denominator <= 64:
				cycles64 += c
			if denominator <= 16:
				cycles16 += c
	cycles /= 255*256
	cycles64 /= 63*256
	cycles16 /= 15*256
	clist.sort()
	median = clist[len(clist)//2]
	worst = clist[-1]
	return cycles, cycles64, cycles16, median, worst

# The main entry point: see top of file for documentation
def make_divide(max_custom, max_full, numerator, denominator, prefix, insn, label, equb, comment, *, fallback_unrolled_subtraction = True, high_bit_check = False, early_high_bit = False, divide_by_0=None, use_factoring=False, inlining=False, use_choice_tree=False, max_shifting_divider=0, with_stats=False):
	assert (max_full <= max_custom)
	assert (high_bit_check or not early_high_bit)
	assert (max_full >= 2)

	available=True

	internal_div_by_0 = False
	if divide_by_0 is None:
		internal_div_by_0 = True
		divide_by_0 = f"{prefix}divide_by_0"
	text = []

	generic_limit = 255
	low_iters_max = 0
	if high_bit_check is True and fallback_unrolled_subtraction is True:
		low_iters_max = 2

	# Reduce if there is wasted space at the top of the table
	while max_custom not in CUSTOMS:
		max_custom -= 1

	# Find highest point which can be handled without the generic function
	max_custom_avail = max_custom
	for i in range(1, max_custom+1):
		if i not in CUSTOMS:
			max_custom_avail = i-1
			break

	max_iters = generic_limit // max_custom_avail
	max_iters = max(low_iters_max, max_iters)
	text.append(f"{comment}Division, 8 / 8 bits.")

	text.append(f"{insn}ldx {denominator}")

	# Early high jump
	if early_high_bit is True:
		text.append(f"{insn}bmi {prefix}high_bit_denom")

	# Check jump vs. subtract
	text.append(f"{insn}cpx #{max_custom+1}")
	text.append(f"{insn}bcs {prefix}use_sub")

	# Jump table (or choice tree) dispatch
	# Jumps to use_sub will always bypass high bit check
	if use_choice_tree:
		if max_custom == 2:
			text.append(f"{insn}cpx #1")
			text.append(f"{insn}beq {prefix}divide_by_1")
			text.append(f"{insn}bcc {prefix}divide_by_2")
			text.append(f"{insn}bcs {prefix}divide_by_0")
		elif max_custom == 3:
			text.append(f"{insn}cpx #2")
			text.append(f"{insn}bcs {prefix}divide_by_1_0")
			text.append(f"{insn}beq {prefix}divide_by_2")
			text.append(f"{insn}bne {prefix}divide_by_3")
			text.append(f"{label}{prefix}divide_by_1_0")
			text.append(f"{insn}cpx #1")
			text.append(f"{insn}beq {prefix}divide_by_1")
			text.append(f"{insn}bne {prefix}divide_by_0")
		elif max_custom == 4:
			text.append(f"{insn}cpx #3")
			text.append(f"{insn}bcs {prefix}divide_by_2_0")
			text.append(f"{insn}beq {prefix}divide_by_3")
			text.append(f"{insn}bne {prefix}divide_by_4")
			text.append(f"{label}{prefix}divide_by_2_0")
			text.append(f"{insn}cpx #1")
			text.append(f"{insn}beq {prefix}divide_by_1")
			text.append(f"{insn}bcs {prefix}divide_by_0")
			text.append(f"{insn}bcc {prefix}divide_by_2")
		elif max_custom == 5:
			text.append(f"{insn}cpx #3")
			text.append(f"{insn}bcs {prefix}divide_by_2_0")
			text.append(f"{insn}beq {prefix}divide_by_3")
			text.append(f"{insn}cpx #4")
			text.append(f"{insn}beq {prefix}divide_by_4")
			text.append(f"{insn}bne {prefix}divide_by_5")
			text.append(f"{label}{prefix}divide_by_2_0")
			text.append(f"{insn}cpx #1")
			text.append(f"{insn}beq {prefix}divide_by_1")
			text.append(f"{insn}bcs {prefix}divide_by_0")
			text.append(f"{insn}bcc {prefix}divide_by_2")
		elif max_custom == 6:
			text.append(f"{insn}cpx #3")
			text.append(f"{insn}bcs {prefix}divide_by_2_0")
			text.append(f"{insn}beq {prefix}divide_by_3")
			text.append(f"{insn}cpx #5")
			text.append(f"{insn}beq {prefix}divide_by_5")
			text.append(f"{insn}bcs {prefix}divide_by_4")
			text.append(f"{insn}bcc {prefix}divide_by_6")
			text.append(f"{label}{prefix}divide_by_2_0")
			text.append(f"{insn}cpx #1")
			text.append(f"{insn}beq {prefix}divide_by_1")
			text.append(f"{insn}bcs {prefix}divide_by_0")
			text.append(f"{insn}bcc {prefix}divide_by_2")
		elif max_custom == 7:
			text.append(f"{insn}cpx #4")
			text.append(f"{insn}bcs {prefix}divide_by_3_0")
			text.append(f"{insn}beq {prefix}divide_by_4")
			text.append(f"{insn}cpx #6")
			text.append(f"{insn}beq {prefix}divide_by_6")
			text.append(f"{insn}bcs {prefix}divide_by_5")
			text.append(f"{insn}bcc {prefix}divide_by_7")
			text.append(f"{label}{prefix}divide_by_3_0")
			text.append(f"{insn}cpx #2")
			text.append(f"{insn}beq {prefix}divide_by_2")
			text.append(f"{insn}bcc {prefix}divide_by_3")
			text.append(f"{insn}cpx #0")
			text.append(f"{insn}beq {prefix}divide_by_0")
			text.append(f"{insn}bne {prefix}divide_by_2")
		else:
			print("WARNING: choice tree not available with this size table", file=sys.stderr)
			use_choice_tree = False
			available=False
	if not use_choice_tree:
		text.append(f"{comment}RTS-trick jump table")
		text.append(f"{insn}lda {prefix}hightable, x")
		text.append(f"{insn}pha")
		text.append(f"{insn}lda {prefix}lowtable, x")
		text.append(f"{insn}pha")
		text.append(f"{insn}lda {numerator}")
		text.append(f"{insn}rts")

	# Limited by branch range to ~60
	if fallback_unrolled_subtraction is True and max_iters > 60:
		print("WARNING: unrolled subtraction not available - branch range limited", file=sys.stderr)
		fallback_unrolled_subtraction = False
		available=False

	# Check high bit
	if high_bit_check is True:
		text.append(f"{label}{prefix}high_bit_denom")
		text.append(f"{insn}cpx {numerator}")
		text.append(f"{insn}bcc {prefix}return_1")
		text.append(f"{insn}beq {prefix}return_1")
		# Fall thru to return 0 if unrolled
		if fallback_unrolled_subtraction is False:
			text.append(f"{insn}lda #0")
			text.append(f"{insn}rts")
			text.append(f"{label}{prefix}return_1")
			text.append(f"{insn}lda #1")
			text.append(f"{insn}rts")

	with_shifting = False
	with_subtraction = False
	# Repeated subtraction, unrolled
	if max_shifting_divider > 0:
		with_shifting = True
	if max_shifting_divider < 256:
		with_subtraction = True

	if with_shifting and with_subtraction:
		text.append(f"{label}{prefix}use_sub")
		text.append(f"{insn}cpx #{max_shifting_divider}+1")
		# Branch to subtraction...
		text.append(f"{insn}bcs {prefix}use_sub_unchecked")
		# or fall through to shifting

	if with_shifting:
		if not with_subtraction:
			text.append(f"{label}{prefix}use_sub")
			if high_bit_check is True: # TODO are these & the only below ever doubled early?
				text.append(f"{insn}bmi {prefix}high_bit_denom")
			text.append(f"{label}{prefix}use_sub_unchecked")
		text.append(f"{label}{prefix}use_shift")
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
		text.append(f"{insn}rts")

	if with_subtraction:
		if fallback_unrolled_subtraction is True:
			midpoint = max(low_iters_max, (max_iters - 4) // 2) # offset because for very large tables the limit is the bcs use_sub
			for i in range(0, midpoint):
				text.append(f"{label}{prefix}return_{i}")
				text.append(f"{insn}lda #{i}")
				text.append(f"{insn}rts")
			if not with_shifting:
				text.append(f"{label}{prefix}use_sub")
			if high_bit_check is True:
				text.append(f"{insn}bmi {prefix}high_bit_denom")
			text.append(f"{label}{prefix}use_sub_unchecked")
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
			if high_bit_check is True and early_high_bit is False:
				text.append(f"{insn}bmi {prefix}high_bit_denom")
			text.append(f"{label}{prefix}use_sub_unchecked")
			text.append(f"{insn}lda {numerator}")
			text.append(f"{insn}ldx #255")
			text.append(f"{insn}sec")
			text.append(f"{label}{prefix}use_sub_loop")
			text.append(f"{insn}sbc {denominator}")
			text.append(f"{insn}inx")
			text.append(f"{insn}bcs {prefix}use_sub_loop")
			text.append(f"{insn}txa")
			text.append(f"{insn}rts")

	# Jump table - make entries
	factors = set()
	jumpentries = []
	jumpentries.append(divide_by_0)
	for i in range(1, max_custom+1):
		if i in CUSTOMS and (i in PRIMES or i <= max_full):
			jumpentries.append(f"{prefix}divide_by_{i}")
		else:
			if use_factoring is True:
				is_good, factor1, factor2 = factoring_is_good(max_full, i, fallback_unrolled_subtraction, high_bit_check, inlining)
			else:
				is_good = False
			if is_good is True:
				assert(i == 9) or (i == 15)
				factors.add(i)
				jumpentries.append(f"{prefix}divide_by_{i}")
			else:
				jumpentries.append(f"{prefix}use_sub_unchecked")

	if use_choice_tree:
		pass
	else:
		for lh in ( ("low", "<"), ("high", ">") ):
			low, lb = lh
			text.append(f"{label}{prefix}{low}table")
			for entry in jumpentries:
				text.append(f"{equb} {lb}({entry}-1)")

	# Custom dividers
	if max_custom >= 64:
		text.append(f"{label}{prefix}divide_by_64")
		text.append(f"{insn}lsr")
	if max_custom >= 32:
		text.append(f"{label}{prefix}divide_by_32")
		text.append(f"{insn}lsr")
		text.append(f"{insn}bpl {prefix}divide_by_16")

	if max_full >= 17:
		if max_custom >= 34:
			text.append(f"{label}{prefix}divide_by_34")
			text.append(f"{insn}lsr")
		if max_custom >= 17:
			text.append(f"{label}{prefix}divide_by_17")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc #0")

	if max_custom >= 16:
		text.append(f"{label}{prefix}divide_by_16")
		text.append(f"{insn}lsr")
	if max_custom >= 8:
		text.append(f"{label}{prefix}divide_by_8")
		text.append(f"{insn}lsr")
	if max_custom >= 4:
		text.append(f"{label}{prefix}divide_by_4")
		text.append(f"{insn}lsr")
	if max_custom >= 2:
		text.append(f"{label}{prefix}divide_by_2")
		text.append(f"{insn}lsr")
	text.append(f"{label}{prefix}divide_by_1")
	if internal_div_by_0 is True:
		text.append(f"{label}{prefix}divide_by_0")
	text.append(f"{insn}rts")

	if max_full >= 3:
		if max_custom >= 48:
			text.append(f"{label}{prefix}divide_by_48")
			text.append(f"{insn}lsr")
		if max_custom >= 24:
			text.append(f"{label}{prefix}divide_by_24")
			text.append(f"{insn}lsr")
		if max_custom >= 12:
			text.append(f"{label}{prefix}divide_by_12")
			text.append(f"{insn}lsr")
		if max_custom >= 6:
			text.append(f"{label}{prefix}divide_by_6")
			text.append(f"{insn}lsr")
		if max_custom >= 3:
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

	if max_full >= 5:
		if max_custom >= 40:
			text.append(f"{label}{prefix}divide_by_40")
			text.append(f"{insn}lsr")
		if max_custom >= 20:
			text.append(f"{label}{prefix}divide_by_20")
			text.append(f"{insn}lsr")
		if max_custom >= 10:
			text.append(f"{label}{prefix}divide_by_10")
			text.append(f"{insn}lsr")
		if max_custom >= 5:
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

	if max_full >= 7:
		if max_custom >= 56:
			text.append(f"{label}{prefix}divide_by_56")
			text.append(f"{insn}lsr")
		if max_custom >= 28:
			text.append(f"{label}{prefix}divide_by_28")
			text.append(f"{insn}lsr")
		if max_custom >= 14:
			text.append(f"{label}{prefix}divide_by_14")
			text.append(f"{insn}lsr")
		if max_custom >= 7:
			text.append(f"{label}{prefix}divide_by_7")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}adc {numerator}")
			
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_5_end")

	if max_full >= 9 or 9 in factors:
		if max_custom >= 36:
			text.append(f"{label}{prefix}divide_by_36")
			text.append(f"{insn}lsr")
		if max_custom >= 18:
			text.append(f"{label}{prefix}divide_by_18")
			text.append(f"{insn}lsr")
		if max_custom >= 9:
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
		else:
			text.append(f"{label}{prefix}divide_by_9")
			text.append(f"{insn}jsr divide_by_3")
			text.append(f"{insn}bpl divide_by_3")

	if max_full >= 11:
		if max_custom >= 44:
			text.append(f"{label}{prefix}divide_by_44")
			text.append(f"{insn}lsr")
		if max_custom >= 22:
			text.append(f"{label}{prefix}divide_by_22")
			text.append(f"{insn}lsr")
		if max_custom >= 11:
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
			if inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_9_end")

	if max_full >= 13:
		if max_custom >= 52:
			text.append(f"{label}{prefix}divide_by_52")
			text.append(f"{insn}lsr")
		if max_custom >= 26:
			text.append(f"{label}{prefix}divide_by_26")
			text.append(f"{insn}lsr")
		if max_custom >= 13:
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
			if inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_9_end")

	if max_full >= 15 or 15 in factors:
		if max_custom >= 60:
			text.append(f"{label}{prefix}divide_by_60")
			text.append(f"{insn}lsr")
		if max_custom >= 30:		
			text.append(f"{label}{prefix}divide_by_30")
			text.append(f"{insn}lsr")
		if max_custom >= 15:
			text.append(f"{label}{prefix}divide_by_15")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #4")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}jmp {prefix}divide_by_9_end")
		else:
			text.append(f"{label}{prefix}divide_by_15")
			text.append(f"{insn}jsr divide_by_3")
			text.append(f"{insn}bpl divide_by_5")

	if max_full >= 19:
		if max_custom >= 76:
			text.append(f"{label}{prefix}divide_by_76")
			text.append(f"{insn}lsr")
		if max_custom >= 38:
			text.append(f"{label}{prefix}divide_by_38")
			text.append(f"{insn}lsr")
		if max_custom >= 19:
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end")

	if max_full >= 21:
		if max_custom >= 42:
			text.append(f"{label}{prefix}divide_by_42")
			text.append(f"{insn}lsr")
		if max_custom >= 21:
			text.append(f"{label}{prefix}divide_by_21")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{label}{prefix}divide_by_21_end_lsr")
			text.append(f"{insn}lsr")
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

	if max_full >= 23:
		if max_custom >= 46:
			text.append(f"{label}{prefix}divide_by_46")
			text.append(f"{insn}lsr")
		if max_custom >= 23:
			text.append(f"{label}{prefix}divide_by_23")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			if inlining is True:
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_adc")

	if max_full >= 25:
		if max_custom >= 50:
			text.append(f"{label}{prefix}divide_by_50")
			text.append(f"{insn}lsr")
		if max_custom >= 25:
			text.append(f"{label}{prefix}divide_by_25")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_lsr")

	if max_full >= 27:
		if max_custom >= 54:
			text.append(f"{label}{prefix}divide_by_54")
			text.append(f"{insn}lsr")
		if max_custom >= 27:
			text.append(f"{label}{prefix}divide_by_27")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_lsr")

	if max_full >= 29:
		if max_custom >= 58:
			text.append(f"{label}{prefix}divide_by_58")
			text.append(f"{insn}lsr")
		if max_custom >= 29:
			text.append(f"{label}{prefix}divide_by_29")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {numerator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_lsr")

	if max_full >= 31:
		if max_custom >= 62:
			text.append(f"{label}{prefix}divide_by_62")
			text.append(f"{insn}lsr")
		if max_custom >= 31:
			text.append(f"{label}{prefix}divide_by_31")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {numerator}")
				text.append(f"{insn}ror")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}lsr")
				text.append(f"{insn}rts")
			else:
				text.append(f"{insn}bpl {prefix}divide_by_21_end_lsr")

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
		(f"{equb}", 1),
		(f"{insn}ld", 2),
		(f"{insn}st", 2),
		(f"{insn}cp", 2),
		(f"{insn}cmp", 2),
		(f"{comment}", 0),
		(f"{label}", 1),
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
			print(f"Not recognized, {line}", file=sys.stderr)

	if with_stats is True:
		mean,mean64,mean16,median,worst=stats_cycles(max_custom, max_full, fallback_unrolled_subtraction, high_bit_check, early_high_bit, inlining, use_factoring, use_choice_tree, max_shifting_divider)
	else:
		mean,mean64,mean16,median,worst=(0,0,0,0,0)
	return (available, "\n".join(text), mean,mean64,mean16,median,worst, size)

def save(text, filename, num, denom):
	testname = filename
	preamble = f"\ndef proc divide_{filename}\n[\n"
	epilog = "\n]\n"
	filename = f"dividers.asm"
	with open(filename,"a") as file:
		file.write(preamble)
		file.write(text)
		file.write(epilog)
	test = f'\n[[test]]\nname="Hash Divide {testname}"'
	test = test + """
timeout=20000000
reps=65536
null="Hash Divide Null"
source=\"\"\"
dim i 1
dim j 1
dim k 1
object_top_cell_y = 1
i = 0
label outer_loop
j = 0
label inner_loop
"""
	test = test + f"{num} = i\n"
	test = test + f"{denom} = j\n"
	test = test + "k = proc divide_"
	test = test + testname
	test = test + """ ()
proc measure_byte k
j = j + 1
if j <> 0 then goto inner_loop
i = i + 1
if i <> 0 then goto outer_loop
object_top_cell_y = 2
\"\"\"
pass=\"\"\"
hash 1a3fb879c6c939fa1cbc4e40b6acfd0053611efa3f1fd0bca497a329520bb58d80da36694e0102bd90a6ec48d3f292ec1c27509484a95f91da59785af954efa7
object_top_cell_y 2
\"\"\"
"""
	with open("./tmp/tests-div.toml","a") as file:
		file.write(test)

def add_line(i, j, fwith, iwith, cwith, max_shifting_divider, sub, hibit, size, mean, mean64, mean16, median, worst, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, with_stats, string, fname, numerator, denominator):
	if with_stats is True:
		line = f"|{i}\t|{j}\t|{fwith}\t|{iwith}\t|{sub}\t|{hibit}\t|{cwith}\t|{max_shifting_divider}\t|{size}\t|{float(mean):.5}\t|{float(mean64):.5}\t|{float(mean16):.5}\t|{median}\t|{float(worst):.5}\t|"
		mean_list.append((mean, mean64, mean16, worst, median, size, line))
		mean_64_list.append((mean64, mean16, mean, worst, median, size, line))
		mean_16_list.append((mean16, mean64, mean, worst, median, size, line))
		median_list.append((median, worst, mean, mean64, mean16, size, line))
		worst_list.append((worst, mean, mean64, mean, median, size, line))
	else:
		line = f"|{i}\t|{j}\t|{fwith}\t|{iwith}\t|{sub}\t|{hibit}\t|{cwith}\t|{max_shifting_divider}\t|{size}\t|"
	full_list.append(line)
	save(string, fname, numerator, denominator)

def add_title(name, slist, args):
	if args.stats:
		dbar= "+===============================================================================================================+"
		title1="|Max\t|Max\t|With\t|With\t|Unroll\t|Hi Bit\t|Choice\t|Max\t|Size\t|Mean\t|Me<=64\t|Me<=16\t|Median\t|Worst\t|"
		title2="|Custom\t|Full\t|Factor\t|Inline\t|Subtrc\t|Check\t|Tree\t|Shift\t|bytes\t|cycles\t|cycles\t|cycles\t|cycles\t|cycles\t|"
	else:
		dbar= "+=======================================================================+"
		title1="|Max\t|Max\t|With\t|With\t|Unroll\t|Hi Bit\t|Choice\t|Max\t|Size\t|"
		title2="|Custom\t|Full\t|Factor\t|Inline\t|Subtrc\t|Check\t|Tree\t|Shift\t|bytes\t|"
		
	slist.append(dbar)
	slist.append(f"|{name.center(len(dbar)-2)}|")
	slist.append(dbar)
	slist.append(title1)
	slist.append(title2)

# Sort the list of lines, and output the first of each length
def best_time(lines):
	out = []
	lines.sort()
	besti = 1000000
	for maxsize in range(0, 1000):
		for sizelinei in range(0,len(lines)):
			sizeline = lines[sizelinei]
			_, _, _, _, _, size, line = sizeline
			if size == maxsize:
				if sizelinei < besti:
					out.append(line)
					besti = sizelinei
				break;
	return out

# Blended score
# This is the average index into all 5 lists (which should already be sorted)
def blended_best_time(lists):
	index = {}
	for item in lists[0]:
		index[item[6]] = []
	for listi in lists:
		for itemi in range(len(listi)):
			item = listi[itemi]
			index[item[6]].append((item[5], itemi))
	indexl = []
	for k, v in index.items():
		vsum = 0
		for ve in v:
			size, value = ve
			vsum += value
		indexl.append((vsum, 0, 0, 0, 0, size, k))
	return best_time(indexl)
	

def do_make_divide(args):
	num = "muldiv_temp_t"
	denom = "muldiv_temp_u"
	equb = "!byte"
	comment = "; "
	label = ""
	i, j, prefix, factoring, inlining, style, choice_tree, max_shifting_divider, stats, assemble = args
	avail1, string1, cycles1, m64_1, m16_1, median1, worst1, size1 = make_divide(i, j, num, denom, prefix+"_un_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, use_factoring=factoring, inlining=inlining, with_stats=stats)
	avail2, string2, cycles2, m64_2, m16_2, median2, worst2, size2 = make_divide(i, j, num, denom, prefix+"_rn_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, fallback_unrolled_subtraction=False, use_factoring=factoring, inlining=inlining, with_stats=stats)
	avail3, string3, cycles3, m64_3, m16_3, median3, worst3, size3 = make_divide(i, j, num, denom, prefix+"_ul_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, high_bit_check=True, use_factoring=factoring, inlining=inlining, with_stats=stats)
	avail4, string4, cycles4, m64_4, m16_4, median4, worst4, size4 = make_divide(i, j, num, denom, prefix+"_rl_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, fallback_unrolled_subtraction=False, high_bit_check=True, use_factoring=factoring, inlining=inlining, with_stats=stats)
	avail5, string5, cycles5, m64_5, m16_5, median5, worst5, size5 = make_divide(i, j, num, denom, prefix+"_ue_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, high_bit_check=True, early_high_bit=True, use_factoring=factoring, inlining=inlining, with_stats=stats)
	avail6, string6, cycles6, m64_6, m16_6, median6, worst6, size6 = make_divide(i, j, num, denom, prefix+"_re_", "\t", label, equb, comment, max_shifting_divider=max_shifting_divider, use_choice_tree=choice_tree, fallback_unrolled_subtraction=False, high_bit_check=True, early_high_bit=True, use_factoring=factoring, inlining=inlining, with_stats=stats)
	result = None
	binary = None
	if assemble is True:
		prolog=f"{num}=0\n{denom}=1\n* = $200\n"
		with tempfile.NamedTemporaryFile('w') as infile:
			src = "\n\n".join([prolog, string1, string2, string3, string4, string5, string6])
			infile.write(src)
			infilename = infile.name
			infile.flush()
			with tempfile.NamedTemporaryFile('rb') as outfile:
				with tempfile.NamedTemporaryFile('r') as reportfile:
					result = subprocess.run(["acme", "-v2", "-o", outfile.name, "-r", reportfile.name, infilename], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True).stdout
					binary = f"Binary output {os.path.getsize(outfile.name)} bytes\n" + "Source:\n" + src + "\n\nReport:\n" + reportfile.read()
	
	return (i, j, prefix, factoring, inlining, style, choice_tree, max_shifting_divider, result, binary, \
																	avail1, string1, cycles1, m64_1, m16_1, median1, worst1, size1, \
																	avail2, string2, cycles2, m64_2, m16_2, median2, worst2, size2, \
																	avail3, string3, cycles3, m64_3, m16_3, median3, worst3, size3, \
																	avail4, string4, cycles4, m64_4, m16_4, median4, worst4, size4, \
																	avail5, string5, cycles5, m64_5, m16_5, median5, worst5, size5, \
																	avail6, string6, cycles6, m64_6, m16_6, median6, worst6, size6)

def single(args):
	avail, string, m256, m64, m16, median, worst, size = make_divide(args.max_custom, args.max_full, args.numerator, args.denominator, args.prefix, args.instruction, args.label, args.equb, args.comment,max_shifting_divider= args.max_shifting, use_choice_tree=args.choice_tree, use_factoring=args.factoring, inlining=args.inlining, with_stats=args.stats)
	# Report stats
	print(f"Divider generated. Size {size} bytes.")
	if args.stats is True:
		print(f"Cycles: {m256:.5} mean, {m64:.5} for denominators <=64, {m16:.5} for <=16, {median} median, {float(worst):.5} worst case.")
	with open(args.output,"w") as file:
		file.write(string)

def main():
	parser = argparse.ArgumentParser(
			prog='makedivide',
			description='A parameterizable division routine builder for 6502')

	# Formatting
	parser.add_argument('-n', '--numerator', default="muldiv_temp_t", help="label of the zero page location containing the numerator")
	parser.add_argument('-d', '--denominator', default="muldiv_temp_u", help="label of the zero page location containing the denominator")
	parser.add_argument('-e', '--equb', default="!byte", help="prefix to assemble a literal byte")
	parser.add_argument('-i', '--instruction', default='\t', help='prefix to instructions (e.g. \\t)')
	parser.add_argument('-l', '--label', default='.', help='prefix to labels (e.g. ".")')
	parser.add_argument('-C', '--comment', default='.', help='prefix to comments (e.g. "#")')
	parser.add_argument('-p', '--prefix', default='.', help='prefix to labels and calls (e.g. "divi_")')

	# Parameters for prducing a single instance
	parser.add_argument('-o', '--output', default=sys.stdout, help="file to output to")
	parser.add_argument('-c', '--max-custom', default=18, help="maximum denominator to use a custom routine")
	parser.add_argument('-f', '--max-full', default=18, help="maximum denominator to use a custom routine that is not just a prefix to another")
	parser.add_argument('-I', '--inlining', action='store_true', help="use inlining (less space, but slower)")
	parser.add_argument('-F', '--factoring', action='store_true', help="use factoring (faster for a few cases, but bigger)")
	parser.add_argument('-T', '--choice-tree', action='store_true', help="use a choice tree if possible (faster and usually smaller, for low --max-custom)")
	parser.add_argument('-S', '--max-shifting', default=0, help="maximum denominator to use the shifting divider as a fallback when over max-custom. 0 = never use it, 256=always.")

	# Test modes
	parser.add_argument('-t', '--test', action="store_true", help="produce all possibilities, save stats and a TOML description")
	parser.add_argument('-s', '--stats', action="store_true", help="generate statistics (this makes the test much slower)")
	parser.add_argument('-a', '--assemble', action="store_true", help="when testing, run ACME assembler to test correctness of each output")

	args = parser.parse_args()

	setattr(args, "max_custom", int(args.max_custom))
	setattr(args, "max_full", int(args.max_full))
	setattr(args, "max_shifting", int(args.max_shifting))

	if args.test is True:
		test(args)
	else:
		single(args)

def test(args):
	if args.stats:
		bar = "+-------+-------+-------+-------+-------+-------+-------+-------+-------+-------+-------+-------+-------+-------+"
	else:
		bar = "+-------+-------+-------+-------+-------+-------+-------+-------+-------+"
	mean_list = []
	mean_64_list = []
	mean_16_list = []
	median_list = []
	worst_list = []
	full_list = []
	futures = []

	# Set up futures for all possibilities
	with concurrent.futures.ProcessPoolExecutor() as executor:
		for i in CUSTOMS:
			for j in CUSTOMS:
				for factoring in (True, False):
					for inlining in (True, False):
						for choice_tree in (True, False):
							for max_shifting_divider in (0, i+4, i+8, i+12, i+16, i+24, i+32, i+48, i+64, 256):
								style = f"{i}_{j}"
								if i >= 2 and j >= 2 and j <= i and (factoring is False or i < 15) and (inlining is False or i >= 7) and (choice_tree is False or i <= 7):
									prefix = f"djbt_{style}"
									pargs = (i, j, prefix, factoring, inlining, style, choice_tree, max_shifting_divider, args.stats, args.assemble)
									futures.append(executor.submit(do_make_divide, pargs))

	# Run them all
	asmout = []
	for future in futures:
		returned = future.result()
		i, j, prefix, factoring, inlining, style, choice_tree, max_shifting_divider, result, binary, \
																	avail1, string1, cycles1, m64_1, m16_1, median1, worst1, size1, \
																	avail2, string2, cycles2, m64_2, m16_2, median2, worst2, size2, \
																	avail3, string3, cycles3, m64_3, m16_3, median3, worst3, size3, \
																	avail4, string4, cycles4, m64_4, m16_4, median4, worst4, size4, \
																	avail5, string5, cycles5, m64_5, m16_5, median5, worst5, size5, \
																	avail6, string6, cycles6, m64_6, m16_6, median6, worst6, size6 = returned

		cwith = "No"
		if choice_tree is True:
			cwith = "Yes" 
			style = style + "_c"
		fwith = "No"
		if factoring is True:
			fwith = "Yes" 
			style = style + "_f"
		iwith = "No"
		if inlining is True:
			iwith = "Yes" 
			style = style + "_i"
		style = style + f"_s{max_shifting_divider}"

		if avail1:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider,"Yes", "No", size1, cycles1, m64_1, m16_1, median1, worst1, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string1, f"{style}UN", args.numerator, args.denominator)
		if avail2:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider,"No", "No", size2, cycles2, m64_2, m16_2, median2, worst2, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string2, f"{style}RN", args.numerator, args.denominator)
		if avail3:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider,"Yes", "Late", size3, cycles3, m64_3, m16_3, median3, worst3, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string3, f"{style}UH", args.numerator, args.denominator)
		if avail4:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider,"No", "Late", size4, cycles4, m64_4, m16_4, median4, worst4, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string4, f"{style}RH", args.numerator, args.denominator)
		if avail5:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider, "Yes", "Early", size5, cycles5, m64_5, m16_5, median5, worst5, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string5, f"{style}UE", args.numerator, args.denominator)
		if avail6:
			add_line(i, j, fwith, iwith, cwith, max_shifting_divider, "No", "Early", size6, cycles6, m64_6, m16_6, median6, worst6, mean_list, mean_64_list, mean_16_list, median_list, worst_list, full_list, args.stats, string6, f"{style}RE", args.numerator, args.denominator)
		full_list.append(bar)

		if result is not None:
			asmout.append(str(result))
			if binary is None:
				asmout.append("(no binary output)")
			else:
				asmout.append(str(binary))
				asmout.append(str(binary))
			asmout.append("")

	if len(asmout) > 0:
		with open("asmout.txt", "w") as file:
			file.write("\n".join(asmout))

	# Add stats
	out = []
	if args.stats is True:
		best_worst  	= best_time(worst_list)
		best_median 	= best_time(median_list)
		best_mean   	= best_time(mean_list)
		best_mean_64   	= best_time(mean_64_list)
		best_mean_16   	= best_time(mean_16_list)
		best_blended   	= blended_best_time([mean_16_list, mean_64_list, mean_list, median_list, worst_list])
		add_title("Best by a mixed score (mean <256,64,16 + median + worst), smallest to fastest", out, args)
		out.extend(best_blended)
		add_title("Best by mean cycles, from smallest to fastest", out, args)
		out.extend(best_mean)
		add_title("Best by mean cycles for denominators <= 64, from smallest to fastest", out, args)
		out.extend(best_mean_64)
		add_title("Best by mean cycles for denominators <= 16, from smallest to fastest", out, args)
		out.extend(best_mean_16)
		add_title("Best by median cycles, from smallest to fastest", out, args)
		out.extend(best_median)
		add_title("Best by worst case cycles, from smallest to fastest", out, args)
		out.extend(best_worst)
	add_title("All cases, sorted by table length", out, args)
	out.extend(full_list)
	print("\n".join(out))

if __name__ == '__main__':
	main()
