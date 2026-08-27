#!/usr/bin/python

##################################################################################
#
# A parameterizable division routine builder for 6502.
#
# "max_custom" is the highest value for which a custom routine (as opposed to repeated subtraction) is used.
#
# "max_full" (which must be no more than max_custom) is the highest value for which a custom routine that is not just a divide-by-2 or 4 in front of another is used.
#
# "inlining" is true, will make every divide-by-constant separate, rather than sharing parts (branching between them). This uses more space but is a little faster (saving 3 cycles for a branch in the affected denominators)
#
# Factoring (e.g. replacing "x/9" with "(x/3)/3") is used when it saves time, when asked for (it adds some size) which is for 9 (22-62 cycles saved) or 15 (4-17 cycles saved) only (and their multiples of powers of two), when the custom
# routine for those denominators is not used.

# TODO - high-bit check before table check (optionally)?
# TODO - option to use dedicated routines for 64, 12 etc.
# TODO - leading sta denom everywhere can be removed?
#		- it's not everywehere (powers of two don't use it for example)
#		- A contains the numerator on entry
#		- If the temp was replaced with numerator, as none require more than 1 temp YES this could be removed

import math

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
	3: 12+16+2,
	5: 12+16+2,
	7: 6+12+3+3+6,
	9: 12+18,
	11: 12+12+3+3+8,
	13: 12+14+3+3+8,
	15: 3+8+2+3+3+8,
	17: 12+8+2+8,
	19: 12+8+3+8,
	21: 6+12,
	23: 6+8+3+3+10,
	25: 6+8+3+3+12,
	27: 6+8+3+3+12,
	29: 9+12+3+3+12,
	31: 3+8+3+3+12
}

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

	if unrolled:
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
def cycles_by_custom(numerator, denominator, high_bit, inlining):
	cycles = cycles_by_high_bit(numerator, denominator, high_bit)
	inline_mod = 0
	if inlining is True and denominator in TAIL:
		inline_mod = -3
	if denominator in CYCLES:
		return CYCLES[denominator]+inline_mod
	elif denominator*2 in CYCLES:
		return CYCLES[denominator]+2+inline_mod
	elif denominator*4 in CYCLES:
		return CYCLES[denominator]+4+inline_mod
	elif denominator*8 in CYCLES:
		return CYCLES[denominator]+6+inline_mod
	elif denominator*16 in CYCLES:
		return CYCLES[denominator]+8+inline_mod
	elif denominator*32 in CYCLES:
		return CYCLES[denominator]+10+inline_mod
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
		#print(f"No factors: {factor1}")
		return (False, factor1, factor2)
	sub_cycles = mean_cycles_by_subtraction(denominator, unrolled, high_bit)
	#if fac_cycles < sub_cycles:
	#	print(f"Cheapest factors: {factor1}, {factor2}, combined cost {fac_cycles}, sub cost {sub_cycles}")
	return (fac_cycles < sub_cycles, factor1, factor2)

# The main entry point: see top of file for docuemntation
def make_divide(max_custom, max_full, numerator, denominator, prefix, insn, label, equb, comment, *, fallback_unrolled_subtraction = True, high_bit_check = False, divide_by_0=None, use_factoring=False, inlining=False):
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
	text.append(f"{comment}Long division (long, but fast), 8 / 8 bits.")
	text.append(f"{comment}0..{max_custom} use a RTS jump into a table of divide-by-constant routines, which ")
	text.append(f"{comment}overlap where possible. In a few cases this isn't the fastest possible (e.g. shifting before")
	text.append(f"{comment}using a divide-by-(N/2) or (N/4), or branching to use a shared epilogue - but it")
	text.append(f"{comment}should be pretty close on average.")
	text.append(f"{comment}The rest use repeated subtraction, unrolled to the maximum iteration count of {max_iters}")

	# Check jump vs. subtract
	text.append(f"{insn}ldx {denominator}")
	text.append(f"{insn}cpx #{max_custom+1}")
	text.append(f"{insn}bcs {prefix}use_sub")

	# Jump table dispatch
	# Jumps to use_sub will always bypass high bit check
	text.append(f"{comment}RTS-trick jump table")
	text.append(f"{insn}lda {prefix}hightable, x")
	text.append(f"{insn}pha")
	text.append(f"{insn}lda {prefix}lowtable, x")
	text.append(f"{insn}pha")
	text.append(f"{insn}lda {numerator}")
	text.append(f"{insn}rts")

	# Limited by branch range to ~60
	if fallback_unrolled_subtraction is True and max_iters > 60:
		print("WARNING: unrolled subtraction not available - branch range limited")
		fallback_unrolled_subtraction = False

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
			text.append(f"{label}{prefix}return_0")
			text.append(f"{insn}lda #1")
			text.append(f"{insn}rts")

	# Repeated subtraction, unrolled
	if fallback_unrolled_subtraction is True:
		midpoint = max(low_iters_max, (max_iters - 4) // 2) # offset because for very large tables the limit is the bcs use_sub
		for i in range(0, midpoint):
			text.append(f"{label}{prefix}return_{i}")
			text.append(f"{insn}lda #{i}")
			text.append(f"{insn}rts")
		text.append(f"{label}{prefix}use_sub")
		if high_bit_check is True:
			text.append(f"{insn}bmi {prefix}high_bit_denom")
		text.append(f"{label}{prefix}use_sub_unchecked")
		text.append(f"{insn}lda {numerator}")
		text.append(f"{insn}sec") # TODO needed every time?
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
		text.append(f"{label}{prefix}use_sub")
		if high_bit_check is True:
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

	# Jump table
	factors = set()
	for lh in ( ("low", "<"), ("high", ">") ):
		low, lb = lh
		text.append(f"{label}{prefix}{low}table")
		text.append(f"{equb} {lb}({divide_by_0}-1)")
		for i in range(1, max_custom+1):
			if i in CUSTOMS and (i in PRIMES or i <= max_full):
				text.append(f"{equb} {lb}({prefix}divide_by_{i}-1)")
			else:
				if use_factoring is True:
					is_good, factor1, factor2 = factoring_is_good(max_full, i, fallback_unrolled_subtraction, high_bit_check, inlining)
				else:
					is_good = False
				if is_good is True:
					#print(f"Denom {i}: {is_good}, {i} = {factor1} x {factor2}")
					assert(i == 9) or (i == 15)
					factors.add(i)
					text.append(f"{equb} {lb}({prefix}divide_by_{i}-1)")
				else:
					text.append(f"{equb} {lb}({prefix}use_sub_unchecked-1)")

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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #21")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #13")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_5_end")
			text.append(f"{insn}adc {denominator}")
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
		text.append(f"{insn}sta {denominator}")
		text.append(f"{insn}lsr")
		text.append(f"{insn}lsr")
		text.append(f"{insn}lsr")
		text.append(f"{insn}adc {denominator}")
		text.append(f"{insn}ror")
		text.append(f"{insn}lsr")
		text.append(f"{insn}lsr")
		if inlining is True:
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{label}{prefix}divide_by_9_end")
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}clc")
			if inlining is True:
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc #4")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{label}{prefix}divide_by_21_end_lsr")
			text.append(f"{insn}lsr")
			text.append(f"{label}{prefix}divide_by_21_end_adc")
			text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			if inlining is True:
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}adc {denominator}")
			text.append(f"{insn}ror")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {denominator}")
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
			text.append(f"{insn}sta {denominator}")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			text.append(f"{insn}lsr")
			if inlining is True:
				text.append(f"{insn}lsr")
				text.append(f"{insn}adc {denominator}")
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
		(f"{insn}clc", 1),
		(f"{insn}sec", 1),
		(f"{insn}txa", 1),
		(f"{insn}tax", 1),
		(f"{insn}in", 1),
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
			print(f"Not recognized, {line}")

	return ("\n".join(text), size)

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

def main():
	num = "muldiv_temp_t"
	denom = "muldiv_temp_u"
	equb = "!byte"
	for i in CUSTOMS:
		for j in CUSTOMS:
			for factoring in (True, False):
				for inlining in (True, False):
					style = f"{i}_{j}"
					fwith = "without"
					if factoring is True:
						fwith = "with" 
						style = style + "_f"
					iwith = "without"
					if inlining is True:
						iwith = "with" 
						style = style + "_i"
					if i >= 2 and j >= 2 and j <= i and (factoring is False or i < 15) and (inlining is False or i >= 7):
						prefix = f"djbt_{style}"
						string1, size = make_divide(i, j, num, denom, prefix+"_un_", "\t", ".", equb, "# ", use_factoring=factoring, inlining=inlining)
						string2, size2 = make_divide(i, j, num, denom, prefix+"_rn_", "\t", ".", equb, "# ", fallback_unrolled_subtraction=False, use_factoring=factoring, inlining=inlining)
						string3, size3 = make_divide(i, j, num, denom, prefix+"_uh_", "\t", ".", equb, "# ", high_bit_check=True, use_factoring=factoring, inlining=inlining)
						string4, size4 = make_divide(i, j, num, denom, prefix+"_rh_", "\t", ".", equb, "# ", fallback_unrolled_subtraction=False, high_bit_check=True, use_factoring=factoring, inlining=inlining)
						print(f"Size of generated code for max {i}, fill {j}, {fwith} factoring, {iwith} inlining: {size} bytes unrolled without high-bit check, {size2} bytes looping, unrolled with check {size3} bytes, rolled {size4}")
						save(string1, f"{style}UN", num, denom)
						save(string2, f"{style}RN", num, denom)
						save(string3, f"{style}UH", num, denom)
						save(string4, f"{style}RH", num, denom)

main()
