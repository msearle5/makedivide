#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#define WITH_SBC
//#define WITH_CLC
//#define WITH_SEC

#define I_ROR 0
#define I_ASR 1
#define I_ADC 2
#define I_SBC 3
#define I_CLC 4
#define I_SEC 5

struct context_t {
	uint8_t insn[64];
	uint8_t length;
	uint8_t suffix[32];
	uint32_t nsuffix;
	uint8_t init_suffix[32];
	uint32_t init_nsuffix;
	uint8_t best_insn[128][64];
	uint32_t best_score[128];
	uint8_t best_length[128];
	uint8_t table[256][256];
} context_t;

static void evaluate(struct context_t *context) {
	/* Determine whether the instruction sequence is useful.
	 * If so, compare it to the best so far and if it beats it then record it.
	 * A "useful" sequence is one which agrees with one of the tables
	 */
	static bool match[128];
	memset(match, 1, sizeof(match));
	int matches = 0;
	uint32_t length = context->length;
	for (uint32_t i=0;i<256;i++) {
		// Compute the result of I/J
		uint32_t reg_a = i;
		uint8_t reg_c = 0;	// C is zero on entry, known as "bcs use_sub"
		for(int k=0;k<=length;k++) {
			uint8_t insn = context->insn[k];
			if (insn == I_ROR) {
				uint8_t new_reg_c = reg_a & 1;
				reg_a = ((reg_a >> 1) | (reg_c << 7)) & 0xff;
				reg_c = new_reg_c;
			} else if (insn == I_ASR) {
				reg_c = reg_a & 1;
				reg_a >>= 1;
			} else if (insn == I_ADC) {
				reg_a += i;
				reg_a += reg_c;
				reg_c = 0;
				if (reg_a > 0xff) {
					reg_c = 1;
					reg_a &= 0xff;
				}
			} 
#ifdef WITH_SBC
			else if (insn == I_SBC) {
				reg_a -= i;
				reg_a -= !reg_c;
				reg_c = 1;
				if (reg_a >= 0x100) {
					reg_c = 0;
					reg_a &= 0xff;
				}
			}
#endif
#ifdef WITH_CLC
			else if (insn == I_CLC) {
				reg_c = 0;
			}
#endif
#ifdef WITH_SEC
			else if (insn == I_SEC) {
				reg_c = 1;
			}
#endif
		}
		matches = 0;
		for(int k=0;k<128;k++) {
			if (reg_a != context->table[i][k])
				match[k] = 0;
			if (match[k] == 1)
				matches++;
		}
		if (matches == 0) {
			// not useful
			return;
		}
	}

	if (matches == 1) {
		int denom = 0;
		for(int k=0;k<128;k++) {
			if (match[k] == 1) {
				denom = k;
				break;
			}
		}
		// This matches denom - is it an improvement?
		// 
		uint32_t score = (length+1) * 256;
		for(int k=0;k<length+1;k++) {
			if (context->insn[k] == I_ADC) {
				score+=126;
			} else if (context->insn[k] == I_ASR) {
				score-=3;
			}
			#ifdef WITH_SBC
			else if (context->insn[k] == I_SBC) {
				score+=127;
			}
			#endif
			#ifdef WITH_CLC
			else if (context->insn[k] == I_CLC) {
				score-=1;
			}
			#endif
			#ifdef WITH_SEC
			else if (context->insn[k] == I_SEC) {
				score-=2;
			}
			#endif
		}
		if ((context->best_score[denom] == 0) || (context->best_score[denom] > score)) {
			context->best_score[denom] = score;
			context->best_length[denom] = length;
			memcpy(context->best_insn[denom], context->insn, length+1);
		}
	}
}

static void find_insns(struct context_t *context, int length) {
	if (context->nsuffix > 0) {
		context->nsuffix--;
		context->insn[length] = context->suffix[context->nsuffix];
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
	} else {
		context->insn[length] = I_ROR;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
		context->insn[length] = I_ASR;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
		context->insn[length] = I_ADC;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
	#ifdef WITH_SBC
		context->insn[length] = I_SBC;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
	#endif
	#ifdef WITH_CLC
		context->insn[length] = I_CLC;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
	#endif
	#ifdef WITH_SEC
		context->insn[length] = I_SEC;
		if (length == 0)
			evaluate(context);
		else
			find_insns(context, length-1);
	#endif
	}
}

static const char *insn_name[] = { "ror", "lsr", "adc {numerator}", "sbc {numerator}", "clc", "sec"  };

int main(int argc, char **argv) {
	/*
	 * Possible instructions are
	 * ROR
	 * ASR
	 * LDA denom
	 * (OPTIONALLY) sbc, etc.
	 * 
	 * RTS is implicit
	 * (after a fixed number of instructions)
	 * 
	 * To allow external parallel should be able to spec at least 3 trailing insns
	 */
	struct context_t *context = calloc(1, sizeof(struct context_t));
	for(int i=0;i<256;i++) {
		for(int j=0;j<256; j++) {
			if (j == 0)
				context->table[i][j] = i;
			else
				context->table[i][j] = i / j;
		}
	}
	for(int i=1;i<argc;i++) {
		int val = atoi(argv[i]);
		context->suffix[context->nsuffix++] = val;
		context->init_suffix[context->init_nsuffix++] = val;
	}
	for(int length=0;length<64;length++) {
		printf("Length %d:\n", length+1);
		memcpy(context->suffix, context->init_suffix, sizeof(uint8_t)*32);
		context->nsuffix = context->init_nsuffix;
		context->length = length;
		find_insns(context, length);
		int found=0;
		for(int k=2;k<32;k++) {
			if (context->best_score[k] > 0) {
				found++;
				printf("Best for denominator %d found:\n", k);
				for(int l=0;l<=context->best_length[k];l++) {
					printf("%s; ", insn_name[context->best_insn[k][l]]);
				}
				printf("\n");
			}
		}
		if (found == 30) {
			exit(0);
		}
		fflush(stdout);
	}
	exit(0);
}
