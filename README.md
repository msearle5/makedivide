
# makedivide

A Python app which makes 6502 assembler code to compute 8x8 bit division. There are millions of possible ways to do it, with trade-offs of size against speed. Speed can be be measured in various different ways - the mean of different groups of denominators, median and worst-case. It includes code to test them all by emulation (using [py65emu](https://github.com/docmarionum1/py65emu)), and rank the best.

## How it works

Any denominator can have a custom routine to divide by that number - these are reasonably fast, but the more that are used the bigger the code is. To reduce the size of the custom denominators, powers of two are used (for example, the divide-by-34 routine is a divide by 2 which then falls into the divide-by-17), and optionally inlining (the ends of these routines are often identical and can be shared, but this adds a little time). In a few cases, factoring can be used (divide by 3 and then by 3 or 5).

When a custom routine isn't present, a fallback method must be used. The main ways are repeated subtraction (which works best when the denominator is large and so the subtraction doesn't have to be repeated many times), and shifting (like long division: slow, but compact and the speed doesn't vary between denominators). It can make sense to use both, switching between them based on the denominator. Repeated subtraction can be performed in a loop (small but slower) or unrolled for more speed at the cost of size. It's also possible to have a special case for denominators over 128 - these can only have a result of 0 or 1, making it reduce to a simple comparison.

## Resource requirements

All variations of the divider (even when the inputs or output are in registers) require 2 bytes of zero page. The code can be between 21 and 700+ bytes, though the largest ones (over 400 bytes) are rarely worth using. Pick what fits.

## I just want the 6502 code!

Check out **dividers.asm**! This contains dividers of all sizes - those picked as best for their size according to the score of ((mean x 2) + ((mean for denominators <= 64) x 3) + ((mean for denominators <= 16) x 4) + (median x 0.5) + (worst case x 1)) in which all these figures are actually ranks (positions in a list of results sorted by that statistic), not the raw figure itself.
To use one, find zero-page addresses for denominator and numerator and call the entry point (*note that this is not necessarily at the top!*) with numerator in that memory location, denominator in X and take the result in A.
Note that many of these will require page alignment (starting at $xx00), and many will also need to run from RAM, not ROM (as they use self-modifying code). Both limitations are mentioned in the leading comment to each routine.

## I just want the 6502 code, but with a different stat mix.

A list of all results produced by the full test (~5MB compressed, 330MB when uncompressed) is at **full-list.txt.xz**. Makedivide can parse this and emit stats again, using a different mix function, e.g.:

	**makedivide.py -t -O full-list.txt -s -E -m 1 2 3 4 5 -o new-list.txt**

(where you can substitute your weights (mean, mean to 64, mean to 16, median and worst-case) for "1 2 3 4 5")
This will produce new-list.txt in the same format as the original full-list.txt.
At the top of this file will be a list of entries, like this:

	|         Parameters  |Size|  Simulated Statistics  | Emulated Statistics    | Command Line
	|5|0|0|N|N|N|N|N|0|Y|Y| 70 |45.8|71.2|109.9|34|370.0|47.7|73.4|112.6|36|372.0|-c5 -f0 -H -M

Pick one that looks good, take the command line from the rightmost field and feed it back to makedivide:

	**makedivide.py -o out.asm -c5 -f0 -H -M**

The list of top (according to **--mix 2 3 4 0.5 1** weights) scoring parameters is in **top-list.txt**, and there is also a script **mkd.py** used to output **dividers.asm**.

## Making a single divider routine

A simple example:

	**makedivide.py -o out.asm**

produces a divider from default parameters, and writes it to the file **out.asm**.

An example of changing the parameters:

	**makedivide.py -c 4 -I -o out.asm**

produces a divider with less (4) custom routines but with inlining switched on - resulting in a 57 byte routine rather than the default 193.

## Running multiple variations

It's possible to run multiple sets of parameters. As well as testing that the code produced is always correct (passing all 256x256 possible inputs into the emulator and checking that the result is as expected), this allows statistics to be obtained which can be used to rank the parameters and obtain the fastest for each size. As the brute-force approach of trying every possible combination takes some hours, there are various methods to cut down the amount of work done.

The default if no additional parameters are given (just **--test**) is to run all possible combinations. This can be reduced to a fixed subset (~100x less) by **--quick**, and to a smaller subset (~40x less again) by **--quickest**. Alternatively a random subset of parameters can be tried (**--random 1000** will generate 1000 random sets of parameters - and print a seed which can be used with **--random-seed \<seed\>** to repeat the same set again.). You can also restrict which parameters are acceptable with some of the same options described below for a single case ("**Making a single divider routine, in more detail**") - either turning an option on or off, in all cases.

The **--assemble** parameter alone will attempt to assemble using ACME, but by itself will ignore the result unless assembly errors occur. If the **--stats** parameter is added, it will be simulated (this is a guess and not cycle accurate, but much faster than emulation). If the **--emulate** parameter is used, it will be emulated - by default, for all possible cases. However a smaller set can be used with the **--fast-stats** option, and it is also possible to select a random subset of cases with **--random-stats \<number of cases\>** - this also respects **--random-seed**.

If either simulation or emulation is done, and there is no assembly or emulation error, there will be stats in the output. (If both, then there will be two sets. If neither, there will just be the size.) This gives means (for all denominators, for denominators <=64 and <=16, median and worst case.) There will also be lists at the top of the output file showing the best for each of these metrics by size, from smallest to fastest. There will also be a combined score obtained by taking the sum of positions in each table, which can optionally be individually scaled (with **--mix**). 

It's also possible to re-use results from a previous output file (such as full-list.txt) with **--old-file \<filename\>**, which is useful for trying a different mixed score. In this case to obtain simulated and/or emulated statistics in the new output you will also have to pass **--stats** and/or **--emulate** (even though this doesn't involve actually running the emulator again.)

By default, errors (failure to assemble, or the emulator producing the wrong result) are logged to the report file (set by **--report**), without exiting. To exit at the first error, use **--one-error**. To include all cases (not just failing ones) in the report **--verbose** can be used (*this can produce very large files if not used with a small subset of cases, though.*)

Typical speeds to complete a run are - all with pypy (CPython works, but at least when using --emulator is likely to be slower):

| Command                                   | Speed |
| ----------------------------------------- | ----- |
| --emulate --stats --quickest --fast-stats | 0.8s  |
| --emulate --stats --quickest              | 11s   |
| --emulate --stats --quick --fast-stats    | 9.7s  |
| --emulate --stats --random 2000           | 36s   |
| --emulate --stats --fast-stats            | 16m   |
| --emulate --stats                         | 7h40m |
| --emulate --stats --old-file              | 1m50s |

## The runtime environment

Two named zero page locations are required, which can be changed by (**--denominator \<denominator\>** and **--numerator \<numerator\>**). By default, on entry the numerator is in the numerator zero page location and the denominator is in the X register, while the result is returned in A. However other conventions can be used with the **--denominator-from** (denominator source), **-numerator-from** (numerator source) and **-result-to** (result destination) parameters. This can reduce performance, though (generally not by much if at all for the inputs, but changing the result destination requires a wrapper subroutine which adds ~15 cycles).

## Handling division by zero

The default approach is to treat it the same as dividing by 1. If you want it to signal an error, **-divide-by-zero \<handler\>** will jump to **\<handler\>**. Alternatively, if you also pass **-error-vector** then it will treat the address as a pointer and jump through it.

## Assembly formatting

The code produced can be formatted in various ways to suit different assemblers. The defaults are intended for ACME: comments are prefixed by **;**, labels have no prefix, instructions are prefixed by a tab, and literal bytes are prefixed by **!byte** but all of these can be changed with the **--comment**, **--label**, **--instruction** and **--equb** arguments. Additionally, all labels (internal, as well as the entry point **_entry**_ have a prefix, set by **-prefix**.

## Making a single divider routine, in more detail

Which denominators get a custom routine is defined by **--max-custom** (the highest denominator to use a custom routine), **--max-full** (the maximum denominator to use a custom routine that is not just a prefix to another one) and **--skip-custom** which allows one of these to be removed. Many of the custom routines share trailing sequences with others, so it is possible to combine them, and this is the default behaviour. It can be disabled with **--inlining** though, gaining speed at the cost of size. If **--factoring** is given and no custom /9 or /15 is present, then custom routines built from /3 /3 or /3 /5 will be used (these are slower but smaller than the custom routines, while still being faster than the generic case.)

The behaviour for denominators outside this is controlled by **--max-shifting** - above this denominator, a shifting divider is used, below it repeated subtraction is used. (Pass 256 to disable it and always use subtraction, pass 0 to disable subtraction and always use shifting.) The special case for denominators >= 128 is controlled by **--high-bit** to enable it, and **--early-high-bit** to perform the check for these high-bit-set values before checking whether the value is in the table of custom routines. Doing so makes high-bit set values faster, but others slower. It's a win on average if your input is close to being randomly distributed (rather than biased towards smaller values). The subtraction loop can be replaced by unrolled code - faster, but it can get very large - with **--unroll**.

How a custom routine is selected and dispatched is controlled by **--self-modifying** which allows the code to modify itself - faster and smaller, but it won't be able to run from ROM - and **--half-table** which uses a table of 8-bit low bytes with the high byte being common to all of them. This is faster and smaller, but can't be used for all parameters (those with more than 256 bytes of table-called routines) and requires that the resulting code is page aligned. Alternatively for very small jump tables, the table can be skipped entirely with **--choice-tree** (replacing it with compare-and-branch code).

## Some special cases

Code generation for 65C02 (rather than the NMOS 6502) can be selected with **--with-65c02**. It won't make much difference though, and it will prevent emulation as the emulator doesn't support the 65C02.

A routine to divide by a constant can be extracted with **--known-denominator**.

When running a potentially slow multiple-parameter mode, a progress bar is displayed using [tqdm](https://github.com/tqdm/tqdm). This can be turned off with **--no-progress**.

## Where the division routine are from

Most are from [this thread](https://forums.nesdev.org/viewtopic.php?f=2&t=11336), however I have also used a superoptimizer (**supero.c**, **supero-run** to run multiple copies of it with different conditions, **cycler.py** to annotate the results with speed, **supero-annotated.txt** the end result of this.)

