# powbench

`pi^100` by 99 multiplications, computed twice over: with a 128-bit mantissa
held in two 64-bit words plus an exponent, and with a double word, a pair of
binary64 numbers.  The point is the speed, not the accuracy: the two do not
carry the same number of digits, 128 bits against 106.

    gcc -O3 -march=native -o powbench powbench.c -lm && ./powbench

Each side is timed with one, two and four powers computed side by side, so
that the run says both how long one multiplication takes when the next one
waits for it, and how many the processor sustains when it has work to
overlap.  The integer multiplication truncates rather than rounds to
nearest: a choice, it makes the integer side as fast as it can be.
