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
nearest is timed both ways, so the price of the rounding can be read off
the two lines.

Nothing in the integer multiplication is decided by a test.  The bit that
says which way to round, and the bit that says whether the product needs a
shift, are both as good as random; a branch on either is guessed wrong half
the time, and the run then says the rounding costs three times what it does.
