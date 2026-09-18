#include <stdio.h>
#include <stdint.h>
/* Same five instructions, same 1-cycle dependency chains, same perfectly
   predictable branches.  A takes ONE branch per iteration, B takes TWO. */
int main(int argc,char**argv){
  uint64_t N=2000000000ULL,a=0,c=N,one=1;
  if(argc>1&&argv[1][0]=='B'){
    __asm__ volatile(
      "1: cmpq $0,%[one]\n\t"
      "   jne 3f\n\t"          /* TAKEN, forward */
      "   jmp 4f\n\t"
      "3: addq $1,%[a]\n\t"
      "   subq $1,%[c]\n\t"
      "   jnz 1b\n\t"          /* TAKEN, backward */
      "4:\n\t"
      :[a]"+r"(a),[c]"+r"(c):[one]"r"(one):"cc");
    printf("B %llu\n",(unsigned long long)a);
  } else {
    __asm__ volatile(
      "1: addq $1,%[a]\n\t"
      "   cmpq $0,%[one]\n\t"
      "   je 2f\n\t"           /* never taken */
      "   subq $1,%[c]\n\t"
      "   jnz 1b\n\t"          /* TAKEN, backward */
      "2:\n\t"
      :[a]"+r"(a),[c]"+r"(c):[one]"r"(one):"cc");
    printf("A %llu\n",(unsigned long long)a);
  }
  return 0;
}
