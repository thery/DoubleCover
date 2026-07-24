// Degree-7 Chebyshev interpolant of exp on [0.25,0.25001], centered at a
// dyadic midpoint c = Cc/2^54.  Output coefficients b_k = A_k/2^D and check
// the rounded polynomial's max error.
#include <stdio.h>
#include <mpfr.h>
#include <math.h>
#define PREC 700
#define DEG 7
#define NN (DEG+1)
#define D 220
static double a_=0.25,b_=0.25001;
int main(){
  mpfr_t node[NN],val[NN],dd[NN],c,pi,t,half,mid,s,tmp,x,step,ex,poly,err,maxe;
  mpfr_inits2(PREC,c,pi,t,half,mid,s,tmp,x,step,ex,poly,err,maxe,(mpfr_ptr)0);
  for(int i=0;i<NN;i++){mpfr_init2(node[i],PREC);mpfr_init2(val[i],PREC);mpfr_init2(dd[i],PREC);}
  // dyadic center Cc/2^54 near midpoint
  long long Cc = llround(((a_+b_)/2)*ldexp(1.0,54));
  mpfr_set_si(c,Cc,MPFR_RNDN); mpfr_div_2si(c,c,54,MPFR_RNDN);
  mpfr_const_pi(pi,MPFR_RNDN);
  mpfr_set_d(mid,(a_+b_)/2,MPFR_RNDN); mpfr_set_d(half,(b_-a_)/2,MPFR_RNDN);
  for(int i=0;i<NN;i++){
    mpfr_mul_si(t,pi,2*i+1,MPFR_RNDN); mpfr_div_si(t,t,2*NN,MPFR_RNDN); mpfr_cos(t,t,MPFR_RNDN);
    mpfr_mul(t,t,half,MPFR_RNDN); mpfr_add(node[i],t,mid,MPFR_RNDN);
    mpfr_exp(val[i],node[i],MPFR_RNDN); mpfr_set(dd[i],val[i],MPFR_RNDN);
  }
  // divided differences in place
  for(int j=1;j<NN;j++) for(int i=NN-1;i>=j;i--){
    mpfr_sub(dd[i],dd[i],dd[i-1],MPFR_RNDN);
    mpfr_sub(tmp,node[i],node[i-j],MPFR_RNDN); mpfr_div(dd[i],dd[i],tmp,MPFR_RNDN);
  }
  // expand Newton form in eps=(x-c): coef[k]
  mpfr_t coef[NN], B[NN+1], newB[NN+1];
  for(int k=0;k<NN;k++){mpfr_init2(coef[k],PREC);mpfr_set_zero(coef[k],1);}
  for(int k=0;k<=NN;k++){mpfr_init2(B[k],PREC);mpfr_init2(newB[k],PREC);mpfr_set_zero(B[k],1);}
  mpfr_set_ui(B[0],1,MPFR_RNDN); int degB=0;
  for(int i=0;i<NN;i++){
    for(int k=0;k<=degB;k++){ mpfr_mul(tmp,dd[i],B[k],MPFR_RNDN); mpfr_add(coef[k],coef[k],tmp,MPFR_RNDN); }
    // B *= ( (c-node_i) + eps )
    mpfr_sub(s,c,node[i],MPFR_RNDN);
    for(int k=0;k<=degB+1;k++) mpfr_set_zero(newB[k],1);
    for(int k=0;k<=degB;k++){ mpfr_mul(tmp,B[k],s,MPFR_RNDN); mpfr_add(newB[k],newB[k],tmp,MPFR_RNDN);
                              mpfr_add(newB[k+1],newB[k+1],B[k],MPFR_RNDN); }
    degB++; for(int k=0;k<=degB;k++) mpfr_set(B[k],newB[k],MPFR_RNDN);
  }
  // round coefficients to A_k/2^D and print
  printf("Cc = %lld   (* c = Cc/2^54 *)\nD = %d\n", Cc, D);
  mpfr_t A[NN];
  for(int k=0;k<NN;k++){ mpfr_init2(A[k],PREC); mpfr_mul_2si(A[k],coef[k],D,MPFR_RNDN); mpfr_round(A[k],A[k]);
    mpfr_printf("A%d = %.0Rf\n", k, A[k]); }
  // check rounded polynomial error over dense samples
  int S=8000; mpfr_set_d(step,(b_-a_)/S,MPFR_RNDN); mpfr_set_zero(maxe,1);
  for(int sidx=0;sidx<=S;sidx++){
    mpfr_mul_si(x,step,sidx,MPFR_RNDN); mpfr_add_d(x,x,a_,MPFR_RNDN);
    mpfr_sub(t,x,c,MPFR_RNDN);                 // eps
    mpfr_set_zero(poly,1); mpfr_set_ui(tmp,1,MPFR_RNDN); // eps^k
    for(int k=0;k<NN;k++){ mpfr_t term; mpfr_init2(term,PREC);
      mpfr_mul(term,A[k],tmp,MPFR_RNDN); mpfr_add(poly,poly,term,MPFR_RNDN); mpfr_clear(term);
      mpfr_mul(tmp,tmp,t,MPFR_RNDN); }
    mpfr_div_2si(poly,poly,D,MPFR_RNDN);        // /2^D
    mpfr_exp(ex,x,MPFR_RNDN); mpfr_sub(err,poly,ex,MPFR_RNDN); mpfr_abs(err,err,MPFR_RNDN);
    if(mpfr_cmp(err,maxe)>0) mpfr_set(maxe,err,MPFR_RNDN);
  }
  mpfr_log2(t,maxe,MPFR_RNDN);
  mpfr_printf("\nrounded degree-7 poly: max|P-exp| = 2^%.2Rf  (target 2^-160)\n", t);
  return 0;
}
