bad=0;tot=0
for M in range(3,200):
 for A in range(1,M):
  q=M-A
  if q>A: continue
  k=A//q
  for j in range(0,k+1):
   tot+=1
   if (A*(j+1))%M != A-j*q: bad+=1
print("pt_desc  Pt(j+1) = A - j*(M-A) for j<=A//(M-A):  checked",tot," bad",bad)
