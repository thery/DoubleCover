From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.

Inductive dwfloat := DWFloat (xh : float) (xl : float).

Implicit Type d : dwfloat.
Implicit Type f : float.

Definition wellFormed d :=
  let: DWFloat xh xl := d in (xh + xl =? xh)%float.

Definition fp2dw (x : float) := DWFloat x 0.

Definition twoSum (a b : float) := 
 let s := (a + b)%float in
 let a' := (s - b)%float in
 let b' := (s - a')%float in
 let da := (a - a')%float in 
 let db := (b - b')%float in DWFloat s (da + db).

Compute (twoSum 2e+16 2.25)%float.

Definition fastTwoSum (a b : float) := 
 let s := (a + b)%float in
 let z := (s - a)%float in
 DWFloat s (b - z).

Compute (fastTwoSum 2e+16 2.25)%float.
Compute (fastTwoSum 2.25 2e+16)%float.

Definition plusDwFp (x : dwfloat) (y : float) :=
  let: DWFloat xh xl := x in 
  let: DWFloat sh sl := twoSum xh y in 
  let:  v := (xl + sl)%float in  
  fastTwoSum sh v.

Compute plusDwFp (DWFloat 20000000000000004 (-1.75)) 2.25.
  
Definition plusDwDw (x y : dwfloat) := 
  let: DWFloat xh xl := x in 
  let: DWFloat yh yl := y in 
  let: DWFloat sh sl := twoSum xh yh in 
  let: DWFloat th tl := twoSum xl yl in 
  let: c := (sl + th)%float in 
  let: DWFloat vh vl := fastTwoSum sh c in 
  let: w := (tl + vl)%float in fastTwoSum vh w.

Compute plusDwDw (DWFloat 20000000000000004 (-1.75)) 
                 (DWFloat 20000000000000004 (-1.75)).

Definition c_const := (134217729)%float.

Definition splitC (x : float) := 
let gamma := (c_const * x)%float in 
let delta := (x - gamma)%float in 
let xh := (gamma + delta)%float in 
let x' :=  (x - xh)%float in DWFloat xh x'.

Compute splitC (c_const * c_const)%float.

Definition dekker (x y : float) := 
  let: DWFloat xh  xl := splitC x in 
  let: DWFloat yh yl := splitC y in 
  let: pi := (x * y)%float in 
  let: t1 := (- pi + xh * yh)%float in 
  let: t2 := (t1 + xh * yl)%float in 
  let: t3 := (t2 + xl * yh)%float in 
  let: e := (t3 + xl * yl)%float in 
  DWFloat pi e.

Compute dekker 2 2.
Compute dekker c_const c_const.

Definition twoProd x y := dekker x y.

Definition timesDwFp1 (x : dwfloat) (y : float) := 
  let: DWFloat xh xl := x in 
  let: DWFloat ch cl1 := twoProd xh y in 
  let: cl2 := (xl * y)%float in 
  let: DWFloat th tl1 := fastTwoSum ch cl2 in 
  let: tl2 := (tl1 + cl1)%float in 
  fastTwoSum th tl2.

Compute timesDwFp1 (dekker c_const c_const) c_const.
Compute (c_const * c_const * c_const)%float.

Definition timesDwFp2 (x : dwfloat) (y : float) := 
  let: DWFloat xh xl := x in 
  let: DWFloat ch cl1 := twoProd xh y in 
  let: cl2 := (xl * y)%float in 
  let: cl3 := (cl1 + cl2)%float in 
  fastTwoSum ch cl3.

Compute timesDwFp2 (dekker c_const c_const) c_const.
Compute (c_const * c_const * c_const)%float.

Definition timesDwDw (x y : dwfloat) := 
  let: DWFloat xh xl := x in 
  let: DWFloat yh yl := y in 
  let: DWFloat ch cl1 := twoProd xh yh in
  let: tl1 := (xh * yl)%float in
  let: tl2 := (xl * yh)%float in
  let: cl2 := (tl1 + tl2)%float in 
  let: cl3 := (cl1 + cl2)%float in  fastTwoSum ch cl3.

Compute timesDwDw (dekker c_const c_const) (dekker c_const c_const).
Compute (c_const * c_const * c_const * c_const)%float.

Definition divDwFp1 (x : dwfloat) (y : float) :=
  let: DWFloat xh xl := x in 
  let: th := (xh/y)%float in
  let: DWFloat pih pil := twoProd th y in
  let: DWFloat dh d' := twoSum xh (-pih) in
  let: d'' := (xl -pil)%float in 
  let: dl := (d' + d'')%float in
  let: d := (dh + dl)%float in
  let: tl := (d/y)%float in fastTwoSum th tl.

Compute divDwFp1 (plusDwFp (dekker c_const c_const) 1) c_const.

Definition divDwFp2 (x : dwfloat) (y : float) :=
  let: DWFloat xh xl := x in 
  let: th := (xh/y)%float in
  let: DWFloat pih pil := twoProd th y in
  let: dh := (xh - pih)%float in
  let: dl := (xl - pil)%float in
  let: d := (dh + dl)%float in
  let: tl := (d/y)%float in fastTwoSum th tl.

Compute divDwFp2 (plusDwFp (dekker c_const c_const) 1) c_const.

Definition divDwFp3 (x : dwfloat) (y : float) :=
  let: DWFloat xh xl := x in 
  let: th := (xh / y)%float in
  let: DWFloat pih pil := twoProd th y in
  let: dh := (xh  - pih)%float in
  let: dt := (dh - pil)%float in 
  let d := (dt + xl)%float in
  let tl := (d / y)%float in fastTwoSum th tl.

Compute divDwFp3 (plusDwFp (dekker c_const c_const) 1) c_const.

Definition divDwDw1 (x y : dwfloat) :=
  let: DWFloat xh xl := x in 
  let: DWFloat yh yl := y in 
  let: th := (xh / yh)%float in 
  let: DWFloat rh rl := timesDwFp1 y th in 
  let: DWFloat pih pil := twoSum xh (- rh) in 
  let: dh := (pil - rl)%float in 
  let: dl := (dh + xl)%float in
  let: d := (pih + dl)%float in 
  let: tl := (d / yh)%float in 
  fastTwoSum th tl.

Compute divDwDw1 (plusDwFp (dekker c_const c_const) 1) (dekker c_const c_const).

Definition divDwDw2 (x y : dwfloat) :=
  let: DWFloat xh xl := x in 
  let: DWFloat yh yl := y in 
  let: th := (xh / yh)%float in 
  let: DWFloat rh rl := timesDwFp1 y th in 
  let: pih :=  (xh - rh)%float in 
  let: dl := (xl - rl)%float in 
  let: d := (pih + dl)%float in 
  let tl := (d / yh)%float in fastTwoSum th tl.
  
Compute divDwDw2 (plusDwFp (dekker c_const c_const) 1) (dekker c_const c_const).

