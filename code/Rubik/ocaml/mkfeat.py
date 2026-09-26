#!/usr/bin/env python3
# mkfeat.py -- variants of rubik_row_rocq.ml, each with ONE thing the code
# native_compute generates does and the translation does not (read off
# .coq-native/NRubik_RowMin.native).  Written to feat/v_<name>.ml; the run
# is runfeat.sh.
#   f1int   every int operation tests its arguments are ints, shifts their range
#   f2bool  a comparison builds a three constructor bool and matches it
#   f3accu  a nat may be an accumulator; the pairs taken apart are tag checked
#   f4type  every ifold of the search builds its type argument
#   f5case  every if of the search is a function of its own, never inlined
#   f6arr   an array access checks array and int, the kernel called out of line
#   fall    the six together
import re
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rubik_row_rocq.ml')).read()
A = '(* ---- reading the tables from the .v files'
B = '(* ---- RowCoord, RowCoordLeaf, RowLeafFast'
M = '(* ---- main ---'
T = 'type rmap = arr Parray.t\n'

def around(s, shadow, restore):
    # shadow for the run's code, back to Stdlib for the parsing and main
    s = s.replace(T, T + shadow, 1)
    s = s.replace(A, restore + A, 1)
    s = s.replace(B, shadow + B, 1)
    s = s.replace(M, restore + M, 1)
    return s

RESTORE = '''
let ( + ) = Stdlib.( + ) let ( - ) = Stdlib.( - ) let ( * ) = Stdlib.( * )
let ( / ) = Stdlib.( / ) let ( mod ) = Stdlib.( mod )
let ( land ) = Stdlib.( land ) let ( lor ) = Stdlib.( lor )
let ( lxor ) = Stdlib.( lxor ) let ( lsl ) = Stdlib.( lsl )
let ( lsr ) = Stdlib.( lsr ) let ( = ) = Stdlib.( = ) let ( <> ) = Stdlib.( <> )
let ( < ) = Stdlib.( < ) let ( <= ) = Stdlib.( <= )
let ( > ) = Stdlib.( > ) let ( >= ) = Stdlib.( >= )

'''

# 1. every int operation guarded, as Nativevalues does it
F1 = '''
(* VARIANT f1int: every int operation tests its arguments are ints, as the
   generated code does before no_check_*; shifts check their range *)
let[@inline never] accu () = failwith "accumulator"
let isi (x : int) = Obj.is_int (Obj.repr x)
let ( + ) x y = if isi x && isi y then Stdlib.( + ) x y else accu ()
let ( - ) x y = if isi x && isi y then Stdlib.( - ) x y else accu ()
let ( * ) x y = if isi x && isi y then Stdlib.( * ) x y else accu ()
let ( / ) x y = if isi x && isi y then Stdlib.( / ) x y else accu ()
let ( mod ) x y = if isi x && isi y then Stdlib.( mod ) x y else accu ()
let ( land ) x y = if isi x && isi y then Stdlib.( land ) x y else accu ()
let ( lor ) x y = if isi x && isi y then Stdlib.( lor ) x y else accu ()
let ( lxor ) x y = if isi x && isi y then Stdlib.( lxor ) x y else accu ()
let ( lsl ) x y = if isi x && isi y then
    (if 0 <= y && y < 63 then Stdlib.( lsl ) x y else 0) else accu ()
let ( lsr ) x y = if isi x && isi y then
    (if 0 <= y && y < 63 then Stdlib.( lsr ) x y else 0) else accu ()
let ( = ) (x : int) y = if isi x && isi y then Stdlib.( = ) x y else accu ()
let ( <> ) (x : int) y = if isi x && isi y then Stdlib.( <> ) x y else accu ()
let ( < ) (x : int) y = if isi x && isi y then Stdlib.( < ) x y else accu ()
let ( <= ) (x : int) y = if isi x && isi y then Stdlib.( <= ) x y else accu ()
let ( > ) (x : int) y = if isi x && isi y then Stdlib.( > ) x y else accu ()
let ( >= ) (x : int) y = if isi x && isi y then Stdlib.( >= ) x y else accu ()

'''

# 2. every comparison makes a Rocq bool and matches it on three cases
F2 = '''
(* VARIANT f2bool: a comparison builds a bool of three constructors, the
   accumulator, true and false, and the test matches it *)
type rb = RAccu of int array | RTrue | RFalse
let[@inline never] accu () = failwith "accumulator"
let rt (b : rb) = match Sys.opaque_identity b with
  | RAccu _ -> accu () | RTrue -> true | RFalse -> false
let ( = ) (x : int) y = rt (if Stdlib.( = ) x y then RTrue else RFalse)
let ( <> ) (x : int) y = rt (if Stdlib.( <> ) x y then RTrue else RFalse)
let ( < ) (x : int) y = rt (if Stdlib.( < ) x y then RTrue else RFalse)
let ( <= ) (x : int) y = rt (if Stdlib.( <= ) x y then RTrue else RFalse)
let ( > ) (x : int) y = rt (if Stdlib.( > ) x y then RTrue else RFalse)
let ( >= ) (x : int) y = rt (if Stdlib.( >= ) x y then RTrue else RFalse)

'''

def f1(s):
    return around(s, F1, RESTORE)

def f2(s):
    s = around(s, F2, RESTORE)
    old = '''let negb b = if b then false else true
let orb a b = if a then true else b
let andb a b = if a then b else false'''
    assert old in s
    return s.replace(old, '''(* VARIANT f2bool: negb, orb, andb are calls, as the constants they are *)
let[@inline never] negb b = if b then false else true
let[@inline never] orb a b = if a then true else b
let[@inline never] andb a b = if a then b else false''')

# 3. matches test for the accumulator
def f3(s):
    old = 'type nat = O | S of nat\n'
    assert old in s
    s = s.replace(old, '''(* VARIANT f3accu: a nat may be an accumulator, so a match on it tests the
   tag; the pairs the search takes apart are checked the same way *)
type nat = O | S of nat | NAccu of int array
let[@inline never] accu () = failwith "accumulator"
let chk (p : 'a) = if Obj.tag (Obj.repr p) <> 0 then accu ()
''')
    s = re.sub(r'(\n\s*)let \(m, n\) = mn in', r'\1chk mn;\1let (m, n) = mn in', s)
    s = s.replace('let (((c, u), d), m) = x in', 'chk x; let (((c, u), d), m) = x in')
    s = s.replace('''let place24 e8num e4bit x =
  ((mcp x''', '''let place24 e8num e4bit x =
  chk x;
  ((mcp x''')
    s = s.replace('''    let ((pg, gr), bt) = place24 e8num e4bit (tomemb x) in''',
                  '''    let p = place24 e8num e4bit (tomemb x) in chk p;
    let ((pg, gr), bt) = p in''')
    return s

# 4. every ifold of the search builds its type argument
def f4(s):
    old = '(* ---- RowFoldSrchI: the searches'
    assert old in s
    s = s.replace(old, '''(* VARIANT f4type: every ifold of the search builds its type argument,
   prod (array (array int)) int, and forces the lazy nmvn, as the generated
   code does *)
type ty = TInt | TArr of ty | TProd of ty * ty | TAccu of int array
let symtbl = Array.make 32 TInt
let mk_ty () =
  let t0 = Sys.opaque_identity symtbl.(13) in
  TProd (TArr (TArr t0), Sys.opaque_identity TInt)
let nmvn_l = lazy nmvn
let ifoldT ty n x f a = ignore (Sys.opaque_identity ty); ifold n x f a

''' + old, 1)
    i = s.index('(* ---- RowFoldSrchI: the searches')
    j = s.index('(* ---- main ---')
    mid = s[i:j].replace('ifold nmvn 0', 'ifoldT (mk_ty ()) (Lazy.force nmvn_l) 0')
    return s[:i] + mid + s[j:]


F2head = F2[:F2.index("let ( = )")]
F2ops = F2[F2.index("let ( = )"):]
def f2b(s):
    s = s.replace(T, T + F2head + F2ops, 1)
    s = s.replace(A, RESTORE + A, 1)
    s = s.replace(B, F2ops + B, 1)
    s = s.replace(M, RESTORE + M, 1)
    old = '''let negb b = if b then false else true
let orb a b = if a then true else b
let andb a b = if a then b else false'''
    assert old in s
    return s.replace(old, '''let[@inline never] negb b = if b then false else true
let[@inline never] orb a b = if a then true else b
let[@inline never] andb a b = if a then b else false''')

i0 = src.index('(* RowFoldN.iwsrchL *)')
i1 = src.index('  iwsrchL\n', i0) + len('  iwsrchL\n')
OLD_IW = src[i0:i1]

NEW_IW = '''(* VARIANT f5case: each if of the search is a function of its own, never
   inlined, handed its free variables and the tested bool, as native_compute
   makes case_iwsrchL_80, 79, 76, 72 and the tests inside them *)
let rec cs_eq nd togoi' (cond : bool) =
  if cond then true else frcutii <= togoi' + nd
[@@inline never]
let rec cs_cut nd togoi' (cut : bool) =
  if cut then cs_eq nd togoi' (nd = togoi') else true
[@@inline never]
let rec cs_le nd togoi' cut (cond : bool) =
  if cond then cs_cut nd togoi' cut else false
[@@inline never]
let rec cs_cuth ishm k (cond : bool) =
  if cond then negb (ishm land (1 lsl k) = 0) else false
[@@inline never]
let rec cs_cutt ishm k togo' (cut : bool) =
  if cut then cs_cuth ishm k (eqn togo' O) else false
[@@inline never]
let rec cs_depth iwsrchL xstep dnlo dnhi fllo flhi cut togo' togoi' c' x k w nd
                 a' (cond : bool) =
  if cond then iwsrchL cut togo' togoi' c' (xstep x k)
                 (mmask dnlo dnhi fllo flhi w (fsslack (togoi' - nd))) k a'
  else a'
[@@inline never]
let rec cs_try iwsrchL cstep xstep f frep fsym twsym dnlo dnhi fllo flhi
               cut togo' togoi' c x k a' (cond : bool) =
  if cond then a'
  else
    let c' = cstep c k in
    let w = sp1g f frep fsym twsym c' in
    let nd = mdist w in
    cs_depth iwsrchL xstep dnlo dnhi fllo flhi cut togo' togoi' c' x k w nd a'
      (cs_le nd togoi' cut (nd <= togoi'))
[@@inline never]
let rec cs_ok iwsrchL cstep xstep f frep fsym twsym dnlo dnhi fllo flhi
              cut ishm togo' togoi' c x k a' (cond : bool) =
  if cond then a'
  else cs_try iwsrchL cstep xstep f frep fsym twsym dnlo dnhi fllo flhi
         cut togo' togoi' c x k a' (cs_cutt ishm k togo' cut)
[@@inline never]
let rec cs_msk iwsrchL cstep xstep okmv f frep fsym twsym dnlo dnhi fllo flhi
               cut ishm togo' togoi' c x pv k a' (cond : bool) =
  if cond then a'
  else cs_ok iwsrchL cstep xstep f frep fsym twsym dnlo dnhi fllo flhi
         cut ishm togo' togoi' c x k a' (negb (okmv pv k))
[@@inline never]
let rec cl_cut e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep xstep
               c x k a' (cond : bool) =
  if cond then a'
  else wleaf e8num e4bit fpg fsgr fsbt forb tomemb csolved
         (cstep c k) (xstep x k) a'
[@@inline never]
let rec cl_ok e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep xstep
              cut ishm c x k a' (cond : bool) =
  if cond then a'
  else cl_cut e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep xstep
         c x k a' (andb cut (negb (ishm land (1 lsl k) = 0)))
[@@inline never]
let rec cl_msk e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep xstep okmv
               cut ishm c x pv k a' (cond : bool) =
  if cond then a'
  else cl_ok e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep xstep
         cut ishm c x k a' (negb (okmv pv k))
[@@inline never]

(* RowFoldN.iwsrchL *)
let iwsrchL e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
            cstep xstep tomemb okmv csolved forb ishm =
  let rec iwsrchL cut togo togoi c x msk pv (a : rmap * int) =
    match togo with
    | S togo' ->
        (match togo' with
         | O ->
             ifold nmvn 0
               (fun k a' ->
                  cl_msk e8num e4bit fpg fsgr fsbt forb tomemb csolved cstep
                    xstep okmv cut ishm c x pv k a' (msk land (1 lsl k) = 0))
               a
         | _ ->
             let togoi' = togoi - 1 in
             ifold nmvn 0
               (fun k a' ->
                  cs_msk iwsrchL cstep xstep okmv f frep fsym twsym
                    dnlo dnhi fllo flhi cut ishm togo' togoi' c x pv k a'
                    (msk land (1 lsl k) = 0))
               a)
    | O -> wleaf e8num e4bit fpg fsgr fsbt forb tomemb csolved c x a in
  iwsrchL
'''

def f5(s):
    assert OLD_IW in s
    return s.replace(OLD_IW, NEW_IW)

def f6(s):
    s = s.replace('module Parray = struct', 'module ParrayK = struct', 1)
    return s.replace('type arr = int Parray.t\n', '''
(* VARIANT f6arr: an array access first checks it has an array and an int,
   as Nativevalues.arrayget and arrayset do, and calls the kernel out of line *)
let[@inline never] accu6 () = failwith "accumulator"
module Parray = struct
  include ParrayK
  let[@inline never] kget t n = ParrayK.get t n
  let[@inline never] kset t n v = ParrayK.set t n v
  let is_parray t = Obj.is_block (Obj.repr t) && Obj.size (Obj.repr t) = 1
  let get t n = if is_parray t && Obj.is_int (Obj.repr n) then kget t n
                else accu6 ()
  let set t n v = if is_parray t && Obj.is_int (Obj.repr n) then kset t n v
                  else accu6 ()
end
''' + 'type arr = int Parray.t\n', 1)

def fall(s):
    return f1(f2b(f3(f4(f6(f5(s))))))


os.makedirs('feat', exist_ok=True)
for name, f in [('f1int', f1), ('f2bool', f2b), ('f3accu', f3), ('f4type', f4),
                ('f5case', f5), ('f6arr', f6), ('fall', fall)]:
    open('feat/v_%s.ml' % name, 'w').write(f(src))
    print('feat/v_%s.ml' % name)
