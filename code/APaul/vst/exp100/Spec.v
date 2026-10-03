Require Import VST.floyd.proofauto.
Require Import E.Limbs E.exp100_clight E.Common.
Definition num_zero_spec : ident * funspec :=
 DECLARE _num_zero
 WITH sh : share, p : val
 PRE [ tptr tulong ]
   PROP (writable_share sh) PARAMS (p)
   SEP (data_at_ sh (tarray tulong NL) p)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (num sh (Zrepeat 0 NL) p).
Definition num_add_spec : ident * funspec :=
 DECLARE _num_add
 WITH sha : share, shb : share, pa : val, pb : val, a : list Z, b : list Z
 PRE [ tptr tulong, tptr tulong ]
   PROP (writable_share sha; readable_share shb;
         Zlength a = NL; Zlength b = NL; Forall limb a; Forall limb b;
         (valL a + valL b < 2 ^ (lbits * NL))%Z)
   PARAMS (pa; pb)
   SEP (num sha a pa; num shb b pb)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a'; (valL a' = valL a + valL b)%Z)
   RETURN ()
   SEP (num sha a' pa; num shb b pb).
(* a spec reading the global table T: checks that gv and the 2D type work *)
Definition Tval : list (list Z) := map (fun _ => Zrepeat 0 NL) (Zrepeat 0 64). (* placeholder *)
Definition exp_core_shape : ident * funspec :=
 DECLARE _exp_core
 WITH gv : globals, xb : Z, py : val, ps : val, T : list (list val)
 PRE [ tulong, tptr tulong, tptr tlong ]
   PROP (0 <= xb < Int64.modulus)
   PARAMS (Vlong (Int64.repr xb); py; ps) GLOBALS (gv)
   SEP (data_at Ews (tarray tulong NL) (Zrepeat Vundef NL) py;
        data_at Ews tlong Vundef ps;
        data_at Ers (tarray (tarray tulong NL) 64) T (gv _T))
 POST [ tint ]
   EX rc : Z, EX y : list Z, EX s : Z,
   PROP () RETURN (Vint (Int.repr rc))
   SEP (num Ews y py; data_at Ews tlong (Vlong (Int64.repr s)) ps;
        data_at Ers (tarray (tarray tulong NL) 64) T (gv _T)).
