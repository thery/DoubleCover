/* Generated from htr3.b by Capla (`ccomp -dcaplac`, an unverified
   backend): the Capla search written out as C, so that htr3gcc
   needs only gcc.  Regenerate it with `make capla-c` (needs the
   Capla compiler).  Read htr3.b, not this file. */

#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <float.h>
#include <stdint.h>
#include <assert.h>

#if defined(__HAVE_FLOAT32) && defined(__HAVE_FLOAT64)
#else
static int __f32_test[sizeof(float) == 4 ? 1 : -1];
static int __f64_test[sizeof(double) == 8 ? 1 : -1];
typedef float _Float32;
typedef double _Float64;
#endif

#define __builtin_umulh64(a, b) ((unsigned __int128) a * b) >> 64;


uint64_t search(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5, uint64_t n35, uint64_t err36, uint64_t* restrict out37, uint64_t cap38);
void addw(uint64_t* restrict B1, uint64_t m2, uint64_t ia3, uint64_t ib4, uint64_t l5);
void subw(uint64_t* restrict B1, uint64_t m2, uint64_t ia3, uint64_t ib4, uint64_t l5);
void tstep(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5);
void difftab(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5);


uint64_t search(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5, uint64_t n35, uint64_t err36, uint64_t* restrict out37, uint64_t cap38)
{
  uint64_t __tmp__var__80;
  uint64_t _tmp55_1_1_78;
  uint64_t out37_1_1_74;
  uint64_t _tmp49_1_1_77;
  uint64_t B1_1_1_76;
  uint64_t __copy_err72;
  uint64_t _tmp56;
  uint64_t _tmp52;
  uint64_t _tmp50;
  uint64_t j42;
  uint64_t _tmp58;
  uint64_t __copy_l70;
  uint8_t _tmp54;
  uint64_t _tmp57;
  uint64_t __copy_k69;
  uint8_t _tmp53;
  uint64_t _tmp51;
  uint64_t __copy_n71;
  uint64_t count39;
  uint64_t _j_hi79;
  /*skip*/;
  out37_1_1_74 = cap38;
  B1_1_1_76 = m2;
  __copy_n71 = n35;
  __copy_l70 = l5;
  __copy_k69 = k20;
  __copy_err72 = err36;
  count39 = 0LL;
  _tmp50 = m2;
  _tmp51 = __copy_k69;
  _tmp52 = __copy_l70;
  {
    uint64_t* restrict _tmp49 = B1;
    
    _tmp49_1_1_77 = B1_1_1_76;
    assert (_tmp50 == _tmp49_1_1_77);
    difftab(_tmp49, _tmp50, _tmp51, _tmp52);
  }
  assert ((uint64_t) (__copy_l70) - (uint64_t) (1LL) < B1_1_1_76);
  B1[(uint64_t) (__copy_l70) - (uint64_t) (1LL)] =
    (uint64_t) (B1[((uint64_t) (__copy_l70) - (uint64_t) (1LL))])
      + (uint64_t) (__copy_err72);
  {
    j42 = 0LL;
    _j_hi79 = __copy_n71;
    while (1) {
      if (j42 < _j_hi79) {
        {
          {
            assert ((uint64_t) (__copy_l70) - (uint64_t) (1LL) < B1_1_1_76);
            if (B1[((uint64_t) (__copy_l70) - (uint64_t) (1LL))]
                  <= (uint64_t) (2LL) * (uint64_t) (__copy_err72)) {
              _tmp53 = 1;
            } else {
              _tmp53 = 0;
            }
            if (_tmp53) {
              {
                if (count39 < cap38) {
                  _tmp54 = 1;
                } else {
                  _tmp54 = 0;
                }
                if (_tmp54) {
                  {
                    assert (count39 < out37_1_1_74);
                    out37[count39] = j42;
                  }
                    $134: ;
                }
                count39 = (uint64_t) (count39) + (uint64_t) (1LL);
              }
                $133: ;
            }
            _tmp56 = m2;
            _tmp57 = __copy_k69;
            _tmp58 = __copy_l70;
            {
              uint64_t* restrict _tmp55 = B1;
              
              _tmp55_1_1_78 = B1_1_1_76;
              assert (_tmp56 == _tmp55_1_1_78);
              tstep(_tmp55, _tmp56, _tmp57, _tmp58);
            }
          }
            $132: ;
        }
          $131: ;
        j42 = (uint64_t) (j42) + (uint64_t) (1LL);
      } else {
        break;
      }
    }
  }
    $130: ;
  return count39;
}

void addw(uint64_t* restrict B1, uint64_t m2, uint64_t ia3, uint64_t ib4, uint64_t l5)
{
  uint64_t __tmp__var__86;
  uint64_t B1_1_1_84;
  uint64_t __copy_ib82;
  uint64_t i10;
  uint64_t cy6;
  uint64_t __copy_ia81;
  uint64_t _i_hi85;
  uint64_t __copy_l83;
  uint64_t t7;
  /*skip*/;
  B1_1_1_84 = m2;
  __copy_ia81 = ia3;
  __copy_l83 = l5;
  __copy_ib82 = ib4;
  cy6 = 0LL;
  {
    i10 = 0LL;
    _i_hi85 = __copy_l83;
    while (1) {
      if (i10 < _i_hi85) {
        {
          {
            assert ((uint64_t) (__copy_ib82) + (uint64_t) (i10) < B1_1_1_84);
            t7 =
              (uint64_t) (B1[((uint64_t) (__copy_ib82) + (uint64_t) (i10))])
                + (uint64_t) (cy6);
            assert ((uint64_t) (__copy_ia81) + (uint64_t) (i10) < B1_1_1_84);
            B1[(uint64_t) (__copy_ia81) + (uint64_t) (i10)] =
              (uint64_t) (B1[((uint64_t) (__copy_ia81) + (uint64_t) (i10))])
                + (uint64_t) (t7);
            if (t7 < cy6) {
              cy6 = (uint64_t) 1;
            } else {
              assert ((uint64_t) (__copy_ia81) + (uint64_t) (i10) < B1_1_1_84);
              cy6 =
                (uint64_t) (B1[((uint64_t) (__copy_ia81) + (uint64_t) (i10))]
                             < t7);
            }
          }
            $137: ;
        }
          $136: ;
        i10 = (uint64_t) (i10) + (uint64_t) (1LL);
      } else {
        break;
      }
    }
  }
    $135: ;
  return;
}

void subw(uint64_t* restrict B1, uint64_t m2, uint64_t ia3, uint64_t ib4, uint64_t l5)
{
  uint64_t __tmp__var__92;
  uint64_t B1_1_1_90;
  uint64_t __copy_ib88;
  uint64_t t14;
  uint64_t i17;
  uint64_t __copy_l89;
  uint64_t cy13;
  uint64_t _i_hi91;
  uint64_t __copy_ia87;
  /*skip*/;
  B1_1_1_90 = m2;
  __copy_ia87 = ia3;
  __copy_l89 = l5;
  __copy_ib88 = ib4;
  cy13 = 0LL;
  {
    i17 = 0LL;
    _i_hi91 = __copy_l89;
    while (1) {
      if (i17 < _i_hi91) {
        {
          {
            assert ((uint64_t) (__copy_ib88) + (uint64_t) (i17) < B1_1_1_90);
            t14 =
              (uint64_t) (B1[((uint64_t) (__copy_ib88) + (uint64_t) (i17))])
                + (uint64_t) (cy13);
            if (t14 < cy13) {
              cy13 = (uint64_t) 1;
            } else {
              assert ((uint64_t) (__copy_ia87) + (uint64_t) (i17) < B1_1_1_90);
              cy13 =
                (uint64_t) (B1[((uint64_t) (__copy_ia87) + (uint64_t) (i17))]
                             < t14);
            }
            assert ((uint64_t) (__copy_ia87) + (uint64_t) (i17) < B1_1_1_90);
            B1[(uint64_t) (__copy_ia87) + (uint64_t) (i17)] =
              (uint64_t) (B1[((uint64_t) (__copy_ia87) + (uint64_t) (i17))])
                - (uint64_t) (t14);
          }
            $140: ;
        }
          $139: ;
        i17 = (uint64_t) (i17) + (uint64_t) (1LL);
      } else {
        break;
      }
    }
  }
    $138: ;
  return;
}

void tstep(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5)
{
  uint64_t __tmp__var__99;
  uint64_t _tmp59_1_1_97;
  uint64_t B1_1_1_96;
  uint64_t t32;
  uint64_t _tmp60;
  uint64_t _t_hi98;
  uint64_t __copy_l94;
  uint64_t _tmp62;
  uint64_t __copy_k93;
  uint64_t _tmp61;
  uint64_t _tmp63;
  /*skip*/;
  B1_1_1_96 = m2;
  __copy_l94 = l5;
  __copy_k93 = k20;
  {
    t32 = 0LL;
    _t_hi98 = (uint64_t) (__copy_k93) - (uint64_t) (1LL);
    while (1) {
      if (t32 < _t_hi98) {
        {
          {
            _tmp60 = m2;
            _tmp61 = (uint64_t) (t32) * (uint64_t) (__copy_l94);
            _tmp62 =
              (uint64_t) (((uint64_t) (t32) + (uint64_t) (1LL)))
                * (uint64_t) (__copy_l94);
            _tmp63 = __copy_l94;
            {
              uint64_t* restrict _tmp59 = B1;
              
              _tmp59_1_1_97 = B1_1_1_96;
              assert (_tmp60 == _tmp59_1_1_97);
              addw(_tmp59, _tmp60, _tmp61, _tmp62, _tmp63);
            }
          }
            $143: ;
        }
          $142: ;
        t32 = (uint64_t) (t32) + (uint64_t) (1LL);
      } else {
        break;
      }
    }
  }
    $141: ;
  return;
}

void difftab(uint64_t* restrict B1, uint64_t m2, uint64_t k20, uint64_t l5)
{
  uint64_t __tmp__var__106;
  uint64_t B1_1_1_102;
  uint64_t _tmp64_1_1_104;
  uint64_t i24;
  uint64_t _tmp68;
  uint64_t __copy_k100;
  uint64_t _tmp66;
  uint64_t _tmp65;
  uint64_t _i_hi105;
  uint64_t __copy_l101;
  uint64_t j21;
  uint64_t _tmp67;
  /*skip*/;
  B1_1_1_102 = m2;
  __copy_l101 = l5;
  __copy_k100 = k20;
  {
    i24 = 1LL;
    _i_hi105 = __copy_k100;
    while (1) {
      if (i24 < _i_hi105) {
        {
          {
            j21 = (uint64_t) (__copy_k100) - (uint64_t) (1LL);
            {
              while (1) {
                if (j21 >= i24) {
                  {
                    {
                      _tmp65 = m2;
                      _tmp66 = (uint64_t) (j21) * (uint64_t) (__copy_l101);
                      _tmp67 =
                        (uint64_t) (((uint64_t) (j21) - (uint64_t) (1LL)))
                          * (uint64_t) (__copy_l101);
                      _tmp68 = __copy_l101;
                      {
                        uint64_t* restrict _tmp64 = B1;
                        
                        _tmp64_1_1_104 = B1_1_1_102;
                        assert (_tmp65 == _tmp64_1_1_104);
                        subw(_tmp64, _tmp65, _tmp66, _tmp67, _tmp68);
                      }
                      j21 = (uint64_t) (j21) - (uint64_t) (1LL);
                    }
                      $149: ;
                  }
                    $148: ;
                } else {
                  break;
                }
              }
            }
              $147: ;
          }
            $146: ;
        }
          $145: ;
        i24 = (uint64_t) (i24) + (uint64_t) (1LL);
      } else {
        break;
      }
    }
  }
    $144: ;
  return;
}


