import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 200000000
set_option maxRecDepth 8000

namespace QiushiMatmul

abbrev NVAR_279 := 31
abbrev NOCC_279 := 64

-- compressed row 0 = original row 5, source orbit 150, lb 16, cap 0, mask 536870912
def occRow_279_0 (j : Fin 31) : Int := (if j.val = 29 then 1 else 0)
-- compressed row 1 = original row 9, source orbit 120, lb 15, cap 1, mask 32
def occRow_279_1 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0)
-- compressed row 2 = original row 10, source orbit 120, lb 15, cap 1, mask 64
def occRow_279_2 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0)
-- compressed row 3 = original row 11, source orbit 120, lb 15, cap 1, mask 128
def occRow_279_3 (j : Fin 31) : Int := (if j.val = 7 then 1 else 0)
-- compressed row 4 = original row 15, source orbit 29, lb 15, cap 1, mask 6145
def occRow_279_4 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- compressed row 5 = original row 18, source orbit 29, lb 15, cap 1, mask 24577
def occRow_279_5 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- compressed row 6 = original row 27, source orbit 65, lb 15, cap 1, mask 9441280
def occRow_279_6 (j : Fin 31) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- compressed row 7 = original row 29, source orbit 65, lb 15, cap 1, mask 17305600
def occRow_279_7 (j : Fin 31) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- compressed row 8 = original row 30, source orbit 65, lb 15, cap 1, mask 17827840
def occRow_279_8 (j : Fin 31) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- compressed row 9 = original row 35, source orbit 65, lb 15, cap 1, mask 69210112
def occRow_279_9 (j : Fin 31) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 10 = original row 156, source orbit 11, lb 12, cap 4, mask 42272002
def occRow_279_10 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- compressed row 11 = original row 168, source orbit 11, lb 12, cap 4, mask 84214402
def occRow_279_11 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 12 = original row 189, source orbit 10, lb 12, cap 4, mask 169904672
def occRow_279_12 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 13 = original row 204, source orbit 14, lb 12, cap 4, mask 303186112
def occRow_279_13 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 14 = original row 207, source orbit 14, lb 12, cap 4, mask 336216352
def occRow_279_14 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 15 = original row 235, source orbit 11, lb 12, cap 4, mask 808453252
def occRow_279_15 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 16 = original row 246, source orbit 10, lb 12, cap 4, mask 1083314752
def occRow_279_16 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 17 = original row 249, source orbit 10, lb 12, cap 4, mask 1091179552
def occRow_279_17 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 18 = original row 261, source orbit 10, lb 12, cap 4, mask 1208168452
def occRow_279_18 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 19 = original row 262, source orbit 10, lb 12, cap 4, mask 1208272900
def occRow_279_19 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 20 = original row 264, source orbit 10, lb 12, cap 4, mask 1342361602
def occRow_279_20 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 21 = original row 2, source orbit 150, lb 16, cap 0, mask 65536
def occRow_279_21 (j : Fin 31) : Int := (if j.val = 16 then 1 else 0)
-- compressed row 22 = original row 4, source orbit 150, lb 16, cap 0, mask 268435456
def occRow_279_22 (j : Fin 31) : Int := (if j.val = 28 then 1 else 0)
-- compressed row 23 = original row 26, source orbit 65, lb 15, cap 1, mask 8914944
def occRow_279_23 (j : Fin 31) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- compressed row 24 = original row 144, source orbit 11, lb 12, cap 4, mask 5570602
def occRow_279_24 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- compressed row 25 = original row 194, source orbit 10, lb 12, cap 4, mask 205556800
def occRow_279_25 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 26 = original row 231, source orbit 10, lb 12, cap 4, mask 671262722
def occRow_279_26 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 27 = original row 236, source orbit 11, lb 12, cap 4, mask 810025732
def occRow_279_27 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 28 = original row 237, source orbit 11, lb 12, cap 4, mask 855638092
def occRow_279_28 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 29 = original row 318, source orbit 3, lb 9, cap 7, mask 718624042
def occRow_279_29 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 30 = original row 322, source orbit 3, lb 9, cap 7, mask 860664652
def occRow_279_30 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 31 = original row 180, source orbit 10, lb 12, cap 4, mask 143165576
def occRow_279_31 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 32 = original row 258, source orbit 10, lb 12, cap 4, mask 1143083272
def occRow_279_32 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 33 = original row 321, source orbit 3, lb 9, cap 7, mask 859000012
def occRow_279_33 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 34 = original row 338, source orbit 3, lb 9, cap 7, mask 1431644842
def occRow_279_34 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 35 = original row 3, source orbit 150, lb 16, cap 0, mask 262144
def occRow_279_35 (j : Fin 31) : Int := (if j.val = 18 then 1 else 0)
-- compressed row 36 = original row 7, source orbit 120, lb 15, cap 1, mask 8
def occRow_279_36 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0)
-- compressed row 37 = original row 32, source orbit 65, lb 15, cap 1, mask 35653632
def occRow_279_37 (j : Fin 31) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- compressed row 38 = original row 138, source orbit 11, lb 12, cap 4, mask 2949202
def occRow_279_38 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0)
-- compressed row 39 = original row 227, source orbit 14, lb 12, cap 4, mask 605070352
def occRow_279_39 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 40 = original row 238, source orbit 11, lb 12, cap 4, mask 880803892
def occRow_279_40 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 41 = original row 255, source orbit 10, lb 12, cap 4, mask 1111625872
def occRow_279_41 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 42 = original row 320, source orbit 3, lb 9, cap 7, mask 757945042
def occRow_279_42 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 43 = original row 336, source orbit 3, lb 9, cap 7, mask 1387081042
def occRow_279_43 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 44 = original row 222, source orbit 14, lb 12, cap 4, mask 570991112
def occRow_279_44 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 45 = original row 13, source orbit 120, lb 15, cap 1, mask 512
def occRow_279_45 (j : Fin 31) : Int := (if j.val = 9 then 1 else 0)
-- compressed row 46 = original row 14, source orbit 120, lb 15, cap 1, mask 1024
def occRow_279_46 (j : Fin 31) : Int := (if j.val = 10 then 1 else 0)
-- compressed row 47 = original row 185, source orbit 10, lb 12, cap 4, mask 152078608
def occRow_279_47 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 48 = original row 188, source orbit 14, lb 12, cap 4, mask 169099552
def occRow_279_48 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 49 = original row 257, source orbit 14, lb 12, cap 4, mask 1141973512
def occRow_279_49 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 50 = original row 324, source orbit 3, lb 9, cap 7, mask 885738292
def occRow_279_50 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 51 = original row 49, source orbit 65, lb 15, cap 1, mask 1073815552
def occRow_279_51 (j : Fin 31) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 52 = original row 323, source orbit 3, lb 9, cap 7, mask 884257972
def occRow_279_52 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 53 = original row 216, source orbit 14, lb 12, cap 4, mask 547397792
def occRow_279_53 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 54 = original row 33, source orbit 65, lb 15, cap 1, mask 37752832
def occRow_279_54 (j : Fin 31) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- compressed row 55 = original row 36, source orbit 65, lb 15, cap 1, mask 71305216
def occRow_279_55 (j : Fin 31) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 56 = original row 221, source orbit 14, lb 12, cap 4, mask 557883712
def occRow_279_56 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 57 = original row 251, source orbit 14, lb 12, cap 4, mask 1094787232
def occRow_279_57 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 58 = original row 152, source orbit 10, lb 12, cap 4, mask 31481857
def occRow_279_58 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- compressed row 59 = original row 161, source orbit 14, lb 12, cap 4, mask 55062532
def occRow_279_59 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- compressed row 60 = original row 186, source orbit 14, lb 12, cap 4, mask 153371152
def occRow_279_60 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 61 = original row 182, source orbit 14, lb 12, cap 4, mask 147080200
def occRow_279_61 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 62 = original row 198, source orbit 14, lb 12, cap 4, mask 281166352
def occRow_279_62 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 63 = original row 247, source orbit 14, lb 12, cap 4, mask 1084301632
def occRow_279_63 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0)

def occCoeff_279 : Fin 64 → Fin 31 → Int
  | i, j => match i.val with
    | 0 => occRow_279_0 j
    | 1 => occRow_279_1 j
    | 2 => occRow_279_2 j
    | 3 => occRow_279_3 j
    | 4 => occRow_279_4 j
    | 5 => occRow_279_5 j
    | 6 => occRow_279_6 j
    | 7 => occRow_279_7 j
    | 8 => occRow_279_8 j
    | 9 => occRow_279_9 j
    | 10 => occRow_279_10 j
    | 11 => occRow_279_11 j
    | 12 => occRow_279_12 j
    | 13 => occRow_279_13 j
    | 14 => occRow_279_14 j
    | 15 => occRow_279_15 j
    | 16 => occRow_279_16 j
    | 17 => occRow_279_17 j
    | 18 => occRow_279_18 j
    | 19 => occRow_279_19 j
    | 20 => occRow_279_20 j
    | 21 => occRow_279_21 j
    | 22 => occRow_279_22 j
    | 23 => occRow_279_23 j
    | 24 => occRow_279_24 j
    | 25 => occRow_279_25 j
    | 26 => occRow_279_26 j
    | 27 => occRow_279_27 j
    | 28 => occRow_279_28 j
    | 29 => occRow_279_29 j
    | 30 => occRow_279_30 j
    | 31 => occRow_279_31 j
    | 32 => occRow_279_32 j
    | 33 => occRow_279_33 j
    | 34 => occRow_279_34 j
    | 35 => occRow_279_35 j
    | 36 => occRow_279_36 j
    | 37 => occRow_279_37 j
    | 38 => occRow_279_38 j
    | 39 => occRow_279_39 j
    | 40 => occRow_279_40 j
    | 41 => occRow_279_41 j
    | 42 => occRow_279_42 j
    | 43 => occRow_279_43 j
    | 44 => occRow_279_44 j
    | 45 => occRow_279_45 j
    | 46 => occRow_279_46 j
    | 47 => occRow_279_47 j
    | 48 => occRow_279_48 j
    | 49 => occRow_279_49 j
    | 50 => occRow_279_50 j
    | 51 => occRow_279_51 j
    | 52 => occRow_279_52 j
    | 53 => occRow_279_53 j
    | 54 => occRow_279_54 j
    | 55 => occRow_279_55 j
    | 56 => occRow_279_56 j
    | 57 => occRow_279_57 j
    | 58 => occRow_279_58 j
    | 59 => occRow_279_59 j
    | 60 => occRow_279_60 j
    | 61 => occRow_279_61 j
    | 62 => occRow_279_62 j
    | 63 => occRow_279_63 j
    | _ => 0

def occRhs_279 : Fin 64 → Int
  | i => match i.val with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => 1
    | 8 => 1
    | 9 => 1
    | 10 => 4
    | 11 => 4
    | 12 => 4
    | 13 => 4
    | 14 => 4
    | 15 => 4
    | 16 => 4
    | 17 => 4
    | 18 => 4
    | 19 => 4
    | 20 => 4
    | 21 => 0
    | 22 => 0
    | 23 => 1
    | 24 => 4
    | 25 => 4
    | 26 => 4
    | 27 => 4
    | 28 => 4
    | 29 => 7
    | 30 => 7
    | 31 => 4
    | 32 => 4
    | 33 => 7
    | 34 => 7
    | 35 => 0
    | 36 => 1
    | 37 => 1
    | 38 => 4
    | 39 => 4
    | 40 => 4
    | 41 => 4
    | 42 => 7
    | 43 => 7
    | 44 => 4
    | 45 => 1
    | 46 => 1
    | 47 => 4
    | 48 => 4
    | 49 => 4
    | 50 => 7
    | 51 => 1
    | 52 => 7
    | 53 => 4
    | 54 => 1
    | 55 => 1
    | 56 => 4
    | 57 => 4
    | 58 => 4
    | 59 => 4
    | 60 => 4
    | 61 => 4
    | 62 => 4
    | 63 => 4
    | _ => 0

def S_279 : OccSys 31 64 :=
  { occCoeff := occCoeff_279, occRhs := occRhs_279, target := 16 }

-- leaf 0, path LLL, original Farkas rhs -4
def refs_279_L0 : Fin 29 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨1, by decide⟩
    | 2 => .occ ⟨2, by decide⟩
    | 3 => .occ ⟨3, by decide⟩
    | 4 => .occ ⟨4, by decide⟩
    | 5 => .occ ⟨5, by decide⟩
    | 6 => .occ ⟨6, by decide⟩
    | 7 => .occ ⟨7, by decide⟩
    | 8 => .occ ⟨8, by decide⟩
    | 9 => .occ ⟨9, by decide⟩
    | 10 => .occ ⟨10, by decide⟩
    | 11 => .occ ⟨11, by decide⟩
    | 12 => .occ ⟨12, by decide⟩
    | 13 => .occ ⟨13, by decide⟩
    | 14 => .occ ⟨14, by decide⟩
    | 15 => .occ ⟨15, by decide⟩
    | 16 => .occ ⟨16, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨18, by decide⟩
    | 19 => .occ ⟨19, by decide⟩
    | 20 => .occ ⟨20, by decide⟩
    | 21 => .sumGe
    | 22 => .nonneg ⟨11, by decide⟩
    | 23 => .nonneg ⟨12, by decide⟩
    | 24 => .nonneg ⟨14, by decide⟩
    | 25 => .nonneg ⟨18, by decide⟩
    | 26 => .branchLe ⟨3, by decide⟩ 0
    | 27 => .branchLe ⟨4, by decide⟩ 0
    | 28 => .branchLe ⟨22, by decide⟩ 0
    | _ => .sumGe

def mults_279_L0 : Fin 29 → Nat
  | i => match i.val with
    | 0 => 12
    | 1 => 2
    | 2 => 14
    | 3 => 4
    | 4 => 2
    | 5 => 18
    | 6 => 4
    | 7 => 10
    | 8 => 2
    | 9 => 4
    | 10 => 11
    | 11 => 7
    | 12 => 8
    | 13 => 1
    | 14 => 9
    | 15 => 8
    | 16 => 5
    | 17 => 1
    | 18 => 2
    | 19 => 10
    | 20 => 2
    | 21 => 20
    | 22 => 2
    | 23 => 10
    | 24 => 20
    | 25 => 8
    | 26 => 20
    | 27 => 20
    | 28 => 20
    | _ => 0

theorem coeff_cancel_279_L0 :
    ∀ j : Fin 31, (∑ i : Fin 29, (mults_279_L0 i : Int) * (refs_279_L0 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L0 :
    (∑ i : Fin 29, (mults_279_L0 i : Int) * (refs_279_L0 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf0_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_4_0 : x ⟨3, by decide⟩ ≤ 0)
    (h_le_5_0 : x ⟨4, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 29,
      (∑ j : Fin 31, (refs_279_L0 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L0 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_4_0]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_5_0]
    · simp only [refs_279_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
  exact farkas_leaf_unsat _ _ (mults_279_L0) coeff_cancel_279_L0 rhs_neg_279_L0 x hrows

-- leaf 1, path LLRL, original Farkas rhs -6
def refs_279_L1 : Fin 31 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨21, by decide⟩
    | 1 => .occ ⟨22, by decide⟩
    | 2 => .occ ⟨4, by decide⟩
    | 3 => .occ ⟨5, by decide⟩
    | 4 => .occ ⟨23, by decide⟩
    | 5 => .occ ⟨9, by decide⟩
    | 6 => .occ ⟨24, by decide⟩
    | 7 => .occ ⟨10, by decide⟩
    | 8 => .occ ⟨11, by decide⟩
    | 9 => .occ ⟨12, by decide⟩
    | 10 => .occ ⟨25, by decide⟩
    | 11 => .occ ⟨26, by decide⟩
    | 12 => .occ ⟨15, by decide⟩
    | 13 => .occ ⟨27, by decide⟩
    | 14 => .occ ⟨28, by decide⟩
    | 15 => .occ ⟨16, by decide⟩
    | 16 => .occ ⟨17, by decide⟩
    | 17 => .occ ⟨19, by decide⟩
    | 18 => .occ ⟨29, by decide⟩
    | 19 => .occ ⟨30, by decide⟩
    | 20 => .sumGe
    | 21 => .nonneg ⟨12, by decide⟩
    | 22 => .nonneg ⟨13, by decide⟩
    | 23 => .nonneg ⟨14, by decide⟩
    | 24 => .nonneg ⟨18, by decide⟩
    | 25 => .nonneg ⟨22, by decide⟩
    | 26 => .nonneg ⟨25, by decide⟩
    | 27 => .nonneg ⟨29, by decide⟩
    | 28 => .branchLe ⟨4, by decide⟩ 0
    | 29 => .branchLe ⟨7, by decide⟩ 0
    | 30 => .branchGe ⟨3, by decide⟩ 1
    | _ => .sumGe

def mults_279_L1 : Fin 31 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 4
    | 2 => 4
    | 3 => 12
    | 4 => 2
    | 5 => 14
    | 6 => 3
    | 7 => 2
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 4
    | 12 => 1
    | 13 => 2
    | 14 => 3
    | 15 => 6
    | 16 => 6
    | 17 => 4
    | 18 => 6
    | 19 => 6
    | 20 => 16
    | 21 => 26
    | 22 => 6
    | 23 => 6
    | 24 => 6
    | 25 => 2
    | 26 => 2
    | 27 => 6
    | 28 => 16
    | 29 => 14
    | 30 => 2
    | _ => 0

theorem coeff_cancel_279_L1 :
    ∀ j : Fin 31, (∑ i : Fin 31, (mults_279_L1 i : Int) * (refs_279_L1 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L1 :
    (∑ i : Fin 31, (mults_279_L1 i : Int) * (refs_279_L1 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf1_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_5_0 : x ⟨4, by decide⟩ ≤ 0)
    (h_le_8_0 : x ⟨7, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_4_1 : (1 : Int) ≤ x ⟨3, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 31,
      (∑ j : Fin 31, (refs_279_L1 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L1 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_5_0]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_8_0]
    · simp only [refs_279_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_4_1]
  exact farkas_leaf_unsat _ _ (mults_279_L1) coeff_cancel_279_L1 rhs_neg_279_L1 x hrows

-- leaf 2, path LLRR, original Farkas rhs -5
def refs_279_L2 : Fin 31 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨1, by decide⟩
    | 1 => .occ ⟨2, by decide⟩
    | 2 => .occ ⟨5, by decide⟩
    | 3 => .occ ⟨10, by decide⟩
    | 4 => .occ ⟨11, by decide⟩
    | 5 => .occ ⟨31, by decide⟩
    | 6 => .occ ⟨12, by decide⟩
    | 7 => .occ ⟨26, by decide⟩
    | 8 => .occ ⟨15, by decide⟩
    | 9 => .occ ⟨28, by decide⟩
    | 10 => .occ ⟨16, by decide⟩
    | 11 => .occ ⟨17, by decide⟩
    | 12 => .occ ⟨32, by decide⟩
    | 13 => .occ ⟨18, by decide⟩
    | 14 => .occ ⟨29, by decide⟩
    | 15 => .occ ⟨33, by decide⟩
    | 16 => .occ ⟨30, by decide⟩
    | 17 => .occ ⟨34, by decide⟩
    | 18 => .sumGe
    | 19 => .nonneg ⟨11, by decide⟩
    | 20 => .nonneg ⟨12, by decide⟩
    | 21 => .nonneg ⟨13, by decide⟩
    | 22 => .nonneg ⟨14, by decide⟩
    | 23 => .nonneg ⟨16, by decide⟩
    | 24 => .nonneg ⟨18, by decide⟩
    | 25 => .nonneg ⟨24, by decide⟩
    | 26 => .nonneg ⟨28, by decide⟩
    | 27 => .branchLe ⟨4, by decide⟩ 0
    | 28 => .branchLe ⟨22, by decide⟩ 0
    | 29 => .branchGe ⟨3, by decide⟩ 1
    | 30 => .branchGe ⟨7, by decide⟩ 1
    | _ => .sumGe

def mults_279_L2 : Fin 31 → Nat
  | i => match i.val with
    | 0 => 10
    | 1 => 10
    | 2 => 26
    | 3 => 6
    | 4 => 8
    | 5 => 16
    | 6 => 2
    | 7 => 1
    | 8 => 7
    | 9 => 1
    | 10 => 1
    | 11 => 3
    | 12 => 10
    | 13 => 4
    | 14 => 3
    | 15 => 7
    | 16 => 7
    | 17 => 8
    | 18 => 26
    | 19 => 8
    | 20 => 2
    | 21 => 20
    | 22 => 10
    | 23 => 10
    | 24 => 6
    | 25 => 8
    | 26 => 4
    | 27 => 26
    | 28 => 8
    | 29 => 26
    | 30 => 20
    | _ => 0

theorem coeff_cancel_279_L2 :
    ∀ j : Fin 31, (∑ i : Fin 31, (mults_279_L2 i : Int) * (refs_279_L2 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L2 :
    (∑ i : Fin 31, (mults_279_L2 i : Int) * (refs_279_L2 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf2_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_5_0 : x ⟨4, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_4_1 : (1 : Int) ≤ x ⟨3, by decide⟩)
    (h_ge_8_1 : (1 : Int) ≤ x ⟨7, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 31,
      (∑ j : Fin 31, (refs_279_L2 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L2 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_5_0]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_4_1]
    · simp only [refs_279_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_8_1]
  exact farkas_leaf_unsat _ _ (mults_279_L2) coeff_cancel_279_L2 rhs_neg_279_L2 x hrows

-- leaf 3, path LRLL, original Farkas rhs -4
def refs_279_L3 : Fin 32 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨21, by decide⟩
    | 1 => .occ ⟨35, by decide⟩
    | 2 => .occ ⟨22, by decide⟩
    | 3 => .occ ⟨36, by decide⟩
    | 4 => .occ ⟨4, by decide⟩
    | 5 => .occ ⟨5, by decide⟩
    | 6 => .occ ⟨37, by decide⟩
    | 7 => .occ ⟨38, by decide⟩
    | 8 => .occ ⟨11, by decide⟩
    | 9 => .occ ⟨31, by decide⟩
    | 10 => .occ ⟨12, by decide⟩
    | 11 => .occ ⟨39, by decide⟩
    | 12 => .occ ⟨26, by decide⟩
    | 13 => .occ ⟨28, by decide⟩
    | 14 => .occ ⟨40, by decide⟩
    | 15 => .occ ⟨16, by decide⟩
    | 16 => .occ ⟨17, by decide⟩
    | 17 => .occ ⟨41, by decide⟩
    | 18 => .occ ⟨29, by decide⟩
    | 19 => .occ ⟨42, by decide⟩
    | 20 => .occ ⟨33, by decide⟩
    | 21 => .occ ⟨43, by decide⟩
    | 22 => .occ ⟨34, by decide⟩
    | 23 => .sumGe
    | 24 => .nonneg ⟨11, by decide⟩
    | 25 => .nonneg ⟨13, by decide⟩
    | 26 => .nonneg ⟨14, by decide⟩
    | 27 => .nonneg ⟨29, by decide⟩
    | 28 => .branchLe ⟨2, by decide⟩ 1
    | 29 => .branchLe ⟨8, by decide⟩ 0
    | 30 => .branchLe ⟨22, by decide⟩ 0
    | 31 => .branchGe ⟨4, by decide⟩ 1
    | _ => .sumGe

def mults_279_L3 : Fin 32 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 28
    | 2 => 30
    | 3 => 36
    | 4 => 4
    | 5 => 150
    | 6 => 18
    | 7 => 13
    | 8 => 13
    | 9 => 39
    | 10 => 39
    | 11 => 48
    | 12 => 28
    | 13 => 15
    | 14 => 33
    | 15 => 42
    | 16 => 42
    | 17 => 18
    | 18 => 14
    | 19 => 34
    | 20 => 24
    | 21 => 26
    | 22 => 26
    | 23 => 154
    | 24 => 50
    | 25 => 124
    | 26 => 68
    | 27 => 42
    | 28 => 82
    | 29 => 114
    | 30 => 96
    | 31 => 18
    | _ => 0

theorem coeff_cancel_279_L3 :
    ∀ j : Fin 31, (∑ i : Fin 32, (mults_279_L3 i : Int) * (refs_279_L3 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L3 :
    (∑ i : Fin 32, (mults_279_L3 i : Int) * (refs_279_L3 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf3_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_3_1 : x ⟨2, by decide⟩ ≤ 1)
    (h_le_9_0 : x ⟨8, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 32,
      (∑ j : Fin 31, (refs_279_L3 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L3 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_3_1]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_9_0]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
    · simp only [refs_279_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_5_1]
  exact farkas_leaf_unsat _ _ (mults_279_L3) coeff_cancel_279_L3 rhs_neg_279_L3 x hrows

-- leaf 4, path LRLR, original Farkas rhs -4
def refs_279_L4 : Fin 23 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨5, by decide⟩
    | 2 => .occ ⟨38, by decide⟩
    | 3 => .occ ⟨24, by decide⟩
    | 4 => .occ ⟨10, by decide⟩
    | 5 => .occ ⟨11, by decide⟩
    | 6 => .occ ⟨44, by decide⟩
    | 7 => .occ ⟨26, by decide⟩
    | 8 => .occ ⟨15, by decide⟩
    | 9 => .occ ⟨27, by decide⟩
    | 10 => .occ ⟨28, by decide⟩
    | 11 => .occ ⟨40, by decide⟩
    | 12 => .occ ⟨16, by decide⟩
    | 13 => .occ ⟨17, by decide⟩
    | 14 => .occ ⟨18, by decide⟩
    | 15 => .occ ⟨19, by decide⟩
    | 16 => .sumGe
    | 17 => .nonneg ⟨13, by decide⟩
    | 18 => .nonneg ⟨28, by decide⟩
    | 19 => .nonneg ⟨29, by decide⟩
    | 20 => .branchLe ⟨8, by decide⟩ 0
    | 21 => .branchLe ⟨22, by decide⟩ 0
    | 22 => .branchGe ⟨2, by decide⟩ 2
    | _ => .sumGe

def mults_279_L4 : Fin 23 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 8
    | 2 => 3
    | 3 => 1
    | 4 => 1
    | 5 => 3
    | 6 => 4
    | 7 => 4
    | 8 => 9
    | 9 => 3
    | 10 => 7
    | 11 => 9
    | 12 => 2
    | 13 => 2
    | 14 => 4
    | 15 => 4
    | 16 => 12
    | 17 => 8
    | 18 => 16
    | 19 => 24
    | 20 => 8
    | 21 => 8
    | 22 => 24
    | _ => 0

theorem coeff_cancel_279_L4 :
    ∀ j : Fin 31, (∑ i : Fin 23, (mults_279_L4 i : Int) * (refs_279_L4 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L4 :
    (∑ i : Fin 23, (mults_279_L4 i : Int) * (refs_279_L4 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf4_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_9_0 : x ⟨8, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_3_2 : (2 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 23,
      (∑ j : Fin 31, (refs_279_L4 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L4 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_9_0]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
    · simp only [refs_279_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_3_2]
  exact farkas_leaf_unsat _ _ (mults_279_L4) coeff_cancel_279_L4 rhs_neg_279_L4 x hrows

-- leaf 5, path LRRLL, original Farkas rhs -24
def refs_279_L5 : Fin 31 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨22, by decide⟩
    | 1 => .occ ⟨3, by decide⟩
    | 2 => .occ ⟨45, by decide⟩
    | 3 => .occ ⟨46, by decide⟩
    | 4 => .occ ⟨4, by decide⟩
    | 5 => .occ ⟨5, by decide⟩
    | 6 => .occ ⟨31, by decide⟩
    | 7 => .occ ⟨47, by decide⟩
    | 8 => .occ ⟨48, by decide⟩
    | 9 => .occ ⟨28, by decide⟩
    | 10 => .occ ⟨40, by decide⟩
    | 11 => .occ ⟨16, by decide⟩
    | 12 => .occ ⟨17, by decide⟩
    | 13 => .occ ⟨41, by decide⟩
    | 14 => .occ ⟨49, by decide⟩
    | 15 => .occ ⟨32, by decide⟩
    | 16 => .occ ⟨29, by decide⟩
    | 17 => .occ ⟨42, by decide⟩
    | 18 => .occ ⟨33, by decide⟩
    | 19 => .occ ⟨50, by decide⟩
    | 20 => .occ ⟨43, by decide⟩
    | 21 => .occ ⟨34, by decide⟩
    | 22 => .sumGe
    | 23 => .nonneg ⟨12, by decide⟩
    | 24 => .nonneg ⟨14, by decide⟩
    | 25 => .nonneg ⟨16, by decide⟩
    | 26 => .nonneg ⟨18, by decide⟩
    | 27 => .nonneg ⟨29, by decide⟩
    | 28 => .branchLe ⟨2, by decide⟩ 1
    | 29 => .branchLe ⟨15, by decide⟩ 0
    | 30 => .branchLe ⟨22, by decide⟩ 0
    | _ => .sumGe

def mults_279_L5 : Fin 31 → Nat
  | i => match i.val with
    | 0 => 32
    | 1 => 16
    | 2 => 24
    | 3 => 8
    | 4 => 40
    | 5 => 88
    | 6 => 10
    | 7 => 6
    | 8 => 16
    | 9 => 6
    | 10 => 18
    | 11 => 20
    | 12 => 28
    | 13 => 14
    | 14 => 8
    | 15 => 26
    | 16 => 43
    | 17 => 53
    | 18 => 26
    | 19 => 14
    | 20 => 23
    | 21 => 9
    | 22 => 128
    | 23 => 96
    | 24 => 112
    | 25 => 48
    | 26 => 16
    | 27 => 32
    | 28 => 64
    | 29 => 112
    | 30 => 48
    | _ => 0

theorem coeff_cancel_279_L5 :
    ∀ j : Fin 31, (∑ i : Fin 31, (mults_279_L5 i : Int) * (refs_279_L5 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L5 :
    (∑ i : Fin 31, (mults_279_L5 i : Int) * (refs_279_L5 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf5_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_3_1 : x ⟨2, by decide⟩ ≤ 1)
    (h_le_16_0 : x ⟨15, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 31,
      (∑ j : Fin 31, (refs_279_L5 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L5 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_3_1]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_16_0]
    · simp only [refs_279_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
  exact farkas_leaf_unsat _ _ (mults_279_L5) coeff_cancel_279_L5 rhs_neg_279_L5 x hrows

-- leaf 6, path LRRLR, original Farkas rhs -6
def refs_279_L6 : Fin 21 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨5, by decide⟩
    | 2 => .occ ⟨24, by decide⟩
    | 3 => .occ ⟨10, by decide⟩
    | 4 => .occ ⟨15, by decide⟩
    | 5 => .occ ⟨27, by decide⟩
    | 6 => .occ ⟨28, by decide⟩
    | 7 => .occ ⟨40, by decide⟩
    | 8 => .occ ⟨18, by decide⟩
    | 9 => .occ ⟨42, by decide⟩
    | 10 => .occ ⟨50, by decide⟩
    | 11 => .occ ⟨43, by decide⟩
    | 12 => .occ ⟨34, by decide⟩
    | 13 => .sumGe
    | 14 => .nonneg ⟨12, by decide⟩
    | 15 => .nonneg ⟨13, by decide⟩
    | 16 => .nonneg ⟨16, by decide⟩
    | 17 => .nonneg ⟨28, by decide⟩
    | 18 => .nonneg ⟨29, by decide⟩
    | 19 => .branchLe ⟨15, by decide⟩ 0
    | 20 => .branchGe ⟨2, by decide⟩ 2
    | _ => .sumGe

def mults_279_L6 : Fin 21 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 4
    | 2 => 2
    | 3 => 2
    | 4 => 5
    | 5 => 3
    | 6 => 5
    | 7 => 3
    | 8 => 6
    | 9 => 2
    | 10 => 2
    | 11 => 1
    | 12 => 1
    | 13 => 8
    | 14 => 4
    | 15 => 4
    | 16 => 8
    | 17 => 12
    | 18 => 12
    | 19 => 8
    | 20 => 16
    | _ => 0

theorem coeff_cancel_279_L6 :
    ∀ j : Fin 31, (∑ i : Fin 21, (mults_279_L6 i : Int) * (refs_279_L6 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L6 :
    (∑ i : Fin 21, (mults_279_L6 i : Int) * (refs_279_L6 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf6_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_16_0 : x ⟨15, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_3_2 : (2 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 21,
      (∑ j : Fin 31, (refs_279_L6 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L6 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_16_0]
    · simp only [refs_279_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_3_2]
  exact farkas_leaf_unsat _ _ (mults_279_L6) coeff_cancel_279_L6 rhs_neg_279_L6 x hrows

-- leaf 7, path LRRRLL, original Farkas rhs -2
def refs_279_L7 : Fin 18 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨5, by decide⟩
    | 1 => .occ ⟨51, by decide⟩
    | 2 => .occ ⟨31, by decide⟩
    | 3 => .occ ⟨47, by decide⟩
    | 4 => .occ ⟨12, by decide⟩
    | 5 => .occ ⟨25, by decide⟩
    | 6 => .occ ⟨30, by decide⟩
    | 7 => .occ ⟨52, by decide⟩
    | 8 => .occ ⟨43, by decide⟩
    | 9 => .occ ⟨34, by decide⟩
    | 10 => .sumGe
    | 11 => .nonneg ⟨11, by decide⟩
    | 12 => .nonneg ⟨13, by decide⟩
    | 13 => .nonneg ⟨18, by decide⟩
    | 14 => .nonneg ⟨28, by decide⟩
    | 15 => .branchLe ⟨1, by decide⟩ 1
    | 16 => .branchLe ⟨17, by decide⟩ 0
    | 17 => .branchGe ⟨15, by decide⟩ 1
    | _ => .sumGe

def mults_279_L7 : Fin 18 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 2
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 2
    | 7 => 2
    | 8 => 1
    | 9 => 1
    | 10 => 4
    | 11 => 2
    | 12 => 8
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 4
    | 17 => 4
    | _ => 0

theorem coeff_cancel_279_L7 :
    ∀ j : Fin 31, (∑ i : Fin 18, (mults_279_L7 i : Int) * (refs_279_L7 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L7 :
    (∑ i : Fin 18, (mults_279_L7 i : Int) * (refs_279_L7 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf7_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 18,
      (∑ j : Fin 31, (refs_279_L7 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L7 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨51, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_279_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_16_1]
  exact farkas_leaf_unsat _ _ (mults_279_L7) coeff_cancel_279_L7 rhs_neg_279_L7 x hrows

-- leaf 8, path LRRRLRL, original Farkas rhs -2
def refs_279_L8 : Fin 22 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨22, by decide⟩
    | 1 => .occ ⟨0, by decide⟩
    | 2 => .occ ⟨36, by decide⟩
    | 3 => .occ ⟨1, by decide⟩
    | 4 => .occ ⟨5, by decide⟩
    | 5 => .occ ⟨10, by decide⟩
    | 6 => .occ ⟨11, by decide⟩
    | 7 => .occ ⟨31, by decide⟩
    | 8 => .occ ⟨47, by decide⟩
    | 9 => .occ ⟨12, by decide⟩
    | 10 => .occ ⟨13, by decide⟩
    | 11 => .occ ⟨39, by decide⟩
    | 12 => .occ ⟨16, by decide⟩
    | 13 => .occ ⟨17, by decide⟩
    | 14 => .occ ⟨32, by decide⟩
    | 15 => .occ ⟨42, by decide⟩
    | 16 => .occ ⟨43, by decide⟩
    | 17 => .sumGe
    | 18 => .nonneg ⟨13, by decide⟩
    | 19 => .nonneg ⟨14, by decide⟩
    | 20 => .branchLe ⟨2, by decide⟩ 0
    | 21 => .branchLe ⟨22, by decide⟩ 0
    | _ => .sumGe

def mults_279_L8 : Fin 22 → Nat
  | i => match i.val with
    | 0 => 2
    | 1 => 2
    | 2 => 2
    | 3 => 2
    | 4 => 4
    | 5 => 1
    | 6 => 1
    | 7 => 1
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 1
    | 12 => 1
    | 13 => 1
    | 14 => 1
    | 15 => 1
    | 16 => 1
    | 17 => 4
    | 18 => 2
    | 19 => 2
    | 20 => 4
    | 21 => 4
    | _ => 0

theorem coeff_cancel_279_L8 :
    ∀ j : Fin 31, (∑ i : Fin 22, (mults_279_L8 i : Int) * (refs_279_L8 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L8 :
    (∑ i : Fin 22, (mults_279_L8 i : Int) * (refs_279_L8 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf8_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_3_0 : x ⟨2, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 22,
      (∑ j : Fin 31, (refs_279_L8 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L8 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_3_0]
    · simp only [refs_279_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
  exact farkas_leaf_unsat _ _ (mults_279_L8) coeff_cancel_279_L8 rhs_neg_279_L8 x hrows

-- leaf 9, path LRRRLRRLLL, original Farkas rhs -1
def refs_279_L9 : Fin 20 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨21, by decide⟩
    | 1 => .occ ⟨35, by decide⟩
    | 2 => .occ ⟨22, by decide⟩
    | 3 => .occ ⟨0, by decide⟩
    | 4 => .occ ⟨1, by decide⟩
    | 5 => .occ ⟨45, by decide⟩
    | 6 => .occ ⟨5, by decide⟩
    | 7 => .occ ⟨47, by decide⟩
    | 8 => .occ ⟨25, by decide⟩
    | 9 => .occ ⟨41, by decide⟩
    | 10 => .occ ⟨32, by decide⟩
    | 11 => .occ ⟨33, by decide⟩
    | 12 => .sumGe
    | 13 => .nonneg ⟨11, by decide⟩
    | 14 => .nonneg ⟨14, by decide⟩
    | 15 => .branchLe ⟨1, by decide⟩ 1
    | 16 => .branchLe ⟨2, by decide⟩ 1
    | 17 => .branchLe ⟨19, by decide⟩ 0
    | 18 => .branchLe ⟨23, by decide⟩ 0
    | 19 => .branchGe ⟨17, by decide⟩ 1
    | _ => .sumGe

def mults_279_L9 : Fin 20 → Nat
  | i => match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => 1
    | 3 => 1
    | 4 => 2
    | 5 => 2
    | 6 => 2
    | 7 => 1
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 1
    | 12 => 2
    | 13 => 1
    | 14 => 1
    | 15 => 2
    | 16 => 1
    | 17 => 2
    | 18 => 2
    | 19 => 1
    | _ => 0

theorem coeff_cancel_279_L9 :
    ∀ j : Fin 31, (∑ i : Fin 20, (mults_279_L9 i : Int) * (refs_279_L9 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L9 :
    (∑ i : Fin 20, (mults_279_L9 i : Int) * (refs_279_L9 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf9_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_3_1 : x ⟨2, by decide⟩ ≤ 1)
    (h_le_20_0 : x ⟨19, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_le_24_0 : x ⟨23, by decide⟩ ≤ 0)
    (h_ge_3_1 : (1 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 20,
      (∑ j : Fin 31, (refs_279_L9 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L9 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_3_1]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_20_0]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_24_0]
    · simp only [refs_279_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_18_1]
  exact farkas_leaf_unsat _ _ (mults_279_L9) coeff_cancel_279_L9 rhs_neg_279_L9 x hrows

-- leaf 10, path LRRRLRRLLR, original Farkas rhs -2
def refs_279_L10 : Fin 25 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨5, by decide⟩
    | 2 => .occ ⟨10, by decide⟩
    | 3 => .occ ⟨31, by decide⟩
    | 4 => .occ ⟨47, by decide⟩
    | 5 => .occ ⟨53, by decide⟩
    | 6 => .occ ⟨28, by decide⟩
    | 7 => .occ ⟨16, by decide⟩
    | 8 => .occ ⟨32, by decide⟩
    | 9 => .occ ⟨52, by decide⟩
    | 10 => .occ ⟨50, by decide⟩
    | 11 => .sumGe
    | 12 => .nonneg ⟨11, by decide⟩
    | 13 => .nonneg ⟨12, by decide⟩
    | 14 => .nonneg ⟨13, by decide⟩
    | 15 => .nonneg ⟨20, by decide⟩
    | 16 => .nonneg ⟨29, by decide⟩
    | 17 => .branchLe ⟨1, by decide⟩ 1
    | 18 => .branchLe ⟨19, by decide⟩ 0
    | 19 => .branchLe ⟨22, by decide⟩ 0
    | 20 => .branchGe ⟨4, by decide⟩ 1
    | 21 => .branchGe ⟨8, by decide⟩ 1
    | 22 => .branchGe ⟨15, by decide⟩ 1
    | 23 => .branchGe ⟨17, by decide⟩ 1
    | 24 => .branchGe ⟨23, by decide⟩ 1
    | _ => .sumGe

def mults_279_L10 : Fin 25 → Nat
  | i => match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => 2
    | 3 => 1
    | 4 => 2
    | 5 => 1
    | 6 => 1
    | 7 => 2
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 3
    | 12 => 2
    | 13 => 2
    | 14 => 1
    | 15 => 2
    | 16 => 1
    | 17 => 1
    | 18 => 1
    | 19 => 2
    | 20 => 1
    | 21 => 3
    | 22 => 2
    | 23 => 1
    | 24 => 5
    | _ => 0

theorem coeff_cancel_279_L10 :
    ∀ j : Fin 31, (∑ i : Fin 25, (mults_279_L10 i : Int) * (refs_279_L10 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L10 :
    (∑ i : Fin 25, (mults_279_L10 i : Int) * (refs_279_L10 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf10_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_3_1 : x ⟨2, by decide⟩ ≤ 1)
    (h_le_20_0 : x ⟨19, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_3_1 : (1 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    (h_ge_24_1 : (1 : Int) ≤ x ⟨23, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 25,
      (∑ j : Fin 31, (refs_279_L10 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L10 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨53, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_20_0]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_23_0]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_5_1]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_9_1]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_16_1]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_18_1]
    · simp only [refs_279_L10, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_24_1]
  exact farkas_leaf_unsat _ _ (mults_279_L10) coeff_cancel_279_L10 rhs_neg_279_L10 x hrows

-- leaf 11, path LRRRLRRLR, original Farkas rhs -4
def refs_279_L11 : Fin 18 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨5, by decide⟩
    | 2 => .occ ⟨18, by decide⟩
    | 3 => .occ ⟨33, by decide⟩
    | 4 => .occ ⟨30, by decide⟩
    | 5 => .occ ⟨52, by decide⟩
    | 6 => .occ ⟨50, by decide⟩
    | 7 => .sumGe
    | 8 => .nonneg ⟨12, by decide⟩
    | 9 => .nonneg ⟨13, by decide⟩
    | 10 => .nonneg ⟨16, by decide⟩
    | 11 => .nonneg ⟨18, by decide⟩
    | 12 => .nonneg ⟨28, by decide⟩
    | 13 => .nonneg ⟨29, by decide⟩
    | 14 => .branchLe ⟨1, by decide⟩ 1
    | 15 => .branchGe ⟨2, by decide⟩ 2
    | 16 => .branchGe ⟨15, by decide⟩ 1
    | 17 => .branchGe ⟨17, by decide⟩ 1
    | _ => .sumGe

def mults_279_L11 : Fin 18 → Nat
  | i => match i.val with
    | 0 => 2
    | 1 => 2
    | 2 => 4
    | 3 => 1
    | 4 => 3
    | 5 => 3
    | 6 => 1
    | 7 => 4
    | 8 => 8
    | 9 => 8
    | 10 => 2
    | 11 => 2
    | 12 => 4
    | 13 => 4
    | 14 => 4
    | 15 => 8
    | 16 => 2
    | 17 => 2
    | _ => 0

theorem coeff_cancel_279_L11 :
    ∀ j : Fin 31, (∑ i : Fin 18, (mults_279_L11 i : Int) * (refs_279_L11 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L11 :
    (∑ i : Fin 18, (mults_279_L11 i : Int) * (refs_279_L11 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf11_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_20_0 : x ⟨19, by decide⟩ ≤ 0)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_3_2 : (2 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 18,
      (∑ j : Fin 31, (refs_279_L11 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L11 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_3_2]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_16_1]
    · simp only [refs_279_L11, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_18_1]
  exact farkas_leaf_unsat _ _ (mults_279_L11) coeff_cancel_279_L11 rhs_neg_279_L11 x hrows

-- leaf 12, path LRRRLRRR, original Farkas rhs -4
def refs_279_L12 : Fin 32 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨5, by decide⟩
    | 1 => .occ ⟨38, by decide⟩
    | 2 => .occ ⟨31, by decide⟩
    | 3 => .occ ⟨47, by decide⟩
    | 4 => .occ ⟨44, by decide⟩
    | 5 => .occ ⟨39, by decide⟩
    | 6 => .occ ⟨15, by decide⟩
    | 7 => .occ ⟨17, by decide⟩
    | 8 => .occ ⟨41, by decide⟩
    | 9 => .occ ⟨32, by decide⟩
    | 10 => .occ ⟨30, by decide⟩
    | 11 => .occ ⟨52, by decide⟩
    | 12 => .occ ⟨50, by decide⟩
    | 13 => .occ ⟨43, by decide⟩
    | 14 => .sumGe
    | 15 => .nonneg ⟨11, by decide⟩
    | 16 => .nonneg ⟨12, by decide⟩
    | 17 => .nonneg ⟨13, by decide⟩
    | 18 => .nonneg ⟨14, by decide⟩
    | 19 => .nonneg ⟨16, by decide⟩
    | 20 => .nonneg ⟨18, by decide⟩
    | 21 => .nonneg ⟨22, by decide⟩
    | 22 => .nonneg ⟨23, by decide⟩
    | 23 => .nonneg ⟨24, by decide⟩
    | 24 => .nonneg ⟨28, by decide⟩
    | 25 => .nonneg ⟨29, by decide⟩
    | 26 => .branchLe ⟨1, by decide⟩ 1
    | 27 => .branchGe ⟨4, by decide⟩ 1
    | 28 => .branchGe ⟨8, by decide⟩ 1
    | 29 => .branchGe ⟨15, by decide⟩ 1
    | 30 => .branchGe ⟨17, by decide⟩ 1
    | 31 => .branchGe ⟨19, by decide⟩ 1
    | _ => .sumGe

def mults_279_L12 : Fin 32 → Nat
  | i => match i.val with
    | 0 => 11
    | 1 => 6
    | 2 => 5
    | 3 => 6
    | 4 => 2
    | 5 => 3
    | 6 => 1
    | 7 => 4
    | 8 => 4
    | 9 => 1
    | 10 => 3
    | 11 => 1
    | 12 => 6
    | 13 => 2
    | 14 => 11
    | 15 => 8
    | 16 => 2
    | 17 => 11
    | 18 => 6
    | 19 => 3
    | 20 => 1
    | 21 => 2
    | 22 => 3
    | 23 => 2
    | 24 => 2
    | 25 => 5
    | 26 => 3
    | 27 => 17
    | 28 => 7
    | 29 => 9
    | 30 => 4
    | 31 => 17
    | _ => 0

theorem coeff_cancel_279_L12 :
    ∀ j : Fin 31, (∑ i : Fin 32, (mults_279_L12 i : Int) * (refs_279_L12 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L12 :
    (∑ i : Fin 32, (mults_279_L12 i : Int) * (refs_279_L12 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf12_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_3_1 : (1 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    (h_ge_20_1 : (1 : Int) ≤ x ⟨19, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 32,
      (∑ j : Fin 31, (refs_279_L12 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L12 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨23, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_5_1]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_9_1]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_16_1]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_18_1]
    · simp only [refs_279_L12, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_20_1]
  exact farkas_leaf_unsat _ _ (mults_279_L12) coeff_cancel_279_L12 rhs_neg_279_L12 x hrows

-- leaf 13, path LRRRR, original Farkas rhs -2
def refs_279_L13 : Fin 17 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨38, by decide⟩
    | 2 => .occ ⟨24, by decide⟩
    | 3 => .occ ⟨10, by decide⟩
    | 4 => .occ ⟨11, by decide⟩
    | 5 => .occ ⟨26, by decide⟩
    | 6 => .occ ⟨19, by decide⟩
    | 7 => .occ ⟨20, by decide⟩
    | 8 => .occ ⟨30, by decide⟩
    | 9 => .occ ⟨52, by decide⟩
    | 10 => .sumGe
    | 11 => .nonneg ⟨11, by decide⟩
    | 12 => .nonneg ⟨12, by decide⟩
    | 13 => .nonneg ⟨16, by decide⟩
    | 14 => .nonneg ⟨18, by decide⟩
    | 15 => .branchGe ⟨1, by decide⟩ 2
    | 16 => .branchGe ⟨15, by decide⟩ 1
    | _ => .sumGe

def mults_279_L13 : Fin 17 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 3
    | 2 => 3
    | 3 => 3
    | 4 => 3
    | 5 => 2
    | 6 => 2
    | 7 => 2
    | 8 => 1
    | 9 => 1
    | 10 => 4
    | 11 => 4
    | 12 => 4
    | 13 => 8
    | 14 => 12
    | 15 => 12
    | 16 => 4
    | _ => 0

theorem coeff_cancel_279_L13 :
    ∀ j : Fin 31, (∑ i : Fin 17, (mults_279_L13 i : Int) * (refs_279_L13 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L13 :
    (∑ i : Fin 17, (mults_279_L13 i : Int) * (refs_279_L13 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf13_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_23_0 : x ⟨22, by decide⟩ ≤ 0)
    (h_ge_2_2 : (2 : Int) ≤ x ⟨1, by decide⟩)
    (h_ge_5_1 : (1 : Int) ≤ x ⟨4, by decide⟩)
    (h_ge_9_1 : (1 : Int) ≤ x ⟨8, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 17,
      (∑ j : Fin 31, (refs_279_L13 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L13 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_2_2]
    · simp only [refs_279_L13, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_16_1]
  exact farkas_leaf_unsat _ _ (mults_279_L13) coeff_cancel_279_L13 rhs_neg_279_L13 x hrows

-- leaf 14, path RLL, original Farkas rhs -4
def refs_279_L14 : Fin 31 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨35, by decide⟩
    | 1 => .occ ⟨22, by decide⟩
    | 2 => .occ ⟨5, by decide⟩
    | 3 => .occ ⟨54, by decide⟩
    | 4 => .occ ⟨55, by decide⟩
    | 5 => .occ ⟨38, by decide⟩
    | 6 => .occ ⟨24, by decide⟩
    | 7 => .occ ⟨10, by decide⟩
    | 8 => .occ ⟨47, by decide⟩
    | 9 => .occ ⟨12, by decide⟩
    | 10 => .occ ⟨25, by decide⟩
    | 11 => .occ ⟨53, by decide⟩
    | 12 => .occ ⟨56, by decide⟩
    | 13 => .occ ⟨26, by decide⟩
    | 14 => .occ ⟨15, by decide⟩
    | 15 => .occ ⟨27, by decide⟩
    | 16 => .occ ⟨16, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨57, by decide⟩
    | 19 => .occ ⟨41, by decide⟩
    | 20 => .occ ⟨29, by decide⟩
    | 21 => .occ ⟨42, by decide⟩
    | 22 => .sumGe
    | 23 => .nonneg ⟨11, by decide⟩
    | 24 => .nonneg ⟨12, by decide⟩
    | 25 => .nonneg ⟨13, by decide⟩
    | 26 => .nonneg ⟨14, by decide⟩
    | 27 => .nonneg ⟨29, by decide⟩
    | 28 => .branchLe ⟨2, by decide⟩ 1
    | 29 => .branchLe ⟨3, by decide⟩ 0
    | 30 => .branchGe ⟨22, by decide⟩ 1
    | _ => .sumGe

def mults_279_L14 : Fin 31 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 36
    | 2 => 60
    | 3 => 12
    | 4 => 36
    | 5 => 11
    | 6 => 7
    | 7 => 18
    | 8 => 18
    | 9 => 9
    | 10 => 9
    | 11 => 16
    | 12 => 4
    | 13 => 4
    | 14 => 9
    | 15 => 15
    | 16 => 21
    | 17 => 19
    | 18 => 4
    | 19 => 16
    | 20 => 5
    | 21 => 15
    | 22 => 60
    | 23 => 16
    | 24 => 28
    | 25 => 28
    | 26 => 20
    | 27 => 8
    | 28 => 36
    | 29 => 48
    | 30 => 48
    | _ => 0

theorem coeff_cancel_279_L14 :
    ∀ j : Fin 31, (∑ i : Fin 31, (mults_279_L14 i : Int) * (refs_279_L14 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L14 :
    (∑ i : Fin 31, (mults_279_L14 i : Int) * (refs_279_L14 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf14_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_3_1 : x ⟨2, by decide⟩ ≤ 1)
    (h_le_4_0 : x ⟨3, by decide⟩ ≤ 0)
    (h_ge_23_1 : (1 : Int) ≤ x ⟨22, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 31,
      (∑ j : Fin 31, (refs_279_L14 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L14 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨53, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_3_1]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_4_0]
    · simp only [refs_279_L14, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_23_1]
  exact farkas_leaf_unsat _ _ (mults_279_L14) coeff_cancel_279_L14 rhs_neg_279_L14 x hrows

-- leaf 15, path RLR, original Farkas rhs -8
def refs_279_L15 : Fin 30 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨35, by decide⟩
    | 1 => .occ ⟨4, by decide⟩
    | 2 => .occ ⟨5, by decide⟩
    | 3 => .occ ⟨54, by decide⟩
    | 4 => .occ ⟨38, by decide⟩
    | 5 => .occ ⟨24, by decide⟩
    | 6 => .occ ⟨58, by decide⟩
    | 7 => .occ ⟨10, by decide⟩
    | 8 => .occ ⟨59, by decide⟩
    | 9 => .occ ⟨11, by decide⟩
    | 10 => .occ ⟨25, by decide⟩
    | 11 => .occ ⟨56, by decide⟩
    | 12 => .occ ⟨26, by decide⟩
    | 13 => .occ ⟨15, by decide⟩
    | 14 => .occ ⟨27, by decide⟩
    | 15 => .occ ⟨28, by decide⟩
    | 16 => .occ ⟨40, by decide⟩
    | 17 => .occ ⟨16, by decide⟩
    | 18 => .occ ⟨18, by decide⟩
    | 19 => .occ ⟨19, by decide⟩
    | 20 => .occ ⟨20, by decide⟩
    | 21 => .sumGe
    | 22 => .nonneg ⟨12, by decide⟩
    | 23 => .nonneg ⟨13, by decide⟩
    | 24 => .nonneg ⟨26, by decide⟩
    | 25 => .nonneg ⟨28, by decide⟩
    | 26 => .nonneg ⟨29, by decide⟩
    | 27 => .branchLe ⟨3, by decide⟩ 0
    | 28 => .branchGe ⟨2, by decide⟩ 2
    | 29 => .branchGe ⟨22, by decide⟩ 1
    | _ => .sumGe

def mults_279_L15 : Fin 30 → Nat
  | i => match i.val with
    | 0 => 6
    | 1 => 10
    | 2 => 10
    | 3 => 8
    | 4 => 3
    | 5 => 3
    | 6 => 1
    | 7 => 1
    | 8 => 2
    | 9 => 4
    | 10 => 3
    | 11 => 4
    | 12 => 4
    | 13 => 17
    | 14 => 16
    | 15 => 10
    | 16 => 18
    | 17 => 1
    | 18 => 10
    | 19 => 4
    | 20 => 6
    | 21 => 21
    | 22 => 16
    | 23 => 10
    | 24 => 4
    | 25 => 46
    | 26 => 48
    | 27 => 8
    | 28 => 56
    | 29 => 16
    | _ => 0

theorem coeff_cancel_279_L15 :
    ∀ j : Fin 31, (∑ i : Fin 30, (mults_279_L15 i : Int) * (refs_279_L15 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L15 :
    (∑ i : Fin 30, (mults_279_L15 i : Int) * (refs_279_L15 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf15_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_4_0 : x ⟨3, by decide⟩ ≤ 0)
    (h_ge_3_2 : (2 : Int) ≤ x ⟨2, by decide⟩)
    (h_ge_23_1 : (1 : Int) ≤ x ⟨22, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 30,
      (∑ j : Fin 31, (refs_279_L15 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L15 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨58, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨59, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_4_0]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_3_2]
    · simp only [refs_279_L15, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_23_1]
  exact farkas_leaf_unsat _ _ (mults_279_L15) coeff_cancel_279_L15 rhs_neg_279_L15 x hrows

-- leaf 16, path RRL, original Farkas rhs -1
def refs_279_L16 : Fin 18 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨4, by decide⟩
    | 1 => .occ ⟨5, by decide⟩
    | 2 => .occ ⟨7, by decide⟩
    | 3 => .occ ⟨24, by decide⟩
    | 4 => .occ ⟨60, by decide⟩
    | 5 => .occ ⟨25, by decide⟩
    | 6 => .occ ⟨15, by decide⟩
    | 7 => .occ ⟨27, by decide⟩
    | 8 => .occ ⟨41, by decide⟩
    | 9 => .occ ⟨32, by decide⟩
    | 10 => .occ ⟨30, by decide⟩
    | 11 => .sumGe
    | 12 => .nonneg ⟨12, by decide⟩
    | 13 => .nonneg ⟨18, by decide⟩
    | 14 => .nonneg ⟨20, by decide⟩
    | 15 => .branchLe ⟨23, by decide⟩ 0
    | 16 => .branchGe ⟨3, by decide⟩ 1
    | 17 => .branchGe ⟨22, by decide⟩ 1
    | _ => .sumGe

def mults_279_L16 : Fin 18 → Nat
  | i => match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => 1
    | 3 => 3
    | 4 => 1
    | 5 => 2
    | 6 => 1
    | 7 => 1
    | 8 => 2
    | 9 => 1
    | 10 => 1
    | 11 => 3
    | 12 => 3
    | 13 => 2
    | 14 => 1
    | 15 => 3
    | 16 => 2
    | 17 => 6
    | _ => 0

theorem coeff_cancel_279_L16 :
    ∀ j : Fin 31, (∑ i : Fin 18, (mults_279_L16 i : Int) * (refs_279_L16 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L16 :
    (∑ i : Fin 18, (mults_279_L16 i : Int) * (refs_279_L16 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf16_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_le_24_0 : x ⟨23, by decide⟩ ≤ 0)
    (h_ge_4_1 : (1 : Int) ≤ x ⟨3, by decide⟩)
    (h_ge_23_1 : (1 : Int) ≤ x ⟨22, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 18,
      (∑ j : Fin 31, (refs_279_L16 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L16 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_24_0]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_4_1]
    · simp only [refs_279_L16, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_23_1]
  exact farkas_leaf_unsat _ _ (mults_279_L16) coeff_cancel_279_L16 rhs_neg_279_L16 x hrows

-- leaf 17, path RRR, original Farkas rhs -3
def refs_279_L17 : Fin 29 → RowRef 64 31
  | i => match i.val with
    | 0 => .occ ⟨5, by decide⟩
    | 1 => .occ ⟨55, by decide⟩
    | 2 => .occ ⟨24, by decide⟩
    | 3 => .occ ⟨58, by decide⟩
    | 4 => .occ ⟨31, by decide⟩
    | 5 => .occ ⟨61, by decide⟩
    | 6 => .occ ⟨62, by decide⟩
    | 7 => .occ ⟨15, by decide⟩
    | 8 => .occ ⟨40, by decide⟩
    | 9 => .occ ⟨16, by decide⟩
    | 10 => .occ ⟨63, by decide⟩
    | 11 => .occ ⟨41, by decide⟩
    | 12 => .occ ⟨32, by decide⟩
    | 13 => .occ ⟨20, by decide⟩
    | 14 => .occ ⟨30, by decide⟩
    | 15 => .occ ⟨43, by decide⟩
    | 16 => .sumGe
    | 17 => .nonneg ⟨11, by decide⟩
    | 18 => .nonneg ⟨12, by decide⟩
    | 19 => .nonneg ⟨13, by decide⟩
    | 20 => .nonneg ⟨14, by decide⟩
    | 21 => .nonneg ⟨16, by decide⟩
    | 22 => .nonneg ⟨18, by decide⟩
    | 23 => .nonneg ⟨20, by decide⟩
    | 24 => .nonneg ⟨25, by decide⟩
    | 25 => .nonneg ⟨28, by decide⟩
    | 26 => .branchGe ⟨3, by decide⟩ 1
    | 27 => .branchGe ⟨22, by decide⟩ 1
    | 28 => .branchGe ⟨23, by decide⟩ 1
    | _ => .sumGe

def mults_279_L17 : Fin 29 → Nat
  | i => match i.val with
    | 0 => 8
    | 1 => 10
    | 2 => 11
    | 3 => 5
    | 4 => 4
    | 5 => 9
    | 6 => 4
    | 7 => 3
    | 8 => 2
    | 9 => 1
    | 10 => 3
    | 11 => 6
    | 12 => 1
    | 13 => 1
    | 14 => 8
    | 15 => 1
    | 16 => 13
    | 17 => 2
    | 18 => 4
    | 19 => 12
    | 20 => 14
    | 21 => 2
    | 22 => 16
    | 23 => 2
    | 24 => 2
    | 25 => 6
    | 26 => 20
    | 27 => 40
    | 28 => 16
    | _ => 0

theorem coeff_cancel_279_L17 :
    ∀ j : Fin 31, (∑ i : Fin 29, (mults_279_L17 i : Int) * (refs_279_L17 i).resolveCoeff S_279 j) = 0 := by
  decide

theorem rhs_neg_279_L17 :
    (∑ i : Fin 29, (mults_279_L17 i : Int) * (refs_279_L17 i).resolveRhs S_279) < 0 := by
  decide

theorem leaf17_infeasible_279 (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x)
    (h_ge_4_1 : (1 : Int) ≤ x ⟨3, by decide⟩)
    (h_ge_23_1 : (1 : Int) ≤ x ⟨22, by decide⟩)
    (h_ge_24_1 : (1 : Int) ≤ x ⟨23, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 29,
      (∑ j : Fin 31, (refs_279_L17 i).resolveCoeff S_279 j * x j) ≤
      (refs_279_L17 i).resolveRhs S_279 := by
    intro i; fin_cases i
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨58, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨13, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_4_1]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_23_1]
    · simp only [refs_279_L17, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_24_1]
  exact farkas_leaf_unsat _ _ (mults_279_L17) coeff_cancel_279_L17 rhs_neg_279_L17 x hrows

theorem orbit279_occupation_no_model (x : Fin 31 → Int)
    (hroot : S_279.RootHolds x) : False := by
  by_cases hbr_root_23_0 : x ⟨22, by decide⟩ ≤ 0
  ·
    by_cases hbr_L_5_0 : x ⟨4, by decide⟩ ≤ 0
    ·
      by_cases hbr_LL_4_0 : x ⟨3, by decide⟩ ≤ 0
      ·
        exact leaf0_infeasible_279 x hroot hbr_LL_4_0 hbr_L_5_0 hbr_root_23_0
      ·
        have hbr_LL_4_0_ge : (1 : Int) ≤ x ⟨3, by decide⟩ := by omega
        by_cases hbr_LLR_8_0 : x ⟨7, by decide⟩ ≤ 0
        ·
          exact leaf1_infeasible_279 x hroot hbr_L_5_0 hbr_LLR_8_0 hbr_root_23_0 hbr_LL_4_0_ge
        ·
          have hbr_LLR_8_0_ge : (1 : Int) ≤ x ⟨7, by decide⟩ := by omega
          exact leaf2_infeasible_279 x hroot hbr_L_5_0 hbr_root_23_0 hbr_LL_4_0_ge hbr_LLR_8_0_ge
    ·
      have hbr_L_5_0_ge : (1 : Int) ≤ x ⟨4, by decide⟩ := by omega
      by_cases hbr_LR_9_0 : x ⟨8, by decide⟩ ≤ 0
      ·
        by_cases hbr_LRL_3_1 : x ⟨2, by decide⟩ ≤ 1
        ·
          exact leaf3_infeasible_279 x hroot hbr_LRL_3_1 hbr_LR_9_0 hbr_root_23_0 hbr_L_5_0_ge
        ·
          have hbr_LRL_3_1_ge : (2 : Int) ≤ x ⟨2, by decide⟩ := by omega
          exact leaf4_infeasible_279 x hroot hbr_LR_9_0 hbr_root_23_0 hbr_LRL_3_1_ge hbr_L_5_0_ge
      ·
        have hbr_LR_9_0_ge : (1 : Int) ≤ x ⟨8, by decide⟩ := by omega
        by_cases hbr_LRR_16_0 : x ⟨15, by decide⟩ ≤ 0
        ·
          by_cases hbr_LRRL_3_1 : x ⟨2, by decide⟩ ≤ 1
          ·
            exact leaf5_infeasible_279 x hroot hbr_LRRL_3_1 hbr_LRR_16_0 hbr_root_23_0 hbr_L_5_0_ge hbr_LR_9_0_ge
          ·
            have hbr_LRRL_3_1_ge : (2 : Int) ≤ x ⟨2, by decide⟩ := by omega
            exact leaf6_infeasible_279 x hroot hbr_LRR_16_0 hbr_root_23_0 hbr_LRRL_3_1_ge hbr_L_5_0_ge hbr_LR_9_0_ge
        ·
          have hbr_LRR_16_0_ge : (1 : Int) ≤ x ⟨15, by decide⟩ := by omega
          by_cases hbr_LRRR_2_1 : x ⟨1, by decide⟩ ≤ 1
          ·
            by_cases hbr_LRRRL_18_0 : x ⟨17, by decide⟩ ≤ 0
            ·
              exact leaf7_infeasible_279 x hroot hbr_LRRR_2_1 hbr_LRRRL_18_0 hbr_root_23_0 hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge
            ·
              have hbr_LRRRL_18_0_ge : (1 : Int) ≤ x ⟨17, by decide⟩ := by omega
              by_cases hbr_LRRRLR_3_0 : x ⟨2, by decide⟩ ≤ 0
              ·
                exact leaf8_infeasible_279 x hroot hbr_LRRR_2_1 hbr_LRRRLR_3_0 hbr_root_23_0 hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge hbr_LRRRL_18_0_ge
              ·
                have hbr_LRRRLR_3_0_ge : (1 : Int) ≤ x ⟨2, by decide⟩ := by omega
                by_cases hbr_LRRRLRR_20_0 : x ⟨19, by decide⟩ ≤ 0
                ·
                  by_cases hbr_LRRRLRRL_3_1 : x ⟨2, by decide⟩ ≤ 1
                  ·
                    by_cases hbr_LRRRLRRLL_24_0 : x ⟨23, by decide⟩ ≤ 0
                    ·
                      exact leaf9_infeasible_279 x hroot hbr_LRRR_2_1 hbr_LRRRLRRL_3_1 hbr_LRRRLRR_20_0 hbr_root_23_0 hbr_LRRRLRRLL_24_0 hbr_LRRRLR_3_0_ge hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge hbr_LRRRL_18_0_ge
                    ·
                      have hbr_LRRRLRRLL_24_0_ge : (1 : Int) ≤ x ⟨23, by decide⟩ := by omega
                      exact leaf10_infeasible_279 x hroot hbr_LRRR_2_1 hbr_LRRRLRRL_3_1 hbr_LRRRLRR_20_0 hbr_root_23_0 hbr_LRRRLR_3_0_ge hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge hbr_LRRRL_18_0_ge hbr_LRRRLRRLL_24_0_ge
                  ·
                    have hbr_LRRRLRRL_3_1_ge : (2 : Int) ≤ x ⟨2, by decide⟩ := by omega
                    exact leaf11_infeasible_279 x hroot hbr_LRRR_2_1 hbr_LRRRLRR_20_0 hbr_root_23_0 hbr_LRRRLRRL_3_1_ge hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge hbr_LRRRL_18_0_ge
                ·
                  have hbr_LRRRLRR_20_0_ge : (1 : Int) ≤ x ⟨19, by decide⟩ := by omega
                  exact leaf12_infeasible_279 x hroot hbr_LRRR_2_1 hbr_root_23_0 hbr_LRRRLR_3_0_ge hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge hbr_LRRRL_18_0_ge hbr_LRRRLRR_20_0_ge
          ·
            have hbr_LRRR_2_1_ge : (2 : Int) ≤ x ⟨1, by decide⟩ := by omega
            exact leaf13_infeasible_279 x hroot hbr_root_23_0 hbr_LRRR_2_1_ge hbr_L_5_0_ge hbr_LR_9_0_ge hbr_LRR_16_0_ge
  ·
    have hbr_root_23_0_ge : (1 : Int) ≤ x ⟨22, by decide⟩ := by omega
    by_cases hbr_R_4_0 : x ⟨3, by decide⟩ ≤ 0
    ·
      by_cases hbr_RL_3_1 : x ⟨2, by decide⟩ ≤ 1
      ·
        exact leaf14_infeasible_279 x hroot hbr_RL_3_1 hbr_R_4_0 hbr_root_23_0_ge
      ·
        have hbr_RL_3_1_ge : (2 : Int) ≤ x ⟨2, by decide⟩ := by omega
        exact leaf15_infeasible_279 x hroot hbr_R_4_0 hbr_RL_3_1_ge hbr_root_23_0_ge
    ·
      have hbr_R_4_0_ge : (1 : Int) ≤ x ⟨3, by decide⟩ := by omega
      by_cases hbr_RR_24_0 : x ⟨23, by decide⟩ ≤ 0
      ·
        exact leaf16_infeasible_279 x hroot hbr_RR_24_0 hbr_R_4_0_ge hbr_root_23_0_ge
      ·
        have hbr_RR_24_0_ge : (1 : Int) ≤ x ⟨23, by decide⟩ := by omega
        exact leaf17_infeasible_279 x hroot hbr_R_4_0_ge hbr_root_23_0_ge hbr_RR_24_0_ge

end QiushiMatmul
