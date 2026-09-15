import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 200000000
set_option maxRecDepth 8000

namespace QiushiMatmul

abbrev NVAR_373 := 31
abbrev NOCC_373 := 57

-- compressed row 0 = original row 0, source orbit 196, lb 16, cap 0, mask 64
private def occRow_373_0 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0)
-- compressed row 1 = original row 2, source orbit 196, lb 16, cap 0, mask 131072
private def occRow_373_1 (j : Fin 31) : Int := (if j.val = 17 then 1 else 0)
-- compressed row 2 = original row 3, source orbit 217, lb 16, cap 0, mask 1048576
private def occRow_373_2 (j : Fin 31) : Int := (if j.val = 20 then 1 else 0)
-- compressed row 3 = original row 7, source orbit 144, lb 15, cap 1, mask 4
private def occRow_373_3 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0)
-- compressed row 4 = original row 17, source orbit 144, lb 15, cap 1, mask 32768
private def occRow_373_4 (j : Fin 31) : Int := (if j.val = 15 then 1 else 0)
-- compressed row 5 = original row 31, source orbit 65, lb 15, cap 1, mask 16842880
private def occRow_373_5 (j : Fin 31) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- compressed row 6 = original row 37, source orbit 69, lb 15, cap 1, mask 138413056
private def occRow_373_6 (j : Fin 31) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 7 = original row 59, source orbit 55, lb 14, cap 2, mask 20482
private def occRow_373_7 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- compressed row 8 = original row 100, source orbit 17, lb 14, cap 2, mask 281166352
private def occRow_373_8 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 9 = original row 114, source orbit 55, lb 14, cap 2, mask 570425352
private def occRow_373_9 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 10 = original row 160, source orbit 11, lb 12, cap 4, mask 21202
private def occRow_373_10 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- compressed row 11 = original row 194, source orbit 14, lb 12, cap 4, mask 80234500
private def occRow_373_11 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 12 = original row 207, source orbit 14, lb 12, cap 4, mask 143724808
private def occRow_373_12 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 13 = original row 209, source orbit 14, lb 12, cap 4, mask 151589008
private def occRow_373_13 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- compressed row 14 = original row 224, source orbit 14, lb 12, cap 4, mask 289677832
private def occRow_373_14 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 15 = original row 245, source orbit 11, lb 12, cap 4, mask 572655752
private def occRow_373_15 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 16 = original row 266, source orbit 10, lb 12, cap 4, mask 1094787232
private def occRow_373_16 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 17 = original row 272, source orbit 14, lb 12, cap 4, mask 1143083272
private def occRow_373_17 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 18 = original row 273, source orbit 14, lb 12, cap 4, mask 1145309320
private def occRow_373_18 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 19 = original row 322, source orbit 3, lb 9, cap 7, mask 509714017
private def occRow_373_19 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 20 = original row 330, source orbit 3, lb 9, cap 7, mask 718624042
private def occRow_373_20 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 21 = original row 331, source orbit 3, lb 9, cap 7, mask 757945042
private def occRow_373_21 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 22 = original row 334, source orbit 3, lb 9, cap 7, mask 885738292
private def occRow_373_22 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 23 = original row 343, source orbit 3, lb 9, cap 7, mask 1387081042
private def occRow_373_23 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 24 = original row 5, source orbit 237, lb 16, cap 0, mask 268435456
private def occRow_373_24 (j : Fin 31) : Int := (if j.val = 28 then 1 else 0)
-- compressed row 25 = original row 9, source orbit 153, lb 15, cap 1, mask 32
private def occRow_373_25 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0)
-- compressed row 26 = original row 21, source orbit 65, lb 15, cap 1, mask 1310752
private def occRow_373_26 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0)
-- compressed row 27 = original row 28, source orbit 69, lb 15, cap 1, mask 8454400
private def occRow_373_27 (j : Fin 31) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- compressed row 28 = original row 46, source orbit 65, lb 15, cap 1, mask 1077936256
private def occRow_373_28 (j : Fin 31) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 29 = original row 50, source orbit 55, lb 14, cap 2, mask 1537
private def occRow_373_29 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0)
-- compressed row 30 = original row 54, source orbit 55, lb 14, cap 2, mask 5152
private def occRow_373_30 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- compressed row 31 = original row 169, source orbit 10, lb 12, cap 4, mask 3440692
private def occRow_373_31 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0)
-- compressed row 32 = original row 178, source orbit 10, lb 12, cap 4, mask 25264513
private def occRow_373_32 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- compressed row 33 = original row 200, source orbit 10, lb 12, cap 4, mask 102260737
private def occRow_373_33 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 34 = original row 256, source orbit 14, lb 12, cap 4, mask 810025732
private def occRow_373_34 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 35 = original row 278, source orbit 14, lb 12, cap 4, mask 1344800002
private def occRow_373_35 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 36 = original row 285, source orbit 14, lb 12, cap 4, mask 1711276057
private def occRow_373_36 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 37 = original row 321, source orbit 3, lb 9, cap 7, mask 434529817
private def occRow_373_37 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 38 = original row 25, source orbit 69, lb 15, cap 1, mask 4259872
private def occRow_373_38 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- compressed row 39 = original row 55, source orbit 55, lb 14, cap 2, mask 6145
private def occRow_373_39 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- compressed row 40 = original row 189, source orbit 14, lb 12, cap 4, mask 53495812
private def occRow_373_40 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- compressed row 41 = original row 197, source orbit 14, lb 12, cap 4, mask 86528002
private def occRow_373_41 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 42 = original row 232, source orbit 14, lb 12, cap 4, mask 402757633
private def occRow_373_42 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 43 = original row 235, source orbit 14, lb 12, cap 4, mask 427819033
private def occRow_373_43 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 44 = original row 238, source orbit 11, lb 12, cap 4, mask 545917472
private def occRow_373_44 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 45 = original row 253, source orbit 14, lb 12, cap 4, mask 754974802
private def occRow_373_45 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- compressed row 46 = original row 265, source orbit 14, lb 12, cap 4, mask 1091832352
private def occRow_373_46 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 47 = original row 277, source orbit 14, lb 12, cap 4, mask 1342515202
private def occRow_373_47 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 48 = original row 150, source orbit 11, lb 12, cap 4, mask 7777
private def occRow_373_48 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- compressed row 49 = original row 229, source orbit 10, lb 12, cap 4, mask 336863392
private def occRow_373_49 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 50 = original row 275, source orbit 10, lb 12, cap 4, mask 1212679300
private def occRow_373_50 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 51 = original row 348, source orbit 3, lb 9, cap 7, mask 1717967257
private def occRow_373_51 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- compressed row 52 = original row 49, source orbit 55, lb 14, cap 2, mask 82
private def occRow_373_52 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0)
-- compressed row 53 = original row 172, source orbit 14, lb 12, cap 4, mask 5570602
private def occRow_373_53 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- compressed row 54 = original row 196, source orbit 14, lb 12, cap 4, mask 84214402
private def occRow_373_54 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- compressed row 55 = original row 236, source orbit 14, lb 12, cap 4, mask 503316577
private def occRow_373_55 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- compressed row 56 = original row 252, source orbit 14, lb 12, cap 4, mask 676332802
private def occRow_373_56 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)

def occCoeff_373 : Fin 57 → Fin 31 → Int
  | i, j => match i.val with
    | 0 => occRow_373_0 j
    | 1 => occRow_373_1 j
    | 2 => occRow_373_2 j
    | 3 => occRow_373_3 j
    | 4 => occRow_373_4 j
    | 5 => occRow_373_5 j
    | 6 => occRow_373_6 j
    | 7 => occRow_373_7 j
    | 8 => occRow_373_8 j
    | 9 => occRow_373_9 j
    | 10 => occRow_373_10 j
    | 11 => occRow_373_11 j
    | 12 => occRow_373_12 j
    | 13 => occRow_373_13 j
    | 14 => occRow_373_14 j
    | 15 => occRow_373_15 j
    | 16 => occRow_373_16 j
    | 17 => occRow_373_17 j
    | 18 => occRow_373_18 j
    | 19 => occRow_373_19 j
    | 20 => occRow_373_20 j
    | 21 => occRow_373_21 j
    | 22 => occRow_373_22 j
    | 23 => occRow_373_23 j
    | 24 => occRow_373_24 j
    | 25 => occRow_373_25 j
    | 26 => occRow_373_26 j
    | 27 => occRow_373_27 j
    | 28 => occRow_373_28 j
    | 29 => occRow_373_29 j
    | 30 => occRow_373_30 j
    | 31 => occRow_373_31 j
    | 32 => occRow_373_32 j
    | 33 => occRow_373_33 j
    | 34 => occRow_373_34 j
    | 35 => occRow_373_35 j
    | 36 => occRow_373_36 j
    | 37 => occRow_373_37 j
    | 38 => occRow_373_38 j
    | 39 => occRow_373_39 j
    | 40 => occRow_373_40 j
    | 41 => occRow_373_41 j
    | 42 => occRow_373_42 j
    | 43 => occRow_373_43 j
    | 44 => occRow_373_44 j
    | 45 => occRow_373_45 j
    | 46 => occRow_373_46 j
    | 47 => occRow_373_47 j
    | 48 => occRow_373_48 j
    | 49 => occRow_373_49 j
    | 50 => occRow_373_50 j
    | 51 => occRow_373_51 j
    | 52 => occRow_373_52 j
    | 53 => occRow_373_53 j
    | 54 => occRow_373_54 j
    | 55 => occRow_373_55 j
    | 56 => occRow_373_56 j
    | _ => 0

def occRhs_373 : Fin 57 → Int
  | i => match i.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 4
    | 11 => 4
    | 12 => 4
    | 13 => 4
    | 14 => 4
    | 15 => 4
    | 16 => 4
    | 17 => 4
    | 18 => 4
    | 19 => 7
    | 20 => 7
    | 21 => 7
    | 22 => 7
    | 23 => 7
    | 24 => 0
    | 25 => 1
    | 26 => 1
    | 27 => 1
    | 28 => 1
    | 29 => 2
    | 30 => 2
    | 31 => 4
    | 32 => 4
    | 33 => 4
    | 34 => 4
    | 35 => 4
    | 36 => 4
    | 37 => 7
    | 38 => 1
    | 39 => 2
    | 40 => 4
    | 41 => 4
    | 42 => 4
    | 43 => 4
    | 44 => 4
    | 45 => 4
    | 46 => 4
    | 47 => 4
    | 48 => 4
    | 49 => 4
    | 50 => 4
    | 51 => 7
    | 52 => 2
    | 53 => 4
    | 54 => 4
    | 55 => 4
    | 56 => 4
    | _ => 0

def S_373 : OccSys 31 57 :=
  { occCoeff := occCoeff_373, occRhs := occRhs_373, target := 16 }

-- leaf 0, path L, original Farkas rhs -8
def refs_373_L0 : Fin 29 → RowRef 57 31
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
    | 21 => .occ ⟨21, by decide⟩
    | 22 => .occ ⟨22, by decide⟩
    | 23 => .occ ⟨23, by decide⟩
    | 24 => .sumGe
    | 25 => .nonneg ⟨16, by decide⟩
    | 26 => .nonneg ⟨18, by decide⟩
    | 27 => .nonneg ⟨22, by decide⟩
    | 28 => .branchLe ⟨0, by decide⟩ 0
    | _ => .sumGe

def mults_373_L0 : Fin 29 → Nat
  | i => match i.val with
    | 0 => 8
    | 1 => 36
    | 2 => 48
    | 3 => 44
    | 4 => 56
    | 5 => 4
    | 6 => 18
    | 7 => 4
    | 8 => 2
    | 9 => 14
    | 10 => 5
    | 11 => 7
    | 12 => 4
    | 13 => 1
    | 14 => 15
    | 15 => 4
    | 16 => 27
    | 17 => 9
    | 18 => 6
    | 19 => 10
    | 20 => 14
    | 21 => 19
    | 22 => 15
    | 23 => 24
    | 24 => 66
    | 25 => 52
    | 26 => 12
    | 27 => 48
    | 28 => 56
    | _ => 0

theorem coeff_cancel_373_L0 :
    ∀ j : Fin 31, (∑ i : Fin 29, (mults_373_L0 i : Int) * (refs_373_L0 i).resolveCoeff S_373 j) = 0 := by
  decide

theorem rhs_neg_373_L0 :
    (∑ i : Fin 29, (mults_373_L0 i : Int) * (refs_373_L0 i).resolveRhs S_373) < 0 := by
  decide

theorem leaf0_infeasible_373 (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x)
    (h_le_1_0 : x ⟨0, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 29,
      (∑ j : Fin 31, (refs_373_L0 i).resolveCoeff S_373 j * x j) ≤
      (refs_373_L0 i).resolveRhs S_373 := by
    intro i; fin_cases i
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_373_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_1_0]
  exact farkas_leaf_unsat _ _ (mults_373_L0) coeff_cancel_373_L0 rhs_neg_373_L0 x hrows

-- leaf 1, path RL, original Farkas rhs -11
def refs_373_L1 : Fin 31 → RowRef 57 31
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨1, by decide⟩
    | 2 => .occ ⟨24, by decide⟩
    | 3 => .occ ⟨3, by decide⟩
    | 4 => .occ ⟨25, by decide⟩
    | 5 => .occ ⟨4, by decide⟩
    | 6 => .occ ⟨26, by decide⟩
    | 7 => .occ ⟨27, by decide⟩
    | 8 => .occ ⟨28, by decide⟩
    | 9 => .occ ⟨29, by decide⟩
    | 10 => .occ ⟨30, by decide⟩
    | 11 => .occ ⟨7, by decide⟩
    | 12 => .occ ⟨31, by decide⟩
    | 13 => .occ ⟨32, by decide⟩
    | 14 => .occ ⟨33, by decide⟩
    | 15 => .occ ⟨34, by decide⟩
    | 16 => .occ ⟨16, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨35, by decide⟩
    | 19 => .occ ⟨36, by decide⟩
    | 20 => .occ ⟨37, by decide⟩
    | 21 => .occ ⟨19, by decide⟩
    | 22 => .occ ⟨20, by decide⟩
    | 23 => .occ ⟨21, by decide⟩
    | 24 => .sumGe
    | 25 => .nonneg ⟨14, by decide⟩
    | 26 => .nonneg ⟨16, by decide⟩
    | 27 => .nonneg ⟨18, by decide⟩
    | 28 => .nonneg ⟨22, by decide⟩
    | 29 => .branchLe ⟨11, by decide⟩ 0
    | 30 => .branchGe ⟨0, by decide⟩ 1
    | _ => .sumGe

def mults_373_L1 : Fin 31 → Nat
  | i => match i.val with
    | 0 => 34
    | 1 => 26
    | 2 => 11
    | 3 => 32
    | 4 => 8
    | 5 => 32
    | 6 => 7
    | 7 => 6
    | 8 => 19
    | 9 => 5
    | 10 => 1
    | 11 => 15
    | 12 => 6
    | 13 => 8
    | 14 => 20
    | 15 => 10
    | 16 => 9
    | 17 => 3
    | 18 => 6
    | 19 => 11
    | 20 => 19
    | 21 => 2
    | 22 => 15
    | 23 => 12
    | 24 => 48
    | 25 => 33
    | 26 => 4
    | 27 => 11
    | 28 => 26
    | 29 => 46
    | 30 => 17
    | _ => 0

theorem coeff_cancel_373_L1 :
    ∀ j : Fin 31, (∑ i : Fin 31, (mults_373_L1 i : Int) * (refs_373_L1 i).resolveCoeff S_373 j) = 0 := by
  decide

theorem rhs_neg_373_L1 :
    (∑ i : Fin 31, (mults_373_L1 i : Int) * (refs_373_L1 i).resolveRhs S_373) < 0 := by
  decide

theorem leaf1_infeasible_373 (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x)
    (h_le_12_0 : x ⟨11, by decide⟩ ≤ 0)
    (h_ge_1_1 : (1 : Int) ≤ x ⟨0, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 31,
      (∑ j : Fin 31, (refs_373_L1 i).resolveCoeff S_373 j * x j) ≤
      (refs_373_L1 i).resolveRhs S_373 := by
    intro i; fin_cases i
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_12_0]
    · simp only [refs_373_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_1_1]
  exact farkas_leaf_unsat _ _ (mults_373_L1) coeff_cancel_373_L1 rhs_neg_373_L1 x hrows

-- leaf 2, path RRL, original Farkas rhs -14
def refs_373_L2 : Fin 32 → RowRef 57 31
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨1, by decide⟩
    | 2 => .occ ⟨3, by decide⟩
    | 3 => .occ ⟨4, by decide⟩
    | 4 => .occ ⟨26, by decide⟩
    | 5 => .occ ⟨38, by decide⟩
    | 6 => .occ ⟨27, by decide⟩
    | 7 => .occ ⟨39, by decide⟩
    | 8 => .occ ⟨9, by decide⟩
    | 9 => .occ ⟨40, by decide⟩
    | 10 => .occ ⟨41, by decide⟩
    | 11 => .occ ⟨33, by decide⟩
    | 12 => .occ ⟨42, by decide⟩
    | 13 => .occ ⟨43, by decide⟩
    | 14 => .occ ⟨44, by decide⟩
    | 15 => .occ ⟨45, by decide⟩
    | 16 => .occ ⟨34, by decide⟩
    | 17 => .occ ⟨46, by decide⟩
    | 18 => .occ ⟨47, by decide⟩
    | 19 => .occ ⟨35, by decide⟩
    | 20 => .occ ⟨36, by decide⟩
    | 21 => .occ ⟨37, by decide⟩
    | 22 => .occ ⟨19, by decide⟩
    | 23 => .occ ⟨20, by decide⟩
    | 24 => .occ ⟨22, by decide⟩
    | 25 => .sumGe
    | 26 => .nonneg ⟨16, by decide⟩
    | 27 => .nonneg ⟨18, by decide⟩
    | 28 => .nonneg ⟨28, by decide⟩
    | 29 => .branchLe ⟨7, by decide⟩ 0
    | 30 => .branchGe ⟨0, by decide⟩ 1
    | 31 => .branchGe ⟨11, by decide⟩ 1
    | _ => .sumGe

def mults_373_L2 : Fin 32 → Nat
  | i => match i.val with
    | 0 => 28
    | 1 => 21
    | 2 => 31
    | 3 => 36
    | 4 => 16
    | 5 => 5
    | 6 => 13
    | 7 => 30
    | 8 => 10
    | 9 => 2
    | 10 => 2
    | 11 => 14
    | 12 => 2
    | 13 => 4
    | 14 => 1
    | 15 => 10
    | 16 => 7
    | 17 => 8
    | 18 => 12
    | 19 => 16
    | 20 => 8
    | 21 => 18
    | 22 => 6
    | 23 => 4
    | 24 => 4
    | 25 => 44
    | 26 => 2
    | 27 => 14
    | 28 => 25
    | 29 => 44
    | 30 => 38
    | 31 => 21
    | _ => 0

theorem coeff_cancel_373_L2 :
    ∀ j : Fin 31, (∑ i : Fin 32, (mults_373_L2 i : Int) * (refs_373_L2 i).resolveCoeff S_373 j) = 0 := by
  decide

theorem rhs_neg_373_L2 :
    (∑ i : Fin 32, (mults_373_L2 i : Int) * (refs_373_L2 i).resolveRhs S_373) < 0 := by
  decide

theorem leaf2_infeasible_373 (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x)
    (h_le_8_0 : x ⟨7, by decide⟩ ≤ 0)
    (h_ge_1_1 : (1 : Int) ≤ x ⟨0, by decide⟩)
    (h_ge_12_1 : (1 : Int) ≤ x ⟨11, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 32,
      (∑ j : Fin 31, (refs_373_L2 i).resolveCoeff S_373 j * x j) ≤
      (refs_373_L2 i).resolveRhs S_373 := by
    intro i; fin_cases i
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_8_0]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_1_1]
    · simp only [refs_373_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_12_1]
  exact farkas_leaf_unsat _ _ (mults_373_L2) coeff_cancel_373_L2 rhs_neg_373_L2 x hrows

-- leaf 3, path RRRL, original Farkas rhs -2
def refs_373_L3 : Fin 29 → RowRef 57 31
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨2, by decide⟩
    | 2 => .occ ⟨3, by decide⟩
    | 3 => .occ ⟨5, by decide⟩
    | 4 => .occ ⟨28, by decide⟩
    | 5 => .occ ⟨39, by decide⟩
    | 6 => .occ ⟨48, by decide⟩
    | 7 => .occ ⟨31, by decide⟩
    | 8 => .occ ⟨32, by decide⟩
    | 9 => .occ ⟨33, by decide⟩
    | 10 => .occ ⟨49, by decide⟩
    | 11 => .occ ⟨42, by decide⟩
    | 12 => .occ ⟨15, by decide⟩
    | 13 => .occ ⟨50, by decide⟩
    | 14 => .occ ⟨47, by decide⟩
    | 15 => .occ ⟨37, by decide⟩
    | 16 => .occ ⟨22, by decide⟩
    | 17 => .occ ⟨51, by decide⟩
    | 18 => .sumGe
    | 19 => .nonneg ⟨16, by decide⟩
    | 20 => .nonneg ⟨17, by decide⟩
    | 21 => .nonneg ⟨21, by decide⟩
    | 22 => .nonneg ⟨22, by decide⟩
    | 23 => .nonneg ⟨23, by decide⟩
    | 24 => .nonneg ⟨28, by decide⟩
    | 25 => .branchLe ⟨1, by decide⟩ 1
    | 26 => .branchGe ⟨0, by decide⟩ 1
    | 27 => .branchGe ⟨7, by decide⟩ 1
    | 28 => .branchGe ⟨11, by decide⟩ 1
    | _ => .sumGe

def mults_373_L3 : Fin 29 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 2
    | 2 => 1
    | 3 => 1
    | 4 => 2
    | 5 => 1
    | 6 => 2
    | 7 => 1
    | 8 => 3
    | 9 => 2
    | 10 => 1
    | 11 => 2
    | 12 => 3
    | 13 => 2
    | 14 => 1
    | 15 => 2
    | 16 => 2
    | 17 => 1
    | 18 => 6
    | 19 => 3
    | 20 => 2
    | 21 => 1
    | 22 => 3
    | 23 => 1
    | 24 => 2
    | 25 => 5
    | 26 => 7
    | 27 => 7
    | 28 => 6
    | _ => 0

theorem coeff_cancel_373_L3 :
    ∀ j : Fin 31, (∑ i : Fin 29, (mults_373_L3 i : Int) * (refs_373_L3 i).resolveCoeff S_373 j) = 0 := by
  decide

theorem rhs_neg_373_L3 :
    (∑ i : Fin 29, (mults_373_L3 i : Int) * (refs_373_L3 i).resolveRhs S_373) < 0 := by
  decide

theorem leaf3_infeasible_373 (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x)
    (h_le_2_1 : x ⟨1, by decide⟩ ≤ 1)
    (h_ge_1_1 : (1 : Int) ≤ x ⟨0, by decide⟩)
    (h_ge_8_1 : (1 : Int) ≤ x ⟨7, by decide⟩)
    (h_ge_12_1 : (1 : Int) ≤ x ⟨11, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 29,
      (∑ j : Fin 31, (refs_373_L3 i).resolveCoeff S_373 j * x j) ≤
      (refs_373_L3 i).resolveRhs S_373 := by
    intro i; fin_cases i
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨51, by decide⟩
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨17, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨23, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_le_2_1]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_1_1]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_8_1]
    · simp only [refs_373_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_12_1]
  exact farkas_leaf_unsat _ _ (mults_373_L3) coeff_cancel_373_L3 rhs_neg_373_L3 x hrows

-- leaf 4, path RRRR, original Farkas rhs -12
def refs_373_L4 : Fin 30 → RowRef 57 31
  | i => match i.val with
    | 0 => .occ ⟨1, by decide⟩
    | 1 => .occ ⟨3, by decide⟩
    | 2 => .occ ⟨52, by decide⟩
    | 3 => .occ ⟨7, by decide⟩
    | 4 => .occ ⟨10, by decide⟩
    | 5 => .occ ⟨31, by decide⟩
    | 6 => .occ ⟨53, by decide⟩
    | 7 => .occ ⟨32, by decide⟩
    | 8 => .occ ⟨11, by decide⟩
    | 9 => .occ ⟨54, by decide⟩
    | 10 => .occ ⟨33, by decide⟩
    | 11 => .occ ⟨42, by decide⟩
    | 12 => .occ ⟨55, by decide⟩
    | 13 => .occ ⟨44, by decide⟩
    | 14 => .occ ⟨15, by decide⟩
    | 15 => .occ ⟨56, by decide⟩
    | 16 => .occ ⟨50, by decide⟩
    | 17 => .occ ⟨47, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨23, by decide⟩
    | 20 => .sumGe
    | 21 => .nonneg ⟨16, by decide⟩
    | 22 => .nonneg ⟨18, by decide⟩
    | 23 => .nonneg ⟨22, by decide⟩
    | 24 => .nonneg ⟨24, by decide⟩
    | 25 => .nonneg ⟨28, by decide⟩
    | 26 => .nonneg ⟨30, by decide⟩
    | 27 => .branchGe ⟨1, by decide⟩ 2
    | 28 => .branchGe ⟨7, by decide⟩ 1
    | 29 => .branchGe ⟨11, by decide⟩ 1
    | _ => .sumGe

def mults_373_L4 : Fin 30 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 4
    | 2 => 10
    | 3 => 12
    | 4 => 1
    | 5 => 3
    | 6 => 7
    | 7 => 10
    | 8 => 1
    | 9 => 10
    | 10 => 2
    | 11 => 1
    | 12 => 1
    | 13 => 3
    | 14 => 9
    | 15 => 4
    | 16 => 8
    | 17 => 12
    | 18 => 2
    | 19 => 2
    | 20 => 16
    | 21 => 28
    | 22 => 18
    | 23 => 6
    | 24 => 4
    | 25 => 2
    | 26 => 6
    | 27 => 42
    | 28 => 22
    | 29 => 14
    | _ => 0

theorem coeff_cancel_373_L4 :
    ∀ j : Fin 31, (∑ i : Fin 30, (mults_373_L4 i : Int) * (refs_373_L4 i).resolveCoeff S_373 j) = 0 := by
  decide

theorem rhs_neg_373_L4 :
    (∑ i : Fin 30, (mults_373_L4 i : Int) * (refs_373_L4 i).resolveRhs S_373) < 0 := by
  decide

theorem leaf4_infeasible_373 (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x)
    (h_ge_1_1 : (1 : Int) ≤ x ⟨0, by decide⟩)
    (h_ge_2_2 : (2 : Int) ≤ x ⟨1, by decide⟩)
    (h_ge_8_1 : (1 : Int) ≤ x ⟨7, by decide⟩)
    (h_ge_12_1 : (1 : Int) ≤ x ⟨11, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 30,
      (∑ j : Fin 31, (refs_373_L4 i).resolveCoeff S_373 j * x j) ≤
      (refs_373_L4 i).resolveRhs S_373 := by
    intro i; fin_cases i
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨53, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]
      linarith [hroot.hTotal]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_2_2]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_8_1]
    · simp only [refs_373_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]
      linarith [h_ge_12_1]
  exact farkas_leaf_unsat _ _ (mults_373_L4) coeff_cancel_373_L4 rhs_neg_373_L4 x hrows

theorem orbit373_occupation_no_model (x : Fin 31 → Int)
    (hroot : S_373.RootHolds x) : False := by
  by_cases hbr_root_1_0 : x ⟨0, by decide⟩ ≤ 0
  ·
    exact leaf0_infeasible_373 x hroot hbr_root_1_0
  ·
    have hbr_root_1_0_ge : (1 : Int) ≤ x ⟨0, by decide⟩ := by omega
    by_cases hbr_R_12_0 : x ⟨11, by decide⟩ ≤ 0
    ·
      exact leaf1_infeasible_373 x hroot hbr_R_12_0 hbr_root_1_0_ge
    ·
      have hbr_R_12_0_ge : (1 : Int) ≤ x ⟨11, by decide⟩ := by omega
      by_cases hbr_RR_8_0 : x ⟨7, by decide⟩ ≤ 0
      ·
        exact leaf2_infeasible_373 x hroot hbr_RR_8_0 hbr_root_1_0_ge hbr_R_12_0_ge
      ·
        have hbr_RR_8_0_ge : (1 : Int) ≤ x ⟨7, by decide⟩ := by omega
        by_cases hbr_RRR_2_1 : x ⟨1, by decide⟩ ≤ 1
        ·
          exact leaf3_infeasible_373 x hroot hbr_RRR_2_1 hbr_root_1_0_ge hbr_RR_8_0_ge hbr_R_12_0_ge
        ·
          have hbr_RRR_2_1_ge : (2 : Int) ≤ x ⟨1, by decide⟩ := by omega
          exact leaf4_infeasible_373 x hroot hbr_root_1_0_ge hbr_RRR_2_1_ge hbr_RR_8_0_ge hbr_R_12_0_ge

end QiushiMatmul
