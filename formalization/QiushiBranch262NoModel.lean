import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 200000000
set_option maxRecDepth 8000

namespace QiushiMatmul

abbrev NVAR_262 := 31
abbrev NOCC_262 := 49

-- row 0 = original 38, orbit 23, lb 12, cap 4
private def occRow_262_0 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0)
-- row 1 = original 47, orbit 31, lb 15, cap 1
private def occRow_262_1 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0)
-- row 2 = original 48, orbit 31, lb 15, cap 1
private def occRow_262_2 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0)
-- row 3 = original 52, orbit 31, lb 15, cap 1
private def occRow_262_3 (j : Fin 31) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- row 4 = original 53, orbit 31, lb 15, cap 1
private def occRow_262_4 (j : Fin 31) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- row 5 = original 78, orbit 35, lb 15, cap 1
private def occRow_262_5 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 6 = original 79, orbit 35, lb 15, cap 1
private def occRow_262_6 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 7 = original 80, orbit 35, lb 15, cap 1
private def occRow_262_7 (j : Fin 31) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 8 = original 81, orbit 35, lb 15, cap 1
private def occRow_262_8 (j : Fin 31) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- row 9 = original 82, orbit 35, lb 15, cap 1
private def occRow_262_9 (j : Fin 31) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 10 = original 84, orbit 35, lb 15, cap 1
private def occRow_262_10 (j : Fin 31) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 11 = original 130, orbit 55, lb 14, cap 2
private def occRow_262_11 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0)
-- row 12 = original 131, orbit 55, lb 14, cap 2
private def occRow_262_12 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0)
-- row 13 = original 181, orbit 7, lb 9, cap 7
private def occRow_262_13 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0)
-- row 14 = original 182, orbit 7, lb 9, cap 7
private def occRow_262_14 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- row 15 = original 297, orbit 16, lb 12, cap 4
private def occRow_262_15 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 16 = original 298, orbit 16, lb 12, cap 4
private def occRow_262_16 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 17 = original 320, orbit 2, lb 6, cap 10
private def occRow_262_17 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- row 18 = original 323, orbit 2, lb 6, cap 10
private def occRow_262_18 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 19 = original 328, orbit 2, lb 6, cap 10
private def occRow_262_19 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 20 = original 329, orbit 2, lb 6, cap 10
private def occRow_262_20 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 21 = original 333, orbit 3, lb 9, cap 7
private def occRow_262_21 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 22 = original 335, orbit 3, lb 9, cap 7
private def occRow_262_22 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 23 = original 1, orbit 96, lb 16, cap 0
private def occRow_262_23 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0)
-- row 24 = original 50, orbit 31, lb 15, cap 1
private def occRow_262_24 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0)
-- row 25 = original 51, orbit 31, lb 15, cap 1
private def occRow_262_25 (j : Fin 31) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0)
-- row 26 = original 83, orbit 35, lb 15, cap 1
private def occRow_262_26 (j : Fin 31) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 27 = original 184, orbit 7, lb 9, cap 7
private def occRow_262_27 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- row 28 = original 189, orbit 7, lb 9, cap 7
private def occRow_262_28 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 29 = original 215, orbit 11, lb 12, cap 4
private def occRow_262_29 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 30 = original 216, orbit 11, lb 12, cap 4
private def occRow_262_30 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 31 = original 321, orbit 2, lb 6, cap 10
private def occRow_262_31 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 32 = original 322, orbit 2, lb 6, cap 10
private def occRow_262_32 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 33 = original 336, orbit 3, lb 9, cap 7
private def occRow_262_33 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 34 = original 337, orbit 3, lb 9, cap 7
private def occRow_262_34 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 35 = original 85, orbit 35, lb 15, cap 1
private def occRow_262_35 (j : Fin 31) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 36 = original 148, orbit 55, lb 14, cap 2
private def occRow_262_36 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 37 = original 192, orbit 7, lb 9, cap 7
private def occRow_262_37 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 38 = original 331, orbit 2, lb 6, cap 10
private def occRow_262_38 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 39 = original 338, orbit 3, lb 9, cap 7
private def occRow_262_39 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 40 = original 149, orbit 55, lb 14, cap 2
private def occRow_262_40 (j : Fin 31) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 41 = original 153, orbit 55, lb 14, cap 2
private def occRow_262_41 (j : Fin 31) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 42 = original 154, orbit 55, lb 14, cap 2
private def occRow_262_42 (j : Fin 31) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 43 = original 157, orbit 55, lb 14, cap 2
private def occRow_262_43 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 44 = original 185, orbit 7, lb 9, cap 7
private def occRow_262_44 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- row 45 = original 194, orbit 7, lb 9, cap 7
private def occRow_262_45 (j : Fin 31) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 46 = original 309, orbit 16, lb 12, cap 4
private def occRow_262_46 (j : Fin 31) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 47 = original 312, orbit 16, lb 12, cap 4
private def occRow_262_47 (j : Fin 31) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 48 = original 339, orbit 3, lb 9, cap 7
private def occRow_262_48 (j : Fin 31) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)

def occCoeff_262 : Fin 49 → Fin 31 → Int
  | i, j => match i.val with
    | 0 => occRow_262_0 j
    | 1 => occRow_262_1 j
    | 2 => occRow_262_2 j
    | 3 => occRow_262_3 j
    | 4 => occRow_262_4 j
    | 5 => occRow_262_5 j
    | 6 => occRow_262_6 j
    | 7 => occRow_262_7 j
    | 8 => occRow_262_8 j
    | 9 => occRow_262_9 j
    | 10 => occRow_262_10 j
    | 11 => occRow_262_11 j
    | 12 => occRow_262_12 j
    | 13 => occRow_262_13 j
    | 14 => occRow_262_14 j
    | 15 => occRow_262_15 j
    | 16 => occRow_262_16 j
    | 17 => occRow_262_17 j
    | 18 => occRow_262_18 j
    | 19 => occRow_262_19 j
    | 20 => occRow_262_20 j
    | 21 => occRow_262_21 j
    | 22 => occRow_262_22 j
    | 23 => occRow_262_23 j
    | 24 => occRow_262_24 j
    | 25 => occRow_262_25 j
    | 26 => occRow_262_26 j
    | 27 => occRow_262_27 j
    | 28 => occRow_262_28 j
    | 29 => occRow_262_29 j
    | 30 => occRow_262_30 j
    | 31 => occRow_262_31 j
    | 32 => occRow_262_32 j
    | 33 => occRow_262_33 j
    | 34 => occRow_262_34 j
    | 35 => occRow_262_35 j
    | 36 => occRow_262_36 j
    | 37 => occRow_262_37 j
    | 38 => occRow_262_38 j
    | 39 => occRow_262_39 j
    | 40 => occRow_262_40 j
    | 41 => occRow_262_41 j
    | 42 => occRow_262_42 j
    | 43 => occRow_262_43 j
    | 44 => occRow_262_44 j
    | 45 => occRow_262_45 j
    | 46 => occRow_262_46 j
    | 47 => occRow_262_47 j
    | 48 => occRow_262_48 j
    | _ => 0

def occRhs_262 : Fin 49 → Int
  | i => match i.val with
    | 0 => 4
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => 1
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 2
    | 12 => 2
    | 13 => 7
    | 14 => 7
    | 15 => 4
    | 16 => 4
    | 17 => 10
    | 18 => 10
    | 19 => 10
    | 20 => 10
    | 21 => 7
    | 22 => 7
    | 23 => 0
    | 24 => 1
    | 25 => 1
    | 26 => 1
    | 27 => 7
    | 28 => 7
    | 29 => 4
    | 30 => 4
    | 31 => 10
    | 32 => 10
    | 33 => 7
    | 34 => 7
    | 35 => 1
    | 36 => 2
    | 37 => 7
    | 38 => 10
    | 39 => 7
    | 40 => 2
    | 41 => 2
    | 42 => 2
    | 43 => 2
    | 44 => 7
    | 45 => 7
    | 46 => 4
    | 47 => 4
    | 48 => 7
    | _ => 0

def S_262 : OccSys 31 49 :=
  { occCoeff := occCoeff_262, occRhs := occRhs_262, target := 16 }

-- leaf 0, path LL, Farkas rhs -8
def refs_262_L0 : Fin 28 → RowRef 49 31
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
    | 23 => .sumGe
    | 24 => .nonneg ⟨1, by decide⟩
    | 25 => .nonneg ⟨9, by decide⟩
    | 26 => .branchLe ⟨28, by decide⟩ 0
    | 27 => .branchLe ⟨30, by decide⟩ 0
    | _ => .sumGe

def mults_262_L0 : Fin 28 → Nat
  | i => match i.val with
    | 0 => 6
    | 1 => 15
    | 2 => 15
    | 3 => 19
    | 4 => 19
    | 5 => 15
    | 6 => 15
    | 7 => 11
    | 8 => 11
    | 9 => 12
    | 10 => 16
    | 11 => 4
    | 12 => 4
    | 13 => 8
    | 14 => 4
    | 15 => 2
    | 16 => 2
    | 17 => 8
    | 18 => 6
    | 19 => 1
    | 20 => 5
    | 21 => 8
    | 22 => 8
    | 23 => 38
    | 24 => 16
    | 25 => 8
    | 26 => 32
    | 27 => 32
    | _ => 0

theorem coeff_cancel_262_L0 :
    ∀ j : Fin 31, (∑ i : Fin 28, (mults_262_L0 i : Int) * (refs_262_L0 i).resolveCoeff S_262 j) = 0 := by
  decide

theorem rhs_neg_262_L0 :
    (∑ i : Fin 28, (mults_262_L0 i : Int) * (refs_262_L0 i).resolveRhs S_262) < 0 := by
  decide

theorem leaf0_infeasible_262 (x : Fin 31 → Int)
    (hroot : S_262.RootHolds x)
    (h_le_29_0 : x ⟨28, by decide⟩ ≤ 0)
    (h_le_31_0 : x ⟨30, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 28,
      (∑ j : Fin 31, (refs_262_L0 i).resolveCoeff S_262 j * x j) ≤
      (refs_262_L0 i).resolveRhs S_262 := by
    intro i; fin_cases i
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨1, by decide⟩]
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨9, by decide⟩]
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_29_0]
    · simp only [refs_262_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_31_0]
  exact farkas_leaf_unsat _ _ (mults_262_L0) coeff_cancel_262_L0 rhs_neg_262_L0 x hrows

-- leaf 1, path LR, Farkas rhs -14
def refs_262_L1 : Fin 29 → RowRef 49 31
  | i => match i.val with
    | 0 => .occ ⟨23, by decide⟩
    | 1 => .occ ⟨1, by decide⟩
    | 2 => .occ ⟨2, by decide⟩
    | 3 => .occ ⟨24, by decide⟩
    | 4 => .occ ⟨25, by decide⟩
    | 5 => .occ ⟨3, by decide⟩
    | 6 => .occ ⟨4, by decide⟩
    | 7 => .occ ⟨5, by decide⟩
    | 8 => .occ ⟨6, by decide⟩
    | 9 => .occ ⟨7, by decide⟩
    | 10 => .occ ⟨8, by decide⟩
    | 11 => .occ ⟨9, by decide⟩
    | 12 => .occ ⟨26, by decide⟩
    | 13 => .occ ⟨10, by decide⟩
    | 14 => .occ ⟨27, by decide⟩
    | 15 => .occ ⟨28, by decide⟩
    | 16 => .occ ⟨29, by decide⟩
    | 17 => .occ ⟨30, by decide⟩
    | 18 => .occ ⟨31, by decide⟩
    | 19 => .occ ⟨32, by decide⟩
    | 20 => .occ ⟨18, by decide⟩
    | 21 => .occ ⟨20, by decide⟩
    | 22 => .occ ⟨33, by decide⟩
    | 23 => .occ ⟨34, by decide⟩
    | 24 => .sumGe
    | 25 => .nonneg ⟨7, by decide⟩
    | 26 => .nonneg ⟨9, by decide⟩
    | 27 => .branchLe ⟨30, by decide⟩ 0
    | 28 => .branchGe ⟨28, by decide⟩ 1
    | _ => .sumGe

def mults_262_L1 : Fin 29 → Nat
  | i => match i.val with
    | 0 => 2
    | 1 => 27
    | 2 => 27
    | 3 => 2
    | 4 => 6
    | 5 => 21
    | 6 => 21
    | 7 => 15
    | 8 => 15
    | 9 => 21
    | 10 => 21
    | 11 => 14
    | 12 => 44
    | 13 => 26
    | 14 => 12
    | 15 => 12
    | 16 => 2
    | 17 => 2
    | 18 => 12
    | 19 => 14
    | 20 => 6
    | 21 => 6
    | 22 => 15
    | 23 => 15
    | 24 => 62
    | 25 => 30
    | 26 => 46
    | 27 => 56
    | 28 => 56
    | _ => 0

theorem coeff_cancel_262_L1 :
    ∀ j : Fin 31, (∑ i : Fin 29, (mults_262_L1 i : Int) * (refs_262_L1 i).resolveCoeff S_262 j) = 0 := by
  decide

theorem rhs_neg_262_L1 :
    (∑ i : Fin 29, (mults_262_L1 i : Int) * (refs_262_L1 i).resolveRhs S_262) < 0 := by
  decide

theorem leaf1_infeasible_262 (x : Fin 31 → Int)
    (hroot : S_262.RootHolds x)
    (h_le_31_0 : x ⟨30, by decide⟩ ≤ 0)
    (h_ge_29_1 : (1 : Int) ≤ x ⟨28, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 29,
      (∑ j : Fin 31, (refs_262_L1 i).resolveCoeff S_262 j * x j) ≤
      (refs_262_L1 i).resolveRhs S_262 := by
    intro i; fin_cases i
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨9, by decide⟩]
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_31_0]
    · simp only [refs_262_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_29_1]
  exact farkas_leaf_unsat _ _ (mults_262_L1) coeff_cancel_262_L1 rhs_neg_262_L1 x hrows

-- leaf 2, path RL, Farkas rhs -4
def refs_262_L2 : Fin 27 → RowRef 49 31
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
    | 10 => .occ ⟨26, by decide⟩
    | 11 => .occ ⟨10, by decide⟩
    | 12 => .occ ⟨35, by decide⟩
    | 13 => .occ ⟨11, by decide⟩
    | 14 => .occ ⟨36, by decide⟩
    | 15 => .occ ⟨37, by decide⟩
    | 16 => .occ ⟨31, by decide⟩
    | 17 => .occ ⟨19, by decide⟩
    | 18 => .occ ⟨38, by decide⟩
    | 19 => .occ ⟨39, by decide⟩
    | 20 => .sumGe
    | 21 => .nonneg ⟨1, by decide⟩
    | 22 => .nonneg ⟨2, by decide⟩
    | 23 => .nonneg ⟨7, by decide⟩
    | 24 => .nonneg ⟨9, by decide⟩
    | 25 => .branchLe ⟨26, by decide⟩ 0
    | 26 => .branchGe ⟨30, by decide⟩ 1
    | _ => .sumGe

def mults_262_L2 : Fin 27 → Nat
  | i => match i.val with
    | 0 => 14
    | 1 => 15
    | 2 => 17
    | 3 => 18
    | 4 => 14
    | 5 => 13
    | 6 => 17
    | 7 => 16
    | 8 => 6
    | 9 => 15
    | 10 => 17
    | 11 => 15
    | 12 => 19
    | 13 => 6
    | 14 => 2
    | 15 => 2
    | 16 => 1
    | 17 => 3
    | 18 => 2
    | 19 => 4
    | 20 => 22
    | 21 => 12
    | 22 => 14
    | 23 => 14
    | 24 => 62
    | 25 => 16
    | 26 => 8
    | _ => 0

theorem coeff_cancel_262_L2 :
    ∀ j : Fin 31, (∑ i : Fin 27, (mults_262_L2 i : Int) * (refs_262_L2 i).resolveCoeff S_262 j) = 0 := by
  decide

theorem rhs_neg_262_L2 :
    (∑ i : Fin 27, (mults_262_L2 i : Int) * (refs_262_L2 i).resolveRhs S_262) < 0 := by
  decide

theorem leaf2_infeasible_262 (x : Fin 31 → Int)
    (hroot : S_262.RootHolds x)
    (h_le_27_0 : x ⟨26, by decide⟩ ≤ 0)
    (h_ge_31_1 : (1 : Int) ≤ x ⟨30, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 27,
      (∑ j : Fin 31, (refs_262_L2 i).resolveCoeff S_262 j * x j) ≤
      (refs_262_L2 i).resolveRhs S_262 := by
    intro i; fin_cases i
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨1, by decide⟩]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨9, by decide⟩]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_27_0]
    · simp only [refs_262_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_31_1]
  exact farkas_leaf_unsat _ _ (mults_262_L2) coeff_cancel_262_L2 rhs_neg_262_L2 x hrows

-- leaf 3, path RR, Farkas rhs -11
def refs_262_L3 : Fin 30 → RowRef 49 31
  | i => match i.val with
    | 0 => .occ ⟨23, by decide⟩
    | 1 => .occ ⟨2, by decide⟩
    | 2 => .occ ⟨3, by decide⟩
    | 3 => .occ ⟨4, by decide⟩
    | 4 => .occ ⟨5, by decide⟩
    | 5 => .occ ⟨7, by decide⟩
    | 6 => .occ ⟨8, by decide⟩
    | 7 => .occ ⟨9, by decide⟩
    | 8 => .occ ⟨10, by decide⟩
    | 9 => .occ ⟨35, by decide⟩
    | 10 => .occ ⟨12, by decide⟩
    | 11 => .occ ⟨40, by decide⟩
    | 12 => .occ ⟨41, by decide⟩
    | 13 => .occ ⟨42, by decide⟩
    | 14 => .occ ⟨43, by decide⟩
    | 15 => .occ ⟨44, by decide⟩
    | 16 => .occ ⟨45, by decide⟩
    | 17 => .occ ⟨46, by decide⟩
    | 18 => .occ ⟨47, by decide⟩
    | 19 => .occ ⟨17, by decide⟩
    | 20 => .occ ⟨18, by decide⟩
    | 21 => .occ ⟨20, by decide⟩
    | 22 => .occ ⟨48, by decide⟩
    | 23 => .sumGe
    | 24 => .nonneg ⟨2, by decide⟩
    | 25 => .nonneg ⟨7, by decide⟩
    | 26 => .nonneg ⟨8, by decide⟩
    | 27 => .nonneg ⟨9, by decide⟩
    | 28 => .branchGe ⟨26, by decide⟩ 1
    | 29 => .branchGe ⟨30, by decide⟩ 1
    | _ => .sumGe

def mults_262_L3 : Fin 30 → Nat
  | i => match i.val with
    | 0 => 22
    | 1 => 2
    | 2 => 1
    | 3 => 18
    | 4 => 17
    | 5 => 6
    | 6 => 26
    | 7 => 8
    | 8 => 5
    | 9 => 23
    | 10 => 3
    | 11 => 19
    | 12 => 10
    | 13 => 5
    | 14 => 3
    | 15 => 6
    | 16 => 10
    | 17 => 6
    | 18 => 1
    | 19 => 2
    | 20 => 7
    | 21 => 1
    | 22 => 11
    | 23 => 26
    | 24 => 4
    | 25 => 4
    | 26 => 6
    | 27 => 18
    | 28 => 64
    | 29 => 34
    | _ => 0

theorem coeff_cancel_262_L3 :
    ∀ j : Fin 31, (∑ i : Fin 30, (mults_262_L3 i : Int) * (refs_262_L3 i).resolveCoeff S_262 j) = 0 := by
  decide

theorem rhs_neg_262_L3 :
    (∑ i : Fin 30, (mults_262_L3 i : Int) * (refs_262_L3 i).resolveRhs S_262) < 0 := by
  decide

theorem leaf3_infeasible_262 (x : Fin 31 → Int)
    (hroot : S_262.RootHolds x)
    (h_ge_27_1 : (1 : Int) ≤ x ⟨26, by decide⟩)
    (h_ge_31_1 : (1 : Int) ≤ x ⟨30, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 30,
      (∑ j : Fin 31, (refs_262_L3 i).resolveCoeff S_262 j * x j) ≤
      (refs_262_L3 i).resolveRhs S_262 := by
    intro i; fin_cases i
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨9, by decide⟩]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_27_1]
    · simp only [refs_262_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_31_1]
  exact farkas_leaf_unsat _ _ (mults_262_L3) coeff_cancel_262_L3 rhs_neg_262_L3 x hrows

theorem orbit262_occupation_no_model (x : Fin 31 → Int)
    (hroot : S_262.RootHolds x) : False := by
  by_cases hbr_root_31_0 : x ⟨30, by decide⟩ ≤ 0
  ·
    by_cases hbr_L_29_0 : x ⟨28, by decide⟩ ≤ 0
    ·
      exact leaf0_infeasible_262 x hroot hbr_L_29_0 hbr_root_31_0
    ·
      have hbr_L_29_0_ge : (1 : Int) ≤ x ⟨28, by decide⟩ := by omega
      exact leaf1_infeasible_262 x hroot hbr_root_31_0 hbr_L_29_0_ge
  ·
    have hbr_root_31_0_ge : (1 : Int) ≤ x ⟨30, by decide⟩ := by omega
    by_cases hbr_R_27_0 : x ⟨26, by decide⟩ ≤ 0
    ·
      exact leaf2_infeasible_262 x hroot hbr_R_27_0 hbr_root_31_0_ge
    ·
      have hbr_R_27_0_ge : (1 : Int) ≤ x ⟨26, by decide⟩ := by omega
      exact leaf3_infeasible_262 x hroot hbr_R_27_0_ge hbr_root_31_0_ge

end QiushiMatmul
