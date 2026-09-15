import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 200000000
set_option maxRecDepth 8000

namespace QiushiMatmul

abbrev NVAR_415 := 63
abbrev NOCC_415 := 101

-- row 0 = original 29, orbit 101, lb 15, cap 1
private def occRow_415_0 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0)
-- row 1 = original 30, orbit 101, lb 15, cap 1
private def occRow_415_1 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 2 = original 31, orbit 101, lb 15, cap 1
private def occRow_415_2 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 3 = original 42, orbit 101, lb 15, cap 1
private def occRow_415_3 (j : Fin 63) : Int := (if j.val = 16 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 48 then 1 else 0)
-- row 4 = original 47, orbit 101, lb 15, cap 1
private def occRow_415_4 (j : Fin 63) : Int := (if j.val = 18 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 5 = original 327, orbit 141, lb 15, cap 1
private def occRow_415_5 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 6 = original 465, orbit 144, lb 15, cap 1
private def occRow_415_6 (j : Fin 63) : Int := (if j.val = 27 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 7 = original 512, orbit 146, lb 15, cap 1
private def occRow_415_7 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 8 = original 594, orbit 25, lb 11, cap 5
private def occRow_415_8 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- row 9 = original 603, orbit 25, lb 11, cap 5
private def occRow_415_9 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 10 = original 644, orbit 25, lb 11, cap 5
private def occRow_415_10 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 11 = original 645, orbit 25, lb 11, cap 5
private def occRow_415_11 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 12 = original 654, orbit 25, lb 11, cap 5
private def occRow_415_12 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 13 = original 664, orbit 25, lb 11, cap 5
private def occRow_415_13 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 14 = original 673, orbit 25, lb 11, cap 5
private def occRow_415_14 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 15 = original 726, orbit 29, lb 15, cap 1
private def occRow_415_15 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 16 = original 727, orbit 29, lb 15, cap 1
private def occRow_415_16 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 17 = original 730, orbit 29, lb 15, cap 1
private def occRow_415_17 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 18 = original 769, orbit 35, lb 15, cap 1
private def occRow_415_18 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0)
-- row 19 = original 770, orbit 35, lb 15, cap 1
private def occRow_415_19 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0)
-- row 20 = original 771, orbit 35, lb 15, cap 1
private def occRow_415_20 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 21 = original 772, orbit 35, lb 15, cap 1
private def occRow_415_21 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 22 = original 775, orbit 35, lb 15, cap 1
private def occRow_415_22 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0)
-- row 23 = original 776, orbit 35, lb 15, cap 1
private def occRow_415_23 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0)
-- row 24 = original 779, orbit 35, lb 15, cap 1
private def occRow_415_24 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 25 = original 780, orbit 35, lb 15, cap 1
private def occRow_415_25 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 26 = original 782, orbit 35, lb 15, cap 1
private def occRow_415_26 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 27 = original 783, orbit 35, lb 15, cap 1
private def occRow_415_27 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 28 = original 784, orbit 35, lb 15, cap 1
private def occRow_415_28 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 29 = original 786, orbit 35, lb 15, cap 1
private def occRow_415_29 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 30 = original 787, orbit 35, lb 15, cap 1
private def occRow_415_30 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 31 = original 788, orbit 35, lb 15, cap 1
private def occRow_415_31 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 32 = original 789, orbit 35, lb 15, cap 1
private def occRow_415_32 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 33 = original 792, orbit 35, lb 15, cap 1
private def occRow_415_33 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 34 = original 794, orbit 35, lb 15, cap 1
private def occRow_415_34 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 35 = original 795, orbit 35, lb 15, cap 1
private def occRow_415_35 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 36 = original 796, orbit 35, lb 15, cap 1
private def occRow_415_36 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 37 = original 799, orbit 35, lb 15, cap 1
private def occRow_415_37 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 38 = original 800, orbit 35, lb 15, cap 1
private def occRow_415_38 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 39 = original 801, orbit 35, lb 15, cap 1
private def occRow_415_39 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 40 = original 803, orbit 35, lb 15, cap 1
private def occRow_415_40 (j : Fin 63) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 41 = original 804, orbit 35, lb 15, cap 1
private def occRow_415_41 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 42 = original 2187, orbit 10, lb 12, cap 4
private def occRow_415_42 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 43 = original 2566, orbit 2, lb 6, cap 10
private def occRow_415_43 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 44 = original 2573, orbit 2, lb 6, cap 10
private def occRow_415_44 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 45 = original 2602, orbit 2, lb 6, cap 10
private def occRow_415_45 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 46 = original 44, orbit 101, lb 15, cap 1
private def occRow_415_46 (j : Fin 63) : Int := (if j.val = 20 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 47 = original 46, orbit 101, lb 15, cap 1
private def occRow_415_47 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 48 = original 48, orbit 101, lb 15, cap 1
private def occRow_415_48 (j : Fin 63) : Int := (if j.val = 17 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 49 = original 55, orbit 103, lb 15, cap 1
private def occRow_415_49 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 50 = original 57, orbit 103, lb 15, cap 1
private def occRow_415_50 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0)
-- row 51 = original 69, orbit 103, lb 15, cap 1
private def occRow_415_51 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 52 = original 238, orbit 134, lb 15, cap 1
private def occRow_415_52 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 53 = original 286, orbit 141, lb 15, cap 1
private def occRow_415_53 (j : Fin 63) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 54 = original 301, orbit 141, lb 15, cap 1
private def occRow_415_54 (j : Fin 63) : Int := (if j.val = 25 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 55 = original 314, orbit 141, lb 15, cap 1
private def occRow_415_55 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 56 = original 319, orbit 141, lb 15, cap 1
private def occRow_415_56 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 57 = original 322, orbit 141, lb 15, cap 1
private def occRow_415_57 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 58 = original 323, orbit 141, lb 15, cap 1
private def occRow_415_58 (j : Fin 63) : Int := (if j.val = 20 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 59 = original 442, orbit 144, lb 15, cap 1
private def occRow_415_59 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- row 60 = original 444, orbit 144, lb 15, cap 1
private def occRow_415_60 (j : Fin 63) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- row 61 = original 453, orbit 144, lb 15, cap 1
private def occRow_415_61 (j : Fin 63) : Int := (if j.val = 25 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 48 then 1 else 0)
-- row 62 = original 466, orbit 144, lb 15, cap 1
private def occRow_415_62 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 63 = original 471, orbit 144, lb 15, cap 1
private def occRow_415_63 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 64 = original 482, orbit 144, lb 15, cap 1
private def occRow_415_64 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 65 = original 725, orbit 29, lb 15, cap 1
private def occRow_415_65 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 45 then 1 else 0)
-- row 66 = original 785, orbit 35, lb 15, cap 1
private def occRow_415_66 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 67 = original 802, orbit 35, lb 15, cap 1
private def occRow_415_67 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 68 = original 1909, orbit 5, lb 9, cap 7
private def occRow_415_68 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- row 69 = original 1910, orbit 5, lb 9, cap 7
private def occRow_415_69 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 70 = original 1962, orbit 7, lb 9, cap 7
private def occRow_415_70 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 71 = original 1972, orbit 7, lb 9, cap 7
private def occRow_415_71 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 72 = original 2081, orbit 7, lb 9, cap 7
private def occRow_415_72 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 73 = original 2175, orbit 10, lb 12, cap 4
private def occRow_415_73 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 74 = original 2181, orbit 10, lb 12, cap 4
private def occRow_415_74 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 75 = original 2253, orbit 14, lb 12, cap 4
private def occRow_415_75 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 76 = original 2254, orbit 14, lb 12, cap 4
private def occRow_415_76 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 77 = original 28, orbit 101, lb 15, cap 1
private def occRow_415_77 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0)
-- row 78 = original 41, orbit 101, lb 15, cap 1
private def occRow_415_78 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 79 = original 43, orbit 101, lb 15, cap 1
private def occRow_415_79 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 80 = original 63, orbit 103, lb 15, cap 1
private def occRow_415_80 (j : Fin 63) : Int := (if j.val = 16 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 81 = original 64, orbit 103, lb 15, cap 1
private def occRow_415_81 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 82 = original 298, orbit 141, lb 15, cap 1
private def occRow_415_82 (j : Fin 63) : Int := (if j.val = 25 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 83 = original 299, orbit 141, lb 15, cap 1
private def occRow_415_83 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 84 = original 458, orbit 144, lb 15, cap 1
private def occRow_415_84 (j : Fin 63) : Int := (if j.val = 21 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 85 = original 459, orbit 144, lb 15, cap 1
private def occRow_415_85 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 86 = original 463, orbit 144, lb 15, cap 1
private def occRow_415_86 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 87 = original 464, orbit 144, lb 15, cap 1
private def occRow_415_87 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 88 = original 484, orbit 144, lb 15, cap 1
private def occRow_415_88 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 89 = original 488, orbit 144, lb 15, cap 1
private def occRow_415_89 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 90 = original 729, orbit 29, lb 15, cap 1
private def occRow_415_90 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 91 = original 781, orbit 35, lb 15, cap 1
private def occRow_415_91 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 92 = original 790, orbit 35, lb 15, cap 1
private def occRow_415_92 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 93 = original 791, orbit 35, lb 15, cap 1
private def occRow_415_93 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 94 = original 793, orbit 35, lb 15, cap 1
private def occRow_415_94 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 95 = original 1919, orbit 5, lb 9, cap 7
private def occRow_415_95 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 96 = original 1921, orbit 5, lb 9, cap 7
private def occRow_415_96 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 97 = original 1928, orbit 5, lb 9, cap 7
private def occRow_415_97 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 98 = original 2007, orbit 7, lb 9, cap 7
private def occRow_415_98 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 99 = original 2012, orbit 7, lb 9, cap 7
private def occRow_415_99 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 100 = original 2090, orbit 7, lb 9, cap 7
private def occRow_415_100 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)

def occCoeff_415 : Fin 101 → Fin 63 → Int
  | i, j => match i.val with
    | 0 => occRow_415_0 j
    | 1 => occRow_415_1 j
    | 2 => occRow_415_2 j
    | 3 => occRow_415_3 j
    | 4 => occRow_415_4 j
    | 5 => occRow_415_5 j
    | 6 => occRow_415_6 j
    | 7 => occRow_415_7 j
    | 8 => occRow_415_8 j
    | 9 => occRow_415_9 j
    | 10 => occRow_415_10 j
    | 11 => occRow_415_11 j
    | 12 => occRow_415_12 j
    | 13 => occRow_415_13 j
    | 14 => occRow_415_14 j
    | 15 => occRow_415_15 j
    | 16 => occRow_415_16 j
    | 17 => occRow_415_17 j
    | 18 => occRow_415_18 j
    | 19 => occRow_415_19 j
    | 20 => occRow_415_20 j
    | 21 => occRow_415_21 j
    | 22 => occRow_415_22 j
    | 23 => occRow_415_23 j
    | 24 => occRow_415_24 j
    | 25 => occRow_415_25 j
    | 26 => occRow_415_26 j
    | 27 => occRow_415_27 j
    | 28 => occRow_415_28 j
    | 29 => occRow_415_29 j
    | 30 => occRow_415_30 j
    | 31 => occRow_415_31 j
    | 32 => occRow_415_32 j
    | 33 => occRow_415_33 j
    | 34 => occRow_415_34 j
    | 35 => occRow_415_35 j
    | 36 => occRow_415_36 j
    | 37 => occRow_415_37 j
    | 38 => occRow_415_38 j
    | 39 => occRow_415_39 j
    | 40 => occRow_415_40 j
    | 41 => occRow_415_41 j
    | 42 => occRow_415_42 j
    | 43 => occRow_415_43 j
    | 44 => occRow_415_44 j
    | 45 => occRow_415_45 j
    | 46 => occRow_415_46 j
    | 47 => occRow_415_47 j
    | 48 => occRow_415_48 j
    | 49 => occRow_415_49 j
    | 50 => occRow_415_50 j
    | 51 => occRow_415_51 j
    | 52 => occRow_415_52 j
    | 53 => occRow_415_53 j
    | 54 => occRow_415_54 j
    | 55 => occRow_415_55 j
    | 56 => occRow_415_56 j
    | 57 => occRow_415_57 j
    | 58 => occRow_415_58 j
    | 59 => occRow_415_59 j
    | 60 => occRow_415_60 j
    | 61 => occRow_415_61 j
    | 62 => occRow_415_62 j
    | 63 => occRow_415_63 j
    | 64 => occRow_415_64 j
    | 65 => occRow_415_65 j
    | 66 => occRow_415_66 j
    | 67 => occRow_415_67 j
    | 68 => occRow_415_68 j
    | 69 => occRow_415_69 j
    | 70 => occRow_415_70 j
    | 71 => occRow_415_71 j
    | 72 => occRow_415_72 j
    | 73 => occRow_415_73 j
    | 74 => occRow_415_74 j
    | 75 => occRow_415_75 j
    | 76 => occRow_415_76 j
    | 77 => occRow_415_77 j
    | 78 => occRow_415_78 j
    | 79 => occRow_415_79 j
    | 80 => occRow_415_80 j
    | 81 => occRow_415_81 j
    | 82 => occRow_415_82 j
    | 83 => occRow_415_83 j
    | 84 => occRow_415_84 j
    | 85 => occRow_415_85 j
    | 86 => occRow_415_86 j
    | 87 => occRow_415_87 j
    | 88 => occRow_415_88 j
    | 89 => occRow_415_89 j
    | 90 => occRow_415_90 j
    | 91 => occRow_415_91 j
    | 92 => occRow_415_92 j
    | 93 => occRow_415_93 j
    | 94 => occRow_415_94 j
    | 95 => occRow_415_95 j
    | 96 => occRow_415_96 j
    | 97 => occRow_415_97 j
    | 98 => occRow_415_98 j
    | 99 => occRow_415_99 j
    | 100 => occRow_415_100 j
    | _ => 0

def occRhs_415 : Fin 101 → Int
  | i => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => 1
    | 8 => 5
    | 9 => 5
    | 10 => 5
    | 11 => 5
    | 12 => 5
    | 13 => 5
    | 14 => 5
    | 15 => 1
    | 16 => 1
    | 17 => 1
    | 18 => 1
    | 19 => 1
    | 20 => 1
    | 21 => 1
    | 22 => 1
    | 23 => 1
    | 24 => 1
    | 25 => 1
    | 26 => 1
    | 27 => 1
    | 28 => 1
    | 29 => 1
    | 30 => 1
    | 31 => 1
    | 32 => 1
    | 33 => 1
    | 34 => 1
    | 35 => 1
    | 36 => 1
    | 37 => 1
    | 38 => 1
    | 39 => 1
    | 40 => 1
    | 41 => 1
    | 42 => 4
    | 43 => 10
    | 44 => 10
    | 45 => 10
    | 46 => 1
    | 47 => 1
    | 48 => 1
    | 49 => 1
    | 50 => 1
    | 51 => 1
    | 52 => 1
    | 53 => 1
    | 54 => 1
    | 55 => 1
    | 56 => 1
    | 57 => 1
    | 58 => 1
    | 59 => 1
    | 60 => 1
    | 61 => 1
    | 62 => 1
    | 63 => 1
    | 64 => 1
    | 65 => 1
    | 66 => 1
    | 67 => 1
    | 68 => 7
    | 69 => 7
    | 70 => 7
    | 71 => 7
    | 72 => 7
    | 73 => 4
    | 74 => 4
    | 75 => 4
    | 76 => 4
    | 77 => 1
    | 78 => 1
    | 79 => 1
    | 80 => 1
    | 81 => 1
    | 82 => 1
    | 83 => 1
    | 84 => 1
    | 85 => 1
    | 86 => 1
    | 87 => 1
    | 88 => 1
    | 89 => 1
    | 90 => 1
    | 91 => 1
    | 92 => 1
    | 93 => 1
    | 94 => 1
    | 95 => 7
    | 96 => 7
    | 97 => 7
    | 98 => 7
    | 99 => 7
    | 100 => 7
    | _ => 0

def S_415 : OccSys 63 101 :=
  { occCoeff := occCoeff_415, occRhs := occRhs_415, target := 16 }

-- leaf 0, path LL, Farkas rhs -10
def refs_415_L0 : Fin 59 → RowRef 101 63
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
    | 24 => .occ ⟨24, by decide⟩
    | 25 => .occ ⟨25, by decide⟩
    | 26 => .occ ⟨26, by decide⟩
    | 27 => .occ ⟨27, by decide⟩
    | 28 => .occ ⟨28, by decide⟩
    | 29 => .occ ⟨29, by decide⟩
    | 30 => .occ ⟨30, by decide⟩
    | 31 => .occ ⟨31, by decide⟩
    | 32 => .occ ⟨32, by decide⟩
    | 33 => .occ ⟨33, by decide⟩
    | 34 => .occ ⟨34, by decide⟩
    | 35 => .occ ⟨35, by decide⟩
    | 36 => .occ ⟨36, by decide⟩
    | 37 => .occ ⟨37, by decide⟩
    | 38 => .occ ⟨38, by decide⟩
    | 39 => .occ ⟨39, by decide⟩
    | 40 => .occ ⟨40, by decide⟩
    | 41 => .occ ⟨41, by decide⟩
    | 42 => .occ ⟨42, by decide⟩
    | 43 => .occ ⟨43, by decide⟩
    | 44 => .occ ⟨44, by decide⟩
    | 45 => .occ ⟨45, by decide⟩
    | 46 => .sumGe
    | 47 => .nonneg ⟨4, by decide⟩
    | 48 => .nonneg ⟨8, by decide⟩
    | 49 => .nonneg ⟨11, by decide⟩
    | 50 => .nonneg ⟨12, by decide⟩
    | 51 => .nonneg ⟨32, by decide⟩
    | 52 => .nonneg ⟨35, by decide⟩
    | 53 => .nonneg ⟨36, by decide⟩
    | 54 => .nonneg ⟨39, by decide⟩
    | 55 => .nonneg ⟨43, by decide⟩
    | 56 => .nonneg ⟨44, by decide⟩
    | 57 => .branchLe ⟨29, by decide⟩ 0
    | 58 => .branchLe ⟨51, by decide⟩ 0
    | _ => .sumGe

def mults_415_L0 : Fin 59 → Nat
  | i => match i.val with
    | 0 => 20
    | 1 => 84
    | 2 => 104
    | 3 => 180
    | 4 => 180
    | 5 => 12
    | 6 => 12
    | 7 => 24
    | 8 => 60
    | 9 => 6
    | 10 => 36
    | 11 => 60
    | 12 => 60
    | 13 => 60
    | 14 => 6
    | 15 => 74
    | 16 => 108
    | 17 => 108
    | 18 => 71
    | 19 => 21
    | 20 => 199
    | 21 => 169
    | 22 => 77
    | 23 => 193
    | 24 => 27
    | 25 => 163
    | 26 => 222
    | 27 => 108
    | 28 => 66
    | 29 => 54
    | 30 => 114
    | 31 => 114
    | 32 => 114
    | 33 => 54
    | 34 => 72
    | 35 => 114
    | 36 => 66
    | 37 => 222
    | 38 => 108
    | 39 => 72
    | 40 => 66
    | 41 => 66
    | 42 => 6
    | 43 => 42
    | 44 => 6
    | 45 => 6
    | 46 => 342
    | 47 => 228
    | 48 => 288
    | 49 => 528
    | 50 => 228
    | 51 => 964
    | 52 => 192
    | 53 => 192
    | 54 => 436
    | 55 => 532
    | 56 => 1060
    | 57 => 336
    | 58 => 336
    | _ => 0

theorem coeff_cancel_415_L0 :
    ∀ j : Fin 63, (∑ i : Fin 59, (mults_415_L0 i : Int) * (refs_415_L0 i).resolveCoeff S_415 j) = 0 := by
  decide

theorem rhs_neg_415_L0 :
    (∑ i : Fin 59, (mults_415_L0 i : Int) * (refs_415_L0 i).resolveRhs S_415) < 0 := by
  decide

theorem leaf0_infeasible_415 (x : Fin 63 → Int)
    (hroot : S_415.RootHolds x)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 59,
      (∑ j : Fin 63, (refs_415_L0 i).resolveCoeff S_415 j * x j) ≤
      (refs_415_L0 i).resolveRhs S_415 := by
    intro i; fin_cases i
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨11, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨35, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨36, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_415_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
  exact farkas_leaf_unsat _ _ (mults_415_L0) coeff_cancel_415_L0 rhs_neg_415_L0 x hrows

-- leaf 1, path LR, Farkas rhs -34658
def refs_415_L1 : Fin 64 → RowRef 101 63
  | i => match i.val with
    | 0 => .sumGe
    | 1 => .nonneg ⟨8, by decide⟩
    | 2 => .nonneg ⟨12, by decide⟩
    | 3 => .nonneg ⟨22, by decide⟩
    | 4 => .nonneg ⟨32, by decide⟩
    | 5 => .nonneg ⟨34, by decide⟩
    | 6 => .nonneg ⟨35, by decide⟩
    | 7 => .nonneg ⟨39, by decide⟩
    | 8 => .nonneg ⟨40, by decide⟩
    | 9 => .nonneg ⟨43, by decide⟩
    | 10 => .nonneg ⟨44, by decide⟩
    | 11 => .nonneg ⟨59, by decide⟩
    | 12 => .nonneg ⟨62, by decide⟩
    | 13 => .occ ⟨1, by decide⟩
    | 14 => .occ ⟨2, by decide⟩
    | 15 => .occ ⟨46, by decide⟩
    | 16 => .occ ⟨47, by decide⟩
    | 17 => .occ ⟨48, by decide⟩
    | 18 => .occ ⟨49, by decide⟩
    | 19 => .occ ⟨50, by decide⟩
    | 20 => .occ ⟨51, by decide⟩
    | 21 => .occ ⟨52, by decide⟩
    | 22 => .occ ⟨53, by decide⟩
    | 23 => .occ ⟨54, by decide⟩
    | 24 => .occ ⟨55, by decide⟩
    | 25 => .occ ⟨56, by decide⟩
    | 26 => .occ ⟨57, by decide⟩
    | 27 => .occ ⟨58, by decide⟩
    | 28 => .occ ⟨59, by decide⟩
    | 29 => .occ ⟨60, by decide⟩
    | 30 => .occ ⟨61, by decide⟩
    | 31 => .occ ⟨62, by decide⟩
    | 32 => .occ ⟨63, by decide⟩
    | 33 => .occ ⟨64, by decide⟩
    | 34 => .occ ⟨65, by decide⟩
    | 35 => .occ ⟨15, by decide⟩
    | 36 => .occ ⟨16, by decide⟩
    | 37 => .occ ⟨20, by decide⟩
    | 38 => .occ ⟨21, by decide⟩
    | 39 => .occ ⟨22, by decide⟩
    | 40 => .occ ⟨23, by decide⟩
    | 41 => .occ ⟨24, by decide⟩
    | 42 => .occ ⟨25, by decide⟩
    | 43 => .occ ⟨26, by decide⟩
    | 44 => .occ ⟨27, by decide⟩
    | 45 => .occ ⟨28, by decide⟩
    | 46 => .occ ⟨66, by decide⟩
    | 47 => .occ ⟨30, by decide⟩
    | 48 => .occ ⟨31, by decide⟩
    | 49 => .occ ⟨32, by decide⟩
    | 50 => .occ ⟨37, by decide⟩
    | 51 => .occ ⟨67, by decide⟩
    | 52 => .occ ⟨41, by decide⟩
    | 53 => .occ ⟨68, by decide⟩
    | 54 => .occ ⟨69, by decide⟩
    | 55 => .occ ⟨70, by decide⟩
    | 56 => .occ ⟨71, by decide⟩
    | 57 => .occ ⟨72, by decide⟩
    | 58 => .occ ⟨73, by decide⟩
    | 59 => .occ ⟨74, by decide⟩
    | 60 => .occ ⟨75, by decide⟩
    | 61 => .occ ⟨76, by decide⟩
    | 62 => .branchGe ⟨29, by decide⟩ 1
    | 63 => .branchLe ⟨51, by decide⟩ 0
    | _ => .sumGe

def mults_415_L1 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 22950
    | 1 => 42310
    | 2 => 3216
    | 3 => 10354
    | 4 => 31824
    | 5 => 1291
    | 6 => 16126
    | 7 => 3714
    | 8 => 2688
    | 9 => 36257
    | 10 => 43039
    | 11 => 1393
    | 12 => 8164
    | 13 => 5444
    | 14 => 214
    | 15 => 8290
    | 16 => 22950
    | 17 => 2688
    | 18 => 5305
    | 19 => 4929
    | 20 => 5056
    | 21 => 1448
    | 22 => 4208
    | 23 => 846
    | 24 => 14934
    | 25 => 22254
    | 26 => 4404
    | 27 => 4878
    | 28 => 4904
    | 29 => 948
    | 30 => 922
    | 31 => 14262
    | 32 => 11777
    | 33 => 1144
    | 34 => 1879
    | 35 => 803
    | 36 => 3856
    | 37 => 6809
    | 38 => 7906
    | 39 => 6522
    | 40 => 4369
    | 41 => 7473
    | 42 => 488
    | 43 => 9061
    | 44 => 8688
    | 45 => 4853
    | 46 => 17894
    | 47 => 7639
    | 48 => 10855
    | 49 => 3785
    | 50 => 1720
    | 51 => 13591
    | 52 => 8487
    | 53 => 7633
    | 54 => 3203
    | 55 => 1726
    | 56 => 1352
    | 57 => 9036
    | 58 => 696
    | 59 => 1768
    | 60 => 3336
    | 61 => 272
    | 62 => 120879
    | 63 => 19614
    | _ => 0

theorem coeff_cancel_415_L1 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_415_L1 i : Int) * (refs_415_L1 i).resolveCoeff S_415 j) = 0 := by
  decide

theorem rhs_neg_415_L1 :
    (∑ i : Fin 64, (mults_415_L1 i : Int) * (refs_415_L1 i).resolveRhs S_415) < 0 := by
  decide

theorem leaf1_infeasible_415 (x : Fin 63 → Int)
    (hroot : S_415.RootHolds x)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_ge_30_1 : (1 : Int) ≤ x ⟨29, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_415_L1 i).resolveCoeff S_415 j * x j) ≤
      (refs_415_L1 i).resolveRhs S_415 := by
    intro i; fin_cases i
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨35, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨62, by decide⟩]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨51, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨53, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨58, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨59, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨65, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨66, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨67, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨68, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨69, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨70, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨71, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨72, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨73, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨74, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨75, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_30_1]
    · simp only [refs_415_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
  exact farkas_leaf_unsat _ _ (mults_415_L1) coeff_cancel_415_L1 rhs_neg_415_L1 x hrows

-- leaf 2, path R, Farkas rhs -284
def refs_415_L2 : Fin 60 → RowRef 101 63
  | i => match i.val with
    | 0 => .sumGe
    | 1 => .nonneg ⟨4, by decide⟩
    | 2 => .nonneg ⟨8, by decide⟩
    | 3 => .nonneg ⟨27, by decide⟩
    | 4 => .nonneg ⟨31, by decide⟩
    | 5 => .nonneg ⟨32, by decide⟩
    | 6 => .nonneg ⟨36, by decide⟩
    | 7 => .nonneg ⟨39, by decide⟩
    | 8 => .nonneg ⟨43, by decide⟩
    | 9 => .nonneg ⟨44, by decide⟩
    | 10 => .nonneg ⟨60, by decide⟩
    | 11 => .occ ⟨77, by decide⟩
    | 12 => .occ ⟨0, by decide⟩
    | 13 => .occ ⟨2, by decide⟩
    | 14 => .occ ⟨78, by decide⟩
    | 15 => .occ ⟨79, by decide⟩
    | 16 => .occ ⟨4, by decide⟩
    | 17 => .occ ⟨48, by decide⟩
    | 18 => .occ ⟨80, by decide⟩
    | 19 => .occ ⟨81, by decide⟩
    | 20 => .occ ⟨82, by decide⟩
    | 21 => .occ ⟨83, by decide⟩
    | 22 => .occ ⟨84, by decide⟩
    | 23 => .occ ⟨85, by decide⟩
    | 24 => .occ ⟨86, by decide⟩
    | 25 => .occ ⟨87, by decide⟩
    | 26 => .occ ⟨88, by decide⟩
    | 27 => .occ ⟨89, by decide⟩
    | 28 => .occ ⟨15, by decide⟩
    | 29 => .occ ⟨90, by decide⟩
    | 30 => .occ ⟨18, by decide⟩
    | 31 => .occ ⟨19, by decide⟩
    | 32 => .occ ⟨20, by decide⟩
    | 33 => .occ ⟨21, by decide⟩
    | 34 => .occ ⟨22, by decide⟩
    | 35 => .occ ⟨23, by decide⟩
    | 36 => .occ ⟨24, by decide⟩
    | 37 => .occ ⟨25, by decide⟩
    | 38 => .occ ⟨91, by decide⟩
    | 39 => .occ ⟨26, by decide⟩
    | 40 => .occ ⟨28, by decide⟩
    | 41 => .occ ⟨66, by decide⟩
    | 42 => .occ ⟨29, by decide⟩
    | 43 => .occ ⟨30, by decide⟩
    | 44 => .occ ⟨31, by decide⟩
    | 45 => .occ ⟨92, by decide⟩
    | 46 => .occ ⟨93, by decide⟩
    | 47 => .occ ⟨94, by decide⟩
    | 48 => .occ ⟨35, by decide⟩
    | 49 => .occ ⟨37, by decide⟩
    | 50 => .occ ⟨38, by decide⟩
    | 51 => .occ ⟨67, by decide⟩
    | 52 => .occ ⟨41, by decide⟩
    | 53 => .occ ⟨95, by decide⟩
    | 54 => .occ ⟨96, by decide⟩
    | 55 => .occ ⟨97, by decide⟩
    | 56 => .occ ⟨98, by decide⟩
    | 57 => .occ ⟨99, by decide⟩
    | 58 => .occ ⟨100, by decide⟩
    | 59 => .branchGe ⟨51, by decide⟩ 1
    | _ => .sumGe

def mults_415_L2 : Fin 60 → Nat
  | i => match i.val with
    | 0 => 192
    | 1 => 192
    | 2 => 268
    | 3 => 96
    | 4 => 12
    | 5 => 200
    | 6 => 24
    | 7 => 436
    | 8 => 356
    | 9 => 524
    | 10 => 96
    | 11 => 36
    | 12 => 44
    | 13 => 8
    | 14 => 12
    | 15 => 192
    | 16 => 44
    | 17 => 44
    | 18 => 12
    | 19 => 12
    | 20 => 132
    | 21 => 132
    | 22 => 132
    | 23 => 132
    | 24 => 36
    | 25 => 36
    | 26 => 36
    | 27 => 36
    | 28 => 8
    | 29 => 8
    | 30 => 47
    | 31 => 39
    | 32 => 79
    | 33 => 79
    | 34 => 47
    | 35 => 13
    | 36 => 39
    | 37 => 13
    | 38 => 180
    | 39 => 84
    | 40 => 96
    | 41 => 41
    | 42 => 15
    | 43 => 45
    | 44 => 11
    | 45 => 12
    | 46 => 12
    | 47 => 96
    | 48 => 96
    | 49 => 77
    | 50 => 41
    | 51 => 81
    | 52 => 45
    | 53 => 4
    | 54 => 22
    | 55 => 66
    | 56 => 8
    | 57 => 62
    | 58 => 30
    | 59 => 936
    | _ => 0

theorem coeff_cancel_415_L2 :
    ∀ j : Fin 63, (∑ i : Fin 60, (mults_415_L2 i : Int) * (refs_415_L2 i).resolveCoeff S_415 j) = 0 := by
  decide

theorem rhs_neg_415_L2 :
    (∑ i : Fin 60, (mults_415_L2 i : Int) * (refs_415_L2 i).resolveRhs S_415) < 0 := by
  decide

theorem leaf2_infeasible_415 (x : Fin 63 → Int)
    (hroot : S_415.RootHolds x)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 60,
      (∑ j : Fin 63, (refs_415_L2 i).resolveCoeff S_415 j * x j) ≤
      (refs_415_L2 i).resolveRhs S_415 := by
    intro i; fin_cases i
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨36, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨60, by decide⟩]
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨77, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨78, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨82, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨83, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨84, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨86, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨88, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨89, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨90, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨66, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨92, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨93, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨67, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨95, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨96, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨97, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨98, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨99, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨100, by decide⟩
    · simp only [refs_415_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
  exact farkas_leaf_unsat _ _ (mults_415_L2) coeff_cancel_415_L2 rhs_neg_415_L2 x hrows

theorem orbit415_occupation_no_model (x : Fin 63 → Int)
    (hroot : S_415.RootHolds x) : False := by
  by_cases hbr_root_52_0 : x ⟨51, by decide⟩ ≤ 0
  ·
    by_cases hbr_L_30_0 : x ⟨29, by decide⟩ ≤ 0
    ·
      exact leaf0_infeasible_415 x hroot hbr_L_30_0 hbr_root_52_0
    ·
      have hbr_L_30_0_ge : (1 : Int) ≤ x ⟨29, by decide⟩ := by omega
      exact leaf1_infeasible_415 x hroot hbr_root_52_0 hbr_L_30_0_ge
  ·
    have hbr_root_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
    exact leaf2_infeasible_415 x hroot hbr_root_52_0_ge

end QiushiMatmul
