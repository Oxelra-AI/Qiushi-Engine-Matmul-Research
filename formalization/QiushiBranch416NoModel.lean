import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 200000000
set_option maxRecDepth 8000

namespace QiushiMatmul

abbrev NVAR_416 := 63
abbrev NOCC_416 := 373

-- row 0 = original 53, orbit 103, lb 15, cap 1
private def occRow_416_0 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0)
-- row 1 = original 63, orbit 103, lb 15, cap 1
private def occRow_416_1 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 2 = original 280, orbit 134, lb 15, cap 1
private def occRow_416_2 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 3 = original 368, orbit 141, lb 15, cap 1
private def occRow_416_3 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 4 = original 508, orbit 23, lb 12, cap 4
private def occRow_416_4 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 5 = original 509, orbit 23, lb 12, cap 4
private def occRow_416_5 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 6 = original 510, orbit 23, lb 12, cap 4
private def occRow_416_6 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 7 = original 668, orbit 29, lb 15, cap 1
private def occRow_416_7 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 8 = original 732, orbit 35, lb 15, cap 1
private def occRow_416_8 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 9 = original 735, orbit 35, lb 15, cap 1
private def occRow_416_9 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- row 10 = original 737, orbit 35, lb 15, cap 1
private def occRow_416_10 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 11 = original 738, orbit 35, lb 15, cap 1
private def occRow_416_11 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 12 = original 739, orbit 35, lb 15, cap 1
private def occRow_416_12 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 13 = original 742, orbit 35, lb 15, cap 1
private def occRow_416_13 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 14 = original 744, orbit 35, lb 15, cap 1
private def occRow_416_14 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 15 = original 748, orbit 35, lb 15, cap 1
private def occRow_416_15 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 16 = original 750, orbit 35, lb 15, cap 1
private def occRow_416_16 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 17 = original 751, orbit 35, lb 15, cap 1
private def occRow_416_17 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 18 = original 753, orbit 35, lb 15, cap 1
private def occRow_416_18 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 19 = original 754, orbit 35, lb 15, cap 1
private def occRow_416_19 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 20 = original 755, orbit 35, lb 15, cap 1
private def occRow_416_20 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 21 = original 1640, orbit 55, lb 14, cap 2
private def occRow_416_21 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 22 = original 1710, orbit 56, lb 14, cap 2
private def occRow_416_22 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 23 = original 1814, orbit 5, lb 9, cap 7
private def occRow_416_23 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 24 = original 1885, orbit 7, lb 9, cap 7
private def occRow_416_24 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 25 = original 1937, orbit 7, lb 9, cap 7
private def occRow_416_25 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 26 = original 1974, orbit 7, lb 9, cap 7
private def occRow_416_26 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 27 = original 2053, orbit 10, lb 12, cap 4
private def occRow_416_27 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 28 = original 2058, orbit 10, lb 12, cap 4
private def occRow_416_28 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 29 = original 2062, orbit 10, lb 12, cap 4
private def occRow_416_29 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 30 = original 2079, orbit 11, lb 12, cap 4
private def occRow_416_30 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 31 = original 2254, orbit 14, lb 12, cap 4
private def occRow_416_31 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 32 = original 2260, orbit 14, lb 12, cap 4
private def occRow_416_32 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 33 = original 2275, orbit 14, lb 12, cap 4
private def occRow_416_33 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 34 = original 2278, orbit 14, lb 12, cap 4
private def occRow_416_34 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 35 = original 2293, orbit 14, lb 12, cap 4
private def occRow_416_35 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 36 = original 2303, orbit 14, lb 12, cap 4
private def occRow_416_36 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 37 = original 2339, orbit 14, lb 12, cap 4
private def occRow_416_37 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 38 = original 2485, orbit 2, lb 6, cap 10
private def occRow_416_38 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 39 = original 2501, orbit 3, lb 9, cap 7
private def occRow_416_39 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 40 = original 2502, orbit 3, lb 9, cap 7
private def occRow_416_40 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 41 = original 2507, orbit 3, lb 9, cap 7
private def occRow_416_41 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 42 = original 15, orbit 89, lb 12, cap 4
private def occRow_416_42 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- row 43 = original 61, orbit 103, lb 15, cap 1
private def occRow_416_43 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 44 = original 64, orbit 103, lb 15, cap 1
private def occRow_416_44 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 45 = original 67, orbit 103, lb 15, cap 1
private def occRow_416_45 (j : Fin 63) : Int := (if j.val = 17 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 46 = original 357, orbit 141, lb 15, cap 1
private def occRow_416_46 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 47 = original 417, orbit 144, lb 15, cap 1
private def occRow_416_47 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 48 = original 418, orbit 144, lb 15, cap 1
private def occRow_416_48 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 49 = original 667, orbit 29, lb 15, cap 1
private def occRow_416_49 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0)
-- row 50 = original 749, orbit 35, lb 15, cap 1
private def occRow_416_50 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 51 = original 1617, orbit 55, lb 14, cap 2
private def occRow_416_51 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 52 = original 1631, orbit 55, lb 14, cap 2
private def occRow_416_52 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 53 = original 1657, orbit 55, lb 14, cap 2
private def occRow_416_53 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 54 = original 1931, orbit 7, lb 9, cap 7
private def occRow_416_54 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 55 = original 2052, orbit 10, lb 12, cap 4
private def occRow_416_55 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 56 = original 2080, orbit 11, lb 12, cap 4
private def occRow_416_56 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 57 = original 2081, orbit 11, lb 12, cap 4
private def occRow_416_57 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 58 = original 2219, orbit 14, lb 12, cap 4
private def occRow_416_58 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 59 = original 2223, orbit 14, lb 12, cap 4
private def occRow_416_59 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 60 = original 2252, orbit 14, lb 12, cap 4
private def occRow_416_60 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 61 = original 2326, orbit 14, lb 12, cap 4
private def occRow_416_61 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 62 = original 2329, orbit 14, lb 12, cap 4
private def occRow_416_62 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 63 = original 2496, orbit 3, lb 9, cap 7
private def occRow_416_63 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 64 = original 55, orbit 103, lb 15, cap 1
private def occRow_416_64 (j : Fin 63) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- row 65 = original 58, orbit 103, lb 15, cap 1
private def occRow_416_65 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 66 = original 129, orbit 112, lb 15, cap 1
private def occRow_416_66 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 67 = original 359, orbit 141, lb 15, cap 1
private def occRow_416_67 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 68 = original 372, orbit 141, lb 15, cap 1
private def occRow_416_68 (j : Fin 63) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 69 = original 449, orbit 146, lb 15, cap 1
private def occRow_416_69 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 70 = original 576, orbit 25, lb 11, cap 5
private def occRow_416_70 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 71 = original 1132, orbit 43, lb 12, cap 4
private def occRow_416_71 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 72 = original 1602, orbit 55, lb 14, cap 2
private def occRow_416_72 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 73 = original 1607, orbit 55, lb 14, cap 2
private def occRow_416_73 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 74 = original 1662, orbit 55, lb 14, cap 2
private def occRow_416_74 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 75 = original 1698, orbit 56, lb 14, cap 2
private def occRow_416_75 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 76 = original 1882, orbit 7, lb 9, cap 7
private def occRow_416_76 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 77 = original 1969, orbit 7, lb 9, cap 7
private def occRow_416_77 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 78 = original 2048, orbit 10, lb 12, cap 4
private def occRow_416_78 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 79 = original 2284, orbit 14, lb 12, cap 4
private def occRow_416_79 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 80 = original 2497, orbit 3, lb 9, cap 7
private def occRow_416_80 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 81 = original 16, orbit 89, lb 12, cap 4
private def occRow_416_81 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0)
-- row 82 = original 161, orbit 120, lb 15, cap 1
private def occRow_416_82 (j : Fin 63) : Int := (if j.val = 16 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 47 then 1 else 0)
-- row 83 = original 165, orbit 120, lb 15, cap 1
private def occRow_416_83 (j : Fin 63) : Int := (if j.val = 30 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 84 = original 254, orbit 130, lb 15, cap 1
private def occRow_416_84 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 85 = original 363, orbit 141, lb 15, cap 1
private def occRow_416_85 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 86 = original 425, orbit 144, lb 15, cap 1
private def occRow_416_86 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 87 = original 695, orbit 31, lb 15, cap 1
private def occRow_416_87 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 88 = original 1126, orbit 43, lb 12, cap 4
private def occRow_416_88 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 89 = original 1816, orbit 5, lb 9, cap 7
private def occRow_416_89 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 90 = original 1881, orbit 7, lb 9, cap 7
private def occRow_416_90 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 91 = original 2054, orbit 10, lb 12, cap 4
private def occRow_416_91 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 92 = original 2085, orbit 11, lb 12, cap 4
private def occRow_416_92 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 93 = original 2322, orbit 14, lb 12, cap 4
private def occRow_416_93 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 94 = original 65, orbit 103, lb 15, cap 1
private def occRow_416_94 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 95 = original 133, orbit 112, lb 15, cap 1
private def occRow_416_95 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 96 = original 369, orbit 141, lb 15, cap 1
private def occRow_416_96 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 97 = original 370, orbit 141, lb 15, cap 1
private def occRow_416_97 (j : Fin 63) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 98 = original 457, orbit 146, lb 15, cap 1
private def occRow_416_98 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 99 = original 458, orbit 146, lb 15, cap 1
private def occRow_416_99 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 100 = original 743, orbit 35, lb 15, cap 1
private def occRow_416_100 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 101 = original 746, orbit 35, lb 15, cap 1
private def occRow_416_101 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0)
-- row 102 = original 1108, orbit 43, lb 12, cap 4
private def occRow_416_102 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 103 = original 1133, orbit 43, lb 12, cap 4
private def occRow_416_103 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 104 = original 1665, orbit 55, lb 14, cap 2
private def occRow_416_104 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 105 = original 1699, orbit 56, lb 14, cap 2
private def occRow_416_105 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 106 = original 1972, orbit 7, lb 9, cap 7
private def occRow_416_106 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 107 = original 2227, orbit 14, lb 12, cap 4
private def occRow_416_107 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 108 = original 2244, orbit 14, lb 12, cap 4
private def occRow_416_108 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 109 = original 2285, orbit 14, lb 12, cap 4
private def occRow_416_109 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 110 = original 2465, orbit 2, lb 6, cap 10
private def occRow_416_110 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 111 = original 62, orbit 103, lb 15, cap 1
private def occRow_416_111 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 48 then 1 else 0)
-- row 112 = original 128, orbit 112, lb 15, cap 1
private def occRow_416_112 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 113 = original 367, orbit 141, lb 15, cap 1
private def occRow_416_113 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 114 = original 462, orbit 146, lb 15, cap 1
private def occRow_416_114 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 115 = original 553, orbit 25, lb 11, cap 5
private def occRow_416_115 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0)
-- row 116 = original 557, orbit 25, lb 11, cap 5
private def occRow_416_116 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0)
-- row 117 = original 573, orbit 25, lb 11, cap 5
private def occRow_416_117 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 118 = original 747, orbit 35, lb 15, cap 1
private def occRow_416_118 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 119 = original 1637, orbit 55, lb 14, cap 2
private def occRow_416_119 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 120 = original 1726, orbit 56, lb 14, cap 2
private def occRow_416_120 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 121 = original 2075, orbit 11, lb 12, cap 4
private def occRow_416_121 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 122 = original 2258, orbit 14, lb 12, cap 4
private def occRow_416_122 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 123 = original 2265, orbit 14, lb 12, cap 4
private def occRow_416_123 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 124 = original 2315, orbit 14, lb 12, cap 4
private def occRow_416_124 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 125 = original 2494, orbit 2, lb 6, cap 10
private def occRow_416_125 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 126 = original 2506, orbit 3, lb 9, cap 7
private def occRow_416_126 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 127 = original 127, orbit 112, lb 15, cap 1
private def occRow_416_127 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 45 then 1 else 0)
-- row 128 = original 135, orbit 112, lb 15, cap 1
private def occRow_416_128 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 129 = original 361, orbit 141, lb 15, cap 1
private def occRow_416_129 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 130 = original 362, orbit 141, lb 15, cap 1
private def occRow_416_130 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 131 = original 364, orbit 141, lb 15, cap 1
private def occRow_416_131 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 132 = original 452, orbit 146, lb 15, cap 1
private def occRow_416_132 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 133 = original 456, orbit 146, lb 15, cap 1
private def occRow_416_133 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 134 = original 562, orbit 25, lb 11, cap 5
private def occRow_416_134 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 135 = original 1605, orbit 55, lb 14, cap 2
private def occRow_416_135 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 136 = original 1636, orbit 55, lb 14, cap 2
private def occRow_416_136 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 137 = original 1643, orbit 55, lb 14, cap 2
private def occRow_416_137 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 138 = original 1647, orbit 55, lb 14, cap 2
private def occRow_416_138 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 139 = original 1689, orbit 56, lb 14, cap 2
private def occRow_416_139 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 140 = original 1934, orbit 7, lb 9, cap 7
private def occRow_416_140 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 141 = original 2050, orbit 10, lb 12, cap 4
private def occRow_416_141 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 142 = original 2056, orbit 10, lb 12, cap 4
private def occRow_416_142 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 143 = original 2060, orbit 10, lb 12, cap 4
private def occRow_416_143 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 144 = original 2063, orbit 10, lb 12, cap 4
private def occRow_416_144 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 145 = original 2198, orbit 14, lb 12, cap 4
private def occRow_416_145 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 146 = original 2203, orbit 14, lb 12, cap 4
private def occRow_416_146 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 147 = original 2290, orbit 14, lb 12, cap 4
private def occRow_416_147 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 148 = original 2331, orbit 14, lb 12, cap 4
private def occRow_416_148 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 149 = original 2505, orbit 3, lb 9, cap 7
private def occRow_416_149 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 150 = original 166, orbit 120, lb 15, cap 1
private def occRow_416_150 (j : Fin 63) : Int := (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 151 = original 252, orbit 130, lb 15, cap 1
private def occRow_416_151 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 152 = original 358, orbit 141, lb 15, cap 1
private def occRow_416_152 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 48 then 1 else 0)
-- row 153 = original 427, orbit 144, lb 15, cap 1
private def occRow_416_153 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 154 = original 428, orbit 144, lb 15, cap 1
private def occRow_416_154 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 155 = original 752, orbit 35, lb 15, cap 1
private def occRow_416_155 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 156 = original 1621, orbit 55, lb 14, cap 2
private def occRow_416_156 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 157 = original 1629, orbit 55, lb 14, cap 2
private def occRow_416_157 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 158 = original 1653, orbit 55, lb 14, cap 2
private def occRow_416_158 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 159 = original 1661, orbit 55, lb 14, cap 2
private def occRow_416_159 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 160 = original 1936, orbit 7, lb 9, cap 7
private def occRow_416_160 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 161 = original 2066, orbit 10, lb 12, cap 4
private def occRow_416_161 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 162 = original 2283, orbit 14, lb 12, cap 4
private def occRow_416_162 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 163 = original 2302, orbit 14, lb 12, cap 4
private def occRow_416_163 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 164 = original 52, orbit 103, lb 15, cap 1
private def occRow_416_164 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 165 = original 60, orbit 103, lb 15, cap 1
private def occRow_416_165 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 166 = original 66, orbit 103, lb 15, cap 1
private def occRow_416_166 (j : Fin 63) : Int := (if j.val = 29 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 167 = original 745, orbit 35, lb 15, cap 1
private def occRow_416_167 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0)
-- row 168 = original 2222, orbit 14, lb 12, cap 4
private def occRow_416_168 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 169 = original 2225, orbit 14, lb 12, cap 4
private def occRow_416_169 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 170 = original 2226, orbit 14, lb 12, cap 4
private def occRow_416_170 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 171 = original 2229, orbit 14, lb 12, cap 4
private def occRow_416_171 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 172 = original 18, orbit 93, lb 15, cap 1
private def occRow_416_172 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0)
-- row 173 = original 106, orbit 111, lb 14, cap 2
private def occRow_416_173 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0)
-- row 174 = original 108, orbit 111, lb 14, cap 2
private def occRow_416_174 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 175 = original 1098, orbit 43, lb 12, cap 4
private def occRow_416_175 (j : Fin 63) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 176 = original 1915, orbit 7, lb 9, cap 7
private def occRow_416_176 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 177 = original 2051, orbit 10, lb 12, cap 4
private def occRow_416_177 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 178 = original 2084, orbit 11, lb 12, cap 4
private def occRow_416_178 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 179 = original 2087, orbit 11, lb 12, cap 4
private def occRow_416_179 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 180 = original 421, orbit 144, lb 15, cap 1
private def occRow_416_180 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 181 = original 1973, orbit 7, lb 9, cap 7
private def occRow_416_181 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 182 = original 2076, orbit 11, lb 12, cap 4
private def occRow_416_182 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 183 = original 2077, orbit 11, lb 12, cap 4
private def occRow_416_183 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 184 = original 2201, orbit 14, lb 12, cap 4
private def occRow_416_184 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 185 = original 2221, orbit 14, lb 12, cap 4
private def occRow_416_185 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 186 = original 27, orbit 99, lb 15, cap 1
private def occRow_416_186 (j : Fin 63) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 187 = original 54, orbit 103, lb 15, cap 1
private def occRow_416_187 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 23 then 1 else 0)
-- row 188 = original 59, orbit 103, lb 15, cap 1
private def occRow_416_188 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 189 = original 375, orbit 141, lb 15, cap 1
private def occRow_416_189 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 190 = original 376, orbit 141, lb 15, cap 1
private def occRow_416_190 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 191 = original 571, orbit 25, lb 11, cap 5
private def occRow_416_191 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 192 = original 1603, orbit 55, lb 14, cap 2
private def occRow_416_192 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 193 = original 1634, orbit 55, lb 14, cap 2
private def occRow_416_193 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 194 = original 1646, orbit 55, lb 14, cap 2
private def occRow_416_194 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 195 = original 1652, orbit 55, lb 14, cap 2
private def occRow_416_195 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 196 = original 1682, orbit 56, lb 14, cap 2
private def occRow_416_196 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 197 = original 1684, orbit 56, lb 14, cap 2
private def occRow_416_197 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 198 = original 1729, orbit 56, lb 14, cap 2
private def occRow_416_198 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 199 = original 1739, orbit 56, lb 14, cap 2
private def occRow_416_199 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 200 = original 1913, orbit 7, lb 9, cap 7
private def occRow_416_200 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 201 = original 1914, orbit 7, lb 9, cap 7
private def occRow_416_201 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 202 = original 2212, orbit 14, lb 12, cap 4
private def occRow_416_202 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 203 = original 2299, orbit 14, lb 12, cap 4
private def occRow_416_203 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 204 = original 2304, orbit 14, lb 12, cap 4
private def occRow_416_204 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 205 = original 2336, orbit 14, lb 12, cap 4
private def occRow_416_205 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 206 = original 2493, orbit 2, lb 6, cap 10
private def occRow_416_206 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 207 = original 186, orbit 124, lb 15, cap 1
private def occRow_416_207 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0)
-- row 208 = original 244, orbit 130, lb 15, cap 1
private def occRow_416_208 (j : Fin 63) : Int := (if j.val = 20 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 209 = original 2082, orbit 11, lb 12, cap 4
private def occRow_416_209 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 210 = original 2434, orbit 16, lb 12, cap 4
private def occRow_416_210 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 211 = original 2343, orbit 14, lb 12, cap 4
private def occRow_416_211 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 212 = original 2348, orbit 14, lb 12, cap 4
private def occRow_416_212 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 213 = original 580, orbit 25, lb 11, cap 5
private def occRow_416_213 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 214 = original 597, orbit 25, lb 11, cap 5
private def occRow_416_214 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 215 = original 1806, orbit 5, lb 9, cap 7
private def occRow_416_215 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 216 = original 2270, orbit 14, lb 12, cap 4
private def occRow_416_216 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 217 = original 2456, orbit 2, lb 6, cap 10
private def occRow_416_217 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 218 = original 2460, orbit 2, lb 6, cap 10
private def occRow_416_218 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 219 = original 13, orbit 89, lb 12, cap 4
private def occRow_416_219 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0)
-- row 220 = original 23, orbit 98, lb 15, cap 1
private def occRow_416_220 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 221 = original 238, orbit 130, lb 15, cap 1
private def occRow_416_221 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 222 = original 604, orbit 25, lb 11, cap 5
private def occRow_416_222 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 223 = original 1678, orbit 56, lb 14, cap 2
private def occRow_416_223 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 224 = original 1891, orbit 7, lb 9, cap 7
private def occRow_416_224 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 225 = original 2055, orbit 10, lb 12, cap 4
private def occRow_416_225 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 226 = original 2202, orbit 14, lb 12, cap 4
private def occRow_416_226 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 227 = original 131, orbit 112, lb 15, cap 1
private def occRow_416_227 (j : Fin 63) : Int := (if j.val = 17 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 228 = original 243, orbit 130, lb 15, cap 1
private def occRow_416_228 (j : Fin 63) : Int := (if j.val = 20 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 229 = original 1628, orbit 55, lb 14, cap 2
private def occRow_416_229 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 230 = original 1670, orbit 56, lb 14, cap 2
private def occRow_416_230 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 231 = original 1679, orbit 56, lb 14, cap 2
private def occRow_416_231 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 232 = original 1681, orbit 56, lb 14, cap 2
private def occRow_416_232 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 233 = original 2335, orbit 14, lb 12, cap 4
private def occRow_416_233 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 234 = original 26, orbit 99, lb 15, cap 1
private def occRow_416_234 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 235 = original 56, orbit 103, lb 15, cap 1
private def occRow_416_235 (j : Fin 63) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 236 = original 57, orbit 103, lb 15, cap 1
private def occRow_416_236 (j : Fin 63) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 237 = original 588, orbit 25, lb 11, cap 5
private def occRow_416_237 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 238 = original 602, orbit 25, lb 11, cap 5
private def occRow_416_238 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 239 = original 1608, orbit 55, lb 14, cap 2
private def occRow_416_239 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 240 = original 1625, orbit 55, lb 14, cap 2
private def occRow_416_240 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 241 = original 1659, orbit 55, lb 14, cap 2
private def occRow_416_241 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 242 = original 1667, orbit 56, lb 14, cap 2
private def occRow_416_242 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 243 = original 1685, orbit 56, lb 14, cap 2
private def occRow_416_243 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 244 = original 1697, orbit 56, lb 14, cap 2
private def occRow_416_244 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 245 = original 1744, orbit 56, lb 14, cap 2
private def occRow_416_245 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 246 = original 1975, orbit 8, lb 9, cap 7
private def occRow_416_246 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 247 = original 2039, orbit 9, lb 9, cap 7
private def occRow_416_247 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 248 = original 68, orbit 103, lb 15, cap 1
private def occRow_416_248 (j : Fin 63) : Int := (if j.val = 17 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 249 = original 130, orbit 112, lb 15, cap 1
private def occRow_416_249 (j : Fin 63) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 250 = original 360, orbit 141, lb 15, cap 1
private def occRow_416_250 (j : Fin 63) : Int := (if j.val = 26 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 251 = original 451, orbit 146, lb 15, cap 1
private def occRow_416_251 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 50 then 1 else 0)
-- row 252 = original 1609, orbit 55, lb 14, cap 2
private def occRow_416_252 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 253 = original 1627, orbit 55, lb 14, cap 2
private def occRow_416_253 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 254 = original 1654, orbit 55, lb 14, cap 2
private def occRow_416_254 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 255 = original 1675, orbit 56, lb 14, cap 2
private def occRow_416_255 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 256 = original 2255, orbit 14, lb 12, cap 4
private def occRow_416_256 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 257 = original 2489, orbit 2, lb 6, cap 10
private def occRow_416_257 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 258 = original 734, orbit 35, lb 15, cap 1
private def occRow_416_258 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 259 = original 741, orbit 35, lb 15, cap 1
private def occRow_416_259 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 260 = original 1884, orbit 7, lb 9, cap 7
private def occRow_416_260 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 261 = original 1916, orbit 7, lb 9, cap 7
private def occRow_416_261 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 262 = original 1971, orbit 7, lb 9, cap 7
private def occRow_416_262 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 263 = original 2059, orbit 10, lb 12, cap 4
private def occRow_416_263 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 264 = original 2239, orbit 14, lb 12, cap 4
private def occRow_416_264 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 265 = original 2458, orbit 2, lb 6, cap 10
private def occRow_416_265 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 266 = original 374, orbit 141, lb 15, cap 1
private def occRow_416_266 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 267 = original 583, orbit 25, lb 11, cap 5
private def occRow_416_267 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 268 = original 1619, orbit 55, lb 14, cap 2
private def occRow_416_268 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 269 = original 1648, orbit 55, lb 14, cap 2
private def occRow_416_269 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 270 = original 1656, orbit 55, lb 14, cap 2
private def occRow_416_270 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 271 = original 1745, orbit 56, lb 14, cap 2
private def occRow_416_271 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 272 = original 2061, orbit 10, lb 12, cap 4
private def occRow_416_272 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 273 = original 2251, orbit 14, lb 12, cap 4
private def occRow_416_273 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 274 = original 2286, orbit 14, lb 12, cap 4
private def occRow_416_274 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 275 = original 2301, orbit 14, lb 12, cap 4
private def occRow_416_275 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 276 = original 277, orbit 134, lb 15, cap 1
private def occRow_416_276 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0)
-- row 277 = original 1623, orbit 55, lb 14, cap 2
private def occRow_416_277 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 278 = original 2308, orbit 14, lb 12, cap 4
private def occRow_416_278 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 279 = original 2498, orbit 3, lb 9, cap 7
private def occRow_416_279 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 280 = original 450, orbit 146, lb 15, cap 1
private def occRow_416_280 (j : Fin 63) : Int := (if j.val = 28 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0)
-- row 281 = original 454, orbit 146, lb 15, cap 1
private def occRow_416_281 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 282 = original 561, orbit 25, lb 11, cap 5
private def occRow_416_282 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 283 = original 1650, orbit 55, lb 14, cap 2
private def occRow_416_283 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 284 = original 1658, orbit 55, lb 14, cap 2
private def occRow_416_284 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 285 = original 1688, orbit 56, lb 14, cap 2
private def occRow_416_285 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 286 = original 2462, orbit 2, lb 6, cap 10
private def occRow_416_286 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 287 = original 2490, orbit 2, lb 6, cap 10
private def occRow_416_287 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 288 = original 136, orbit 112, lb 15, cap 1
private def occRow_416_288 (j : Fin 63) : Int := (if j.val = 19 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 289 = original 168, orbit 120, lb 15, cap 1
private def occRow_416_289 (j : Fin 63) : Int := (if j.val = 18 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 290 = original 1963, orbit 7, lb 9, cap 7
private def occRow_416_290 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 291 = original 2083, orbit 11, lb 12, cap 4
private def occRow_416_291 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 292 = original 2311, orbit 14, lb 12, cap 4
private def occRow_416_292 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 293 = original 163, orbit 120, lb 15, cap 1
private def occRow_416_293 (j : Fin 63) : Int := (if j.val = 20 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 294 = original 356, orbit 140, lb 14, cap 2
private def occRow_416_294 (j : Fin 63) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 295 = original 422, orbit 144, lb 15, cap 1
private def occRow_416_295 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 296 = original 431, orbit 144, lb 15, cap 1
private def occRow_416_296 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 297 = original 1604, orbit 55, lb 14, cap 2
private def occRow_416_297 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0)
-- row 298 = original 2078, orbit 11, lb 12, cap 4
private def occRow_416_298 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 299 = original 1097, orbit 43, lb 12, cap 4
private def occRow_416_299 (j : Fin 63) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 300 = original 1642, orbit 55, lb 14, cap 2
private def occRow_416_300 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 301 = original 1899, orbit 7, lb 9, cap 7
private def occRow_416_301 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 302 = original 1933, orbit 7, lb 9, cap 7
private def occRow_416_302 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 303 = original 1966, orbit 7, lb 9, cap 7
private def occRow_416_303 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 304 = original 2064, orbit 10, lb 12, cap 4
private def occRow_416_304 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 305 = original 2332, orbit 14, lb 12, cap 4
private def occRow_416_305 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 306 = original 2448, orbit 1, lb 3, cap 13
private def occRow_416_306 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 307 = original 2459, orbit 2, lb 6, cap 10
private def occRow_416_307 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 308 = original 2463, orbit 2, lb 6, cap 10
private def occRow_416_308 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 309 = original 33, orbit 100, lb 14, cap 2
private def occRow_416_309 (j : Fin 63) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0)
-- row 310 = original 603, orbit 25, lb 11, cap 5
private def occRow_416_310 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 311 = original 1611, orbit 55, lb 14, cap 2
private def occRow_416_311 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0)
-- row 312 = original 1693, orbit 56, lb 14, cap 2
private def occRow_416_312 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 313 = original 2424, orbit 16, lb 12, cap 4
private def occRow_416_313 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 314 = original 2428, orbit 16, lb 12, cap 4
private def occRow_416_314 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 315 = original 2429, orbit 16, lb 12, cap 4
private def occRow_416_315 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 316 = original 2437, orbit 16, lb 12, cap 4
private def occRow_416_316 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 60 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 317 = original 2488, orbit 2, lb 6, cap 10
private def occRow_416_317 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 318 = original 258, orbit 130, lb 15, cap 1
private def occRow_416_318 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 319 = original 432, orbit 144, lb 15, cap 1
private def occRow_416_319 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 320 = original 1614, orbit 55, lb 14, cap 2
private def occRow_416_320 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 321 = original 1655, orbit 55, lb 14, cap 2
private def occRow_416_321 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 322 = original 1660, orbit 55, lb 14, cap 2
private def occRow_416_322 (j : Fin 63) : Int := (if j.val = 8 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 323 = original 1691, orbit 56, lb 14, cap 2
private def occRow_416_323 (j : Fin 63) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 324 = original 1711, orbit 56, lb 14, cap 2
private def occRow_416_324 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 325 = original 2261, orbit 14, lb 12, cap 4
private def occRow_416_325 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 326 = original 740, orbit 35, lb 15, cap 1
private def occRow_416_326 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0)
-- row 327 = original 1900, orbit 7, lb 9, cap 7
private def occRow_416_327 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 56 then 1 else 0)
-- row 328 = original 167, orbit 120, lb 15, cap 1
private def occRow_416_328 (j : Fin 63) : Int := (if j.val = 18 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 329 = original 1630, orbit 55, lb 14, cap 2
private def occRow_416_329 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 330 = original 1664, orbit 55, lb 14, cap 2
private def occRow_416_330 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 331 = original 1809, orbit 5, lb 9, cap 7
private def occRow_416_331 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 332 = original 430, orbit 144, lb 15, cap 1
private def occRow_416_332 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 333 = original 1086, orbit 43, lb 12, cap 4
private def occRow_416_333 (j : Fin 63) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 334 = original 2086, orbit 11, lb 12, cap 4
private def occRow_416_334 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 335 = original 2204, orbit 14, lb 12, cap 4
private def occRow_416_335 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 336 = original 2236, orbit 14, lb 12, cap 4
private def occRow_416_336 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 337 = original 2323, orbit 14, lb 12, cap 4
private def occRow_416_337 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 338 = original 2504, orbit 3, lb 9, cap 7
private def occRow_416_338 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 339 = original 429, orbit 144, lb 15, cap 1
private def occRow_416_339 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 340 = original 564, orbit 25, lb 11, cap 5
private def occRow_416_340 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 341 = original 1977, orbit 8, lb 9, cap 7
private def occRow_416_341 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0)
-- row 342 = original 2430, orbit 16, lb 12, cap 4
private def occRow_416_342 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 343 = original 155, orbit 118, lb 15, cap 1
private def occRow_416_343 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 344 = original 193, orbit 124, lb 15, cap 1
private def occRow_416_344 (j : Fin 63) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 28 then 1 else 0)
-- row 345 = original 423, orbit 144, lb 15, cap 1
private def occRow_416_345 (j : Fin 63) : Int := (if j.val = 22 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 346 = original 424, orbit 144, lb 15, cap 1
private def occRow_416_346 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 52 then 1 else 0)
-- row 347 = original 1651, orbit 55, lb 14, cap 2
private def occRow_416_347 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 348 = original 1813, orbit 5, lb 9, cap 7
private def occRow_416_348 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 349 = original 2088, orbit 11, lb 12, cap 4
private def occRow_416_349 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 59 then 1 else 0) + (if j.val = 62 then 1 else 0)
-- row 350 = original 35, orbit 100, lb 14, cap 2
private def occRow_416_350 (j : Fin 63) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0)
-- row 351 = original 156, orbit 118, lb 15, cap 1
private def occRow_416_351 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0)
-- row 352 = original 365, orbit 141, lb 15, cap 1
private def occRow_416_352 (j : Fin 63) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 353 = original 1088, orbit 43, lb 12, cap 4
private def occRow_416_353 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 57 then 1 else 0)
-- row 354 = original 1292, orbit 47, lb 14, cap 2
private def occRow_416_354 (j : Fin 63) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 44 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 55 then 1 else 0)
-- row 355 = original 2250, orbit 14, lb 12, cap 4
private def occRow_416_355 (j : Fin 63) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 356 = original 40, orbit 101, lb 15, cap 1
private def occRow_416_356 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 14 then 1 else 0)
-- row 357 = original 49, orbit 103, lb 15, cap 1
private def occRow_416_357 (j : Fin 63) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0)
-- row 358 = original 50, orbit 103, lb 15, cap 1
private def occRow_416_358 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0)
-- row 359 = original 105, orbit 111, lb 14, cap 2
private def occRow_416_359 (j : Fin 63) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0)
-- row 360 = original 354, orbit 140, lb 14, cap 2
private def occRow_416_360 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 361 = original 414, orbit 144, lb 15, cap 1
private def occRow_416_361 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0)
-- row 362 = original 2241, orbit 14, lb 12, cap 4
private def occRow_416_362 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 363 = original 2256, orbit 14, lb 12, cap 4
private def occRow_416_363 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 364 = original 2276, orbit 14, lb 12, cap 4
private def occRow_416_364 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 42 then 1 else 0) + (if j.val = 43 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 56 then 1 else 0) + (if j.val = 61 then 1 else 0)
-- row 365 = original 162, orbit 120, lb 15, cap 1
private def occRow_416_365 (j : Fin 63) : Int := (if j.val = 16 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 48 then 1 else 0)
-- row 366 = original 410, orbit 143, lb 14, cap 2
private def occRow_416_366 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
-- row 367 = original 416, orbit 144, lb 15, cap 1
private def occRow_416_367 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 41 then 1 else 0) + (if j.val = 44 then 1 else 0)
-- row 368 = original 563, orbit 25, lb 11, cap 5
private def occRow_416_368 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0)
-- row 369 = original 1807, orbit 5, lb 9, cap 7
private def occRow_416_369 (j : Fin 63) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 45 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 47 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 53 then 1 else 0) + (if j.val = 54 then 1 else 0)
-- row 370 = original 2242, orbit 14, lb 12, cap 4
private def occRow_416_370 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 49 then 1 else 0) + (if j.val = 52 then 1 else 0) + (if j.val = 58 then 1 else 0) + (if j.val = 59 then 1 else 0)
-- row 371 = original 2257, orbit 14, lb 12, cap 4
private def occRow_416_371 (j : Fin 63) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 50 then 1 else 0) + (if j.val = 51 then 1 else 0) + (if j.val = 57 then 1 else 0) + (if j.val = 60 then 1 else 0)
-- row 372 = original 2271, orbit 14, lb 12, cap 4
private def occRow_416_372 (j : Fin 63) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 40 then 1 else 0) + (if j.val = 46 then 1 else 0) + (if j.val = 48 then 1 else 0) + (if j.val = 54 then 1 else 0) + (if j.val = 55 then 1 else 0) + (if j.val = 61 then 1 else 0)

def occCoeff_416 : Fin 373 → Fin 63 → Int
  | i, j => match i.val with
    | 0 => occRow_416_0 j
    | 1 => occRow_416_1 j
    | 2 => occRow_416_2 j
    | 3 => occRow_416_3 j
    | 4 => occRow_416_4 j
    | 5 => occRow_416_5 j
    | 6 => occRow_416_6 j
    | 7 => occRow_416_7 j
    | 8 => occRow_416_8 j
    | 9 => occRow_416_9 j
    | 10 => occRow_416_10 j
    | 11 => occRow_416_11 j
    | 12 => occRow_416_12 j
    | 13 => occRow_416_13 j
    | 14 => occRow_416_14 j
    | 15 => occRow_416_15 j
    | 16 => occRow_416_16 j
    | 17 => occRow_416_17 j
    | 18 => occRow_416_18 j
    | 19 => occRow_416_19 j
    | 20 => occRow_416_20 j
    | 21 => occRow_416_21 j
    | 22 => occRow_416_22 j
    | 23 => occRow_416_23 j
    | 24 => occRow_416_24 j
    | 25 => occRow_416_25 j
    | 26 => occRow_416_26 j
    | 27 => occRow_416_27 j
    | 28 => occRow_416_28 j
    | 29 => occRow_416_29 j
    | 30 => occRow_416_30 j
    | 31 => occRow_416_31 j
    | 32 => occRow_416_32 j
    | 33 => occRow_416_33 j
    | 34 => occRow_416_34 j
    | 35 => occRow_416_35 j
    | 36 => occRow_416_36 j
    | 37 => occRow_416_37 j
    | 38 => occRow_416_38 j
    | 39 => occRow_416_39 j
    | 40 => occRow_416_40 j
    | 41 => occRow_416_41 j
    | 42 => occRow_416_42 j
    | 43 => occRow_416_43 j
    | 44 => occRow_416_44 j
    | 45 => occRow_416_45 j
    | 46 => occRow_416_46 j
    | 47 => occRow_416_47 j
    | 48 => occRow_416_48 j
    | 49 => occRow_416_49 j
    | 50 => occRow_416_50 j
    | 51 => occRow_416_51 j
    | 52 => occRow_416_52 j
    | 53 => occRow_416_53 j
    | 54 => occRow_416_54 j
    | 55 => occRow_416_55 j
    | 56 => occRow_416_56 j
    | 57 => occRow_416_57 j
    | 58 => occRow_416_58 j
    | 59 => occRow_416_59 j
    | 60 => occRow_416_60 j
    | 61 => occRow_416_61 j
    | 62 => occRow_416_62 j
    | 63 => occRow_416_63 j
    | 64 => occRow_416_64 j
    | 65 => occRow_416_65 j
    | 66 => occRow_416_66 j
    | 67 => occRow_416_67 j
    | 68 => occRow_416_68 j
    | 69 => occRow_416_69 j
    | 70 => occRow_416_70 j
    | 71 => occRow_416_71 j
    | 72 => occRow_416_72 j
    | 73 => occRow_416_73 j
    | 74 => occRow_416_74 j
    | 75 => occRow_416_75 j
    | 76 => occRow_416_76 j
    | 77 => occRow_416_77 j
    | 78 => occRow_416_78 j
    | 79 => occRow_416_79 j
    | 80 => occRow_416_80 j
    | 81 => occRow_416_81 j
    | 82 => occRow_416_82 j
    | 83 => occRow_416_83 j
    | 84 => occRow_416_84 j
    | 85 => occRow_416_85 j
    | 86 => occRow_416_86 j
    | 87 => occRow_416_87 j
    | 88 => occRow_416_88 j
    | 89 => occRow_416_89 j
    | 90 => occRow_416_90 j
    | 91 => occRow_416_91 j
    | 92 => occRow_416_92 j
    | 93 => occRow_416_93 j
    | 94 => occRow_416_94 j
    | 95 => occRow_416_95 j
    | 96 => occRow_416_96 j
    | 97 => occRow_416_97 j
    | 98 => occRow_416_98 j
    | 99 => occRow_416_99 j
    | 100 => occRow_416_100 j
    | 101 => occRow_416_101 j
    | 102 => occRow_416_102 j
    | 103 => occRow_416_103 j
    | 104 => occRow_416_104 j
    | 105 => occRow_416_105 j
    | 106 => occRow_416_106 j
    | 107 => occRow_416_107 j
    | 108 => occRow_416_108 j
    | 109 => occRow_416_109 j
    | 110 => occRow_416_110 j
    | 111 => occRow_416_111 j
    | 112 => occRow_416_112 j
    | 113 => occRow_416_113 j
    | 114 => occRow_416_114 j
    | 115 => occRow_416_115 j
    | 116 => occRow_416_116 j
    | 117 => occRow_416_117 j
    | 118 => occRow_416_118 j
    | 119 => occRow_416_119 j
    | 120 => occRow_416_120 j
    | 121 => occRow_416_121 j
    | 122 => occRow_416_122 j
    | 123 => occRow_416_123 j
    | 124 => occRow_416_124 j
    | 125 => occRow_416_125 j
    | 126 => occRow_416_126 j
    | 127 => occRow_416_127 j
    | 128 => occRow_416_128 j
    | 129 => occRow_416_129 j
    | 130 => occRow_416_130 j
    | 131 => occRow_416_131 j
    | 132 => occRow_416_132 j
    | 133 => occRow_416_133 j
    | 134 => occRow_416_134 j
    | 135 => occRow_416_135 j
    | 136 => occRow_416_136 j
    | 137 => occRow_416_137 j
    | 138 => occRow_416_138 j
    | 139 => occRow_416_139 j
    | 140 => occRow_416_140 j
    | 141 => occRow_416_141 j
    | 142 => occRow_416_142 j
    | 143 => occRow_416_143 j
    | 144 => occRow_416_144 j
    | 145 => occRow_416_145 j
    | 146 => occRow_416_146 j
    | 147 => occRow_416_147 j
    | 148 => occRow_416_148 j
    | 149 => occRow_416_149 j
    | 150 => occRow_416_150 j
    | 151 => occRow_416_151 j
    | 152 => occRow_416_152 j
    | 153 => occRow_416_153 j
    | 154 => occRow_416_154 j
    | 155 => occRow_416_155 j
    | 156 => occRow_416_156 j
    | 157 => occRow_416_157 j
    | 158 => occRow_416_158 j
    | 159 => occRow_416_159 j
    | 160 => occRow_416_160 j
    | 161 => occRow_416_161 j
    | 162 => occRow_416_162 j
    | 163 => occRow_416_163 j
    | 164 => occRow_416_164 j
    | 165 => occRow_416_165 j
    | 166 => occRow_416_166 j
    | 167 => occRow_416_167 j
    | 168 => occRow_416_168 j
    | 169 => occRow_416_169 j
    | 170 => occRow_416_170 j
    | 171 => occRow_416_171 j
    | 172 => occRow_416_172 j
    | 173 => occRow_416_173 j
    | 174 => occRow_416_174 j
    | 175 => occRow_416_175 j
    | 176 => occRow_416_176 j
    | 177 => occRow_416_177 j
    | 178 => occRow_416_178 j
    | 179 => occRow_416_179 j
    | 180 => occRow_416_180 j
    | 181 => occRow_416_181 j
    | 182 => occRow_416_182 j
    | 183 => occRow_416_183 j
    | 184 => occRow_416_184 j
    | 185 => occRow_416_185 j
    | 186 => occRow_416_186 j
    | 187 => occRow_416_187 j
    | 188 => occRow_416_188 j
    | 189 => occRow_416_189 j
    | 190 => occRow_416_190 j
    | 191 => occRow_416_191 j
    | 192 => occRow_416_192 j
    | 193 => occRow_416_193 j
    | 194 => occRow_416_194 j
    | 195 => occRow_416_195 j
    | 196 => occRow_416_196 j
    | 197 => occRow_416_197 j
    | 198 => occRow_416_198 j
    | 199 => occRow_416_199 j
    | 200 => occRow_416_200 j
    | 201 => occRow_416_201 j
    | 202 => occRow_416_202 j
    | 203 => occRow_416_203 j
    | 204 => occRow_416_204 j
    | 205 => occRow_416_205 j
    | 206 => occRow_416_206 j
    | 207 => occRow_416_207 j
    | 208 => occRow_416_208 j
    | 209 => occRow_416_209 j
    | 210 => occRow_416_210 j
    | 211 => occRow_416_211 j
    | 212 => occRow_416_212 j
    | 213 => occRow_416_213 j
    | 214 => occRow_416_214 j
    | 215 => occRow_416_215 j
    | 216 => occRow_416_216 j
    | 217 => occRow_416_217 j
    | 218 => occRow_416_218 j
    | 219 => occRow_416_219 j
    | 220 => occRow_416_220 j
    | 221 => occRow_416_221 j
    | 222 => occRow_416_222 j
    | 223 => occRow_416_223 j
    | 224 => occRow_416_224 j
    | 225 => occRow_416_225 j
    | 226 => occRow_416_226 j
    | 227 => occRow_416_227 j
    | 228 => occRow_416_228 j
    | 229 => occRow_416_229 j
    | 230 => occRow_416_230 j
    | 231 => occRow_416_231 j
    | 232 => occRow_416_232 j
    | 233 => occRow_416_233 j
    | 234 => occRow_416_234 j
    | 235 => occRow_416_235 j
    | 236 => occRow_416_236 j
    | 237 => occRow_416_237 j
    | 238 => occRow_416_238 j
    | 239 => occRow_416_239 j
    | 240 => occRow_416_240 j
    | 241 => occRow_416_241 j
    | 242 => occRow_416_242 j
    | 243 => occRow_416_243 j
    | 244 => occRow_416_244 j
    | 245 => occRow_416_245 j
    | 246 => occRow_416_246 j
    | 247 => occRow_416_247 j
    | 248 => occRow_416_248 j
    | 249 => occRow_416_249 j
    | 250 => occRow_416_250 j
    | 251 => occRow_416_251 j
    | 252 => occRow_416_252 j
    | 253 => occRow_416_253 j
    | 254 => occRow_416_254 j
    | 255 => occRow_416_255 j
    | 256 => occRow_416_256 j
    | 257 => occRow_416_257 j
    | 258 => occRow_416_258 j
    | 259 => occRow_416_259 j
    | 260 => occRow_416_260 j
    | 261 => occRow_416_261 j
    | 262 => occRow_416_262 j
    | 263 => occRow_416_263 j
    | 264 => occRow_416_264 j
    | 265 => occRow_416_265 j
    | 266 => occRow_416_266 j
    | 267 => occRow_416_267 j
    | 268 => occRow_416_268 j
    | 269 => occRow_416_269 j
    | 270 => occRow_416_270 j
    | 271 => occRow_416_271 j
    | 272 => occRow_416_272 j
    | 273 => occRow_416_273 j
    | 274 => occRow_416_274 j
    | 275 => occRow_416_275 j
    | 276 => occRow_416_276 j
    | 277 => occRow_416_277 j
    | 278 => occRow_416_278 j
    | 279 => occRow_416_279 j
    | 280 => occRow_416_280 j
    | 281 => occRow_416_281 j
    | 282 => occRow_416_282 j
    | 283 => occRow_416_283 j
    | 284 => occRow_416_284 j
    | 285 => occRow_416_285 j
    | 286 => occRow_416_286 j
    | 287 => occRow_416_287 j
    | 288 => occRow_416_288 j
    | 289 => occRow_416_289 j
    | 290 => occRow_416_290 j
    | 291 => occRow_416_291 j
    | 292 => occRow_416_292 j
    | 293 => occRow_416_293 j
    | 294 => occRow_416_294 j
    | 295 => occRow_416_295 j
    | 296 => occRow_416_296 j
    | 297 => occRow_416_297 j
    | 298 => occRow_416_298 j
    | 299 => occRow_416_299 j
    | 300 => occRow_416_300 j
    | 301 => occRow_416_301 j
    | 302 => occRow_416_302 j
    | 303 => occRow_416_303 j
    | 304 => occRow_416_304 j
    | 305 => occRow_416_305 j
    | 306 => occRow_416_306 j
    | 307 => occRow_416_307 j
    | 308 => occRow_416_308 j
    | 309 => occRow_416_309 j
    | 310 => occRow_416_310 j
    | 311 => occRow_416_311 j
    | 312 => occRow_416_312 j
    | 313 => occRow_416_313 j
    | 314 => occRow_416_314 j
    | 315 => occRow_416_315 j
    | 316 => occRow_416_316 j
    | 317 => occRow_416_317 j
    | 318 => occRow_416_318 j
    | 319 => occRow_416_319 j
    | 320 => occRow_416_320 j
    | 321 => occRow_416_321 j
    | 322 => occRow_416_322 j
    | 323 => occRow_416_323 j
    | 324 => occRow_416_324 j
    | 325 => occRow_416_325 j
    | 326 => occRow_416_326 j
    | 327 => occRow_416_327 j
    | 328 => occRow_416_328 j
    | 329 => occRow_416_329 j
    | 330 => occRow_416_330 j
    | 331 => occRow_416_331 j
    | 332 => occRow_416_332 j
    | 333 => occRow_416_333 j
    | 334 => occRow_416_334 j
    | 335 => occRow_416_335 j
    | 336 => occRow_416_336 j
    | 337 => occRow_416_337 j
    | 338 => occRow_416_338 j
    | 339 => occRow_416_339 j
    | 340 => occRow_416_340 j
    | 341 => occRow_416_341 j
    | 342 => occRow_416_342 j
    | 343 => occRow_416_343 j
    | 344 => occRow_416_344 j
    | 345 => occRow_416_345 j
    | 346 => occRow_416_346 j
    | 347 => occRow_416_347 j
    | 348 => occRow_416_348 j
    | 349 => occRow_416_349 j
    | 350 => occRow_416_350 j
    | 351 => occRow_416_351 j
    | 352 => occRow_416_352 j
    | 353 => occRow_416_353 j
    | 354 => occRow_416_354 j
    | 355 => occRow_416_355 j
    | 356 => occRow_416_356 j
    | 357 => occRow_416_357 j
    | 358 => occRow_416_358 j
    | 359 => occRow_416_359 j
    | 360 => occRow_416_360 j
    | 361 => occRow_416_361 j
    | 362 => occRow_416_362 j
    | 363 => occRow_416_363 j
    | 364 => occRow_416_364 j
    | 365 => occRow_416_365 j
    | 366 => occRow_416_366 j
    | 367 => occRow_416_367 j
    | 368 => occRow_416_368 j
    | 369 => occRow_416_369 j
    | 370 => occRow_416_370 j
    | 371 => occRow_416_371 j
    | 372 => occRow_416_372 j
    | _ => 0

def occRhs_416 : Fin 373 → Int
  | i => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | 4 => 4
    | 5 => 4
    | 6 => 4
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
    | 17 => 1
    | 18 => 1
    | 19 => 1
    | 20 => 1
    | 21 => 2
    | 22 => 2
    | 23 => 7
    | 24 => 7
    | 25 => 7
    | 26 => 7
    | 27 => 4
    | 28 => 4
    | 29 => 4
    | 30 => 4
    | 31 => 4
    | 32 => 4
    | 33 => 4
    | 34 => 4
    | 35 => 4
    | 36 => 4
    | 37 => 4
    | 38 => 10
    | 39 => 7
    | 40 => 7
    | 41 => 7
    | 42 => 4
    | 43 => 1
    | 44 => 1
    | 45 => 1
    | 46 => 1
    | 47 => 1
    | 48 => 1
    | 49 => 1
    | 50 => 1
    | 51 => 2
    | 52 => 2
    | 53 => 2
    | 54 => 7
    | 55 => 4
    | 56 => 4
    | 57 => 4
    | 58 => 4
    | 59 => 4
    | 60 => 4
    | 61 => 4
    | 62 => 4
    | 63 => 7
    | 64 => 1
    | 65 => 1
    | 66 => 1
    | 67 => 1
    | 68 => 1
    | 69 => 1
    | 70 => 5
    | 71 => 4
    | 72 => 2
    | 73 => 2
    | 74 => 2
    | 75 => 2
    | 76 => 7
    | 77 => 7
    | 78 => 4
    | 79 => 4
    | 80 => 7
    | 81 => 4
    | 82 => 1
    | 83 => 1
    | 84 => 1
    | 85 => 1
    | 86 => 1
    | 87 => 1
    | 88 => 4
    | 89 => 7
    | 90 => 7
    | 91 => 4
    | 92 => 4
    | 93 => 4
    | 94 => 1
    | 95 => 1
    | 96 => 1
    | 97 => 1
    | 98 => 1
    | 99 => 1
    | 100 => 1
    | 101 => 1
    | 102 => 4
    | 103 => 4
    | 104 => 2
    | 105 => 2
    | 106 => 7
    | 107 => 4
    | 108 => 4
    | 109 => 4
    | 110 => 10
    | 111 => 1
    | 112 => 1
    | 113 => 1
    | 114 => 1
    | 115 => 5
    | 116 => 5
    | 117 => 5
    | 118 => 1
    | 119 => 2
    | 120 => 2
    | 121 => 4
    | 122 => 4
    | 123 => 4
    | 124 => 4
    | 125 => 10
    | 126 => 7
    | 127 => 1
    | 128 => 1
    | 129 => 1
    | 130 => 1
    | 131 => 1
    | 132 => 1
    | 133 => 1
    | 134 => 5
    | 135 => 2
    | 136 => 2
    | 137 => 2
    | 138 => 2
    | 139 => 2
    | 140 => 7
    | 141 => 4
    | 142 => 4
    | 143 => 4
    | 144 => 4
    | 145 => 4
    | 146 => 4
    | 147 => 4
    | 148 => 4
    | 149 => 7
    | 150 => 1
    | 151 => 1
    | 152 => 1
    | 153 => 1
    | 154 => 1
    | 155 => 1
    | 156 => 2
    | 157 => 2
    | 158 => 2
    | 159 => 2
    | 160 => 7
    | 161 => 4
    | 162 => 4
    | 163 => 4
    | 164 => 1
    | 165 => 1
    | 166 => 1
    | 167 => 1
    | 168 => 4
    | 169 => 4
    | 170 => 4
    | 171 => 4
    | 172 => 1
    | 173 => 2
    | 174 => 2
    | 175 => 4
    | 176 => 7
    | 177 => 4
    | 178 => 4
    | 179 => 4
    | 180 => 1
    | 181 => 7
    | 182 => 4
    | 183 => 4
    | 184 => 4
    | 185 => 4
    | 186 => 1
    | 187 => 1
    | 188 => 1
    | 189 => 1
    | 190 => 1
    | 191 => 5
    | 192 => 2
    | 193 => 2
    | 194 => 2
    | 195 => 2
    | 196 => 2
    | 197 => 2
    | 198 => 2
    | 199 => 2
    | 200 => 7
    | 201 => 7
    | 202 => 4
    | 203 => 4
    | 204 => 4
    | 205 => 4
    | 206 => 10
    | 207 => 1
    | 208 => 1
    | 209 => 4
    | 210 => 4
    | 211 => 4
    | 212 => 4
    | 213 => 5
    | 214 => 5
    | 215 => 7
    | 216 => 4
    | 217 => 10
    | 218 => 10
    | 219 => 4
    | 220 => 1
    | 221 => 1
    | 222 => 5
    | 223 => 2
    | 224 => 7
    | 225 => 4
    | 226 => 4
    | 227 => 1
    | 228 => 1
    | 229 => 2
    | 230 => 2
    | 231 => 2
    | 232 => 2
    | 233 => 4
    | 234 => 1
    | 235 => 1
    | 236 => 1
    | 237 => 5
    | 238 => 5
    | 239 => 2
    | 240 => 2
    | 241 => 2
    | 242 => 2
    | 243 => 2
    | 244 => 2
    | 245 => 2
    | 246 => 7
    | 247 => 7
    | 248 => 1
    | 249 => 1
    | 250 => 1
    | 251 => 1
    | 252 => 2
    | 253 => 2
    | 254 => 2
    | 255 => 2
    | 256 => 4
    | 257 => 10
    | 258 => 1
    | 259 => 1
    | 260 => 7
    | 261 => 7
    | 262 => 7
    | 263 => 4
    | 264 => 4
    | 265 => 10
    | 266 => 1
    | 267 => 5
    | 268 => 2
    | 269 => 2
    | 270 => 2
    | 271 => 2
    | 272 => 4
    | 273 => 4
    | 274 => 4
    | 275 => 4
    | 276 => 1
    | 277 => 2
    | 278 => 4
    | 279 => 7
    | 280 => 1
    | 281 => 1
    | 282 => 5
    | 283 => 2
    | 284 => 2
    | 285 => 2
    | 286 => 10
    | 287 => 10
    | 288 => 1
    | 289 => 1
    | 290 => 7
    | 291 => 4
    | 292 => 4
    | 293 => 1
    | 294 => 2
    | 295 => 1
    | 296 => 1
    | 297 => 2
    | 298 => 4
    | 299 => 4
    | 300 => 2
    | 301 => 7
    | 302 => 7
    | 303 => 7
    | 304 => 4
    | 305 => 4
    | 306 => 13
    | 307 => 10
    | 308 => 10
    | 309 => 2
    | 310 => 5
    | 311 => 2
    | 312 => 2
    | 313 => 4
    | 314 => 4
    | 315 => 4
    | 316 => 4
    | 317 => 10
    | 318 => 1
    | 319 => 1
    | 320 => 2
    | 321 => 2
    | 322 => 2
    | 323 => 2
    | 324 => 2
    | 325 => 4
    | 326 => 1
    | 327 => 7
    | 328 => 1
    | 329 => 2
    | 330 => 2
    | 331 => 7
    | 332 => 1
    | 333 => 4
    | 334 => 4
    | 335 => 4
    | 336 => 4
    | 337 => 4
    | 338 => 7
    | 339 => 1
    | 340 => 5
    | 341 => 7
    | 342 => 4
    | 343 => 1
    | 344 => 1
    | 345 => 1
    | 346 => 1
    | 347 => 2
    | 348 => 7
    | 349 => 4
    | 350 => 2
    | 351 => 1
    | 352 => 1
    | 353 => 4
    | 354 => 2
    | 355 => 4
    | 356 => 1
    | 357 => 1
    | 358 => 1
    | 359 => 2
    | 360 => 2
    | 361 => 1
    | 362 => 4
    | 363 => 4
    | 364 => 4
    | 365 => 1
    | 366 => 2
    | 367 => 1
    | 368 => 5
    | 369 => 7
    | 370 => 4
    | 371 => 4
    | 372 => 4
    | _ => 0

def S_416 : OccSys 63 373 :=
  { occCoeff := occCoeff_416, occRhs := occRhs_416, target := 16 }

-- leaf 0, path LLLLLLLLL, Farkas rhs -172654
def refs_416_L0 : Fin 64 → RowRef 373 63
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
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨8, by decide⟩
    | 45 => .nonneg ⟨10, by decide⟩
    | 46 => .nonneg ⟨16, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨20, by decide⟩
    | 49 => .nonneg ⟨24, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨31, by decide⟩
    | 52 => .nonneg ⟨32, by decide⟩
    | 53 => .nonneg ⟨44, by decide⟩
    | 54 => .nonneg ⟨55, by decide⟩
    | 55 => .branchLe ⟨6, by decide⟩ 0
    | 56 => .branchLe ⟨13, by decide⟩ 0
    | 57 => .branchLe ⟨25, by decide⟩ 0
    | 58 => .branchLe ⟨29, by decide⟩ 0
    | 59 => .branchLe ⟨38, by decide⟩ 0
    | 60 => .branchLe ⟨45, by decide⟩ 0
    | 61 => .branchLe ⟨47, by decide⟩ 0
    | 62 => .branchLe ⟨50, by decide⟩ 0
    | 63 => .branchLe ⟨54, by decide⟩ 0
    | _ => .sumGe

def mults_416_L0 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 133964
    | 1 => 217916
    | 2 => 87756
    | 3 => 109772
    | 4 => 464549
    | 5 => 469600
    | 6 => 175721
    | 7 => 249322
    | 8 => 364174
    | 9 => 141278
    | 10 => 304812
    | 11 => 55824
    | 12 => 350019
    | 13 => 155985
    | 14 => 188628
    | 15 => 570581
    | 16 => 516556
    | 17 => 545925
    | 18 => 446441
    | 19 => 206406
    | 20 => 402773
    | 21 => 276636
    | 22 => 13912
    | 23 => 100
    | 24 => 105416
    | 25 => 1128
    | 26 => 280438
    | 27 => 324095
    | 28 => 302928
    | 29 => 378167
    | 30 => 225738
    | 31 => 33444
    | 32 => 51110
    | 33 => 133288
    | 34 => 190994
    | 35 => 132132
    | 36 => 166352
    | 37 => 68600
    | 38 => 30902
    | 39 => 84314
    | 40 => 358474
    | 41 => 8400
    | 42 => 1527854
    | 43 => 1336796
    | 44 => 978586
    | 45 => 113422
    | 46 => 1036044
    | 47 => 676112
    | 48 => 691160
    | 49 => 190086
    | 50 => 354128
    | 51 => 210196
    | 52 => 6192
    | 53 => 676538
    | 54 => 32158
    | 55 => 685906
    | 56 => 1021850
    | 57 => 416070
    | 58 => 696680
    | 59 => 931480
    | 60 => 1370794
    | 61 => 1160980
    | 62 => 1032962
    | 63 => 1443540
    | _ => 0

theorem coeff_cancel_416_L0 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L0 i : Int) * (refs_416_L0 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L0 :
    (∑ i : Fin 64, (mults_416_L0 i : Int) * (refs_416_L0 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf0_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_39_0 : x ⟨38, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_48_0 : x ⟨47, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L0 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L0 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨22, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨23, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_39_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_48_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
  exact farkas_leaf_unsat _ _ (mults_416_L0) coeff_cancel_416_L0 rhs_neg_416_L0 x hrows

-- leaf 1, path LLLLLLLLRLL, Farkas rhs -1942
def refs_416_L1 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨42, by decide⟩
    | 1 => .occ ⟨43, by decide⟩
    | 2 => .occ ⟨44, by decide⟩
    | 3 => .occ ⟨45, by decide⟩
    | 4 => .occ ⟨46, by decide⟩
    | 5 => .occ ⟨47, by decide⟩
    | 6 => .occ ⟨48, by decide⟩
    | 7 => .occ ⟨5, by decide⟩
    | 8 => .occ ⟨6, by decide⟩
    | 9 => .occ ⟨49, by decide⟩
    | 10 => .occ ⟨7, by decide⟩
    | 11 => .occ ⟨9, by decide⟩
    | 12 => .occ ⟨10, by decide⟩
    | 13 => .occ ⟨14, by decide⟩
    | 14 => .occ ⟨15, by decide⟩
    | 15 => .occ ⟨50, by decide⟩
    | 16 => .occ ⟨16, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨51, by decide⟩
    | 21 => .occ ⟨52, by decide⟩
    | 22 => .occ ⟨53, by decide⟩
    | 23 => .occ ⟨54, by decide⟩
    | 24 => .occ ⟨26, by decide⟩
    | 25 => .occ ⟨55, by decide⟩
    | 26 => .occ ⟨27, by decide⟩
    | 27 => .occ ⟨30, by decide⟩
    | 28 => .occ ⟨56, by decide⟩
    | 29 => .occ ⟨57, by decide⟩
    | 30 => .occ ⟨58, by decide⟩
    | 31 => .occ ⟨59, by decide⟩
    | 32 => .occ ⟨60, by decide⟩
    | 33 => .occ ⟨61, by decide⟩
    | 34 => .occ ⟨62, by decide⟩
    | 35 => .occ ⟨63, by decide⟩
    | 36 => .occ ⟨39, by decide⟩
    | 37 => .occ ⟨40, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨8, by decide⟩
    | 41 => .nonneg ⟨10, by decide⟩
    | 42 => .nonneg ⟨12, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨30, by decide⟩
    | 47 => .nonneg ⟨31, by decide⟩
    | 48 => .nonneg ⟨32, by decide⟩
    | 49 => .nonneg ⟨40, by decide⟩
    | 50 => .nonneg ⟨42, by decide⟩
    | 51 => .nonneg ⟨43, by decide⟩
    | 52 => .nonneg ⟨44, by decide⟩
    | 53 => .branchLe ⟨6, by decide⟩ 0
    | 54 => .branchLe ⟨13, by decide⟩ 0
    | 55 => .branchLe ⟨25, by decide⟩ 0
    | 56 => .branchLe ⟨29, by decide⟩ 0
    | 57 => .branchLe ⟨38, by decide⟩ 0
    | 58 => .branchLe ⟨45, by decide⟩ 0
    | 59 => .branchLe ⟨49, by decide⟩ 0
    | 60 => .branchLe ⟨50, by decide⟩ 0
    | 61 => .branchLe ⟨53, by decide⟩ 0
    | 62 => .branchLe ⟨54, by decide⟩ 0
    | 63 => .branchGe ⟨47, by decide⟩ 1
    | _ => .sumGe

def mults_416_L1 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1447
    | 1 => 774
    | 2 => 933
    | 3 => 259
    | 4 => 1487
    | 5 => 539
    | 6 => 3358
    | 7 => 2195
    | 8 => 398
    | 9 => 1971
    | 10 => 521
    | 11 => 586
    | 12 => 461
    | 13 => 753
    | 14 => 1589
    | 15 => 1176
    | 16 => 1530
    | 17 => 444
    | 18 => 1651
    | 19 => 1155
    | 20 => 42
    | 21 => 655
    | 22 => 1462
    | 23 => 277
    | 24 => 510
    | 25 => 44
    | 26 => 664
    | 27 => 361
    | 28 => 690
    | 29 => 564
    | 30 => 140
    | 31 => 195
    | 32 => 1023
    | 33 => 1094
    | 34 => 1107
    | 35 => 877
    | 36 => 327
    | 37 => 961
    | 38 => 4827
    | 39 => 5005
    | 40 => 3765
    | 41 => 2383
    | 42 => 412
    | 43 => 1506
    | 44 => 5251
    | 45 => 623
    | 46 => 2176
    | 47 => 477
    | 48 => 237
    | 49 => 11
    | 50 => 668
    | 51 => 525
    | 52 => 2926
    | 53 => 4317
    | 54 => 4827
    | 55 => 1555
    | 56 => 2275
    | 57 => 1735
    | 58 => 4179
    | 59 => 2716
    | 60 => 566
    | 61 => 3866
    | 62 => 2933
    | 63 => 8567
    | _ => 0

theorem coeff_cancel_416_L1 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L1 i : Int) * (refs_416_L1 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L1 :
    (∑ i : Fin 64, (mults_416_L1 i : Int) * (refs_416_L1 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf1_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_39_0 : x ⟨38, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_54_0 : x ⟨53, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_48_1 : (1 : Int) ≤ x ⟨47, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L1 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L1 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨48, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨51, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨52, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨53, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨58, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨59, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_39_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_54_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_48_1]
  exact farkas_leaf_unsat _ _ (mults_416_L1) coeff_cancel_416_L1 rhs_neg_416_L1 x hrows

-- leaf 2, path LLLLLLLLRLR, Farkas rhs -7219
def refs_416_L2 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨64, by decide⟩
    | 1 => .occ ⟨65, by decide⟩
    | 2 => .occ ⟨43, by decide⟩
    | 3 => .occ ⟨1, by decide⟩
    | 4 => .occ ⟨45, by decide⟩
    | 5 => .occ ⟨66, by decide⟩
    | 6 => .occ ⟨46, by decide⟩
    | 7 => .occ ⟨67, by decide⟩
    | 8 => .occ ⟨68, by decide⟩
    | 9 => .occ ⟨47, by decide⟩
    | 10 => .occ ⟨69, by decide⟩
    | 11 => .occ ⟨4, by decide⟩
    | 12 => .occ ⟨5, by decide⟩
    | 13 => .occ ⟨6, by decide⟩
    | 14 => .occ ⟨70, by decide⟩
    | 15 => .occ ⟨7, by decide⟩
    | 16 => .occ ⟨10, by decide⟩
    | 17 => .occ ⟨11, by decide⟩
    | 18 => .occ ⟨12, by decide⟩
    | 19 => .occ ⟨13, by decide⟩
    | 20 => .occ ⟨15, by decide⟩
    | 21 => .occ ⟨50, by decide⟩
    | 22 => .occ ⟨17, by decide⟩
    | 23 => .occ ⟨19, by decide⟩
    | 24 => .occ ⟨71, by decide⟩
    | 25 => .occ ⟨72, by decide⟩
    | 26 => .occ ⟨73, by decide⟩
    | 27 => .occ ⟨74, by decide⟩
    | 28 => .occ ⟨75, by decide⟩
    | 29 => .occ ⟨76, by decide⟩
    | 30 => .occ ⟨77, by decide⟩
    | 31 => .occ ⟨78, by decide⟩
    | 32 => .occ ⟨30, by decide⟩
    | 33 => .occ ⟨57, by decide⟩
    | 34 => .occ ⟨59, by decide⟩
    | 35 => .occ ⟨79, by decide⟩
    | 36 => .occ ⟨61, by decide⟩
    | 37 => .occ ⟨62, by decide⟩
    | 38 => .occ ⟨37, by decide⟩
    | 39 => .occ ⟨80, by decide⟩
    | 40 => .occ ⟨40, by decide⟩
    | 41 => .sumGe
    | 42 => .nonneg ⟨2, by decide⟩
    | 43 => .nonneg ⟨8, by decide⟩
    | 44 => .nonneg ⟨10, by decide⟩
    | 45 => .nonneg ⟨12, by decide⟩
    | 46 => .nonneg ⟨14, by decide⟩
    | 47 => .nonneg ⟨15, by decide⟩
    | 48 => .nonneg ⟨16, by decide⟩
    | 49 => .nonneg ⟨18, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨32, by decide⟩
    | 52 => .nonneg ⟨44, by decide⟩
    | 53 => .nonneg ⟨46, by decide⟩
    | 54 => .branchLe ⟨6, by decide⟩ 0
    | 55 => .branchLe ⟨13, by decide⟩ 0
    | 56 => .branchLe ⟨25, by decide⟩ 0
    | 57 => .branchLe ⟨29, by decide⟩ 0
    | 58 => .branchLe ⟨45, by decide⟩ 0
    | 59 => .branchLe ⟨50, by decide⟩ 0
    | 60 => .branchLe ⟨53, by decide⟩ 0
    | 61 => .branchLe ⟨54, by decide⟩ 0
    | 62 => .branchGe ⟨47, by decide⟩ 1
    | 63 => .branchGe ⟨49, by decide⟩ 1
    | _ => .sumGe

def mults_416_L2 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 993
    | 1 => 245
    | 2 => 969
    | 3 => 667
    | 4 => 3034
    | 5 => 1300
    | 6 => 1253
    | 7 => 258
    | 8 => 5264
    | 9 => 2616
    | 10 => 3173
    | 11 => 358
    | 12 => 1826
    | 13 => 1968
    | 14 => 562
    | 15 => 152
    | 16 => 168
    | 17 => 1390
    | 18 => 374
    | 19 => 1101
    | 20 => 3745
    | 21 => 782
    | 22 => 1018
    | 23 => 1705
    | 24 => 2034
    | 25 => 102
    | 26 => 526
    | 27 => 2757
    | 28 => 245
    | 29 => 744
    | 30 => 331
    | 31 => 2091
    | 32 => 1198
    | 33 => 525
    | 34 => 1453
    | 35 => 1660
    | 36 => 203
    | 37 => 683
    | 38 => 1151
    | 39 => 59
    | 40 => 664
    | 41 => 5789
    | 42 => 2356
    | 43 => 1596
    | 44 => 964
    | 45 => 770
    | 46 => 1193
    | 47 => 1671
    | 48 => 1162
    | 49 => 1476
    | 50 => 2587
    | 51 => 603
    | 52 => 3164
    | 53 => 138
    | 54 => 2296
    | 55 => 2221
    | 56 => 4383
    | 57 => 5789
    | 58 => 5789
    | 59 => 2767
    | 60 => 5125
    | 61 => 4070
    | 62 => 9058
    | 63 => 19000
    | _ => 0

theorem coeff_cancel_416_L2 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L2 i : Int) * (refs_416_L2 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L2 :
    (∑ i : Fin 64, (mults_416_L2 i : Int) * (refs_416_L2 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf2_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_39_0 : x ⟨38, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_54_0 : x ⟨53, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_48_1 : (1 : Int) ≤ x ⟨47, by decide⟩)
    (h_ge_50_1 : (1 : Int) ≤ x ⟨49, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L2 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L2 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨65, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨66, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨67, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨68, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨69, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨70, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨71, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨72, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨73, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨74, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨75, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨77, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨78, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨59, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨15, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨46, by decide⟩]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_54_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_48_1]
    · simp only [refs_416_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_50_1]
  exact farkas_leaf_unsat _ _ (mults_416_L2) coeff_cancel_416_L2 rhs_neg_416_L2 x hrows

-- leaf 3, path LLLLLLLLRRL, Farkas rhs -2694
def refs_416_L3 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨81, by decide⟩
    | 1 => .occ ⟨43, by decide⟩
    | 2 => .occ ⟨1, by decide⟩
    | 3 => .occ ⟨82, by decide⟩
    | 4 => .occ ⟨83, by decide⟩
    | 5 => .occ ⟨84, by decide⟩
    | 6 => .occ ⟨85, by decide⟩
    | 7 => .occ ⟨47, by decide⟩
    | 8 => .occ ⟨86, by decide⟩
    | 9 => .occ ⟨4, by decide⟩
    | 10 => .occ ⟨5, by decide⟩
    | 11 => .occ ⟨49, by decide⟩
    | 12 => .occ ⟨7, by decide⟩
    | 13 => .occ ⟨87, by decide⟩
    | 14 => .occ ⟨9, by decide⟩
    | 15 => .occ ⟨10, by decide⟩
    | 16 => .occ ⟨14, by decide⟩
    | 17 => .occ ⟨15, by decide⟩
    | 18 => .occ ⟨16, by decide⟩
    | 19 => .occ ⟨17, by decide⟩
    | 20 => .occ ⟨18, by decide⟩
    | 21 => .occ ⟨19, by decide⟩
    | 22 => .occ ⟨20, by decide⟩
    | 23 => .occ ⟨88, by decide⟩
    | 24 => .occ ⟨72, by decide⟩
    | 25 => .occ ⟨51, by decide⟩
    | 26 => .occ ⟨89, by decide⟩
    | 27 => .occ ⟨90, by decide⟩
    | 28 => .occ ⟨76, by decide⟩
    | 29 => .occ ⟨91, by decide⟩
    | 30 => .occ ⟨29, by decide⟩
    | 31 => .occ ⟨92, by decide⟩
    | 32 => .occ ⟨59, by decide⟩
    | 33 => .occ ⟨60, by decide⟩
    | 34 => .occ ⟨34, by decide⟩
    | 35 => .occ ⟨35, by decide⟩
    | 36 => .occ ⟨93, by decide⟩
    | 37 => .occ ⟨40, by decide⟩
    | 38 => .occ ⟨41, by decide⟩
    | 39 => .sumGe
    | 40 => .nonneg ⟨2, by decide⟩
    | 41 => .nonneg ⟨8, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨24, by decide⟩
    | 47 => .nonneg ⟨27, by decide⟩
    | 48 => .nonneg ⟨30, by decide⟩
    | 49 => .nonneg ⟨31, by decide⟩
    | 50 => .nonneg ⟨34, by decide⟩
    | 51 => .nonneg ⟨42, by decide⟩
    | 52 => .nonneg ⟨43, by decide⟩
    | 53 => .nonneg ⟨44, by decide⟩
    | 54 => .branchLe ⟨6, by decide⟩ 0
    | 55 => .branchLe ⟨13, by decide⟩ 0
    | 56 => .branchLe ⟨25, by decide⟩ 0
    | 57 => .branchLe ⟨29, by decide⟩ 0
    | 58 => .branchLe ⟨45, by decide⟩ 0
    | 59 => .branchLe ⟨50, by decide⟩ 0
    | 60 => .branchLe ⟨54, by decide⟩ 0
    | 61 => .branchLe ⟨59, by decide⟩ 0
    | 62 => .branchGe ⟨47, by decide⟩ 1
    | 63 => .branchGe ⟨53, by decide⟩ 1
    | _ => .sumGe

def mults_416_L3 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1588
    | 1 => 10184
    | 2 => 234
    | 3 => 2643
    | 4 => 3388
    | 5 => 234
    | 6 => 7853
    | 7 => 7711
    | 8 => 3894
    | 9 => 3492
    | 10 => 4916
    | 11 => 3609
    | 12 => 1765
    | 13 => 1187
    | 14 => 1488
    | 15 => 1731
    | 16 => 1781
    | 17 => 615
    | 18 => 3936
    | 19 => 4558
    | 20 => 4591
    | 21 => 2853
    | 22 => 1650
    | 23 => 3458
    | 24 => 754
    | 25 => 3461
    | 26 => 499
    | 27 => 907
    | 28 => 2841
    | 29 => 15
    | 30 => 1237
    | 31 => 2267
    | 32 => 1541
    | 33 => 1420
    | 34 => 4090
    | 35 => 1076
    | 36 => 4025
    | 37 => 2192
    | 38 => 4640
    | 39 => 14243
    | 40 => 4737
    | 41 => 12957
    | 42 => 10606
    | 43 => 10656
    | 44 => 5475
    | 45 => 5143
    | 46 => 3455
    | 47 => 1871
    | 48 => 2362
    | 49 => 3509
    | 50 => 21
    | 51 => 10706
    | 52 => 997
    | 53 => 3272
    | 54 => 13744
    | 55 => 10290
    | 56 => 6335
    | 57 => 5012
    | 58 => 5578
    | 59 => 4852
    | 60 => 13744
    | 61 => 12051
    | 62 => 22602
    | 63 => 20592
    | _ => 0

theorem coeff_cancel_416_L3 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L3 i : Int) * (refs_416_L3 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L3 :
    (∑ i : Fin 64, (mults_416_L3 i : Int) * (refs_416_L3 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf3_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_39_0 : x ⟨38, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_le_60_0 : x ⟨59, by decide⟩ ≤ 0)
    (h_ge_48_1 : (1 : Int) ≤ x ⟨47, by decide⟩)
    (h_ge_54_1 : (1 : Int) ≤ x ⟨53, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L3 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L3 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨82, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨83, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨84, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨47, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨86, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨88, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨72, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨51, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨89, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨90, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨92, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨59, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨93, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_60_0]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_48_1]
    · simp only [refs_416_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_54_1]
  exact farkas_leaf_unsat _ _ (mults_416_L3) coeff_cancel_416_L3 rhs_neg_416_L3 x hrows

-- leaf 4, path LLLLLLLLRRR, Farkas rhs -2337
def refs_416_L4 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨64, by decide⟩
    | 2 => .occ ⟨65, by decide⟩
    | 3 => .occ ⟨43, by decide⟩
    | 4 => .occ ⟨1, by decide⟩
    | 5 => .occ ⟨94, by decide⟩
    | 6 => .occ ⟨45, by decide⟩
    | 7 => .occ ⟨95, by decide⟩
    | 8 => .occ ⟨85, by decide⟩
    | 9 => .occ ⟨96, by decide⟩
    | 10 => .occ ⟨97, by decide⟩
    | 11 => .occ ⟨98, by decide⟩
    | 12 => .occ ⟨99, by decide⟩
    | 13 => .occ ⟨5, by decide⟩
    | 14 => .occ ⟨6, by decide⟩
    | 15 => .occ ⟨100, by decide⟩
    | 16 => .occ ⟨14, by decide⟩
    | 17 => .occ ⟨101, by decide⟩
    | 18 => .occ ⟨15, by decide⟩
    | 19 => .occ ⟨17, by decide⟩
    | 20 => .occ ⟨18, by decide⟩
    | 21 => .occ ⟨19, by decide⟩
    | 22 => .occ ⟨20, by decide⟩
    | 23 => .occ ⟨102, by decide⟩
    | 24 => .occ ⟨71, by decide⟩
    | 25 => .occ ⟨103, by decide⟩
    | 26 => .occ ⟨21, by decide⟩
    | 27 => .occ ⟨104, by decide⟩
    | 28 => .occ ⟨105, by decide⟩
    | 29 => .occ ⟨76, by decide⟩
    | 30 => .occ ⟨106, by decide⟩
    | 31 => .occ ⟨28, by decide⟩
    | 32 => .occ ⟨29, by decide⟩
    | 33 => .occ ⟨30, by decide⟩
    | 34 => .occ ⟨92, by decide⟩
    | 35 => .occ ⟨107, by decide⟩
    | 36 => .occ ⟨108, by decide⟩
    | 37 => .occ ⟨60, by decide⟩
    | 38 => .occ ⟨109, by decide⟩
    | 39 => .occ ⟨61, by decide⟩
    | 40 => .occ ⟨110, by decide⟩
    | 41 => .occ ⟨40, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨8, by decide⟩
    | 45 => .nonneg ⟨10, by decide⟩
    | 46 => .nonneg ⟨16, by decide⟩
    | 47 => .nonneg ⟨29, by decide⟩
    | 48 => .nonneg ⟨31, by decide⟩
    | 49 => .nonneg ⟨40, by decide⟩
    | 50 => .nonneg ⟨44, by decide⟩
    | 51 => .nonneg ⟨46, by decide⟩
    | 52 => .nonneg ⟨56, by decide⟩
    | 53 => .nonneg ⟨62, by decide⟩
    | 54 => .branchLe ⟨6, by decide⟩ 0
    | 55 => .branchLe ⟨13, by decide⟩ 0
    | 56 => .branchLe ⟨25, by decide⟩ 0
    | 57 => .branchLe ⟨38, by decide⟩ 0
    | 58 => .branchLe ⟨45, by decide⟩ 0
    | 59 => .branchLe ⟨50, by decide⟩ 0
    | 60 => .branchLe ⟨54, by decide⟩ 0
    | 61 => .branchGe ⟨47, by decide⟩ 1
    | 62 => .branchGe ⟨53, by decide⟩ 1
    | 63 => .branchGe ⟨59, by decide⟩ 1
    | _ => .sumGe

def mults_416_L4 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 125
    | 1 => 1242
    | 2 => 281
    | 3 => 1273
    | 4 => 1441
    | 5 => 1513
    | 6 => 37
    | 7 => 1736
    | 8 => 1529
    | 9 => 1705
    | 10 => 381
    | 11 => 2234
    | 12 => 2346
    | 13 => 1738
    | 14 => 206
    | 15 => 677
    | 16 => 290
    | 17 => 206
    | 18 => 958
    | 19 => 1624
    | 20 => 1401
    | 21 => 378
    | 22 => 252
    | 23 => 419
    | 24 => 265
    | 25 => 522
    | 26 => 929
    | 27 => 1881
    | 28 => 837
    | 29 => 122
    | 30 => 1575
    | 31 => 714
    | 32 => 209
    | 33 => 986
    | 34 => 37
    | 35 => 65
    | 36 => 438
    | 37 => 628
    | 38 => 162
    | 39 => 496
    | 40 => 12
    | 41 => 1201
    | 42 => 3653
    | 43 => 4300
    | 44 => 2328
    | 45 => 1165
    | 46 => 1277
    | 47 => 997
    | 48 => 1512
    | 49 => 429
    | 50 => 2434
    | 51 => 790
    | 52 => 57
    | 53 => 1961
    | 54 => 3203
    | 55 => 1130
    | 56 => 2002
    | 57 => 10
    | 58 => 3447
    | 59 => 459
    | 60 => 3203
    | 61 => 3393
    | 62 => 3447
    | 63 => 13918
    | _ => 0

theorem coeff_cancel_416_L4 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L4 i : Int) * (refs_416_L4 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L4 :
    (∑ i : Fin 64, (mults_416_L4 i : Int) * (refs_416_L4 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf4_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_39_0 : x ⟨38, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_48_1 : (1 : Int) ≤ x ⟨47, by decide⟩)
    (h_ge_54_1 : (1 : Int) ≤ x ⟨53, by decide⟩)
    (h_ge_60_1 : (1 : Int) ≤ x ⟨59, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L4 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L4 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨65, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨95, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨96, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨97, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨98, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨99, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨100, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨102, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨71, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨103, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨104, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨105, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨92, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨109, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨110, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨46, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨62, by decide⟩]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_39_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_48_1]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_54_1]
    · simp only [refs_416_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_60_1]
  exact farkas_leaf_unsat _ _ (mults_416_L4) coeff_cancel_416_L4 rhs_neg_416_L4 x hrows

-- leaf 5, path LLLLLLLRL, Farkas rhs -4932
def refs_416_L5 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨64, by decide⟩
    | 2 => .occ ⟨111, by decide⟩
    | 3 => .occ ⟨112, by decide⟩
    | 4 => .occ ⟨46, by decide⟩
    | 5 => .occ ⟨113, by decide⟩
    | 6 => .occ ⟨98, by decide⟩
    | 7 => .occ ⟨114, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨5, by decide⟩
    | 10 => .occ ⟨6, by decide⟩
    | 11 => .occ ⟨115, by decide⟩
    | 12 => .occ ⟨116, by decide⟩
    | 13 => .occ ⟨117, by decide⟩
    | 14 => .occ ⟨7, by decide⟩
    | 15 => .occ ⟨8, by decide⟩
    | 16 => .occ ⟨9, by decide⟩
    | 17 => .occ ⟨12, by decide⟩
    | 18 => .occ ⟨14, by decide⟩
    | 19 => .occ ⟨118, by decide⟩
    | 20 => .occ ⟨15, by decide⟩
    | 21 => .occ ⟨16, by decide⟩
    | 22 => .occ ⟨17, by decide⟩
    | 23 => .occ ⟨18, by decide⟩
    | 24 => .occ ⟨19, by decide⟩
    | 25 => .occ ⟨20, by decide⟩
    | 26 => .occ ⟨119, by decide⟩
    | 27 => .occ ⟨120, by decide⟩
    | 28 => .occ ⟨76, by decide⟩
    | 29 => .occ ⟨55, by decide⟩
    | 30 => .occ ⟨91, by decide⟩
    | 31 => .occ ⟨121, by decide⟩
    | 32 => .occ ⟨30, by decide⟩
    | 33 => .occ ⟨122, by decide⟩
    | 34 => .occ ⟨123, by decide⟩
    | 35 => .occ ⟨35, by decide⟩
    | 36 => .occ ⟨124, by decide⟩
    | 37 => .occ ⟨38, by decide⟩
    | 38 => .occ ⟨125, by decide⟩
    | 39 => .occ ⟨40, by decide⟩
    | 40 => .occ ⟨126, by decide⟩
    | 41 => .occ ⟨41, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨4, by decide⟩
    | 45 => .nonneg ⟨8, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨20, by decide⟩
    | 49 => .nonneg ⟨24, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨32, by decide⟩
    | 52 => .nonneg ⟨41, by decide⟩
    | 53 => .nonneg ⟨43, by decide⟩
    | 54 => .nonneg ⟨49, by decide⟩
    | 55 => .branchLe ⟨6, by decide⟩ 0
    | 56 => .branchLe ⟨13, by decide⟩ 0
    | 57 => .branchLe ⟨25, by decide⟩ 0
    | 58 => .branchLe ⟨29, by decide⟩ 0
    | 59 => .branchLe ⟨45, by decide⟩ 0
    | 60 => .branchLe ⟨46, by decide⟩ 0
    | 61 => .branchLe ⟨50, by decide⟩ 0
    | 62 => .branchLe ⟨54, by decide⟩ 0
    | 63 => .branchGe ⟨38, by decide⟩ 1
    | _ => .sumGe

def mults_416_L5 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1505
    | 1 => 1625
    | 2 => 1325
    | 3 => 2042
    | 4 => 1529
    | 5 => 3852
    | 6 => 3651
    | 7 => 1831
    | 8 => 380
    | 9 => 1809
    | 10 => 1312
    | 11 => 172
    | 12 => 842
    | 13 => 631
    | 14 => 984
    | 15 => 784
    | 16 => 690
    | 17 => 18
    | 18 => 538
    | 19 => 1531
    | 20 => 2008
    | 21 => 495
    | 22 => 1991
    | 23 => 1071
    | 24 => 1403
    | 25 => 1848
    | 26 => 1861
    | 27 => 26
    | 28 => 607
    | 29 => 345
    | 30 => 1049
    | 31 => 723
    | 32 => 712
    | 33 => 320
    | 34 => 1122
    | 35 => 1371
    | 36 => 684
    | 37 => 117
    | 38 => 514
    | 39 => 1162
    | 40 => 41
    | 41 => 2018
    | 42 => 6384
    | 43 => 4431
    | 44 => 23
    | 45 => 931
    | 46 => 2021
    | 47 => 2630
    | 48 => 4265
    | 49 => 326
    | 50 => 4848
    | 51 => 2412
    | 52 => 3247
    | 53 => 1342
    | 54 => 1301
    | 55 => 5392
    | 56 => 6325
    | 57 => 57
    | 58 => 2436
    | 59 => 3863
    | 60 => 1532
    | 61 => 3657
    | 62 => 6384
    | 63 => 17922
    | _ => 0

theorem coeff_cancel_416_L5 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L5 i : Int) * (refs_416_L5 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L5 :
    (∑ i : Fin 64, (mults_416_L5 i : Int) * (refs_416_L5 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf5_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_47_0 : x ⟨46, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_39_1 : (1 : Int) ≤ x ⟨38, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L5 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L5 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨98, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨114, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨115, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨116, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨117, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨119, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨120, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨121, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨122, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨123, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨124, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨125, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨49, by decide⟩]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_46_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_47_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_39_1]
  exact farkas_leaf_unsat _ _ (mults_416_L5) coeff_cancel_416_L5 rhs_neg_416_L5 x hrows

-- leaf 6, path LLLLLLLRR, Farkas rhs -1
def refs_416_L6 : Fin 4 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨112, by decide⟩
    | 1 => .nonneg ⟨7, by decide⟩
    | 2 => .branchGe ⟨38, by decide⟩ 1
    | 3 => .branchGe ⟨46, by decide⟩ 1
    | _ => .sumGe

def mults_416_L6 : Fin 4 → Nat
  | i => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | _ => 0

theorem coeff_cancel_416_L6 :
    ∀ j : Fin 63, (∑ i : Fin 4, (mults_416_L6 i : Int) * (refs_416_L6 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L6 :
    (∑ i : Fin 4, (mults_416_L6 i : Int) * (refs_416_L6 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf6_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_46_0 : x ⟨45, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_39_1 : (1 : Int) ≤ x ⟨38, by decide⟩)
    (h_ge_47_1 : (1 : Int) ≤ x ⟨46, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 4,
      (∑ j : Fin 63, (refs_416_L6 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L6 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_39_1]
    · simp only [refs_416_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_47_1]
  exact farkas_leaf_unsat _ _ (mults_416_L6) coeff_cancel_416_L6 rhs_neg_416_L6 x hrows

-- leaf 7, path LLLLLLR, Farkas rhs -3999
def refs_416_L7 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨64, by decide⟩
    | 2 => .occ ⟨43, by decide⟩
    | 3 => .occ ⟨127, by decide⟩
    | 4 => .occ ⟨128, by decide⟩
    | 5 => .occ ⟨129, by decide⟩
    | 6 => .occ ⟨130, by decide⟩
    | 7 => .occ ⟨131, by decide⟩
    | 8 => .occ ⟨132, by decide⟩
    | 9 => .occ ⟨133, by decide⟩
    | 10 => .occ ⟨4, by decide⟩
    | 11 => .occ ⟨5, by decide⟩
    | 12 => .occ ⟨6, by decide⟩
    | 13 => .occ ⟨134, by decide⟩
    | 14 => .occ ⟨10, by decide⟩
    | 15 => .occ ⟨101, by decide⟩
    | 16 => .occ ⟨15, by decide⟩
    | 17 => .occ ⟨50, by decide⟩
    | 18 => .occ ⟨16, by decide⟩
    | 19 => .occ ⟨17, by decide⟩
    | 20 => .occ ⟨20, by decide⟩
    | 21 => .occ ⟨72, by decide⟩
    | 22 => .occ ⟨135, by decide⟩
    | 23 => .occ ⟨136, by decide⟩
    | 24 => .occ ⟨137, by decide⟩
    | 25 => .occ ⟨138, by decide⟩
    | 26 => .occ ⟨139, by decide⟩
    | 27 => .occ ⟨54, by decide⟩
    | 28 => .occ ⟨140, by decide⟩
    | 29 => .occ ⟨141, by decide⟩
    | 30 => .occ ⟨142, by decide⟩
    | 31 => .occ ⟨143, by decide⟩
    | 32 => .occ ⟨144, by decide⟩
    | 33 => .occ ⟨145, by decide⟩
    | 34 => .occ ⟨146, by decide⟩
    | 35 => .occ ⟨109, by decide⟩
    | 36 => .occ ⟨147, by decide⟩
    | 37 => .occ ⟨93, by decide⟩
    | 38 => .occ ⟨148, by decide⟩
    | 39 => .occ ⟨39, by decide⟩
    | 40 => .occ ⟨40, by decide⟩
    | 41 => .occ ⟨149, by decide⟩
    | 42 => .occ ⟨41, by decide⟩
    | 43 => .sumGe
    | 44 => .nonneg ⟨2, by decide⟩
    | 45 => .nonneg ⟨4, by decide⟩
    | 46 => .nonneg ⟨7, by decide⟩
    | 47 => .nonneg ⟨8, by decide⟩
    | 48 => .nonneg ⟨10, by decide⟩
    | 49 => .nonneg ⟨16, by decide⟩
    | 50 => .nonneg ⟨18, by decide⟩
    | 51 => .nonneg ⟨20, by decide⟩
    | 52 => .nonneg ⟨22, by decide⟩
    | 53 => .nonneg ⟨30, by decide⟩
    | 54 => .nonneg ⟨32, by decide⟩
    | 55 => .nonneg ⟨42, by decide⟩
    | 56 => .nonneg ⟨44, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨13, by decide⟩ 0
    | 59 => .branchLe ⟨25, by decide⟩ 0
    | 60 => .branchLe ⟨29, by decide⟩ 0
    | 61 => .branchLe ⟨50, by decide⟩ 0
    | 62 => .branchLe ⟨54, by decide⟩ 0
    | 63 => .branchGe ⟨45, by decide⟩ 1
    | _ => .sumGe

def mults_416_L7 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1800
    | 1 => 175
    | 2 => 4965
    | 3 => 9142
    | 4 => 3267
    | 5 => 175
    | 6 => 9479
    | 7 => 2614
    | 8 => 5618
    | 9 => 3218
    | 10 => 1299
    | 11 => 2853
    | 12 => 1944
    | 13 => 3115
    | 14 => 3384
    | 15 => 1363
    | 16 => 2076
    | 17 => 522
    | 18 => 3271
    | 19 => 2371
    | 20 => 3419
    | 21 => 777
    | 22 => 1621
    | 23 => 476
    | 24 => 1171
    | 25 => 2184
    | 26 => 104
    | 27 => 410
    | 28 => 2093
    | 29 => 1034
    | 30 => 333
    | 31 => 528
    | 32 => 1656
    | 33 => 322
    | 34 => 1025
    | 35 => 602
    | 36 => 3869
    | 37 => 1342
    | 38 => 404
    | 39 => 3115
    | 40 => 175
    | 41 => 1334
    | 42 => 3384
    | 43 => 11714
    | 44 => 4837
    | 45 => 1230
    | 46 => 2678
    | 47 => 2251
    | 48 => 495
    | 49 => 6519
    | 50 => 11799
    | 51 => 3621
    | 52 => 319
    | 53 => 1343
    | 54 => 418
    | 55 => 6286
    | 56 => 6212
    | 57 => 9530
    | 58 => 9778
    | 59 => 3419
    | 60 => 6264
    | 61 => 9
    | 62 => 3559
    | 63 => 44096
    | _ => 0

theorem coeff_cancel_416_L7 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L7 i : Int) * (refs_416_L7 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L7 :
    (∑ i : Fin 64, (mults_416_L7 i : Int) * (refs_416_L7 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf7_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_55_0 : x ⟨54, by decide⟩ ≤ 0)
    (h_ge_46_1 : (1 : Int) ≤ x ⟨45, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L7 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L7 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨127, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨128, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨130, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨132, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨133, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨134, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨72, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨135, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨136, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨137, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨138, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨139, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨54, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨140, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨141, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨143, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨144, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨145, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨146, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨109, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨147, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨93, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨148, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_55_0]
    · simp only [refs_416_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_46_1]
  exact farkas_leaf_unsat _ _ (mults_416_L7) coeff_cancel_416_L7 rhs_neg_416_L7 x hrows

-- leaf 8, path LLLLLRLLLLLL, Farkas rhs -686
def refs_416_L8 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨111, by decide⟩
    | 1 => .occ ⟨150, by decide⟩
    | 2 => .occ ⟨151, by decide⟩
    | 3 => .occ ⟨46, by decide⟩
    | 4 => .occ ⟨152, by decide⟩
    | 5 => .occ ⟨131, by decide⟩
    | 6 => .occ ⟨153, by decide⟩
    | 7 => .occ ⟨154, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨5, by decide⟩
    | 10 => .occ ⟨10, by decide⟩
    | 11 => .occ ⟨11, by decide⟩
    | 12 => .occ ⟨118, by decide⟩
    | 13 => .occ ⟨50, by decide⟩
    | 14 => .occ ⟨16, by decide⟩
    | 15 => .occ ⟨17, by decide⟩
    | 16 => .occ ⟨155, by decide⟩
    | 17 => .occ ⟨18, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨156, by decide⟩
    | 21 => .occ ⟨157, by decide⟩
    | 22 => .occ ⟨158, by decide⟩
    | 23 => .occ ⟨159, by decide⟩
    | 24 => .occ ⟨160, by decide⟩
    | 25 => .occ ⟨29, by decide⟩
    | 26 => .occ ⟨161, by decide⟩
    | 27 => .occ ⟨30, by decide⟩
    | 28 => .occ ⟨31, by decide⟩
    | 29 => .occ ⟨34, by decide⟩
    | 30 => .occ ⟨162, by decide⟩
    | 31 => .occ ⟨163, by decide⟩
    | 32 => .occ ⟨61, by decide⟩
    | 33 => .occ ⟨37, by decide⟩
    | 34 => .occ ⟨110, by decide⟩
    | 35 => .occ ⟨39, by decide⟩
    | 36 => .occ ⟨40, by decide⟩
    | 37 => .occ ⟨149, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨7, by decide⟩
    | 41 => .nonneg ⟨8, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨24, by decide⟩
    | 47 => .nonneg ⟨30, by decide⟩
    | 48 => .nonneg ⟨32, by decide⟩
    | 49 => .nonneg ⟨33, by decide⟩
    | 50 => .nonneg ⟨41, by decide⟩
    | 51 => .nonneg ⟨43, by decide⟩
    | 52 => .branchLe ⟨1, by decide⟩ 0
    | 53 => .branchLe ⟨5, by decide⟩ 0
    | 54 => .branchLe ⟨6, by decide⟩ 0
    | 55 => .branchLe ⟨11, by decide⟩ 1
    | 56 => .branchLe ⟨13, by decide⟩ 0
    | 57 => .branchLe ⟨21, by decide⟩ 0
    | 58 => .branchLe ⟨25, by decide⟩ 0
    | 59 => .branchLe ⟨29, by decide⟩ 0
    | 60 => .branchLe ⟨49, by decide⟩ 0
    | 61 => .branchLe ⟨50, by decide⟩ 0
    | 62 => .branchLe ⟨51, by decide⟩ 0
    | 63 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L8 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 518
    | 1 => 107
    | 2 => 28
    | 3 => 376
    | 4 => 878
    | 5 => 1441
    | 6 => 1762
    | 7 => 1241
    | 8 => 63
    | 9 => 1207
    | 10 => 268
    | 11 => 26
    | 12 => 710
    | 13 => 834
    | 14 => 931
    | 15 => 830
    | 16 => 708
    | 17 => 448
    | 18 => 1293
    | 19 => 587
    | 20 => 182
    | 21 => 726
    | 22 => 126
    | 23 => 194
    | 24 => 748
    | 25 => 256
    | 26 => 245
    | 27 => 140
    | 28 => 109
    | 29 => 195
    | 30 => 54
    | 31 => 278
    | 32 => 460
    | 33 => 131
    | 34 => 118
    | 35 => 190
    | 36 => 166
    | 37 => 97
    | 38 => 2136
    | 39 => 1321
    | 40 => 26
    | 41 => 754
    | 42 => 2558
    | 43 => 529
    | 44 => 651
    | 45 => 575
    | 46 => 484
    | 47 => 435
    | 48 => 155
    | 49 => 703
    | 50 => 2949
    | 51 => 2018
    | 52 => 1891
    | 53 => 1662
    | 54 => 1764
    | 55 => 1545
    | 56 => 1291
    | 57 => 1271
    | 58 => 1342
    | 59 => 980
    | 60 => 682
    | 61 => 388
    | 62 => 621
    | 63 => 5636
    | _ => 0

theorem coeff_cancel_416_L8 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L8 i : Int) * (refs_416_L8 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L8 :
    (∑ i : Fin 64, (mults_416_L8 i : Int) * (refs_416_L8 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf8_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_2_0 : x ⟨1, by decide⟩ ≤ 0)
    (h_le_6_0 : x ⟨5, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L8 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L8 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨150, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨151, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨152, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨153, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨154, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨156, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨157, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨158, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨159, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨162, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨163, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨110, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_2_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_6_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_12_1]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_22_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L8) coeff_cancel_416_L8 rhs_neg_416_L8 x hrows

-- leaf 9, path LLLLLRLLLLLR, Farkas rhs -3994
def refs_416_L9 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨164, by decide⟩
    | 1 => .occ ⟨0, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨111, by decide⟩
    | 4 => .occ ⟨166, by decide⟩
    | 5 => .occ ⟨150, by decide⟩
    | 6 => .occ ⟨152, by decide⟩
    | 7 => .occ ⟨85, by decide⟩
    | 8 => .occ ⟨131, by decide⟩
    | 9 => .occ ⟨153, by decide⟩
    | 10 => .occ ⟨154, by decide⟩
    | 11 => .occ ⟨4, by decide⟩
    | 12 => .occ ⟨5, by decide⟩
    | 13 => .occ ⟨6, by decide⟩
    | 14 => .occ ⟨49, by decide⟩
    | 15 => .occ ⟨7, by decide⟩
    | 16 => .occ ⟨8, by decide⟩
    | 17 => .occ ⟨14, by decide⟩
    | 18 => .occ ⟨167, by decide⟩
    | 19 => .occ ⟨118, by decide⟩
    | 20 => .occ ⟨15, by decide⟩
    | 21 => .occ ⟨50, by decide⟩
    | 22 => .occ ⟨16, by decide⟩
    | 23 => .occ ⟨17, by decide⟩
    | 24 => .occ ⟨155, by decide⟩
    | 25 => .occ ⟨18, by decide⟩
    | 26 => .occ ⟨19, by decide⟩
    | 27 => .occ ⟨20, by decide⟩
    | 28 => .occ ⟨159, by decide⟩
    | 29 => .occ ⟨90, by decide⟩
    | 30 => .occ ⟨76, by decide⟩
    | 31 => .occ ⟨26, by decide⟩
    | 32 => .occ ⟨78, by decide⟩
    | 33 => .occ ⟨28, by decide⟩
    | 34 => .occ ⟨29, by decide⟩
    | 35 => .occ ⟨161, by decide⟩
    | 36 => .occ ⟨168, by decide⟩
    | 37 => .occ ⟨169, by decide⟩
    | 38 => .occ ⟨170, by decide⟩
    | 39 => .occ ⟨171, by decide⟩
    | 40 => .occ ⟨63, by decide⟩
    | 41 => .occ ⟨41, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨7, by decide⟩
    | 45 => .nonneg ⟨10, by decide⟩
    | 46 => .nonneg ⟨12, by decide⟩
    | 47 => .nonneg ⟨16, by decide⟩
    | 48 => .nonneg ⟨18, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨24, by decide⟩
    | 51 => .nonneg ⟨29, by decide⟩
    | 52 => .nonneg ⟨30, by decide⟩
    | 53 => .nonneg ⟨43, by decide⟩
    | 54 => .branchLe ⟨5, by decide⟩ 0
    | 55 => .branchLe ⟨6, by decide⟩ 0
    | 56 => .branchLe ⟨11, by decide⟩ 1
    | 57 => .branchLe ⟨13, by decide⟩ 0
    | 58 => .branchLe ⟨21, by decide⟩ 0
    | 59 => .branchLe ⟨49, by decide⟩ 0
    | 60 => .branchLe ⟨50, by decide⟩ 0
    | 61 => .branchLe ⟨51, by decide⟩ 0
    | 62 => .branchGe ⟨1, by decide⟩ 1
    | 63 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L9 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 4122
    | 1 => 2410
    | 2 => 3802
    | 3 => 576
    | 4 => 2736
    | 5 => 1012
    | 6 => 32
    | 7 => 1292
    | 8 => 2504
    | 9 => 1148
    | 10 => 350
    | 11 => 1644
    | 12 => 1836
    | 13 => 20
    | 14 => 1858
    | 15 => 560
    | 16 => 614
    | 17 => 334
    | 18 => 4122
    | 19 => 576
    | 20 => 2611
    | 21 => 3311
    | 22 => 3651
    | 23 => 2563
    | 24 => 706
    | 25 => 1942
    | 26 => 1794
    | 27 => 742
    | 28 => 112
    | 29 => 1218
    | 30 => 828
    | 31 => 2040
    | 32 => 334
    | 33 => 2191
    | 34 => 1088
    | 35 => 2643
    | 36 => 934
    | 37 => 544
    | 38 => 216
    | 39 => 328
    | 40 => 1561
    | 41 => 961
    | 42 => 7586
    | 43 => 7808
    | 44 => 2412
    | 45 => 1716
    | 46 => 3740
    | 47 => 7842
    | 48 => 9034
    | 49 => 1244
    | 50 => 3990
    | 51 => 5272
    | 52 => 1856
    | 53 => 914
    | 54 => 3024
    | 55 => 1424
    | 56 => 5942
    | 57 => 7586
    | 58 => 2252
    | 59 => 440
    | 60 => 1168
    | 61 => 2864
    | 62 => 22118
    | 63 => 5402
    | _ => 0

theorem coeff_cancel_416_L9 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L9 i : Int) * (refs_416_L9 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L9 :
    (∑ i : Fin 64, (mults_416_L9 i : Int) * (refs_416_L9 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf9_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_6_0 : x ⟨5, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_ge_2_1 : (1 : Int) ≤ x ⟨1, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L9 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L9 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨164, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨150, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨152, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨153, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨154, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨167, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨159, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨90, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨78, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨168, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨169, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨170, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_6_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_12_1]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_22_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_2_1]
    · simp only [refs_416_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L9) coeff_cancel_416_L9 rhs_neg_416_L9 x hrows

-- leaf 10, path LLLLLRLLLLR, Farkas rhs -3340
def refs_416_L10 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨42, by decide⟩
    | 1 => .occ ⟨172, by decide⟩
    | 2 => .occ ⟨64, by decide⟩
    | 3 => .occ ⟨43, by decide⟩
    | 4 => .occ ⟨111, by decide⟩
    | 5 => .occ ⟨173, by decide⟩
    | 6 => .occ ⟨174, by decide⟩
    | 7 => .occ ⟨131, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨5, by decide⟩
    | 10 => .occ ⟨49, by decide⟩
    | 11 => .occ ⟨7, by decide⟩
    | 12 => .occ ⟨14, by decide⟩
    | 13 => .occ ⟨15, by decide⟩
    | 14 => .occ ⟨16, by decide⟩
    | 15 => .occ ⟨17, by decide⟩
    | 16 => .occ ⟨155, by decide⟩
    | 17 => .occ ⟨18, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨175, by decide⟩
    | 20 => .occ ⟨156, by decide⟩
    | 21 => .occ ⟨176, by decide⟩
    | 22 => .occ ⟨177, by decide⟩
    | 23 => .occ ⟨55, by decide⟩
    | 24 => .occ ⟨27, by decide⟩
    | 25 => .occ ⟨142, by decide⟩
    | 26 => .occ ⟨29, by decide⟩
    | 27 => .occ ⟨161, by decide⟩
    | 28 => .occ ⟨30, by decide⟩
    | 29 => .occ ⟨57, by decide⟩
    | 30 => .occ ⟨178, by decide⟩
    | 31 => .occ ⟨179, by decide⟩
    | 32 => .occ ⟨171, by decide⟩
    | 33 => .occ ⟨108, by decide⟩
    | 34 => .occ ⟨162, by decide⟩
    | 35 => .occ ⟨79, by decide⟩
    | 36 => .occ ⟨35, by decide⟩
    | 37 => .occ ⟨93, by decide⟩
    | 38 => .occ ⟨62, by decide⟩
    | 39 => .sumGe
    | 40 => .nonneg ⟨2, by decide⟩
    | 41 => .nonneg ⟨4, by decide⟩
    | 42 => .nonneg ⟨8, by decide⟩
    | 43 => .nonneg ⟨12, by decide⟩
    | 44 => .nonneg ⟨16, by decide⟩
    | 45 => .nonneg ⟨18, by decide⟩
    | 46 => .nonneg ⟨20, by decide⟩
    | 47 => .nonneg ⟨22, by decide⟩
    | 48 => .nonneg ⟨30, by decide⟩
    | 49 => .nonneg ⟨31, by decide⟩
    | 50 => .nonneg ⟨32, by decide⟩
    | 51 => .nonneg ⟨41, by decide⟩
    | 52 => .nonneg ⟨42, by decide⟩
    | 53 => .nonneg ⟨43, by decide⟩
    | 54 => .nonneg ⟨50, by decide⟩
    | 55 => .nonneg ⟨59, by decide⟩
    | 56 => .branchLe ⟨5, by decide⟩ 0
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨13, by decide⟩ 0
    | 59 => .branchLe ⟨25, by decide⟩ 0
    | 60 => .branchLe ⟨29, by decide⟩ 0
    | 61 => .branchLe ⟨51, by decide⟩ 0
    | 62 => .branchGe ⟨11, by decide⟩ 2
    | 63 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L10 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1532
    | 1 => 2034
    | 2 => 56
    | 3 => 508
    | 4 => 1126
    | 5 => 134
    | 6 => 1818
    | 7 => 210
    | 8 => 3196
    | 9 => 56
    | 10 => 68
    | 11 => 1868
    | 12 => 56
    | 13 => 802
    | 14 => 1186
    | 15 => 856
    | 16 => 344
    | 17 => 890
    | 18 => 1098
    | 19 => 44
    | 20 => 1338
    | 21 => 474
    | 22 => 798
    | 23 => 1938
    | 24 => 1222
    | 25 => 493
    | 26 => 789
    | 27 => 1232
    | 28 => 990
    | 29 => 796
    | 30 => 470
    | 31 => 2936
    | 32 => 1392
    | 33 => 546
    | 34 => 742
    | 35 => 1337
    | 36 => 1118
    | 37 => 169
    | 38 => 132
    | 39 => 5258
    | 40 => 654
    | 41 => 3556
    | 42 => 8074
    | 43 => 3012
    | 44 => 1922
    | 45 => 1642
    | 46 => 3434
    | 47 => 1162
    | 48 => 1968
    | 49 => 3764
    | 50 => 2776
    | 51 => 426
    | 52 => 2076
    | 53 => 5094
    | 54 => 662
    | 55 => 882
    | 56 => 5258
    | 57 => 4578
    | 58 => 5258
    | 59 => 56
    | 60 => 864
    | 61 => 3240
    | 62 => 12550
    | 63 => 2824
    | _ => 0

theorem coeff_cancel_416_L10 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L10 i : Int) * (refs_416_L10 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L10 :
    (∑ i : Fin 64, (mults_416_L10 i : Int) * (refs_416_L10 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf10_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_6_0 : x ⟨5, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_ge_12_2 : (2 : Int) ≤ x ⟨11, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L10 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L10 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨172, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨173, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨174, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨175, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨156, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨176, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨177, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨179, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨162, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨93, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨50, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_6_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_12_2]
    · simp only [refs_416_L10, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L10) coeff_cancel_416_L10 rhs_neg_416_L10 x hrows

-- leaf 11, path LLLLLRLLLR, Farkas rhs -1
def refs_416_L11 : Fin 21 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨1, by decide⟩
    | 1 => .occ ⟨166, by decide⟩
    | 2 => .occ ⟨180, by decide⟩
    | 3 => .occ ⟨153, by decide⟩
    | 4 => .occ ⟨181, by decide⟩
    | 5 => .occ ⟨182, by decide⟩
    | 6 => .occ ⟨183, by decide⟩
    | 7 => .occ ⟨184, by decide⟩
    | 8 => .occ ⟨185, by decide⟩
    | 9 => .sumGe
    | 10 => .nonneg ⟨2, by decide⟩
    | 11 => .nonneg ⟨20, by decide⟩
    | 12 => .nonneg ⟨21, by decide⟩
    | 13 => .nonneg ⟨27, by decide⟩
    | 14 => .nonneg ⟨30, by decide⟩
    | 15 => .nonneg ⟨32, by decide⟩
    | 16 => .nonneg ⟨33, by decide⟩
    | 17 => .nonneg ⟨39, by decide⟩
    | 18 => .nonneg ⟨42, by decide⟩
    | 19 => .branchGe ⟨51, by decide⟩ 1
    | 20 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L11 : Fin 21 → Nat
  | i => match i.val with
    | 0 => 1
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
    | 11 => 1
    | 12 => 1
    | 13 => 1
    | 14 => 1
    | 15 => 1
    | 16 => 1
    | 17 => 1
    | 18 => 1
    | 19 => 6
    | 20 => 6
    | _ => 0

theorem coeff_cancel_416_L11 :
    ∀ j : Fin 63, (∑ i : Fin 21, (mults_416_L11 i : Int) * (refs_416_L11 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L11 :
    (∑ i : Fin 21, (mults_416_L11 i : Int) * (refs_416_L11 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf11_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_6_0 : x ⟨5, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 21,
      (∑ j : Fin 63, (refs_416_L11 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L11 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨180, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨153, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨181, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨182, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨183, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨184, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L11, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L11) coeff_cancel_416_L11 rhs_neg_416_L11 x hrows

-- leaf 12, path LLLLLRLLR, Farkas rhs -55
def refs_416_L12 : Fin 62 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨186, by decide⟩
    | 1 => .occ ⟨0, by decide⟩
    | 2 => .occ ⟨187, by decide⟩
    | 3 => .occ ⟨188, by decide⟩
    | 4 => .occ ⟨111, by decide⟩
    | 5 => .occ ⟨166, by decide⟩
    | 6 => .occ ⟨46, by decide⟩
    | 7 => .occ ⟨189, by decide⟩
    | 8 => .occ ⟨190, by decide⟩
    | 9 => .occ ⟨153, by decide⟩
    | 10 => .occ ⟨5, by decide⟩
    | 11 => .occ ⟨191, by decide⟩
    | 12 => .occ ⟨10, by decide⟩
    | 13 => .occ ⟨11, by decide⟩
    | 14 => .occ ⟨17, by decide⟩
    | 15 => .occ ⟨155, by decide⟩
    | 16 => .occ ⟨18, by decide⟩
    | 17 => .occ ⟨20, by decide⟩
    | 18 => .occ ⟨192, by decide⟩
    | 19 => .occ ⟨73, by decide⟩
    | 20 => .occ ⟨193, by decide⟩
    | 21 => .occ ⟨194, by decide⟩
    | 22 => .occ ⟨138, by decide⟩
    | 23 => .occ ⟨195, by decide⟩
    | 24 => .occ ⟨196, by decide⟩
    | 25 => .occ ⟨197, by decide⟩
    | 26 => .occ ⟨139, by decide⟩
    | 27 => .occ ⟨198, by decide⟩
    | 28 => .occ ⟨199, by decide⟩
    | 29 => .occ ⟨76, by decide⟩
    | 30 => .occ ⟨200, by decide⟩
    | 31 => .occ ⟨201, by decide⟩
    | 32 => .occ ⟨26, by decide⟩
    | 33 => .occ ⟨178, by decide⟩
    | 34 => .occ ⟨202, by decide⟩
    | 35 => .occ ⟨185, by decide⟩
    | 36 => .occ ⟨169, by decide⟩
    | 37 => .occ ⟨108, by decide⟩
    | 38 => .occ ⟨60, by decide⟩
    | 39 => .occ ⟨35, by decide⟩
    | 40 => .occ ⟨203, by decide⟩
    | 41 => .occ ⟨204, by decide⟩
    | 42 => .occ ⟨205, by decide⟩
    | 43 => .occ ⟨206, by decide⟩
    | 44 => .sumGe
    | 45 => .nonneg ⟨2, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨19, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨24, by decide⟩
    | 51 => .nonneg ⟨26, by decide⟩
    | 52 => .nonneg ⟨30, by decide⟩
    | 53 => .nonneg ⟨31, by decide⟩
    | 54 => .nonneg ⟨43, by decide⟩
    | 55 => .nonneg ⟨45, by decide⟩
    | 56 => .branchLe ⟨5, by decide⟩ 0
    | 57 => .branchLe ⟨13, by decide⟩ 0
    | 58 => .branchLe ⟨49, by decide⟩ 0
    | 59 => .branchLe ⟨50, by decide⟩ 0
    | 60 => .branchGe ⟨21, by decide⟩ 1
    | 61 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L12 : Fin 62 → Nat
  | i => match i.val with
    | 0 => 16
    | 1 => 45
    | 2 => 32
    | 3 => 11
    | 4 => 11
    | 5 => 7
    | 6 => 6
    | 7 => 3
    | 8 => 5
    | 9 => 31
    | 10 => 2
    | 11 => 5
    | 12 => 27
    | 13 => 5
    | 14 => 1
    | 15 => 28
    | 16 => 4
    | 17 => 22
    | 18 => 24
    | 19 => 2
    | 20 => 14
    | 21 => 3
    | 22 => 10
    | 23 => 9
    | 24 => 2
    | 25 => 5
    | 26 => 14
    | 27 => 7
    | 28 => 14
    | 29 => 15
    | 30 => 2
    | 31 => 21
    | 32 => 3
    | 33 => 3
    | 34 => 9
    | 35 => 5
    | 36 => 15
    | 37 => 1
    | 38 => 2
    | 39 => 9
    | 40 => 2
    | 41 => 15
    | 42 => 1
    | 43 => 2
    | 44 => 50
    | 45 => 21
    | 46 => 36
    | 47 => 12
    | 48 => 17
    | 49 => 44
    | 50 => 2
    | 51 => 3
    | 52 => 15
    | 53 => 2
    | 54 => 3
    | 55 => 5
    | 56 => 47
    | 57 => 50
    | 58 => 5
    | 59 => 19
    | 60 => 245
    | 61 => 60
    | _ => 0

theorem coeff_cancel_416_L12 :
    ∀ j : Fin 63, (∑ i : Fin 62, (mults_416_L12 i : Int) * (refs_416_L12 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L12 :
    (∑ i : Fin 62, (mults_416_L12 i : Int) * (refs_416_L12 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf12_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_6_0 : x ⟨5, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_22_1 : (1 : Int) ≤ x ⟨21, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 62,
      (∑ j : Fin 63, (refs_416_L12 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L12 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨186, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨187, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨188, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨189, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨190, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨153, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨191, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨192, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨73, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨193, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨194, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨138, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨195, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨196, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨197, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨139, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨198, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨199, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨200, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨201, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨202, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨169, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨203, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨204, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨205, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨206, by decide⟩
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨45, by decide⟩]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_6_0]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_22_1]
    · simp only [refs_416_L12, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L12) coeff_cancel_416_L12 rhs_neg_416_L12 x hrows

-- leaf 13, path LLLLLRLRLL, Farkas rhs -342
def refs_416_L13 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨64, by decide⟩
    | 1 => .occ ⟨207, by decide⟩
    | 2 => .occ ⟨208, by decide⟩
    | 3 => .occ ⟨46, by decide⟩
    | 4 => .occ ⟨131, by decide⟩
    | 5 => .occ ⟨154, by decide⟩
    | 6 => .occ ⟨5, by decide⟩
    | 7 => .occ ⟨6, by decide⟩
    | 8 => .occ ⟨87, by decide⟩
    | 9 => .occ ⟨12, by decide⟩
    | 10 => .occ ⟨13, by decide⟩
    | 11 => .occ ⟨16, by decide⟩
    | 12 => .occ ⟨17, by decide⟩
    | 13 => .occ ⟨18, by decide⟩
    | 14 => .occ ⟨19, by decide⟩
    | 15 => .occ ⟨20, by decide⟩
    | 16 => .occ ⟨158, by decide⟩
    | 17 => .occ ⟨27, by decide⟩
    | 18 => .occ ⟨142, by decide⟩
    | 19 => .occ ⟨29, by decide⟩
    | 20 => .occ ⟨121, by decide⟩
    | 21 => .occ ⟨30, by decide⟩
    | 22 => .occ ⟨56, by decide⟩
    | 23 => .occ ⟨57, by decide⟩
    | 24 => .occ ⟨209, by decide⟩
    | 25 => .occ ⟨169, by decide⟩
    | 26 => .occ ⟨108, by decide⟩
    | 27 => .occ ⟨60, by decide⟩
    | 28 => .occ ⟨31, by decide⟩
    | 29 => .occ ⟨79, by decide⟩
    | 30 => .occ ⟨163, by decide⟩
    | 31 => .occ ⟨124, by decide⟩
    | 32 => .occ ⟨210, by decide⟩
    | 33 => .occ ⟨63, by decide⟩
    | 34 => .occ ⟨39, by decide⟩
    | 35 => .occ ⟨40, by decide⟩
    | 36 => .sumGe
    | 37 => .nonneg ⟨2, by decide⟩
    | 38 => .nonneg ⟨8, by decide⟩
    | 39 => .nonneg ⟨10, by decide⟩
    | 40 => .nonneg ⟨15, by decide⟩
    | 41 => .nonneg ⟨16, by decide⟩
    | 42 => .nonneg ⟨18, by decide⟩
    | 43 => .nonneg ⟨20, by decide⟩
    | 44 => .nonneg ⟨21, by decide⟩
    | 45 => .nonneg ⟨24, by decide⟩
    | 46 => .nonneg ⟨26, by decide⟩
    | 47 => .nonneg ⟨27, by decide⟩
    | 48 => .nonneg ⟨30, by decide⟩
    | 49 => .nonneg ⟨39, by decide⟩
    | 50 => .nonneg ⟨40, by decide⟩
    | 51 => .nonneg ⟨41, by decide⟩
    | 52 => .nonneg ⟨42, by decide⟩
    | 53 => .nonneg ⟨59, by decide⟩
    | 54 => .branchLe ⟨0, by decide⟩ 2
    | 55 => .branchLe ⟨1, by decide⟩ 0
    | 56 => .branchLe ⟨6, by decide⟩ 0
    | 57 => .branchLe ⟨13, by decide⟩ 0
    | 58 => .branchLe ⟨25, by decide⟩ 0
    | 59 => .branchLe ⟨29, by decide⟩ 0
    | 60 => .branchLe ⟨49, by decide⟩ 0
    | 61 => .branchLe ⟨50, by decide⟩ 0
    | 62 => .branchGe ⟨5, by decide⟩ 1
    | 63 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L13 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 396
    | 1 => 250
    | 2 => 480
    | 3 => 1016
    | 4 => 264
    | 5 => 508
    | 6 => 474
    | 7 => 244
    | 8 => 122
    | 9 => 1480
    | 10 => 810
    | 11 => 894
    | 12 => 610
    | 13 => 438
    | 14 => 656
    | 15 => 1190
    | 16 => 196
    | 17 => 136
    | 18 => 299
    | 19 => 545
    | 20 => 122
    | 21 => 369
    | 22 => 610
    | 23 => 207
    | 24 => 132
    | 25 => 534
    | 26 => 366
    | 27 => 14
    | 28 => 620
    | 29 => 196
    | 30 => 302
    | 31 => 122
    | 32 => 146
    | 33 => 54
    | 34 => 1037
    | 35 => 1029
    | 36 => 2886
    | 37 => 1230
    | 38 => 2652
    | 39 => 1302
    | 40 => 146
    | 41 => 1172
    | 42 => 2662
    | 43 => 3340
    | 44 => 216
    | 45 => 1220
    | 46 => 88
    | 47 => 576
    | 48 => 2506
    | 49 => 66
    | 50 => 30
    | 51 => 1682
    | 52 => 994
    | 53 => 76
    | 54 => 2168
    | 55 => 2832
    | 56 => 2520
    | 57 => 474
    | 58 => 58
    | 59 => 1516
    | 60 => 488
    | 61 => 1260
    | 62 => 3028
    | 63 => 1572
    | _ => 0

theorem coeff_cancel_416_L13 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L13 i : Int) * (refs_416_L13 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L13 :
    (∑ i : Fin 64, (mults_416_L13 i : Int) * (refs_416_L13 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf13_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_1_2 : x ⟨0, by decide⟩ ≤ 2)
    (h_le_2_0 : x ⟨1, by decide⟩ ≤ 0)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_6_1 : (1 : Int) ≤ x ⟨5, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L13 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L13 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨207, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨208, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨154, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨158, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨121, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨209, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨169, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨163, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨124, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨210, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨15, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_1_2]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_2_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_6_1]
    · simp only [refs_416_L13, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L13) coeff_cancel_416_L13 rhs_neg_416_L13 x hrows

-- leaf 14, path LLLLLRLRLR, Farkas rhs -12
def refs_416_L14 : Fin 43 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨164, by decide⟩
    | 1 => .occ ⟨0, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨49, by decide⟩
    | 4 => .occ ⟨87, by decide⟩
    | 5 => .occ ⟨14, by decide⟩
    | 6 => .occ ⟨167, by decide⟩
    | 7 => .occ ⟨16, by decide⟩
    | 8 => .occ ⟨17, by decide⟩
    | 9 => .occ ⟨55, by decide⟩
    | 10 => .occ ⟨27, by decide⟩
    | 11 => .occ ⟨28, by decide⟩
    | 12 => .occ ⟨161, by decide⟩
    | 13 => .occ ⟨121, by decide⟩
    | 14 => .occ ⟨182, by decide⟩
    | 15 => .occ ⟨178, by decide⟩
    | 16 => .occ ⟨179, by decide⟩
    | 17 => .occ ⟨109, by decide⟩
    | 18 => .occ ⟨147, by decide⟩
    | 19 => .occ ⟨211, by decide⟩
    | 20 => .occ ⟨212, by decide⟩
    | 21 => .occ ⟨206, by decide⟩
    | 22 => .occ ⟨63, by decide⟩
    | 23 => .occ ⟨39, by decide⟩
    | 24 => .occ ⟨41, by decide⟩
    | 25 => .sumGe
    | 26 => .nonneg ⟨2, by decide⟩
    | 27 => .nonneg ⟨4, by decide⟩
    | 28 => .nonneg ⟨8, by decide⟩
    | 29 => .nonneg ⟨16, by decide⟩
    | 30 => .nonneg ⟨18, by decide⟩
    | 31 => .nonneg ⟨20, by decide⟩
    | 32 => .nonneg ⟨21, by decide⟩
    | 33 => .nonneg ⟨22, by decide⟩
    | 34 => .nonneg ⟨25, by decide⟩
    | 35 => .nonneg ⟨26, by decide⟩
    | 36 => .nonneg ⟨29, by decide⟩
    | 37 => .nonneg ⟨30, by decide⟩
    | 38 => .branchLe ⟨0, by decide⟩ 2
    | 39 => .branchLe ⟨6, by decide⟩ 0
    | 40 => .branchLe ⟨13, by decide⟩ 0
    | 41 => .branchGe ⟨1, by decide⟩ 1
    | 42 => .branchGe ⟨5, by decide⟩ 1
    | _ => .sumGe

def mults_416_L14 : Fin 43 → Nat
  | i => match i.val with
    | 0 => 8
    | 1 => 14
    | 2 => 8
    | 3 => 14
    | 4 => 2
    | 5 => 6
    | 6 => 8
    | 7 => 6
    | 8 => 6
    | 9 => 3
    | 10 => 3
    | 11 => 1
    | 12 => 1
    | 13 => 8
    | 14 => 8
    | 15 => 1
    | 16 => 5
    | 17 => 5
    | 18 => 3
    | 19 => 1
    | 20 => 7
    | 21 => 2
    | 22 => 6
    | 23 => 2
    | 24 => 4
    | 25 => 20
    | 26 => 14
    | 27 => 20
    | 28 => 12
    | 29 => 36
    | 30 => 48
    | 31 => 18
    | 32 => 24
    | 33 => 6
    | 34 => 8
    | 35 => 4
    | 36 => 4
    | 37 => 8
    | 38 => 18
    | 39 => 12
    | 40 => 12
    | 41 => 68
    | 42 => 20
    | _ => 0

theorem coeff_cancel_416_L14 :
    ∀ j : Fin 63, (∑ i : Fin 43, (mults_416_L14 i : Int) * (refs_416_L14 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L14 :
    (∑ i : Fin 43, (mults_416_L14 i : Int) * (refs_416_L14 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf14_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_1_2 : x ⟨0, by decide⟩ ≤ 2)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_2_1 : (1 : Int) ≤ x ⟨1, by decide⟩)
    (h_ge_6_1 : (1 : Int) ≤ x ⟨5, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 43,
      (∑ j : Fin 63, (refs_416_L14 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L14 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨164, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨167, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨121, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨182, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨179, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨109, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨147, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨212, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨206, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_1_2]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_2_1]
    · simp only [refs_416_L14, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_6_1]
  exact farkas_leaf_unsat _ _ (mults_416_L14) coeff_cancel_416_L14 rhs_neg_416_L14 x hrows

-- leaf 15, path LLLLLRLRR, Farkas rhs -1093
def refs_416_L15 : Fin 63 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨111, by decide⟩
    | 2 => .occ ⟨166, by decide⟩
    | 3 => .occ ⟨150, by decide⟩
    | 4 => .occ ⟨207, by decide⟩
    | 5 => .occ ⟨2, by decide⟩
    | 6 => .occ ⟨131, by decide⟩
    | 7 => .occ ⟨153, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨5, by decide⟩
    | 10 => .occ ⟨213, by decide⟩
    | 11 => .occ ⟨214, by decide⟩
    | 12 => .occ ⟨49, by decide⟩
    | 13 => .occ ⟨7, by decide⟩
    | 14 => .occ ⟨8, by decide⟩
    | 15 => .occ ⟨10, by decide⟩
    | 16 => .occ ⟨12, by decide⟩
    | 17 => .occ ⟨118, by decide⟩
    | 18 => .occ ⟨50, by decide⟩
    | 19 => .occ ⟨16, by decide⟩
    | 20 => .occ ⟨155, by decide⟩
    | 21 => .occ ⟨18, by decide⟩
    | 22 => .occ ⟨19, by decide⟩
    | 23 => .occ ⟨20, by decide⟩
    | 24 => .occ ⟨215, by decide⟩
    | 25 => .occ ⟨89, by decide⟩
    | 26 => .occ ⟨76, by decide⟩
    | 27 => .occ ⟨200, by decide⟩
    | 28 => .occ ⟨176, by decide⟩
    | 29 => .occ ⟨140, by decide⟩
    | 30 => .occ ⟨77, by decide⟩
    | 31 => .occ ⟨26, by decide⟩
    | 32 => .occ ⟨216, by decide⟩
    | 33 => .occ ⟨163, by decide⟩
    | 34 => .occ ⟨217, by decide⟩
    | 35 => .occ ⟨218, by decide⟩
    | 36 => .occ ⟨63, by decide⟩
    | 37 => .occ ⟨39, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨4, by decide⟩
    | 41 => .nonneg ⟨7, by decide⟩
    | 42 => .nonneg ⟨8, by decide⟩
    | 43 => .nonneg ⟨10, by decide⟩
    | 44 => .nonneg ⟨12, by decide⟩
    | 45 => .nonneg ⟨18, by decide⟩
    | 46 => .nonneg ⟨24, by decide⟩
    | 47 => .nonneg ⟨28, by decide⟩
    | 48 => .nonneg ⟨29, by decide⟩
    | 49 => .nonneg ⟨30, by decide⟩
    | 50 => .nonneg ⟨31, by decide⟩
    | 51 => .nonneg ⟨32, by decide⟩
    | 52 => .nonneg ⟨33, by decide⟩
    | 53 => .nonneg ⟨57, by decide⟩
    | 54 => .nonneg ⟨61, by decide⟩
    | 55 => .branchLe ⟨6, by decide⟩ 0
    | 56 => .branchLe ⟨13, by decide⟩ 0
    | 57 => .branchLe ⟨25, by decide⟩ 0
    | 58 => .branchLe ⟨49, by decide⟩ 0
    | 59 => .branchLe ⟨50, by decide⟩ 0
    | 60 => .branchGe ⟨0, by decide⟩ 3
    | 61 => .branchGe ⟨5, by decide⟩ 1
    | 62 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L15 : Fin 63 → Nat
  | i => match i.val with
    | 0 => 2006
    | 1 => 3889
    | 2 => 12950
    | 3 => 12678
    | 4 => 3571
    | 5 => 8359
    | 6 => 7340
    | 7 => 272
    | 8 => 5974
    | 9 => 8111
    | 10 => 1619
    | 11 => 129
    | 12 => 537
    | 13 => 178
    | 14 => 4327
    | 15 => 7065
    | 16 => 4532
    | 17 => 3670
    | 18 => 6700
    | 19 => 2811
    | 20 => 1907
    | 21 => 363
    | 22 => 6760
    | 23 => 5216
    | 24 => 223
    | 25 => 2918
    | 26 => 6262
    | 27 => 5401
    | 28 => 3139
    | 29 => 4716
    | 30 => 1178
    | 31 => 7809
    | 32 => 136
    | 33 => 2675
    | 34 => 361
    | 35 => 657
    | 36 => 1903
    | 37 => 772
    | 38 => 17121
    | 39 => 4007
    | 40 => 9604
    | 41 => 3482
    | 42 => 51
    | 43 => 4922
    | 44 => 9128
    | 45 => 16023
    | 46 => 6945
    | 47 => 3601
    | 48 => 1020
    | 49 => 9637
    | 50 => 2895
    | 51 => 633
    | 52 => 1189
    | 53 => 3942
    | 54 => 7030
    | 55 => 4632
    | 56 => 9671
    | 57 => 9101
    | 58 => 14810
    | 59 => 6979
    | 60 => 31376
    | 61 => 14641
    | 62 => 40270
    | _ => 0

theorem coeff_cancel_416_L15 :
    ∀ j : Fin 63, (∑ i : Fin 63, (mults_416_L15 i : Int) * (refs_416_L15 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L15 :
    (∑ i : Fin 63, (mults_416_L15 i : Int) * (refs_416_L15 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf15_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_50_0 : x ⟨49, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_1_3 : (3 : Int) ≤ x ⟨0, by decide⟩)
    (h_ge_6_1 : (1 : Int) ≤ x ⟨5, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 63,
      (∑ j : Fin 63, (refs_416_L15 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L15 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨150, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨207, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨2, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨153, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨213, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨214, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨215, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨89, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨200, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨176, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨140, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨77, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨216, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨163, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨217, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨218, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨29, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨57, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨61, by decide⟩]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_50_0]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_1_3]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_6_1]
    · simp only [refs_416_L15, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L15) coeff_cancel_416_L15 rhs_neg_416_L15 x hrows

-- leaf 16, path LLLLLRRL, Farkas rhs -13330
def refs_416_L16 : Fin 63 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨219, by decide⟩
    | 1 => .occ ⟨220, by decide⟩
    | 2 => .occ ⟨0, by decide⟩
    | 3 => .occ ⟨64, by decide⟩
    | 4 => .occ ⟨43, by decide⟩
    | 5 => .occ ⟨45, by decide⟩
    | 6 => .occ ⟨221, by decide⟩
    | 7 => .occ ⟨151, by decide⟩
    | 8 => .occ ⟨67, by decide⟩
    | 9 => .occ ⟨68, by decide⟩
    | 10 => .occ ⟨154, by decide⟩
    | 11 => .occ ⟨69, by decide⟩
    | 12 => .occ ⟨4, by decide⟩
    | 13 => .occ ⟨5, by decide⟩
    | 14 => .occ ⟨6, by decide⟩
    | 15 => .occ ⟨191, by decide⟩
    | 16 => .occ ⟨70, by decide⟩
    | 17 => .occ ⟨222, by decide⟩
    | 18 => .occ ⟨7, by decide⟩
    | 19 => .occ ⟨13, by decide⟩
    | 20 => .occ ⟨15, by decide⟩
    | 21 => .occ ⟨50, by decide⟩
    | 22 => .occ ⟨16, by decide⟩
    | 23 => .occ ⟨17, by decide⟩
    | 24 => .occ ⟨155, by decide⟩
    | 25 => .occ ⟨19, by decide⟩
    | 26 => .occ ⟨74, by decide⟩
    | 27 => .occ ⟨223, by decide⟩
    | 28 => .occ ⟨90, by decide⟩
    | 29 => .occ ⟨224, by decide⟩
    | 30 => .occ ⟨160, by decide⟩
    | 31 => .occ ⟨78, by decide⟩
    | 32 => .occ ⟨225, by decide⟩
    | 33 => .occ ⟨29, by decide⟩
    | 34 => .occ ⟨161, by decide⟩
    | 35 => .occ ⟨121, by decide⟩
    | 36 => .occ ⟨178, by decide⟩
    | 37 => .occ ⟨145, by decide⟩
    | 38 => .occ ⟨226, by decide⟩
    | 39 => .occ ⟨171, by decide⟩
    | 40 => .occ ⟨31, by decide⟩
    | 41 => .occ ⟨79, by decide⟩
    | 42 => .occ ⟨63, by decide⟩
    | 43 => .occ ⟨149, by decide⟩
    | 44 => .sumGe
    | 45 => .nonneg ⟨2, by decide⟩
    | 46 => .nonneg ⟨4, by decide⟩
    | 47 => .nonneg ⟨8, by decide⟩
    | 48 => .nonneg ⟨10, by decide⟩
    | 49 => .nonneg ⟨16, by decide⟩
    | 50 => .nonneg ⟨18, by decide⟩
    | 51 => .nonneg ⟨20, by decide⟩
    | 52 => .nonneg ⟨30, by decide⟩
    | 53 => .nonneg ⟨41, by decide⟩
    | 54 => .nonneg ⟨44, by decide⟩
    | 55 => .nonneg ⟨46, by decide⟩
    | 56 => .branchLe ⟨6, by decide⟩ 0
    | 57 => .branchLe ⟨13, by decide⟩ 0
    | 58 => .branchLe ⟨25, by decide⟩ 0
    | 59 => .branchLe ⟨29, by decide⟩ 0
    | 60 => .branchLe ⟨51, by decide⟩ 0
    | 61 => .branchGe ⟨49, by decide⟩ 1
    | 62 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L16 : Fin 63 → Nat
  | i => match i.val with
    | 0 => 386
    | 1 => 1432
    | 2 => 3100
    | 3 => 61
    | 4 => 3369
    | 5 => 7093
    | 6 => 5148
    | 7 => 1331
    | 8 => 2111
    | 9 => 8973
    | 10 => 6923
    | 11 => 2594
    | 12 => 1923
    | 13 => 2209
    | 14 => 675
    | 15 => 558
    | 16 => 1289
    | 17 => 1858
    | 18 => 1529
    | 19 => 1741
    | 20 => 4862
    | 21 => 228
    | 22 => 1741
    | 23 => 1590
    | 24 => 6581
    | 25 => 1894
    | 26 => 7681
    | 27 => 6898
    | 28 => 947
    | 29 => 3216
    | 30 => 2124
    | 31 => 6322
    | 32 => 1503
    | 33 => 497
    | 34 => 1952
    | 35 => 3013
    | 36 => 4370
    | 37 => 1002
    | 38 => 1306
    | 39 => 1923
    | 40 => 2136
    | 41 => 5531
    | 42 => 29
    | 43 => 3197
    | 44 => 15185
    | 45 => 6543
    | 46 => 12334
    | 47 => 648
    | 48 => 10017
    | 49 => 3812
    | 50 => 3328
    | 51 => 11152
    | 52 => 6176
    | 53 => 1471
    | 54 => 5848
    | 55 => 423
    | 56 => 6888
    | 57 => 6691
    | 58 => 9480
    | 59 => 7072
    | 60 => 6215
    | 61 => 58938
    | 62 => 26999
    | _ => 0

theorem coeff_cancel_416_L16 :
    ∀ j : Fin 63, (∑ i : Fin 63, (mults_416_L16 i : Int) * (refs_416_L16 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L16 :
    (∑ i : Fin 63, (mults_416_L16 i : Int) * (refs_416_L16 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf16_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_ge_50_1 : (1 : Int) ≤ x ⟨49, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 63,
      (∑ j : Fin 63, (refs_416_L16 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L16 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨219, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨221, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨151, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨67, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨68, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨154, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨69, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨191, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨70, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨222, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨74, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨223, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨90, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨224, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨78, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨225, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨121, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨145, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨226, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨46, by decide⟩]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_26_0]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_50_1]
    · simp only [refs_416_L16, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L16) coeff_cancel_416_L16 rhs_neg_416_L16 x hrows

-- leaf 17, path LLLLLRRR, Farkas rhs -7594
def refs_416_L17 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨172, by decide⟩
    | 1 => .occ ⟨1, by decide⟩
    | 2 => .occ ⟨45, by decide⟩
    | 3 => .occ ⟨66, by decide⟩
    | 4 => .occ ⟨227, by decide⟩
    | 5 => .occ ⟨228, by decide⟩
    | 6 => .occ ⟨151, by decide⟩
    | 7 => .occ ⟨131, by decide⟩
    | 8 => .occ ⟨68, by decide⟩
    | 9 => .occ ⟨180, by decide⟩
    | 10 => .occ ⟨154, by decide⟩
    | 11 => .occ ⟨69, by decide⟩
    | 12 => .occ ⟨5, by decide⟩
    | 13 => .occ ⟨70, by decide⟩
    | 14 => .occ ⟨49, by decide⟩
    | 15 => .occ ⟨15, by decide⟩
    | 16 => .occ ⟨50, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨155, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨229, by decide⟩
    | 21 => .occ ⟨74, by decide⟩
    | 22 => .occ ⟨230, by decide⟩
    | 23 => .occ ⟨223, by decide⟩
    | 24 => .occ ⟨231, by decide⟩
    | 25 => .occ ⟨232, by decide⟩
    | 26 => .occ ⟨76, by decide⟩
    | 27 => .occ ⟨224, by decide⟩
    | 28 => .occ ⟨200, by decide⟩
    | 29 => .occ ⟨160, by decide⟩
    | 30 => .occ ⟨181, by decide⟩
    | 31 => .occ ⟨78, by decide⟩
    | 32 => .occ ⟨225, by decide⟩
    | 33 => .occ ⟨161, by decide⟩
    | 34 => .occ ⟨182, by decide⟩
    | 35 => .occ ⟨183, by decide⟩
    | 36 => .occ ⟨178, by decide⟩
    | 37 => .occ ⟨145, by decide⟩
    | 38 => .occ ⟨202, by decide⟩
    | 39 => .occ ⟨79, by decide⟩
    | 40 => .occ ⟨233, by decide⟩
    | 41 => .occ ⟨217, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨4, by decide⟩
    | 45 => .nonneg ⟨8, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨19, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨33, by decide⟩
    | 52 => .nonneg ⟨39, by decide⟩
    | 53 => .nonneg ⟨44, by decide⟩
    | 54 => .nonneg ⟨46, by decide⟩
    | 55 => .nonneg ⟨56, by decide⟩
    | 56 => .nonneg ⟨60, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨13, by decide⟩ 0
    | 59 => .branchLe ⟨29, by decide⟩ 0
    | 60 => .branchLe ⟨50, by decide⟩ 0
    | 61 => .branchGe ⟨49, by decide⟩ 1
    | 62 => .branchGe ⟨51, by decide⟩ 1
    | 63 => .branchGe ⟨54, by decide⟩ 1
    | _ => .sumGe

def mults_416_L17 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 291
    | 1 => 3768
    | 2 => 570
    | 3 => 2715
    | 4 => 686
    | 5 => 533
    | 6 => 1521
    | 7 => 937
    | 8 => 4052
    | 9 => 1567
    | 10 => 589
    | 11 => 152
    | 12 => 875
    | 13 => 165
    | 14 => 333
    | 15 => 1443
    | 16 => 353
    | 17 => 812
    | 18 => 2184
    | 19 => 631
    | 20 => 338
    | 21 => 3720
    | 22 => 57
    | 23 => 1152
    | 24 => 459
    | 25 => 1506
    | 26 => 1145
    | 27 => 637
    | 28 => 8
    | 29 => 1214
    | 30 => 306
    | 31 => 2852
    | 32 => 514
    | 33 => 568
    | 34 => 408
    | 35 => 1498
    | 36 => 3713
    | 37 => 1354
    | 38 => 298
    | 39 => 1031
    | 40 => 339
    | 41 => 1214
    | 42 => 5564
    | 43 => 3967
    | 44 => 5409
    | 45 => 361
    | 46 => 4865
    | 47 => 2399
    | 48 => 503
    | 49 => 1862
    | 50 => 5755
    | 51 => 2968
    | 52 => 1431
    | 53 => 4840
    | 54 => 1796
    | 55 => 1680
    | 56 => 576
    | 57 => 2317
    | 58 => 2852
    | 59 => 1652
    | 60 => 1981
    | 61 => 21288
    | 62 => 10760
    | 63 => 14058
    | _ => 0

theorem coeff_cancel_416_L17 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L17 i : Int) * (refs_416_L17 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L17 :
    (∑ i : Fin 64, (mults_416_L17 i : Int) * (refs_416_L17 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf17_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_26_0 : x ⟨25, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_50_1 : (1 : Int) ≤ x ⟨49, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_55_1 : (1 : Int) ≤ x ⟨54, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L17 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L17 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨172, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨66, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨227, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨228, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨151, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨68, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨180, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨154, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨69, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨70, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨229, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨74, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨230, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨223, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨231, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨232, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨224, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨200, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨181, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨78, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨225, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨161, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨182, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨183, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨145, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨202, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨233, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨217, by decide⟩
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨46, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨60, by decide⟩]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_50_1]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L17, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_55_1]
  exact farkas_leaf_unsat _ _ (mults_416_L17) coeff_cancel_416_L17 rhs_neg_416_L17 x hrows

-- leaf 18, path LLLLR, Farkas rhs -40
def refs_416_L18 : Fin 53 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨234, by decide⟩
    | 1 => .occ ⟨235, by decide⟩
    | 2 => .occ ⟨236, by decide⟩
    | 3 => .occ ⟨65, by decide⟩
    | 4 => .occ ⟨1, by decide⟩
    | 5 => .occ ⟨44, by decide⟩
    | 6 => .occ ⟨46, by decide⟩
    | 7 => .occ ⟨130, by decide⟩
    | 8 => .occ ⟨6, by decide⟩
    | 9 => .occ ⟨237, by decide⟩
    | 10 => .occ ⟨238, by decide⟩
    | 11 => .occ ⟨8, by decide⟩
    | 12 => .occ ⟨101, by decide⟩
    | 13 => .occ ⟨17, by decide⟩
    | 14 => .occ ⟨239, by decide⟩
    | 15 => .occ ⟨240, by decide⟩
    | 16 => .occ ⟨137, by decide⟩
    | 17 => .occ ⟨158, by decide⟩
    | 18 => .occ ⟨241, by decide⟩
    | 19 => .occ ⟨159, by decide⟩
    | 20 => .occ ⟨242, by decide⟩
    | 21 => .occ ⟨243, by decide⟩
    | 22 => .occ ⟨244, by decide⟩
    | 23 => .occ ⟨245, by decide⟩
    | 24 => .occ ⟨246, by decide⟩
    | 25 => .occ ⟨247, by decide⟩
    | 26 => .occ ⟨91, by decide⟩
    | 27 => .occ ⟨202, by decide⟩
    | 28 => .occ ⟨170, by decide⟩
    | 29 => .occ ⟨107, by decide⟩
    | 30 => .occ ⟨108, by decide⟩
    | 31 => .occ ⟨122, by decide⟩
    | 32 => .occ ⟨33, by decide⟩
    | 33 => .occ ⟨218, by decide⟩
    | 34 => .occ ⟨38, by decide⟩
    | 35 => .occ ⟨125, by decide⟩
    | 36 => .occ ⟨39, by decide⟩
    | 37 => .occ ⟨41, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨4, by decide⟩
    | 41 => .nonneg ⟨7, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨15, by decide⟩
    | 44 => .nonneg ⟨16, by decide⟩
    | 45 => .nonneg ⟨18, by decide⟩
    | 46 => .nonneg ⟨20, by decide⟩
    | 47 => .nonneg ⟨42, by decide⟩
    | 48 => .nonneg ⟨44, by decide⟩
    | 49 => .branchLe ⟨13, by decide⟩ 0
    | 50 => .branchLe ⟨29, by decide⟩ 0
    | 51 => .branchLe ⟨50, by decide⟩ 0
    | 52 => .branchGe ⟨25, by decide⟩ 1
    | _ => .sumGe

def mults_416_L18 : Fin 53 → Nat
  | i => match i.val with
    | 0 => 35
    | 1 => 55
    | 2 => 85
    | 3 => 20
    | 4 => 30
    | 5 => 20
    | 6 => 10
    | 7 => 10
    | 8 => 30
    | 9 => 10
    | 10 => 13
    | 11 => 40
    | 12 => 10
    | 13 => 10
    | 14 => 28
    | 15 => 2
    | 16 => 20
    | 17 => 31
    | 18 => 17
    | 19 => 16
    | 20 => 19
    | 21 => 12
    | 22 => 29
    | 23 => 13
    | 24 => 14
    | 25 => 6
    | 26 => 20
    | 27 => 2
    | 28 => 10
    | 29 => 10
    | 30 => 30
    | 31 => 25
    | 32 => 3
    | 33 => 5
    | 34 => 10
    | 35 => 12
    | 36 => 25
    | 37 => 13
    | 38 => 100
    | 39 => 10
    | 40 => 10
    | 41 => 20
    | 42 => 20
    | 43 => 10
    | 44 => 20
    | 45 => 20
    | 46 => 20
    | 47 => 10
    | 48 => 60
    | 49 => 90
    | 50 => 60
    | 51 => 90
    | 52 => 450
    | _ => 0

theorem coeff_cancel_416_L18 :
    ∀ j : Fin 63, (∑ i : Fin 53, (mults_416_L18 i : Int) * (refs_416_L18 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L18 :
    (∑ i : Fin 53, (mults_416_L18 i : Int) * (refs_416_L18 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf18_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_le_51_0 : x ⟨50, by decide⟩ ≤ 0)
    (h_ge_26_1 : (1 : Int) ≤ x ⟨25, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 53,
      (∑ j : Fin 63, (refs_416_L18 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L18 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨234, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨236, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨65, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨130, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨237, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨238, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨239, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨240, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨137, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨158, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨241, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨159, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨242, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨243, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨244, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨245, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨246, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨247, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨202, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨170, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨122, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨218, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨38, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨125, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨15, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_51_0]
    · simp only [refs_416_L18, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_26_1]
  exact farkas_leaf_unsat _ _ (mults_416_L18) coeff_cancel_416_L18 rhs_neg_416_L18 x hrows

-- leaf 19, path LLLR, Farkas rhs -25
def refs_416_L19 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨248, by decide⟩
    | 1 => .occ ⟨112, by decide⟩
    | 2 => .occ ⟨249, by decide⟩
    | 3 => .occ ⟨250, by decide⟩
    | 4 => .occ ⟨97, by decide⟩
    | 5 => .occ ⟨251, by decide⟩
    | 6 => .occ ⟨132, by decide⟩
    | 7 => .occ ⟨4, by decide⟩
    | 8 => .occ ⟨5, by decide⟩
    | 9 => .occ ⟨6, by decide⟩
    | 10 => .occ ⟨222, by decide⟩
    | 11 => .occ ⟨7, by decide⟩
    | 12 => .occ ⟨8, by decide⟩
    | 13 => .occ ⟨100, by decide⟩
    | 14 => .occ ⟨14, by decide⟩
    | 15 => .occ ⟨15, by decide⟩
    | 16 => .occ ⟨50, by decide⟩
    | 17 => .occ ⟨16, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨72, by decide⟩
    | 21 => .occ ⟨192, by decide⟩
    | 22 => .occ ⟨252, by decide⟩
    | 23 => .occ ⟨253, by decide⟩
    | 24 => .occ ⟨254, by decide⟩
    | 25 => .occ ⟨255, by decide⟩
    | 26 => .occ ⟨160, by decide⟩
    | 27 => .occ ⟨141, by decide⟩
    | 28 => .occ ⟨142, by decide⟩
    | 29 => .occ ⟨179, by decide⟩
    | 30 => .occ ⟨184, by decide⟩
    | 31 => .occ ⟨171, by decide⟩
    | 32 => .occ ⟨31, by decide⟩
    | 33 => .occ ⟨256, by decide⟩
    | 34 => .occ ⟨93, by decide⟩
    | 35 => .occ ⟨257, by decide⟩
    | 36 => .occ ⟨63, by decide⟩
    | 37 => .occ ⟨39, by decide⟩
    | 38 => .occ ⟨126, by decide⟩
    | 39 => .sumGe
    | 40 => .nonneg ⟨2, by decide⟩
    | 41 => .nonneg ⟨4, by decide⟩
    | 42 => .nonneg ⟨8, by decide⟩
    | 43 => .nonneg ⟨10, by decide⟩
    | 44 => .nonneg ⟨12, by decide⟩
    | 45 => .nonneg ⟨14, by decide⟩
    | 46 => .nonneg ⟨15, by decide⟩
    | 47 => .nonneg ⟨16, by decide⟩
    | 48 => .nonneg ⟨18, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨31, by decide⟩
    | 52 => .nonneg ⟨33, by decide⟩
    | 53 => .nonneg ⟨39, by decide⟩
    | 54 => .nonneg ⟨40, by decide⟩
    | 55 => .nonneg ⟨41, by decide⟩
    | 56 => .nonneg ⟨42, by decide⟩
    | 57 => .nonneg ⟨43, by decide⟩
    | 58 => .nonneg ⟨45, by decide⟩
    | 59 => .nonneg ⟨55, by decide⟩
    | 60 => .branchLe ⟨6, by decide⟩ 0
    | 61 => .branchLe ⟨13, by decide⟩ 0
    | 62 => .branchLe ⟨29, by decide⟩ 0
    | 63 => .branchGe ⟨50, by decide⟩ 1
    | _ => .sumGe

def mults_416_L19 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 458
    | 1 => 228
    | 2 => 81
    | 3 => 434
    | 4 => 441
    | 5 => 270
    | 6 => 273
    | 7 => 196
    | 8 => 208
    | 9 => 76
    | 10 => 83
    | 11 => 162
    | 12 => 242
    | 13 => 8
    | 14 => 4
    | 15 => 132
    | 16 => 584
    | 17 => 238
    | 18 => 148
    | 19 => 344
    | 20 => 128
    | 21 => 63
    | 22 => 262
    | 23 => 115
    | 24 => 218
    | 25 => 247
    | 26 => 108
    | 27 => 65
    | 28 => 6
    | 29 => 83
    | 30 => 49
    | 31 => 79
    | 32 => 72
    | 33 => 213
    | 34 => 6
    | 35 => 25
    | 36 => 68
    | 37 => 148
    | 38 => 155
    | 39 => 696
    | 40 => 654
    | 41 => 152
    | 42 => 122
    | 43 => 508
    | 44 => 142
    | 45 => 462
    | 46 => 280
    | 47 => 9
    | 48 => 887
    | 49 => 680
    | 50 => 798
    | 51 => 1075
    | 52 => 51
    | 53 => 462
    | 54 => 144
    | 55 => 72
    | 56 => 416
    | 57 => 464
    | 58 => 54
    | 59 => 80
    | 60 => 492
    | 61 => 220
    | 62 => 628
    | 63 => 3232
    | _ => 0

theorem coeff_cancel_416_L19 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L19 i : Int) * (refs_416_L19 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L19 :
    (∑ i : Fin 64, (mults_416_L19 i : Int) * (refs_416_L19 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf19_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_le_30_0 : x ⟨29, by decide⟩ ≤ 0)
    (h_ge_51_1 : (1 : Int) ≤ x ⟨50, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L19 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L19 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨249, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨250, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨97, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨251, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨132, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨222, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨100, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨72, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨192, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨252, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨253, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨254, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨255, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨141, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨179, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨184, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨93, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨257, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨39, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨15, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨45, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_30_0]
    · simp only [refs_416_L19, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_51_1]
  exact farkas_leaf_unsat _ _ (mults_416_L19) coeff_cancel_416_L19 rhs_neg_416_L19 x hrows

-- leaf 20, path LLR, Farkas rhs -14
def refs_416_L20 : Fin 55 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨235, by decide⟩
    | 1 => .occ ⟨188, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨94, by decide⟩
    | 4 => .occ ⟨166, by decide⟩
    | 5 => .occ ⟨4, by decide⟩
    | 6 => .occ ⟨5, by decide⟩
    | 7 => .occ ⟨6, by decide⟩
    | 8 => .occ ⟨49, by decide⟩
    | 9 => .occ ⟨258, by decide⟩
    | 10 => .occ ⟨9, by decide⟩
    | 11 => .occ ⟨10, by decide⟩
    | 12 => .occ ⟨11, by decide⟩
    | 13 => .occ ⟨259, by decide⟩
    | 14 => .occ ⟨15, by decide⟩
    | 15 => .occ ⟨50, by decide⟩
    | 16 => .occ ⟨16, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨155, by decide⟩
    | 19 => .occ ⟨19, by decide⟩
    | 20 => .occ ⟨20, by decide⟩
    | 21 => .occ ⟨260, by decide⟩
    | 22 => .occ ⟨261, by decide⟩
    | 23 => .occ ⟨25, by decide⟩
    | 24 => .occ ⟨77, by decide⟩
    | 25 => .occ ⟨262, by decide⟩
    | 26 => .occ ⟨55, by decide⟩
    | 27 => .occ ⟨27, by decide⟩
    | 28 => .occ ⟨142, by decide⟩
    | 29 => .occ ⟨263, by decide⟩
    | 30 => .occ ⟨29, by decide⟩
    | 31 => .occ ⟨144, by decide⟩
    | 32 => .occ ⟨264, by decide⟩
    | 33 => .occ ⟨32, by decide⟩
    | 34 => .occ ⟨265, by decide⟩
    | 35 => .occ ⟨125, by decide⟩
    | 36 => .occ ⟨63, by decide⟩
    | 37 => .occ ⟨41, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨8, by decide⟩
    | 41 => .nonneg ⟨10, by decide⟩
    | 42 => .nonneg ⟨16, by decide⟩
    | 43 => .nonneg ⟨18, by decide⟩
    | 44 => .nonneg ⟨22, by decide⟩
    | 45 => .nonneg ⟨27, by decide⟩
    | 46 => .nonneg ⟨30, by decide⟩
    | 47 => .nonneg ⟨33, by decide⟩
    | 48 => .nonneg ⟨34, by decide⟩
    | 49 => .nonneg ⟨41, by decide⟩
    | 50 => .nonneg ⟨42, by decide⟩
    | 51 => .nonneg ⟨59, by decide⟩
    | 52 => .branchLe ⟨6, by decide⟩ 0
    | 53 => .branchLe ⟨13, by decide⟩ 0
    | 54 => .branchGe ⟨29, by decide⟩ 1
    | _ => .sumGe

def mults_416_L20 : Fin 55 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 30
    | 2 => 12
    | 3 => 44
    | 4 => 30
    | 5 => 6
    | 6 => 14
    | 7 => 6
    | 8 => 2
    | 9 => 22
    | 10 => 6
    | 11 => 8
    | 12 => 8
    | 13 => 10
    | 14 => 11
    | 15 => 11
    | 16 => 3
    | 17 => 3
    | 18 => 14
    | 19 => 18
    | 20 => 18
    | 21 => 2
    | 22 => 2
    | 23 => 8
    | 24 => 6
    | 25 => 2
    | 26 => 20
    | 27 => 20
    | 28 => 9
    | 29 => 8
    | 30 => 9
    | 31 => 8
    | 32 => 7
    | 33 => 7
    | 34 => 12
    | 35 => 10
    | 36 => 15
    | 37 => 15
    | 38 => 68
    | 39 => 38
    | 40 => 88
    | 41 => 40
    | 42 => 16
    | 43 => 16
    | 44 => 28
    | 45 => 14
    | 46 => 2
    | 47 => 34
    | 48 => 20
    | 49 => 8
    | 50 => 8
    | 51 => 14
    | 52 => 36
    | 53 => 68
    | 54 => 206
    | _ => 0

theorem coeff_cancel_416_L20 :
    ∀ j : Fin 63, (∑ i : Fin 55, (mults_416_L20 i : Int) * (refs_416_L20 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L20 :
    (∑ i : Fin 55, (mults_416_L20 i : Int) * (refs_416_L20 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf20_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_14_0 : x ⟨13, by decide⟩ ≤ 0)
    (h_ge_30_1 : (1 : Int) ≤ x ⟨29, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 55,
      (∑ j : Fin 63, (refs_416_L20 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L20 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨188, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨258, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨9, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨259, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨260, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨261, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨77, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨262, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨263, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨144, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨264, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨32, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨265, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨125, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_14_0]
    · simp only [refs_416_L20, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_30_1]
  exact farkas_leaf_unsat _ _ (mults_416_L20) coeff_cancel_416_L20 rhs_neg_416_L20 x hrows

-- leaf 21, path LRLLLLL, Farkas rhs -2039
def refs_416_L21 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨165, by decide⟩
    | 2 => .occ ⟨94, by decide⟩
    | 3 => .occ ⟨95, by decide⟩
    | 4 => .occ ⟨266, by decide⟩
    | 5 => .occ ⟨4, by decide⟩
    | 6 => .occ ⟨6, by decide⟩
    | 7 => .occ ⟨267, by decide⟩
    | 8 => .occ ⟨8, by decide⟩
    | 9 => .occ ⟨10, by decide⟩
    | 10 => .occ ⟨12, by decide⟩
    | 11 => .occ ⟨13, by decide⟩
    | 12 => .occ ⟨101, by decide⟩
    | 13 => .occ ⟨15, by decide⟩
    | 14 => .occ ⟨50, by decide⟩
    | 15 => .occ ⟨155, by decide⟩
    | 16 => .occ ⟨19, by decide⟩
    | 17 => .occ ⟨20, by decide⟩
    | 18 => .occ ⟨268, by decide⟩
    | 19 => .occ ⟨21, by decide⟩
    | 20 => .occ ⟨269, by decide⟩
    | 21 => .occ ⟨270, by decide⟩
    | 22 => .occ ⟨271, by decide⟩
    | 23 => .occ ⟨106, by decide⟩
    | 24 => .occ ⟨27, by decide⟩
    | 25 => .occ ⟨272, by decide⟩
    | 26 => .occ ⟨30, by decide⟩
    | 27 => .occ ⟨171, by decide⟩
    | 28 => .occ ⟨273, by decide⟩
    | 29 => .occ ⟨256, by decide⟩
    | 30 => .occ ⟨33, by decide⟩
    | 31 => .occ ⟨274, by decide⟩
    | 32 => .occ ⟨275, by decide⟩
    | 33 => .occ ⟨211, by decide⟩
    | 34 => .occ ⟨218, by decide⟩
    | 35 => .occ ⟨80, by decide⟩
    | 36 => .occ ⟨149, by decide⟩
    | 37 => .sumGe
    | 38 => .nonneg ⟨2, by decide⟩
    | 39 => .nonneg ⟨4, by decide⟩
    | 40 => .nonneg ⟨7, by decide⟩
    | 41 => .nonneg ⟨8, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨12, by decide⟩
    | 44 => .nonneg ⟨16, by decide⟩
    | 45 => .nonneg ⟨18, by decide⟩
    | 46 => .nonneg ⟨19, by decide⟩
    | 47 => .nonneg ⟨20, by decide⟩
    | 48 => .nonneg ⟨24, by decide⟩
    | 49 => .nonneg ⟨26, by decide⟩
    | 50 => .nonneg ⟨30, by decide⟩
    | 51 => .nonneg ⟨31, by decide⟩
    | 52 => .nonneg ⟨32, by decide⟩
    | 53 => .nonneg ⟨34, by decide⟩
    | 54 => .nonneg ⟨39, by decide⟩
    | 55 => .nonneg ⟨44, by decide⟩
    | 56 => .nonneg ⟨54, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨17, by decide⟩ 0
    | 59 => .branchLe ⟨36, by decide⟩ 0
    | 60 => .branchLe ⟨46, by decide⟩ 0
    | 61 => .branchLe ⟨57, by decide⟩ 0
    | 62 => .branchLe ⟨58, by decide⟩ 0
    | 63 => .branchGe ⟨13, by decide⟩ 1
    | _ => .sumGe

def mults_416_L21 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 212
    | 1 => 2226
    | 2 => 1687
    | 3 => 183
    | 4 => 82
    | 5 => 2531
    | 6 => 2112
    | 7 => 1535
    | 8 => 1812
    | 9 => 2933
    | 10 => 3934
    | 11 => 2830
    | 12 => 2362
    | 13 => 3131
    | 14 => 2638
    | 15 => 831
    | 16 => 1987
    | 17 => 3720
    | 18 => 2210
    | 19 => 557
    | 20 => 311
    | 21 => 887
    | 22 => 882
    | 23 => 300
    | 24 => 494
    | 25 => 111
    | 26 => 389
    | 27 => 195
    | 28 => 946
    | 29 => 1603
    | 30 => 605
    | 31 => 201
    | 32 => 1207
    | 33 => 730
    | 34 => 498
    | 35 => 1707
    | 36 => 1233
    | 37 => 6976
    | 38 => 3302
    | 39 => 3441
    | 40 => 2860
    | 41 => 55
    | 42 => 2491
    | 43 => 4183
    | 44 => 4888
    | 45 => 10943
    | 46 => 438
    | 47 => 3138
    | 48 => 105
    | 49 => 1668
    | 50 => 9542
    | 51 => 4460
    | 52 => 2491
    | 53 => 3507
    | 54 => 738
    | 55 => 2871
    | 56 => 102
    | 57 => 3238
    | 58 => 4640
    | 59 => 6976
    | 60 => 3477
    | 61 => 6976
    | 62 => 4036
    | 63 => 10516
    | _ => 0

theorem coeff_cancel_416_L21 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L21 i : Int) * (refs_416_L21 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L21 :
    (∑ i : Fin 64, (mults_416_L21 i : Int) * (refs_416_L21 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf21_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_37_0 : x ⟨36, by decide⟩ ≤ 0)
    (h_le_47_0 : x ⟨46, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_le_59_0 : x ⟨58, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L21 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L21 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨95, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨266, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨267, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨268, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨269, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨270, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨271, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨272, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨273, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨274, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨275, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨218, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨54, by decide⟩]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_37_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_47_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_59_0]
    · simp only [refs_416_L21, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
  exact farkas_leaf_unsat _ _ (mults_416_L21) coeff_cancel_416_L21 rhs_neg_416_L21 x hrows

-- leaf 22, path LRLLLLR, Farkas rhs -1411
def refs_416_L22 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨42, by decide⟩
    | 1 => .occ ⟨81, by decide⟩
    | 2 => .occ ⟨235, by decide⟩
    | 3 => .occ ⟨165, by decide⟩
    | 4 => .occ ⟨166, by decide⟩
    | 5 => .occ ⟨276, by decide⟩
    | 6 => .occ ⟨130, by decide⟩
    | 7 => .occ ⟨5, by decide⟩
    | 8 => .occ ⟨87, by decide⟩
    | 9 => .occ ⟨8, by decide⟩
    | 10 => .occ ⟨258, by decide⟩
    | 11 => .occ ⟨10, by decide⟩
    | 12 => .occ ⟨12, by decide⟩
    | 13 => .occ ⟨13, by decide⟩
    | 14 => .occ ⟨101, by decide⟩
    | 15 => .occ ⟨15, by decide⟩
    | 16 => .occ ⟨50, by decide⟩
    | 17 => .occ ⟨155, by decide⟩
    | 18 => .occ ⟨18, by decide⟩
    | 19 => .occ ⟨19, by decide⟩
    | 20 => .occ ⟨20, by decide⟩
    | 21 => .occ ⟨277, by decide⟩
    | 22 => .occ ⟨241, by decide⟩
    | 23 => .occ ⟨260, by decide⟩
    | 24 => .occ ⟨106, by decide⟩
    | 25 => .occ ⟨55, by decide⟩
    | 26 => .occ ⟨183, by decide⟩
    | 27 => .occ ⟨30, by decide⟩
    | 28 => .occ ⟨57, by decide⟩
    | 29 => .occ ⟨170, by decide⟩
    | 30 => .occ ⟨107, by decide⟩
    | 31 => .occ ⟨31, by decide⟩
    | 32 => .occ ⟨34, by decide⟩
    | 33 => .occ ⟨35, by decide⟩
    | 34 => .occ ⟨278, by decide⟩
    | 35 => .occ ⟨62, by decide⟩
    | 36 => .occ ⟨279, by decide⟩
    | 37 => .occ ⟨126, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨7, by decide⟩
    | 41 => .nonneg ⟨8, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨19, by decide⟩
    | 46 => .nonneg ⟨20, by decide⟩
    | 47 => .nonneg ⟨25, by decide⟩
    | 48 => .nonneg ⟨26, by decide⟩
    | 49 => .nonneg ⟨30, by decide⟩
    | 50 => .nonneg ⟨31, by decide⟩
    | 51 => .nonneg ⟨32, by decide⟩
    | 52 => .nonneg ⟨33, by decide⟩
    | 53 => .nonneg ⟨40, by decide⟩
    | 54 => .nonneg ⟨44, by decide⟩
    | 55 => .nonneg ⟨50, by decide⟩
    | 56 => .nonneg ⟨56, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨17, by decide⟩ 0
    | 59 => .branchLe ⟨46, by decide⟩ 0
    | 60 => .branchLe ⟨57, by decide⟩ 0
    | 61 => .branchLe ⟨58, by decide⟩ 0
    | 62 => .branchGe ⟨13, by decide⟩ 1
    | 63 => .branchGe ⟨36, by decide⟩ 1
    | _ => .sumGe

def mults_416_L22 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1822
    | 1 => 8340
    | 2 => 5906
    | 3 => 9790
    | 4 => 4858
    | 5 => 6108
    | 6 => 1184
    | 7 => 12658
    | 8 => 7989
    | 9 => 5297
    | 10 => 3430
    | 11 => 4513
    | 12 => 14065
    | 13 => 4188
    | 14 => 1232
    | 15 => 4549
    | 16 => 12357
    | 17 => 4143
    | 18 => 1809
    | 19 => 16592
    | 20 => 4512
    | 21 => 15646
    | 22 => 3656
    | 23 => 1319
    | 24 => 2103
    | 25 => 2137
    | 26 => 46
    | 27 => 1035
    | 28 => 2983
    | 29 => 2186
    | 30 => 10844
    | 31 => 4537
    | 32 => 1789
    | 33 => 4209
    | 34 => 3125
    | 35 => 3794
    | 36 => 1549
    | 37 => 9052
    | 38 => 26242
    | 39 => 13784
    | 40 => 13890
    | 41 => 8788
    | 42 => 30962
    | 43 => 25882
    | 44 => 30236
    | 45 => 3914
    | 46 => 23486
    | 47 => 15732
    | 48 => 4856
    | 49 => 37506
    | 50 => 714
    | 51 => 3968
    | 52 => 2288
    | 53 => 12398
    | 54 => 84
    | 55 => 5738
    | 56 => 656
    | 57 => 12516
    | 58 => 22510
    | 59 => 21188
    | 60 => 13806
    | 61 => 26242
    | 62 => 45348
    | 63 => 23498
    | _ => 0

theorem coeff_cancel_416_L22 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L22 i : Int) * (refs_416_L22 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L22 :
    (∑ i : Fin 64, (mults_416_L22 i : Int) * (refs_416_L22 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf22_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_47_0 : x ⟨46, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_le_59_0 : x ⟨58, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_37_1 : (1 : Int) ≤ x ⟨36, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L22 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L22 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨276, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨130, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨258, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨277, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨241, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨260, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨183, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨170, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨31, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨278, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨50, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_47_0]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_59_0]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L22, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_37_1]
  exact farkas_leaf_unsat _ _ (mults_416_L22) coeff_cancel_416_L22 rhs_neg_416_L22 x hrows

-- leaf 23, path LRLLLR, Farkas rhs -2742
def refs_416_L23 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨235, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨111, by decide⟩
    | 4 => .occ ⟨44, by decide⟩
    | 5 => .occ ⟨166, by decide⟩
    | 6 => .occ ⟨112, by decide⟩
    | 7 => .occ ⟨129, by decide⟩
    | 8 => .occ ⟨85, by decide⟩
    | 9 => .occ ⟨280, by decide⟩
    | 10 => .occ ⟨281, by decide⟩
    | 11 => .occ ⟨5, by decide⟩
    | 12 => .occ ⟨6, by decide⟩
    | 13 => .occ ⟨282, by decide⟩
    | 14 => .occ ⟨134, by decide⟩
    | 15 => .occ ⟨87, by decide⟩
    | 16 => .occ ⟨8, by decide⟩
    | 17 => .occ ⟨258, by decide⟩
    | 18 => .occ ⟨10, by decide⟩
    | 19 => .occ ⟨12, by decide⟩
    | 20 => .occ ⟨101, by decide⟩
    | 21 => .occ ⟨118, by decide⟩
    | 22 => .occ ⟨15, by decide⟩
    | 23 => .occ ⟨50, by decide⟩
    | 24 => .occ ⟨16, by decide⟩
    | 25 => .occ ⟨18, by decide⟩
    | 26 => .occ ⟨19, by decide⟩
    | 27 => .occ ⟨20, by decide⟩
    | 28 => .occ ⟨138, by decide⟩
    | 29 => .occ ⟨283, by decide⟩
    | 30 => .occ ⟨284, by decide⟩
    | 31 => .occ ⟨285, by decide⟩
    | 32 => .occ ⟨139, by decide⟩
    | 33 => .occ ⟨91, by decide⟩
    | 34 => .occ ⟨143, by decide⟩
    | 35 => .occ ⟨170, by decide⟩
    | 36 => .occ ⟨171, by decide⟩
    | 37 => .occ ⟨211, by decide⟩
    | 38 => .occ ⟨286, by decide⟩
    | 39 => .occ ⟨287, by decide⟩
    | 40 => .occ ⟨80, by decide⟩
    | 41 => .occ ⟨279, by decide⟩
    | 42 => .occ ⟨40, by decide⟩
    | 43 => .sumGe
    | 44 => .nonneg ⟨4, by decide⟩
    | 45 => .nonneg ⟨7, by decide⟩
    | 46 => .nonneg ⟨8, by decide⟩
    | 47 => .nonneg ⟨10, by decide⟩
    | 48 => .nonneg ⟨16, by decide⟩
    | 49 => .nonneg ⟨18, by decide⟩
    | 50 => .nonneg ⟨22, by decide⟩
    | 51 => .nonneg ⟨25, by decide⟩
    | 52 => .nonneg ⟨26, by decide⟩
    | 53 => .nonneg ⟨30, by decide⟩
    | 54 => .nonneg ⟨31, by decide⟩
    | 55 => .nonneg ⟨32, by decide⟩
    | 56 => .nonneg ⟨43, by decide⟩
    | 57 => .nonneg ⟨59, by decide⟩
    | 58 => .branchLe ⟨6, by decide⟩ 0
    | 59 => .branchLe ⟨17, by decide⟩ 0
    | 60 => .branchLe ⟨57, by decide⟩ 0
    | 61 => .branchLe ⟨58, by decide⟩ 0
    | 62 => .branchGe ⟨13, by decide⟩ 1
    | 63 => .branchGe ⟨46, by decide⟩ 1
    | _ => .sumGe

def mults_416_L23 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 2480
    | 1 => 1338
    | 2 => 823
    | 3 => 180
    | 4 => 399
    | 5 => 1488
    | 6 => 4069
    | 7 => 2922
    | 8 => 1513
    | 9 => 1061
    | 10 => 2217
    | 11 => 1611
    | 12 => 1004
    | 13 => 79
    | 14 => 825
    | 15 => 565
    | 16 => 974
    | 17 => 347
    | 18 => 687
    | 19 => 485
    | 20 => 59
    | 21 => 41
    | 22 => 726
    | 23 => 293
    | 24 => 186
    | 25 => 1112
    | 26 => 811
    | 27 => 1013
    | 28 => 122
    | 29 => 1037
    | 30 => 1053
    | 31 => 247
    | 32 => 52
    | 33 => 192
    | 34 => 454
    | 35 => 1079
    | 36 => 615
    | 37 => 1072
    | 38 => 591
    | 39 => 392
    | 40 => 1241
    | 41 => 567
    | 42 => 972
    | 43 => 4502
    | 44 => 658
    | 45 => 4808
    | 46 => 1315
    | 47 => 2059
    | 48 => 654
    | 49 => 4182
    | 50 => 2067
    | 51 => 1841
    | 52 => 56
    | 53 => 3456
    | 54 => 1186
    | 55 => 1129
    | 56 => 724
    | 57 => 388
    | 58 => 2240
    | 59 => 3158
    | 60 => 2323
    | 61 => 3261
    | 62 => 5060
    | 63 => 14379
    | _ => 0

theorem coeff_cancel_416_L23 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L23 i : Int) * (refs_416_L23 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L23 :
    (∑ i : Fin 64, (mults_416_L23 i : Int) * (refs_416_L23 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf23_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_le_59_0 : x ⟨58, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_47_1 : (1 : Int) ≤ x ⟨46, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L23 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L23 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨280, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨281, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨282, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨134, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨258, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨138, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨283, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨284, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨285, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨139, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨143, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨170, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨286, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨287, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_59_0]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L23, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_47_1]
  exact farkas_leaf_unsat _ _ (mults_416_L23) coeff_cancel_416_L23 rhs_neg_416_L23 x hrows

-- leaf 24, path LRLLRLLL, Farkas rhs -268
def refs_416_L24 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨166, by decide⟩
    | 1 => .occ ⟨248, by decide⟩
    | 2 => .occ ⟨112, by decide⟩
    | 3 => .occ ⟨288, by decide⟩
    | 4 => .occ ⟨289, by decide⟩
    | 5 => .occ ⟨3, by decide⟩
    | 6 => .occ ⟨4, by decide⟩
    | 7 => .occ ⟨5, by decide⟩
    | 8 => .occ ⟨87, by decide⟩
    | 9 => .occ ⟨8, by decide⟩
    | 10 => .occ ⟨10, by decide⟩
    | 11 => .occ ⟨12, by decide⟩
    | 12 => .occ ⟨13, by decide⟩
    | 13 => .occ ⟨101, by decide⟩
    | 14 => .occ ⟨50, by decide⟩
    | 15 => .occ ⟨17, by decide⟩
    | 16 => .occ ⟨155, by decide⟩
    | 17 => .occ ⟨18, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨160, by decide⟩
    | 20 => .occ ⟨290, by decide⟩
    | 21 => .occ ⟨55, by decide⟩
    | 22 => .occ ⟨291, by decide⟩
    | 23 => .occ ⟨168, by decide⟩
    | 24 => .occ ⟨170, by decide⟩
    | 25 => .occ ⟨171, by decide⟩
    | 26 => .occ ⟨256, by decide⟩
    | 27 => .occ ⟨162, by decide⟩
    | 28 => .occ ⟨79, by decide⟩
    | 29 => .occ ⟨292, by decide⟩
    | 30 => .occ ⟨62, by decide⟩
    | 31 => .occ ⟨211, by decide⟩
    | 32 => .occ ⟨286, by decide⟩
    | 33 => .occ ⟨80, by decide⟩
    | 34 => .occ ⟨279, by decide⟩
    | 35 => .occ ⟨149, by decide⟩
    | 36 => .sumGe
    | 37 => .nonneg ⟨4, by decide⟩
    | 38 => .nonneg ⟨7, by decide⟩
    | 39 => .nonneg ⟨8, by decide⟩
    | 40 => .nonneg ⟨10, by decide⟩
    | 41 => .nonneg ⟨12, by decide⟩
    | 42 => .nonneg ⟨16, by decide⟩
    | 43 => .nonneg ⟨17, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨22, by decide⟩
    | 47 => .nonneg ⟨27, by decide⟩
    | 48 => .nonneg ⟨28, by decide⟩
    | 49 => .nonneg ⟨30, by decide⟩
    | 50 => .nonneg ⟨31, by decide⟩
    | 51 => .nonneg ⟨33, by decide⟩
    | 52 => .nonneg ⟨41, by decide⟩
    | 53 => .nonneg ⟨43, by decide⟩
    | 54 => .nonneg ⟨49, by decide⟩
    | 55 => .nonneg ⟨55, by decide⟩
    | 56 => .nonneg ⟨60, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨15, by decide⟩ 0
    | 59 => .branchLe ⟨21, by decide⟩ 0
    | 60 => .branchLe ⟨51, by decide⟩ 0
    | 61 => .branchLe ⟨57, by decide⟩ 0
    | 62 => .branchGe ⟨13, by decide⟩ 1
    | 63 => .branchGe ⟨58, by decide⟩ 1
    | _ => .sumGe

def mults_416_L24 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 362
    | 1 => 1912
    | 2 => 2392
    | 3 => 936
    | 4 => 968
    | 5 => 1939
    | 6 => 2246
    | 7 => 1959
    | 8 => 962
    | 9 => 2203
    | 10 => 1469
    | 11 => 1228
    | 12 => 4849
    | 13 => 275
    | 14 => 648
    | 15 => 2331
    | 16 => 494
    | 17 => 2860
    | 18 => 2037
    | 19 => 1552
    | 20 => 1265
    | 21 => 545
    | 22 => 559
    | 23 => 1714
    | 24 => 1064
    | 25 => 405
    | 26 => 1031
    | 27 => 576
    | 28 => 422
    | 29 => 798
    | 30 => 128
    | 31 => 2100
    | 32 => 17
    | 33 => 1022
    | 34 => 1158
    | 35 => 1812
    | 36 => 7039
    | 37 => 360
    | 38 => 4626
    | 39 => 4031
    | 40 => 4583
    | 41 => 2681
    | 42 => 8245
    | 43 => 736
    | 44 => 2680
    | 45 => 7430
    | 46 => 3758
    | 47 => 112
    | 48 => 487
    | 49 => 7529
    | 50 => 189
    | 51 => 727
    | 52 => 2554
    | 53 => 3967
    | 54 => 76
    | 55 => 940
    | 56 => 1679
    | 57 => 2249
    | 58 => 5815
    | 59 => 1433
    | 60 => 5881
    | 61 => 5881
    | 62 => 11314
    | 63 => 6216
    | _ => 0

theorem coeff_cancel_416_L24 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L24 i : Int) * (refs_416_L24 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L24 :
    (∑ i : Fin 64, (mults_416_L24 i : Int) * (refs_416_L24 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf24_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_16_0 : x ⟨15, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_59_1 : (1 : Int) ≤ x ⟨58, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L24 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L24 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨288, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨289, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨101, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨290, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨291, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨168, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨170, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨162, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨79, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨292, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨62, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨286, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨17, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨49, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨60, by decide⟩]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_16_0]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_22_0]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L24, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_59_1]
  exact farkas_leaf_unsat _ _ (mults_416_L24) coeff_cancel_416_L24 rhs_neg_416_L24 x hrows

-- leaf 25, path LRLLRLLR, Farkas rhs -687
def refs_416_L25 : Fin 63 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨81, by decide⟩
    | 1 => .occ ⟨220, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨1, by decide⟩
    | 4 => .occ ⟨248, by decide⟩
    | 5 => .occ ⟨293, by decide⟩
    | 6 => .occ ⟨289, by decide⟩
    | 7 => .occ ⟨294, by decide⟩
    | 8 => .occ ⟨129, by decide⟩
    | 9 => .occ ⟨3, by decide⟩
    | 10 => .occ ⟨180, by decide⟩
    | 11 => .occ ⟨295, by decide⟩
    | 12 => .occ ⟨296, by decide⟩
    | 13 => .occ ⟨87, by decide⟩
    | 14 => .occ ⟨13, by decide⟩
    | 15 => .occ ⟨17, by decide⟩
    | 16 => .occ ⟨155, by decide⟩
    | 17 => .occ ⟨18, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨297, by decide⟩
    | 21 => .occ ⟨194, by decide⟩
    | 22 => .occ ⟨241, by decide⟩
    | 23 => .occ ⟨260, by decide⟩
    | 24 => .occ ⟨160, by decide⟩
    | 25 => .occ ⟨77, by decide⟩
    | 26 => .occ ⟨106, by decide⟩
    | 27 => .occ ⟨141, by decide⟩
    | 28 => .occ ⟨28, by decide⟩
    | 29 => .occ ⟨298, by decide⟩
    | 30 => .occ ⟨57, by decide⟩
    | 31 => .occ ⟨178, by decide⟩
    | 32 => .occ ⟨185, by decide⟩
    | 33 => .occ ⟨256, by decide⟩
    | 34 => .occ ⟨61, by decide⟩
    | 35 => .occ ⟨80, by decide⟩
    | 36 => .occ ⟨149, by decide⟩
    | 37 => .occ ⟨126, by decide⟩
    | 38 => .occ ⟨41, by decide⟩
    | 39 => .sumGe
    | 40 => .nonneg ⟨7, by decide⟩
    | 41 => .nonneg ⟨10, by decide⟩
    | 42 => .nonneg ⟨12, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨19, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨28, by decide⟩
    | 47 => .nonneg ⟨30, by decide⟩
    | 48 => .nonneg ⟨43, by decide⟩
    | 49 => .nonneg ⟨45, by decide⟩
    | 50 => .nonneg ⟨47, by decide⟩
    | 51 => .nonneg ⟨49, by decide⟩
    | 52 => .nonneg ⟨55, by decide⟩
    | 53 => .nonneg ⟨60, by decide⟩
    | 54 => .nonneg ⟨62, by decide⟩
    | 55 => .branchLe ⟨6, by decide⟩ 0
    | 56 => .branchLe ⟨15, by decide⟩ 0
    | 57 => .branchLe ⟨17, by decide⟩ 0
    | 58 => .branchLe ⟨21, by decide⟩ 0
    | 59 => .branchLe ⟨57, by decide⟩ 0
    | 60 => .branchGe ⟨13, by decide⟩ 1
    | 61 => .branchGe ⟨51, by decide⟩ 1
    | 62 => .branchGe ⟨58, by decide⟩ 1
    | _ => .sumGe

def mults_416_L25 : Fin 63 → Nat
  | i => match i.val with
    | 0 => 36
    | 1 => 744
    | 2 => 215
    | 3 => 271
    | 4 => 81
    | 5 => 331
    | 6 => 44
    | 7 => 143
    | 8 => 493
    | 9 => 704
    | 10 => 456
    | 11 => 287
    | 12 => 393
    | 13 => 22
    | 14 => 11
    | 15 => 259
    | 16 => 320
    | 17 => 204
    | 18 => 21
    | 19 => 729
    | 20 => 138
    | 21 => 452
    | 22 => 159
    | 23 => 325
    | 24 => 219
    | 25 => 287
    | 26 => 225
    | 27 => 312
    | 28 => 209
    | 29 => 340
    | 30 => 170
    | 31 => 285
    | 32 => 192
    | 33 => 11
    | 34 => 285
    | 35 => 65
    | 36 => 54
    | 37 => 38
    | 38 => 28
    | 39 => 1092
    | 40 => 206
    | 41 => 1285
    | 42 => 34
    | 43 => 704
    | 44 => 32
    | 45 => 530
    | 46 => 27
    | 47 => 1099
    | 48 => 204
    | 49 => 16
    | 50 => 6
    | 51 => 71
    | 52 => 297
    | 53 => 255
    | 54 => 713
    | 55 => 648
    | 56 => 1092
    | 57 => 358
    | 58 => 320
    | 59 => 1054
    | 60 => 637
    | 61 => 3901
    | 62 => 2093
    | _ => 0

theorem coeff_cancel_416_L25 :
    ∀ j : Fin 63, (∑ i : Fin 63, (mults_416_L25 i : Int) * (refs_416_L25 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L25 :
    (∑ i : Fin 63, (mults_416_L25 i : Int) * (refs_416_L25 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf25_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_16_0 : x ⟨15, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_59_1 : (1 : Int) ≤ x ⟨58, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 63,
      (∑ j : Fin 63, (refs_416_L25 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L25 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨293, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨289, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨294, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨180, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨295, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨296, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨297, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨194, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨241, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨260, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨77, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨141, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨298, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨57, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨45, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨47, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨49, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨60, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨62, by decide⟩]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_16_0]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_22_0]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L25, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_59_1]
  exact farkas_leaf_unsat _ _ (mults_416_L25) coeff_cancel_416_L25 rhs_neg_416_L25 x hrows

-- leaf 26, path LRLLRLR, Farkas rhs -7609
def refs_416_L26 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨187, by decide⟩
    | 1 => .occ ⟨235, by decide⟩
    | 2 => .occ ⟨165, by decide⟩
    | 3 => .occ ⟨111, by decide⟩
    | 4 => .occ ⟨248, by decide⟩
    | 5 => .occ ⟨249, by decide⟩
    | 6 => .occ ⟨294, by decide⟩
    | 7 => .occ ⟨3, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨5, by decide⟩
    | 10 => .occ ⟨6, by decide⟩
    | 11 => .occ ⟨267, by decide⟩
    | 12 => .occ ⟨87, by decide⟩
    | 13 => .occ ⟨8, by decide⟩
    | 14 => .occ ⟨12, by decide⟩
    | 15 => .occ ⟨13, by decide⟩
    | 16 => .occ ⟨50, by decide⟩
    | 17 => .occ ⟨17, by decide⟩
    | 18 => .occ ⟨18, by decide⟩
    | 19 => .occ ⟨20, by decide⟩
    | 20 => .occ ⟨299, by decide⟩
    | 21 => .occ ⟨300, by decide⟩
    | 22 => .occ ⟨194, by decide⟩
    | 23 => .occ ⟨301, by decide⟩
    | 24 => .occ ⟨261, by decide⟩
    | 25 => .occ ⟨302, by decide⟩
    | 26 => .occ ⟨303, by decide⟩
    | 27 => .occ ⟨91, by decide⟩
    | 28 => .occ ⟨29, by decide⟩
    | 29 => .occ ⟨304, by decide⟩
    | 30 => .occ ⟨298, by decide⟩
    | 31 => .occ ⟨162, by decide⟩
    | 32 => .occ ⟨305, by decide⟩
    | 33 => .occ ⟨306, by decide⟩
    | 34 => .occ ⟨307, by decide⟩
    | 35 => .occ ⟨308, by decide⟩
    | 36 => .occ ⟨80, by decide⟩
    | 37 => .occ ⟨41, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨7, by decide⟩
    | 41 => .nonneg ⟨8, by decide⟩
    | 42 => .nonneg ⟨10, by decide⟩
    | 43 => .nonneg ⟨16, by decide⟩
    | 44 => .nonneg ⟨18, by decide⟩
    | 45 => .nonneg ⟨20, by decide⟩
    | 46 => .nonneg ⟨22, by decide⟩
    | 47 => .nonneg ⟨25, by decide⟩
    | 48 => .nonneg ⟨27, by decide⟩
    | 49 => .nonneg ⟨32, by decide⟩
    | 50 => .nonneg ⟨33, by decide⟩
    | 51 => .nonneg ⟨34, by decide⟩
    | 52 => .nonneg ⟨42, by decide⟩
    | 53 => .nonneg ⟨43, by decide⟩
    | 54 => .nonneg ⟨45, by decide⟩
    | 55 => .nonneg ⟨47, by decide⟩
    | 56 => .nonneg ⟨49, by decide⟩
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨17, by decide⟩ 0
    | 59 => .branchLe ⟨21, by decide⟩ 0
    | 60 => .branchLe ⟨57, by decide⟩ 0
    | 61 => .branchGe ⟨13, by decide⟩ 1
    | 62 => .branchGe ⟨15, by decide⟩ 1
    | 63 => .branchGe ⟨58, by decide⟩ 1
    | _ => .sumGe

def mults_416_L26 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 967
    | 1 => 6839
    | 2 => 3806
    | 3 => 9947
    | 4 => 1937
    | 5 => 403
    | 6 => 165
    | 7 => 2867
    | 8 => 1909
    | 9 => 32
    | 10 => 6
    | 11 => 417
    | 12 => 1918
    | 13 => 1208
    | 14 => 3581
    | 15 => 738
    | 16 => 7798
    | 17 => 2563
    | 18 => 1037
    | 19 => 3
    | 20 => 165
    | 21 => 1100
    | 22 => 913
    | 23 => 392
    | 24 => 289
    | 25 => 1182
    | 26 => 3024
    | 27 => 3105
    | 28 => 767
    | 29 => 4105
    | 30 => 1231
    | 31 => 5193
    | 32 => 84
    | 33 => 713
    | 34 => 237
    | 35 => 1746
    | 36 => 1730
    | 37 => 1964
    | 38 => 9947
    | 39 => 8991
    | 40 => 217
    | 41 => 3664
    | 42 => 3934
    | 43 => 6249
    | 44 => 10028
    | 45 => 3273
    | 46 => 51
    | 47 => 5139
    | 48 => 3414
    | 49 => 5840
    | 50 => 1101
    | 51 => 4968
    | 52 => 2745
    | 53 => 2231
    | 54 => 471
    | 55 => 1545
    | 56 => 5658
    | 57 => 2366
    | 58 => 3503
    | 59 => 6234
    | 60 => 6962
    | 61 => 3856
    | 62 => 36483
    | 63 => 15725
    | _ => 0

theorem coeff_cancel_416_L26 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L26 i : Int) * (refs_416_L26 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L26 :
    (∑ i : Fin 64, (mults_416_L26 i : Int) * (refs_416_L26 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf26_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_22_0 : x ⟨21, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_16_1 : (1 : Int) ≤ x ⟨15, by decide⟩)
    (h_ge_59_1 : (1 : Int) ≤ x ⟨58, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L26 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L26 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨187, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨249, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨294, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨267, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨299, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨300, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨194, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨301, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨261, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨302, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨303, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨91, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨304, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨298, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨162, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨305, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨306, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨307, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨308, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨41, by decide⟩
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨45, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨47, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨49, by decide⟩]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_18_0]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_22_0]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_16_1]
    · simp only [refs_416_L26, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_59_1]
  exact farkas_leaf_unsat _ _ (mults_416_L26) coeff_cancel_416_L26 rhs_neg_416_L26 x hrows

-- leaf 27, path LRLLRRL, Farkas rhs -19912
def refs_416_L27 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨186, by decide⟩
    | 2 => .occ ⟨309, by decide⟩
    | 3 => .occ ⟨0, by decide⟩
    | 4 => .occ ⟨188, by decide⟩
    | 5 => .occ ⟨111, by decide⟩
    | 6 => .occ ⟨248, by decide⟩
    | 7 => .occ ⟨112, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨6, by decide⟩
    | 10 => .occ ⟨191, by decide⟩
    | 11 => .occ ⟨267, by decide⟩
    | 12 => .occ ⟨214, by decide⟩
    | 13 => .occ ⟨238, by decide⟩
    | 14 => .occ ⟨310, by decide⟩
    | 15 => .occ ⟨10, by decide⟩
    | 16 => .occ ⟨13, by decide⟩
    | 17 => .occ ⟨14, by decide⟩
    | 18 => .occ ⟨118, by decide⟩
    | 19 => .occ ⟨50, by decide⟩
    | 20 => .occ ⟨19, by decide⟩
    | 21 => .occ ⟨192, by decide⟩
    | 22 => .occ ⟨311, by decide⟩
    | 23 => .occ ⟨253, by decide⟩
    | 24 => .occ ⟨284, by decide⟩
    | 25 => .occ ⟨312, by decide⟩
    | 26 => .occ ⟨303, by decide⟩
    | 27 => .occ ⟨26, by decide⟩
    | 28 => .occ ⟨29, by decide⟩
    | 29 => .occ ⟨304, by decide⟩
    | 30 => .occ ⟨178, by decide⟩
    | 31 => .occ ⟨108, by decide⟩
    | 32 => .occ ⟨256, by decide⟩
    | 33 => .occ ⟨122, by decide⟩
    | 34 => .occ ⟨162, by decide⟩
    | 35 => .occ ⟨35, by decide⟩
    | 36 => .occ ⟨212, by decide⟩
    | 37 => .occ ⟨313, by decide⟩
    | 38 => .occ ⟨314, by decide⟩
    | 39 => .occ ⟨315, by decide⟩
    | 40 => .occ ⟨316, by decide⟩
    | 41 => .occ ⟨307, by decide⟩
    | 42 => .occ ⟨286, by decide⟩
    | 43 => .occ ⟨317, by decide⟩
    | 44 => .occ ⟨287, by decide⟩
    | 45 => .occ ⟨80, by decide⟩
    | 46 => .occ ⟨149, by decide⟩
    | 47 => .sumGe
    | 48 => .nonneg ⟨2, by decide⟩
    | 49 => .nonneg ⟨4, by decide⟩
    | 50 => .nonneg ⟨7, by decide⟩
    | 51 => .nonneg ⟨10, by decide⟩
    | 52 => .nonneg ⟨18, by decide⟩
    | 53 => .nonneg ⟨20, by decide⟩
    | 54 => .nonneg ⟨24, by decide⟩
    | 55 => .nonneg ⟨27, by decide⟩
    | 56 => .nonneg ⟨41, by decide⟩
    | 57 => .nonneg ⟨49, by decide⟩
    | 58 => .branchLe ⟨6, by decide⟩ 0
    | 59 => .branchLe ⟨51, by decide⟩ 0
    | 60 => .branchLe ⟨57, by decide⟩ 0
    | 61 => .branchGe ⟨13, by decide⟩ 1
    | 62 => .branchGe ⟨21, by decide⟩ 1
    | 63 => .branchGe ⟨58, by decide⟩ 1
    | _ => .sumGe

def mults_416_L27 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 14056
    | 1 => 7612
    | 2 => 1652
    | 3 => 792
    | 4 => 24116
    | 5 => 10000
    | 6 => 17520
    | 7 => 1348
    | 8 => 148
    | 9 => 1256
    | 10 => 3180
    | 11 => 1652
    | 12 => 1652
    | 13 => 1540
    | 14 => 412
    | 15 => 7356
    | 16 => 2736
    | 17 => 9860
    | 18 => 7036
    | 19 => 2588
    | 20 => 788
    | 21 => 10040
    | 22 => 4600
    | 23 => 368
    | 24 => 1164
    | 25 => 5340
    | 26 => 1800
    | 27 => 2944
    | 28 => 2248
    | 29 => 4288
    | 30 => 1492
    | 31 => 4292
    | 32 => 752
    | 33 => 2036
    | 34 => 3192
    | 35 => 5164
    | 36 => 4380
    | 37 => 4424
    | 38 => 3752
    | 39 => 422
    | 40 => 2782
    | 41 => 3843
    | 42 => 2620
    | 43 => 1705
    | 44 => 1364
    | 45 => 933
    | 46 => 2271
    | 47 => 24116
    | 48 => 20192
    | 49 => 6492
    | 50 => 25176
    | 51 => 340
    | 52 => 1668
    | 53 => 24036
    | 54 => 6112
    | 55 => 640
    | 56 => 3320
    | 57 => 2100
    | 58 => 3600
    | 59 => 16768
    | 60 => 13220
    | 61 => 26112
    | 62 => 82560
    | 63 => 33168
    | _ => 0

theorem coeff_cancel_416_L27 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L27 i : Int) * (refs_416_L27 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L27 :
    (∑ i : Fin 64, (mults_416_L27 i : Int) * (refs_416_L27 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf27_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_22_1 : (1 : Int) ≤ x ⟨21, by decide⟩)
    (h_ge_59_1 : (1 : Int) ≤ x ⟨58, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L27 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L27 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨186, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨309, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨188, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨191, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨267, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨214, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨238, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨310, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨14, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨118, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨192, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨311, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨253, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨284, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨312, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨303, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨26, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨304, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨122, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨162, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨35, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨212, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨313, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨314, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨315, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨316, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨307, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨286, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨317, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨287, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨49, by decide⟩]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_22_1]
    · simp only [refs_416_L27, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_59_1]
  exact farkas_leaf_unsat _ _ (mults_416_L27) coeff_cancel_416_L27 rhs_neg_416_L27 x hrows

-- leaf 28, path LRLLRRR, Farkas rhs -372
def refs_416_L28 : Fin 61 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨186, by decide⟩
    | 2 => .occ ⟨309, by decide⟩
    | 3 => .occ ⟨0, by decide⟩
    | 4 => .occ ⟨188, by decide⟩
    | 5 => .occ ⟨111, by decide⟩
    | 6 => .occ ⟨248, by decide⟩
    | 7 => .occ ⟨318, by decide⟩
    | 8 => .occ ⟨3, by decide⟩
    | 9 => .occ ⟨319, by decide⟩
    | 10 => .occ ⟨6, by decide⟩
    | 11 => .occ ⟨50, by decide⟩
    | 12 => .occ ⟨20, by decide⟩
    | 13 => .occ ⟨297, by decide⟩
    | 14 => .occ ⟨320, by decide⟩
    | 15 => .occ ⟨193, by decide⟩
    | 16 => .occ ⟨194, by decide⟩
    | 17 => .occ ⟨321, by decide⟩
    | 18 => .occ ⟨322, by decide⟩
    | 19 => .occ ⟨323, by decide⟩
    | 20 => .occ ⟨105, by decide⟩
    | 21 => .occ ⟨324, by decide⟩
    | 22 => .occ ⟨76, by decide⟩
    | 23 => .occ ⟨24, by decide⟩
    | 24 => .occ ⟨200, by decide⟩
    | 25 => .occ ⟨160, by decide⟩
    | 26 => .occ ⟨303, by decide⟩
    | 27 => .occ ⟨121, by decide⟩
    | 28 => .occ ⟨92, by decide⟩
    | 29 => .occ ⟨185, by decide⟩
    | 30 => .occ ⟨60, by decide⟩
    | 31 => .occ ⟨325, by decide⟩
    | 32 => .occ ⟨278, by decide⟩
    | 33 => .occ ⟨61, by decide⟩
    | 34 => .occ ⟨315, by decide⟩
    | 35 => .occ ⟨286, by decide⟩
    | 36 => .occ ⟨317, by decide⟩
    | 37 => .occ ⟨149, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨2, by decide⟩
    | 40 => .nonneg ⟨4, by decide⟩
    | 41 => .nonneg ⟨6, by decide⟩
    | 42 => .nonneg ⟨7, by decide⟩
    | 43 => .nonneg ⟨10, by decide⟩
    | 44 => .nonneg ⟨12, by decide⟩
    | 45 => .nonneg ⟨14, by decide⟩
    | 46 => .nonneg ⟨16, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨19, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨26, by decide⟩
    | 51 => .nonneg ⟨30, by decide⟩
    | 52 => .nonneg ⟨33, by decide⟩
    | 53 => .nonneg ⟨39, by decide⟩
    | 54 => .nonneg ⟨44, by decide⟩
    | 55 => .nonneg ⟨55, by decide⟩
    | 56 => .branchLe ⟨57, by decide⟩ 0
    | 57 => .branchGe ⟨13, by decide⟩ 1
    | 58 => .branchGe ⟨21, by decide⟩ 1
    | 59 => .branchGe ⟨51, by decide⟩ 1
    | 60 => .branchGe ⟨58, by decide⟩ 1
    | _ => .sumGe

def mults_416_L28 : Fin 61 → Nat
  | i => match i.val with
    | 0 => 48
    | 1 => 52
    | 2 => 72
    | 3 => 146
    | 4 => 146
    | 5 => 24
    | 6 => 48
    | 7 => 24
    | 8 => 16
    | 9 => 48
    | 10 => 24
    | 11 => 8
    | 12 => 24
    | 13 => 52
    | 14 => 56
    | 15 => 54
    | 16 => 16
    | 17 => 80
    | 18 => 8
    | 19 => 106
    | 20 => 10
    | 21 => 110
    | 22 => 9
    | 23 => 22
    | 24 => 12
    | 25 => 12
    | 26 => 12
    | 27 => 34
    | 28 => 8
    | 29 => 57
    | 30 => 19
    | 31 => 34
    | 32 => 5
    | 33 => 12
    | 34 => 48
    | 35 => 9
    | 36 => 46
    | 37 => 15
    | 38 => 146
    | 39 => 32
    | 40 => 176
    | 41 => 6
    | 42 => 56
    | 43 => 64
    | 44 => 14
    | 45 => 24
    | 46 => 46
    | 47 => 152
    | 48 => 24
    | 49 => 16
    | 50 => 6
    | 51 => 8
    | 52 => 260
    | 53 => 16
    | 54 => 284
    | 55 => 8
    | 56 => 88
    | 57 => 40
    | 58 => 1044
    | 59 => 348
    | 60 => 404
    | _ => 0

theorem coeff_cancel_416_L28 :
    ∀ j : Fin 63, (∑ i : Fin 61, (mults_416_L28 i : Int) * (refs_416_L28 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L28 :
    (∑ i : Fin 61, (mults_416_L28 i : Int) * (refs_416_L28 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf28_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_18_0 : x ⟨17, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_22_1 : (1 : Int) ≤ x ⟨21, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_59_1 : (1 : Int) ≤ x ⟨58, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 61,
      (∑ j : Fin 63, (refs_416_L28 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L28 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨186, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨309, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨188, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨111, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨318, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨319, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨297, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨320, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨193, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨194, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨321, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨322, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨323, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨105, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨324, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨76, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨200, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨303, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨121, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨92, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨325, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨278, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨315, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨286, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨317, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨6, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_22_1]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L28, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_59_1]
  exact farkas_leaf_unsat _ _ (mults_416_L28) coeff_cancel_416_L28 rhs_neg_416_L28 x hrows

-- leaf 29, path LRLR, Farkas rhs -46
def refs_416_L29 : Fin 57 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨0, by decide⟩
    | 1 => .occ ⟨64, by decide⟩
    | 2 => .occ ⟨236, by decide⟩
    | 3 => .occ ⟨45, by decide⟩
    | 4 => .occ ⟨248, by decide⟩
    | 5 => .occ ⟨276, by decide⟩
    | 6 => .occ ⟨6, by decide⟩
    | 7 => .occ ⟨87, by decide⟩
    | 8 => .occ ⟨12, by decide⟩
    | 9 => .occ ⟨326, by decide⟩
    | 10 => .occ ⟨13, by decide⟩
    | 11 => .occ ⟨15, by decide⟩
    | 12 => .occ ⟨50, by decide⟩
    | 13 => .occ ⟨16, by decide⟩
    | 14 => .occ ⟨17, by decide⟩
    | 15 => .occ ⟨19, by decide⟩
    | 16 => .occ ⟨20, by decide⟩
    | 17 => .occ ⟨327, by decide⟩
    | 18 => .occ ⟨55, by decide⟩
    | 19 => .occ ⟨27, by decide⟩
    | 20 => .occ ⟨225, by decide⟩
    | 21 => .occ ⟨142, by decide⟩
    | 22 => .occ ⟨263, by decide⟩
    | 23 => .occ ⟨29, by decide⟩
    | 24 => .occ ⟨144, by decide⟩
    | 25 => .occ ⟨183, by decide⟩
    | 26 => .occ ⟨298, by decide⟩
    | 27 => .occ ⟨169, by decide⟩
    | 28 => .occ ⟨60, by decide⟩
    | 29 => .occ ⟨109, by decide⟩
    | 30 => .occ ⟨211, by decide⟩
    | 31 => .occ ⟨286, by decide⟩
    | 32 => .occ ⟨287, by decide⟩
    | 33 => .occ ⟨206, by decide⟩
    | 34 => .occ ⟨279, by decide⟩
    | 35 => .occ ⟨149, by decide⟩
    | 36 => .sumGe
    | 37 => .nonneg ⟨2, by decide⟩
    | 38 => .nonneg ⟨7, by decide⟩
    | 39 => .nonneg ⟨8, by decide⟩
    | 40 => .nonneg ⟨10, by decide⟩
    | 41 => .nonneg ⟨12, by decide⟩
    | 42 => .nonneg ⟨16, by decide⟩
    | 43 => .nonneg ⟨18, by decide⟩
    | 44 => .nonneg ⟨23, by decide⟩
    | 45 => .nonneg ⟨24, by decide⟩
    | 46 => .nonneg ⟨26, by decide⟩
    | 47 => .nonneg ⟨27, by decide⟩
    | 48 => .nonneg ⟨28, by decide⟩
    | 49 => .nonneg ⟨30, by decide⟩
    | 50 => .nonneg ⟨40, by decide⟩
    | 51 => .nonneg ⟨41, by decide⟩
    | 52 => .nonneg ⟨42, by decide⟩
    | 53 => .branchLe ⟨6, by decide⟩ 0
    | 54 => .branchLe ⟨57, by decide⟩ 0
    | 55 => .branchGe ⟨13, by decide⟩ 1
    | 56 => .branchGe ⟨17, by decide⟩ 1
    | _ => .sumGe

def mults_416_L29 : Fin 57 → Nat
  | i => match i.val with
    | 0 => 60
    | 1 => 82
    | 2 => 100
    | 3 => 32
    | 4 => 80
    | 5 => 62
    | 6 => 48
    | 7 => 62
    | 8 => 72
    | 9 => 26
    | 10 => 10
    | 11 => 44
    | 12 => 44
    | 13 => 4
    | 14 => 4
    | 15 => 24
    | 16 => 24
    | 17 => 40
    | 18 => 3
    | 19 => 19
    | 20 => 16
    | 21 => 12
    | 22 => 32
    | 23 => 12
    | 24 => 48
    | 25 => 39
    | 26 => 39
    | 27 => 21
    | 28 => 21
    | 29 => 7
    | 30 => 7
    | 31 => 12
    | 32 => 12
    | 33 => 32
    | 34 => 9
    | 35 => 9
    | 36 => 144
    | 37 => 234
    | 38 => 132
    | 39 => 20
    | 40 => 52
    | 41 => 92
    | 42 => 96
    | 43 => 114
    | 44 => 12
    | 45 => 24
    | 46 => 54
    | 47 => 30
    | 48 => 98
    | 49 => 66
    | 50 => 48
    | 51 => 48
    | 52 => 48
    | 53 => 110
    | 54 => 48
    | 55 => 236
    | 56 => 498
    | _ => 0

theorem coeff_cancel_416_L29 :
    ∀ j : Fin 63, (∑ i : Fin 57, (mults_416_L29 i : Int) * (refs_416_L29 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L29 :
    (∑ i : Fin 57, (mults_416_L29 i : Int) * (refs_416_L29 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf29_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_58_0 : x ⟨57, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_18_1 : (1 : Int) ≤ x ⟨17, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 57,
      (∑ j : Fin 63, (refs_416_L29 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L29 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨64, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨236, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨276, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨326, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨327, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨225, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨263, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨144, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨183, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨298, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨169, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨60, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨109, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨286, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨287, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨206, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨23, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_58_0]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L29, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_18_1]
  exact farkas_leaf_unsat _ _ (mults_416_L29) coeff_cancel_416_L29 rhs_neg_416_L29 x hrows

-- leaf 30, path LRRLLL, Farkas rhs -1039
def refs_416_L30 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨235, by decide⟩
    | 2 => .occ ⟨45, by decide⟩
    | 3 => .occ ⟨328, by decide⟩
    | 4 => .occ ⟨130, by decide⟩
    | 5 => .occ ⟨113, by decide⟩
    | 6 => .occ ⟨5, by decide⟩
    | 7 => .occ ⟨6, by decide⟩
    | 8 => .occ ⟨237, by decide⟩
    | 9 => .occ ⟨49, by decide⟩
    | 10 => .occ ⟨87, by decide⟩
    | 11 => .occ ⟨8, by decide⟩
    | 12 => .occ ⟨10, by decide⟩
    | 13 => .occ ⟨12, by decide⟩
    | 14 => .occ ⟨326, by decide⟩
    | 15 => .occ ⟨13, by decide⟩
    | 16 => .occ ⟨15, by decide⟩
    | 17 => .occ ⟨50, by decide⟩
    | 18 => .occ ⟨16, by decide⟩
    | 19 => .occ ⟨155, by decide⟩
    | 20 => .occ ⟨18, by decide⟩
    | 21 => .occ ⟨19, by decide⟩
    | 22 => .occ ⟨253, by decide⟩
    | 23 => .occ ⟨157, by decide⟩
    | 24 => .occ ⟨329, by decide⟩
    | 25 => .occ ⟨284, by decide⟩
    | 26 => .occ ⟨330, by decide⟩
    | 27 => .occ ⟨331, by decide⟩
    | 28 => .occ ⟨176, by decide⟩
    | 29 => .occ ⟨160, by decide⟩
    | 30 => .occ ⟨262, by decide⟩
    | 31 => .occ ⟨106, by decide⟩
    | 32 => .occ ⟨29, by decide⟩
    | 33 => .occ ⟨291, by decide⟩
    | 34 => .occ ⟨256, by decide⟩
    | 35 => .occ ⟨34, by decide⟩
    | 36 => .occ ⟨211, by decide⟩
    | 37 => .occ ⟨80, by decide⟩
    | 38 => .occ ⟨279, by decide⟩
    | 39 => .occ ⟨40, by decide⟩
    | 40 => .occ ⟨149, by decide⟩
    | 41 => .sumGe
    | 42 => .nonneg ⟨2, by decide⟩
    | 43 => .nonneg ⟨4, by decide⟩
    | 44 => .nonneg ⟨7, by decide⟩
    | 45 => .nonneg ⟨8, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨16, by decide⟩
    | 48 => .nonneg ⟨18, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨24, by decide⟩
    | 51 => .nonneg ⟨28, by decide⟩
    | 52 => .nonneg ⟨30, by decide⟩
    | 53 => .nonneg ⟨34, by decide⟩
    | 54 => .nonneg ⟨39, by decide⟩
    | 55 => .nonneg ⟨44, by decide⟩
    | 56 => .nonneg ⟨56, by decide⟩
    | 57 => .nonneg ⟨61, by decide⟩
    | 58 => .branchLe ⟨6, by decide⟩ 0
    | 59 => .branchLe ⟨11, by decide⟩ 1
    | 60 => .branchLe ⟨51, by decide⟩ 0
    | 61 => .branchLe ⟨55, by decide⟩ 0
    | 62 => .branchGe ⟨13, by decide⟩ 1
    | 63 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L30 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 695
    | 1 => 317
    | 2 => 3361
    | 3 => 5971
    | 4 => 2428
    | 5 => 16289
    | 6 => 7081
    | 7 => 2741
    | 8 => 347
    | 9 => 3086
    | 10 => 3216
    | 11 => 7691
    | 12 => 5409
    | 13 => 6039
    | 14 => 1745
    | 15 => 7861
    | 16 => 5043
    | 17 => 6894
    | 18 => 11485
    | 19 => 5715
    | 20 => 11025
    | 21 => 2196
    | 22 => 3457
    | 23 => 79
    | 24 => 5830
    | 25 => 7735
    | 26 => 1666
    | 27 => 595
    | 28 => 582
    | 29 => 2662
    | 30 => 4211
    | 31 => 266
    | 32 => 1346
    | 33 => 3902
    | 34 => 2698
    | 35 => 1188
    | 36 => 391
    | 37 => 5306
    | 38 => 1443
    | 39 => 674
    | 40 => 2196
    | 41 => 18485
    | 42 => 20228
    | 43 => 9636
    | 44 => 9493
    | 45 => 4763
    | 46 => 18470
    | 47 => 31829
    | 48 => 21516
    | 49 => 26555
    | 50 => 473
    | 51 => 10886
    | 52 => 25204
    | 53 => 8192
    | 54 => 19574
    | 55 => 27
    | 56 => 11613
    | 57 => 27
    | 58 => 9540
    | 59 => 11266
    | 60 => 16447
    | 61 => 13627
    | 62 => 28186
    | 63 => 37027
    | _ => 0

theorem coeff_cancel_416_L30 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L30 i : Int) * (refs_416_L30 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L30 :
    (∑ i : Fin 64, (mults_416_L30 i : Int) * (refs_416_L30 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf30_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_52_0 : x ⟨51, by decide⟩ ≤ 0)
    (h_le_56_0 : x ⟨55, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L30 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L30 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨328, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨130, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨237, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨326, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨253, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨157, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨329, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨284, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨330, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨331, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨176, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨262, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨29, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨291, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨211, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨40, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨61, by decide⟩]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_12_1]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_52_0]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_56_0]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L30, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L30) coeff_cancel_416_L30 rhs_neg_416_L30 x hrows

-- leaf 31, path LRRLLRLL, Farkas rhs -205
def refs_416_L31 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨220, by decide⟩
    | 1 => .occ ⟨164, by decide⟩
    | 2 => .occ ⟨43, by decide⟩
    | 3 => .occ ⟨1, by decide⟩
    | 4 => .occ ⟨94, by decide⟩
    | 5 => .occ ⟨45, by decide⟩
    | 6 => .occ ⟨293, by decide⟩
    | 7 => .occ ⟨328, by decide⟩
    | 8 => .occ ⟨129, by decide⟩
    | 9 => .occ ⟨113, by decide⟩
    | 10 => .occ ⟨3, by decide⟩
    | 11 => .occ ⟨295, by decide⟩
    | 12 => .occ ⟨332, by decide⟩
    | 13 => .occ ⟨49, by decide⟩
    | 14 => .occ ⟨87, by decide⟩
    | 15 => .occ ⟨8, by decide⟩
    | 16 => .occ ⟨10, by decide⟩
    | 17 => .occ ⟨12, by decide⟩
    | 18 => .occ ⟨50, by decide⟩
    | 19 => .occ ⟨16, by decide⟩
    | 20 => .occ ⟨17, by decide⟩
    | 21 => .occ ⟨155, by decide⟩
    | 22 => .occ ⟨18, by decide⟩
    | 23 => .occ ⟨333, by decide⟩
    | 24 => .occ ⟨71, by decide⟩
    | 25 => .occ ⟨193, by decide⟩
    | 26 => .occ ⟨141, by decide⟩
    | 27 => .occ ⟨142, by decide⟩
    | 28 => .occ ⟨28, by decide⟩
    | 29 => .occ ⟨143, by decide⟩
    | 30 => .occ ⟨291, by decide⟩
    | 31 => .occ ⟨334, by decide⟩
    | 32 => .occ ⟨335, by decide⟩
    | 33 => .occ ⟨107, by decide⟩
    | 34 => .occ ⟨336, by decide⟩
    | 35 => .occ ⟨325, by decide⟩
    | 36 => .occ ⟨337, by decide⟩
    | 37 => .occ ⟨61, by decide⟩
    | 38 => .occ ⟨308, by decide⟩
    | 39 => .occ ⟨279, by decide⟩
    | 40 => .occ ⟨338, by decide⟩
    | 41 => .sumGe
    | 42 => .nonneg ⟨4, by decide⟩
    | 43 => .nonneg ⟨7, by decide⟩
    | 44 => .nonneg ⟨10, by decide⟩
    | 45 => .nonneg ⟨12, by decide⟩
    | 46 => .nonneg ⟨16, by decide⟩
    | 47 => .nonneg ⟨18, by decide⟩
    | 48 => .nonneg ⟨19, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨23, by decide⟩
    | 51 => .nonneg ⟨27, by decide⟩
    | 52 => .nonneg ⟨30, by decide⟩
    | 53 => .nonneg ⟨34, by decide⟩
    | 54 => .nonneg ⟨39, by decide⟩
    | 55 => .nonneg ⟨42, by decide⟩
    | 56 => .branchLe ⟨0, by decide⟩ 2
    | 57 => .branchLe ⟨6, by decide⟩ 0
    | 58 => .branchLe ⟨11, by decide⟩ 1
    | 59 => .branchLe ⟨52, by decide⟩ 0
    | 60 => .branchLe ⟨55, by decide⟩ 0
    | 61 => .branchGe ⟨13, by decide⟩ 1
    | 62 => .branchGe ⟨51, by decide⟩ 1
    | 63 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L31 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 310
    | 1 => 292
    | 2 => 43
    | 3 => 680
    | 4 => 102
    | 5 => 761
    | 6 => 398
    | 7 => 365
    | 8 => 116
    | 9 => 345
    | 10 => 42
    | 11 => 357
    | 12 => 26
    | 13 => 40
    | 14 => 288
    | 15 => 462
    | 16 => 243
    | 17 => 217
    | 18 => 62
    | 19 => 220
    | 20 => 44
    | 21 => 437
    | 22 => 634
    | 23 => 326
    | 24 => 292
    | 25 => 194
    | 26 => 394
    | 27 => 284
    | 28 => 19
    | 29 => 107
    | 30 => 323
    | 31 => 801
    | 32 => 87
    | 33 => 329
    | 34 => 183
    | 35 => 262
    | 36 => 176
    | 37 => 305
    | 38 => 22
    | 39 => 561
    | 40 => 304
    | 41 => 1586
    | 42 => 549
    | 43 => 191
    | 44 => 1593
    | 45 => 605
    | 46 => 956
    | 47 => 76
    | 48 => 609
    | 49 => 2413
    | 50 => 68
    | 51 => 112
    | 52 => 1483
    | 53 => 409
    | 54 => 997
    | 55 => 463
    | 56 => 1564
    | 57 => 896
    | 58 => 792
    | 59 => 1241
    | 60 => 1126
    | 61 => 2044
    | 62 => 2422
    | 63 => 2982
    | _ => 0

theorem coeff_cancel_416_L31 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L31 i : Int) * (refs_416_L31 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L31 :
    (∑ i : Fin 64, (mults_416_L31 i : Int) * (refs_416_L31 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf31_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_1_2 : x ⟨0, by decide⟩ ≤ 2)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_53_0 : x ⟨52, by decide⟩ ≤ 0)
    (h_le_56_0 : x ⟨55, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L31 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L31 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨164, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨293, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨328, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨295, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨332, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨49, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨8, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨10, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨333, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨71, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨193, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨141, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨28, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨143, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨291, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨334, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨335, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨336, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨325, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨337, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨61, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨308, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨338, by decide⟩
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨23, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_1_2]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_12_1]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_53_0]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_56_0]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L31, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L31) coeff_cancel_416_L31 rhs_neg_416_L31 x hrows

-- leaf 32, path LRRLLRLR, Farkas rhs -558
def refs_416_L32 : Fin 62 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨81, by decide⟩
    | 1 => .occ ⟨172, by decide⟩
    | 2 => .occ ⟨220, by decide⟩
    | 3 => .occ ⟨234, by decide⟩
    | 4 => .occ ⟨165, by decide⟩
    | 5 => .occ ⟨1, by decide⟩
    | 6 => .occ ⟨94, by decide⟩
    | 7 => .occ ⟨45, by decide⟩
    | 8 => .occ ⟨127, by decide⟩
    | 9 => .occ ⟨293, by decide⟩
    | 10 => .occ ⟨328, by decide⟩
    | 11 => .occ ⟨129, by decide⟩
    | 12 => .occ ⟨113, by decide⟩
    | 13 => .occ ⟨180, by decide⟩
    | 14 => .occ ⟨339, by decide⟩
    | 15 => .occ ⟨5, by decide⟩
    | 16 => .occ ⟨6, by decide⟩
    | 17 => .occ ⟨340, by decide⟩
    | 18 => .occ ⟨11, by decide⟩
    | 19 => .occ ⟨326, by decide⟩
    | 20 => .occ ⟨13, by decide⟩
    | 21 => .occ ⟨167, by decide⟩
    | 22 => .occ ⟨15, by decide⟩
    | 23 => .occ ⟨16, by decide⟩
    | 24 => .occ ⟨155, by decide⟩
    | 25 => .occ ⟨19, by decide⟩
    | 26 => .occ ⟨20, by decide⟩
    | 27 => .occ ⟨260, by decide⟩
    | 28 => .occ ⟨200, by decide⟩
    | 29 => .occ ⟨160, by decide⟩
    | 30 => .occ ⟨303, by decide⟩
    | 31 => .occ ⟨106, by decide⟩
    | 32 => .occ ⟨341, by decide⟩
    | 33 => .occ ⟨273, by decide⟩
    | 34 => .occ ⟨275, by decide⟩
    | 35 => .occ ⟨337, by decide⟩
    | 36 => .occ ⟨342, by decide⟩
    | 37 => .occ ⟨308, by decide⟩
    | 38 => .occ ⟨317, by decide⟩
    | 39 => .occ ⟨287, by decide⟩
    | 40 => .occ ⟨80, by decide⟩
    | 41 => .occ ⟨126, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨4, by decide⟩
    | 45 => .nonneg ⟨7, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨12, by decide⟩
    | 48 => .nonneg ⟨14, by decide⟩
    | 49 => .nonneg ⟨16, by decide⟩
    | 50 => .nonneg ⟨18, by decide⟩
    | 51 => .nonneg ⟨19, by decide⟩
    | 52 => .nonneg ⟨20, by decide⟩
    | 53 => .nonneg ⟨39, by decide⟩
    | 54 => .nonneg ⟨42, by decide⟩
    | 55 => .nonneg ⟨60, by decide⟩
    | 56 => .branchLe ⟨6, by decide⟩ 0
    | 57 => .branchLe ⟨55, by decide⟩ 0
    | 58 => .branchGe ⟨0, by decide⟩ 3
    | 59 => .branchGe ⟨13, by decide⟩ 1
    | 60 => .branchGe ⟨51, by decide⟩ 1
    | 61 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L32 : Fin 62 → Nat
  | i => match i.val with
    | 0 => 812
    | 1 => 124
    | 2 => 1586
    | 3 => 101
    | 4 => 1
    | 5 => 1794
    | 6 => 496
    | 7 => 620
    | 8 => 561
    | 9 => 1640
    | 10 => 774
    | 11 => 967
    | 12 => 155
    | 13 => 48
    | 14 => 448
    | 15 => 183
    | 16 => 437
    | 17 => 59
    | 18 => 375
    | 19 => 430
    | 20 => 334
    | 21 => 274
    | 22 => 310
    | 23 => 1116
    | 24 => 310
    | 25 => 3
    | 26 => 189
    | 27 => 403
    | 28 => 853
    | 29 => 557
    | 30 => 447
    | 31 => 808
    | 32 => 366
    | 33 => 280
    | 34 => 233
    | 35 => 77
    | 36 => 263
    | 37 => 275
    | 38 => 459
    | 39 => 3
    | 40 => 242
    | 41 => 212
    | 42 => 2195
    | 43 => 275
    | 44 => 525
    | 45 => 868
    | 46 => 654
    | 47 => 124
    | 48 => 273
    | 49 => 1922
    | 50 => 315
    | 51 => 248
    | 52 => 265
    | 53 => 1178
    | 54 => 1178
    | 55 => 436
    | 56 => 554
    | 57 => 1426
    | 58 => 3467
    | 59 => 2910
    | 60 => 5381
    | 61 => 3423
    | _ => 0

theorem coeff_cancel_416_L32 :
    ∀ j : Fin 63, (∑ i : Fin 62, (mults_416_L32 i : Int) * (refs_416_L32 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L32 :
    (∑ i : Fin 62, (mults_416_L32 i : Int) * (refs_416_L32 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf32_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_53_0 : x ⟨52, by decide⟩ ≤ 0)
    (h_le_56_0 : x ⟨55, by decide⟩ ≤ 0)
    (h_ge_1_3 : (3 : Int) ≤ x ⟨0, by decide⟩)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 62,
      (∑ j : Fin 63, (refs_416_L32 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L32 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨172, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨234, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨94, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨127, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨293, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨328, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨180, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨339, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨340, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨326, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨167, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨260, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨200, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨303, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨106, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨341, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨273, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨275, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨337, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨342, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨308, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨317, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨287, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨19, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨60, by decide⟩]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_56_0]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_1_3]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L32, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L32) coeff_cancel_416_L32 rhs_neg_416_L32 x hrows

-- leaf 33, path LRRLLRR, Farkas rhs -3350
def refs_416_L33 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨172, by decide⟩
    | 1 => .occ ⟨0, by decide⟩
    | 2 => .occ ⟨235, by decide⟩
    | 3 => .occ ⟨165, by decide⟩
    | 4 => .occ ⟨43, by decide⟩
    | 5 => .occ ⟨44, by decide⟩
    | 6 => .occ ⟨343, by decide⟩
    | 7 => .occ ⟨328, by decide⟩
    | 8 => .occ ⟨344, by decide⟩
    | 9 => .occ ⟨318, by decide⟩
    | 10 => .occ ⟨129, by decide⟩
    | 11 => .occ ⟨130, by decide⟩
    | 12 => .occ ⟨113, by decide⟩
    | 13 => .occ ⟨295, by decide⟩
    | 14 => .occ ⟨345, by decide⟩
    | 15 => .occ ⟨346, by decide⟩
    | 16 => .occ ⟨332, by decide⟩
    | 17 => .occ ⟨6, by decide⟩
    | 18 => .occ ⟨7, by decide⟩
    | 19 => .occ ⟨87, by decide⟩
    | 20 => .occ ⟨258, by decide⟩
    | 21 => .occ ⟨50, by decide⟩
    | 22 => .occ ⟨18, by decide⟩
    | 23 => .occ ⟨19, by decide⟩
    | 24 => .occ ⟨20, by decide⟩
    | 25 => .occ ⟨102, by decide⟩
    | 26 => .occ ⟨21, by decide⟩
    | 27 => .occ ⟨347, by decide⟩
    | 28 => .occ ⟨348, by decide⟩
    | 29 => .occ ⟨260, by decide⟩
    | 30 => .occ ⟨24, by decide⟩
    | 31 => .occ ⟨341, by decide⟩
    | 32 => .occ ⟨183, by decide⟩
    | 33 => .occ ⟨298, by decide⟩
    | 34 => .occ ⟨334, by decide⟩
    | 35 => .occ ⟨349, by decide⟩
    | 36 => .occ ⟨202, by decide⟩
    | 37 => .occ ⟨34, by decide⟩
    | 38 => .occ ⟨307, by decide⟩
    | 39 => .occ ⟨308, by decide⟩
    | 40 => .occ ⟨279, by decide⟩
    | 41 => .occ ⟨149, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨7, by decide⟩
    | 45 => .nonneg ⟨8, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨12, by decide⟩
    | 48 => .nonneg ⟨14, by decide⟩
    | 49 => .nonneg ⟨16, by decide⟩
    | 50 => .nonneg ⟨17, by decide⟩
    | 51 => .nonneg ⟨20, by decide⟩
    | 52 => .nonneg ⟨26, by decide⟩
    | 53 => .nonneg ⟨27, by decide⟩
    | 54 => .nonneg ⟨30, by decide⟩
    | 55 => .nonneg ⟨39, by decide⟩
    | 56 => .nonneg ⟨42, by decide⟩
    | 57 => .nonneg ⟨56, by decide⟩
    | 58 => .branchLe ⟨11, by decide⟩ 1
    | 59 => .branchLe ⟨55, by decide⟩ 0
    | 60 => .branchGe ⟨13, by decide⟩ 1
    | 61 => .branchGe ⟨51, by decide⟩ 1
    | 62 => .branchGe ⟨52, by decide⟩ 1
    | 63 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L33 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 697
    | 1 => 790
    | 2 => 533
    | 3 => 2378
    | 4 => 2186
    | 5 => 2228
    | 6 => 1306
    | 7 => 914
    | 8 => 1277
    | 9 => 2900
    | 10 => 556
    | 11 => 2644
    | 12 => 3012
    | 13 => 857
    | 14 => 656
    | 15 => 1982
    | 16 => 201
    | 17 => 352
    | 18 => 1209
    | 19 => 744
    | 20 => 905
    | 21 => 656
    | 22 => 1544
    | 23 => 1436
    | 24 => 92
    | 25 => 88
    | 26 => 888
    | 27 => 906
    | 28 => 2214
    | 29 => 1246
    | 30 => 888
    | 31 => 44
    | 32 => 2342
    | 33 => 1830
    | 34 => 528
    | 35 => 1322
    | 36 => 956
    | 37 => 1746
    | 38 => 424
    | 39 => 330
    | 40 => 1410
    | 41 => 656
    | 42 => 5498
    | 43 => 5747
    | 44 => 1018
    | 45 => 905
    | 46 => 7026
    | 47 => 3230
    | 48 => 216
    | 49 => 4280
    | 50 => 740
    | 51 => 701
    | 52 => 1438
    | 53 => 4864
    | 54 => 5581
    | 55 => 150
    | 56 => 450
    | 57 => 956
    | 58 => 4118
    | 59 => 2500
    | 60 => 9017
    | 61 => 9655
    | 62 => 15576
    | 63 => 9945
    | _ => 0

theorem coeff_cancel_416_L33 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L33 i : Int) * (refs_416_L33 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L33 :
    (∑ i : Fin 64, (mults_416_L33 i : Int) * (refs_416_L33 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf33_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_12_1 : x ⟨11, by decide⟩ ≤ 1)
    (h_le_56_0 : x ⟨55, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_52_1 : (1 : Int) ≤ x ⟨51, by decide⟩)
    (h_ge_53_1 : (1 : Int) ≤ x ⟨52, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L33 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L33 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨172, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨0, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨343, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨328, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨344, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨318, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨129, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨130, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨295, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨345, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨346, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨332, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨6, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨7, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨258, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨102, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨21, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨347, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨348, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨260, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨341, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨183, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨298, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨334, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨349, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨202, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨307, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨308, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨149, by decide⟩
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨14, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨17, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨26, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨27, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_12_1]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_56_0]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_52_1]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_53_1]
    · simp only [refs_416_L33, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L33) coeff_cancel_416_L33 rhs_neg_416_L33 x hrows

-- leaf 34, path LRRLR, Farkas rhs -170
def refs_416_L34 : Fin 63 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨42, by decide⟩
    | 1 => .occ ⟨220, by decide⟩
    | 2 => .occ ⟨350, by decide⟩
    | 3 => .occ ⟨235, by decide⟩
    | 4 => .occ ⟨165, by decide⟩
    | 5 => .occ ⟨45, by decide⟩
    | 6 => .occ ⟨174, by decide⟩
    | 7 => .occ ⟨113, by decide⟩
    | 8 => .occ ⟨4, by decide⟩
    | 9 => .occ ⟨12, by decide⟩
    | 10 => .occ ⟨13, by decide⟩
    | 11 => .occ ⟨16, by decide⟩
    | 12 => .occ ⟨155, by decide⟩
    | 13 => .occ ⟨18, by decide⟩
    | 14 => .occ ⟨20, by decide⟩
    | 15 => .occ ⟨348, by decide⟩
    | 16 => .occ ⟨55, by decide⟩
    | 17 => .occ ⟨27, by decide⟩
    | 18 => .occ ⟨142, by decide⟩
    | 19 => .occ ⟨30, by decide⟩
    | 20 => .occ ⟨291, by decide⟩
    | 21 => .occ ⟨178, by decide⟩
    | 22 => .occ ⟨334, by decide⟩
    | 23 => .occ ⟨179, by decide⟩
    | 24 => .occ ⟨202, by decide⟩
    | 25 => .occ ⟨185, by decide⟩
    | 26 => .occ ⟨107, by decide⟩
    | 27 => .occ ⟨273, by decide⟩
    | 28 => .occ ⟨256, by decide⟩
    | 29 => .occ ⟨34, by decide⟩
    | 30 => .occ ⟨109, by decide⟩
    | 31 => .occ ⟨36, by decide⟩
    | 32 => .occ ⟨337, by decide⟩
    | 33 => .occ ⟨80, by decide⟩
    | 34 => .occ ⟨126, by decide⟩
    | 35 => .sumGe
    | 36 => .nonneg ⟨2, by decide⟩
    | 37 => .nonneg ⟨4, by decide⟩
    | 38 => .nonneg ⟨8, by decide⟩
    | 39 => .nonneg ⟨10, by decide⟩
    | 40 => .nonneg ⟨12, by decide⟩
    | 41 => .nonneg ⟨16, by decide⟩
    | 42 => .nonneg ⟨18, by decide⟩
    | 43 => .nonneg ⟨20, by decide⟩
    | 44 => .nonneg ⟨21, by decide⟩
    | 45 => .nonneg ⟨22, by decide⟩
    | 46 => .nonneg ⟨25, by decide⟩
    | 47 => .nonneg ⟨28, by decide⟩
    | 48 => .nonneg ⟨30, by decide⟩
    | 49 => .nonneg ⟨31, by decide⟩
    | 50 => .nonneg ⟨32, by decide⟩
    | 51 => .nonneg ⟨34, by decide⟩
    | 52 => .nonneg ⟨39, by decide⟩
    | 53 => .nonneg ⟨40, by decide⟩
    | 54 => .nonneg ⟨44, by decide⟩
    | 55 => .nonneg ⟨56, by decide⟩
    | 56 => .nonneg ⟨61, by decide⟩
    | 57 => .nonneg ⟨62, by decide⟩
    | 58 => .branchLe ⟨6, by decide⟩ 0
    | 59 => .branchLe ⟨55, by decide⟩ 0
    | 60 => .branchGe ⟨11, by decide⟩ 2
    | 61 => .branchGe ⟨13, by decide⟩ 1
    | 62 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L34 : Fin 63 → Nat
  | i => match i.val with
    | 0 => 1348
    | 1 => 12
    | 2 => 106
    | 3 => 1514
    | 4 => 600
    | 5 => 604
    | 6 => 1256
    | 7 => 552
    | 8 => 512
    | 9 => 590
    | 10 => 1258
    | 11 => 680
    | 12 => 96
    | 13 => 272
    | 14 => 32
    | 15 => 84
    | 16 => 317
    | 17 => 343
    | 18 => 142
    | 19 => 338
    | 20 => 393
    | 21 => 751
    | 22 => 489
    | 23 => 765
    | 24 => 2
    | 25 => 254
    | 26 => 191
    | 27 => 316
    | 28 => 239
    | 29 => 348
    | 30 => 456
    | 31 => 264
    | 32 => 288
    | 33 => 462
    | 34 => 426
    | 35 => 1944
    | 36 => 512
    | 37 => 2290
    | 38 => 2288
    | 39 => 574
    | 40 => 712
    | 41 => 2988
    | 42 => 2170
    | 43 => 326
    | 44 => 716
    | 45 => 638
    | 46 => 3428
    | 47 => 684
    | 48 => 3782
    | 49 => 620
    | 50 => 1148
    | 51 => 528
    | 52 => 1064
    | 53 => 220
    | 54 => 1368
    | 55 => 336
    | 56 => 872
    | 57 => 56
    | 58 => 708
    | 59 => 392
    | 60 => 5236
    | 61 => 2656
    | 62 => 2700
    | _ => 0

theorem coeff_cancel_416_L34 :
    ∀ j : Fin 63, (∑ i : Fin 63, (mults_416_L34 i : Int) * (refs_416_L34 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L34 :
    (∑ i : Fin 63, (mults_416_L34 i : Int) * (refs_416_L34 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf34_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_le_56_0 : x ⟨55, by decide⟩ ≤ 0)
    (h_ge_12_2 : (2 : Int) ≤ x ⟨11, by decide⟩)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 63,
      (∑ j : Fin 63, (refs_416_L34 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L34 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨42, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨220, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨350, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨174, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨113, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨4, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨348, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨55, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨142, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨30, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨291, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨178, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨334, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨179, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨202, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨273, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨256, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨109, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨337, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨80, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨56, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨61, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨62, by decide⟩]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_7_0]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_56_0]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_12_2]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L34, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L34) coeff_cancel_416_L34 rhs_neg_416_L34 x hrows

-- leaf 35, path LRRR, Farkas rhs -16
def refs_416_L35 : Fin 59 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨235, by decide⟩
    | 1 => .occ ⟨165, by decide⟩
    | 2 => .occ ⟨43, by decide⟩
    | 3 => .occ ⟨45, by decide⟩
    | 4 => .occ ⟨227, by decide⟩
    | 5 => .occ ⟨351, by decide⟩
    | 6 => .occ ⟨352, by decide⟩
    | 7 => .occ ⟨190, by decide⟩
    | 8 => .occ ⟨339, by decide⟩
    | 9 => .occ ⟨281, by decide⟩
    | 10 => .occ ⟨5, by decide⟩
    | 11 => .occ ⟨87, by decide⟩
    | 12 => .occ ⟨258, by decide⟩
    | 13 => .occ ⟨12, by decide⟩
    | 14 => .occ ⟨15, by decide⟩
    | 15 => .occ ⟨16, by decide⟩
    | 16 => .occ ⟨17, by decide⟩
    | 17 => .occ ⟨155, by decide⟩
    | 18 => .occ ⟨19, by decide⟩
    | 19 => .occ ⟨353, by decide⟩
    | 20 => .occ ⟨102, by decide⟩
    | 21 => .occ ⟨88, by decide⟩
    | 22 => .occ ⟨354, by decide⟩
    | 23 => .occ ⟨329, by decide⟩
    | 24 => .occ ⟨270, by decide⟩
    | 25 => .occ ⟨196, by decide⟩
    | 26 => .occ ⟨197, by decide⟩
    | 27 => .occ ⟨261, by decide⟩
    | 28 => .occ ⟨160, by decide⟩
    | 29 => .occ ⟨335, by decide⟩
    | 30 => .occ ⟨185, by decide⟩
    | 31 => .occ ⟨107, by decide⟩
    | 32 => .occ ⟨355, by decide⟩
    | 33 => .occ ⟨123, by decide⟩
    | 34 => .occ ⟨34, by decide⟩
    | 35 => .occ ⟨307, by decide⟩
    | 36 => .occ ⟨63, by decide⟩
    | 37 => .occ ⟨126, by decide⟩
    | 38 => .sumGe
    | 39 => .nonneg ⟨1, by decide⟩
    | 40 => .nonneg ⟨2, by decide⟩
    | 41 => .nonneg ⟨4, by decide⟩
    | 42 => .nonneg ⟨8, by decide⟩
    | 43 => .nonneg ⟨10, by decide⟩
    | 44 => .nonneg ⟨16, by decide⟩
    | 45 => .nonneg ⟨17, by decide⟩
    | 46 => .nonneg ⟨18, by decide⟩
    | 47 => .nonneg ⟨20, by decide⟩
    | 48 => .nonneg ⟨22, by decide⟩
    | 49 => .nonneg ⟨30, by decide⟩
    | 50 => .nonneg ⟨31, by decide⟩
    | 51 => .nonneg ⟨33, by decide⟩
    | 52 => .nonneg ⟨40, by decide⟩
    | 53 => .nonneg ⟨44, by decide⟩
    | 54 => .nonneg ⟨50, by decide⟩
    | 55 => .nonneg ⟨53, by decide⟩
    | 56 => .branchGe ⟨13, by decide⟩ 1
    | 57 => .branchGe ⟨55, by decide⟩ 1
    | 58 => .branchGe ⟨57, by decide⟩ 1
    | _ => .sumGe

def mults_416_L35 : Fin 59 → Nat
  | i => match i.val with
    | 0 => 4
    | 1 => 4
    | 2 => 58
    | 3 => 52
    | 4 => 11
    | 5 => 2
    | 6 => 8
    | 7 => 37
    | 8 => 26
    | 9 => 38
    | 10 => 22
    | 11 => 22
    | 12 => 2
    | 13 => 26
    | 14 => 6
    | 15 => 18
    | 16 => 37
    | 17 => 14
    | 18 => 22
    | 19 => 19
    | 20 => 7
    | 21 => 5
    | 22 => 6
    | 23 => 4
    | 24 => 12
    | 25 => 1
    | 26 => 11
    | 27 => 10
    | 28 => 23
    | 29 => 9
    | 30 => 8
    | 31 => 18
    | 32 => 2
    | 33 => 9
    | 34 => 14
    | 35 => 15
    | 36 => 8
    | 37 => 33
    | 38 => 70
    | 39 => 28
    | 40 => 66
    | 41 => 10
    | 42 => 4
    | 43 => 82
    | 44 => 44
    | 45 => 48
    | 46 => 30
    | 47 => 43
    | 48 => 14
    | 49 => 26
    | 50 => 44
    | 51 => 28
    | 52 => 54
    | 53 => 39
    | 54 => 22
    | 55 => 26
    | 56 => 88
    | 57 => 245
    | 58 => 138
    | _ => 0

theorem coeff_cancel_416_L35 :
    ∀ j : Fin 63, (∑ i : Fin 59, (mults_416_L35 i : Int) * (refs_416_L35 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L35 :
    (∑ i : Fin 59, (mults_416_L35 i : Int) * (refs_416_L35 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf35_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_7_0 : x ⟨6, by decide⟩ ≤ 0)
    (h_ge_14_1 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (h_ge_56_1 : (1 : Int) ≤ x ⟨55, by decide⟩)
    (h_ge_58_1 : (1 : Int) ≤ x ⟨57, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 59,
      (∑ j : Fin 63, (refs_416_L35 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L35 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨235, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨165, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨227, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨351, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨352, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨190, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨339, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨281, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨87, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨258, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨12, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨353, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨102, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨88, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨354, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨329, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨270, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨196, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨197, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨261, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨160, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨335, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨185, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨107, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨355, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨123, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨34, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨307, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨63, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨1, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨8, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨17, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨50, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨53, by decide⟩]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_14_1]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_56_1]
    · simp only [refs_416_L35, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_58_1]
  exact farkas_leaf_unsat _ _ (mults_416_L35) coeff_cancel_416_L35 rhs_neg_416_L35 x hrows

-- leaf 36, path RL, Farkas rhs -101
def refs_416_L36 : Fin 62 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨81, by decide⟩
    | 1 => .occ ⟨356, by decide⟩
    | 2 => .occ ⟨357, by decide⟩
    | 3 => .occ ⟨358, by decide⟩
    | 4 => .occ ⟨1, by decide⟩
    | 5 => .occ ⟨45, by decide⟩
    | 6 => .occ ⟨248, by decide⟩
    | 7 => .occ ⟨359, by decide⟩
    | 8 => .occ ⟨173, by decide⟩
    | 9 => .occ ⟨360, by decide⟩
    | 10 => .occ ⟨46, by decide⟩
    | 11 => .occ ⟨152, by decide⟩
    | 12 => .occ ⟨131, by decide⟩
    | 13 => .occ ⟨3, by decide⟩
    | 14 => .occ ⟨266, by decide⟩
    | 15 => .occ ⟨190, by decide⟩
    | 16 => .occ ⟨361, by decide⟩
    | 17 => .occ ⟨5, by decide⟩
    | 18 => .occ ⟨11, by decide⟩
    | 19 => .occ ⟨13, by decide⟩
    | 20 => .occ ⟨167, by decide⟩
    | 21 => .occ ⟨15, by decide⟩
    | 22 => .occ ⟨50, by decide⟩
    | 23 => .occ ⟨16, by decide⟩
    | 24 => .occ ⟨17, by decide⟩
    | 25 => .occ ⟨155, by decide⟩
    | 26 => .occ ⟨18, by decide⟩
    | 27 => .occ ⟨19, by decide⟩
    | 28 => .occ ⟨20, by decide⟩
    | 29 => .occ ⟨192, by decide⟩
    | 30 => .occ ⟨215, by decide⟩
    | 31 => .occ ⟨24, by decide⟩
    | 32 => .occ ⟨25, by decide⟩
    | 33 => .occ ⟨272, by decide⟩
    | 34 => .occ ⟨209, by decide⟩
    | 35 => .occ ⟨145, by decide⟩
    | 36 => .occ ⟨362, by decide⟩
    | 37 => .occ ⟨108, by decide⟩
    | 38 => .occ ⟨363, by decide⟩
    | 39 => .occ ⟨364, by decide⟩
    | 40 => .occ ⟨36, by decide⟩
    | 41 => .occ ⟨37, by decide⟩
    | 42 => .occ ⟨126, by decide⟩
    | 43 => .sumGe
    | 44 => .nonneg ⟨2, by decide⟩
    | 45 => .nonneg ⟨7, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨12, by decide⟩
    | 48 => .nonneg ⟨16, by decide⟩
    | 49 => .nonneg ⟨20, by decide⟩
    | 50 => .nonneg ⟨21, by decide⟩
    | 51 => .nonneg ⟨22, by decide⟩
    | 52 => .nonneg ⟨25, by decide⟩
    | 53 => .nonneg ⟨28, by decide⟩
    | 54 => .nonneg ⟨30, by decide⟩
    | 55 => .nonneg ⟨31, by decide⟩
    | 56 => .nonneg ⟨32, by decide⟩
    | 57 => .nonneg ⟨34, by decide⟩
    | 58 => .nonneg ⟨41, by decide⟩
    | 59 => .nonneg ⟨44, by decide⟩
    | 60 => .branchLe ⟨46, by decide⟩ 0
    | 61 => .branchGe ⟨6, by decide⟩ 1
    | _ => .sumGe

def mults_416_L36 : Fin 62 → Nat
  | i => match i.val with
    | 0 => 8
    | 1 => 202
    | 2 => 130
    | 3 => 138
    | 4 => 39
    | 5 => 18
    | 6 => 8
    | 7 => 103
    | 8 => 73
    | 9 => 2
    | 10 => 19
    | 11 => 18
    | 12 => 42
    | 13 => 8
    | 14 => 103
    | 15 => 98
    | 16 => 92
    | 17 => 92
    | 18 => 64
    | 19 => 92
    | 20 => 63
    | 21 => 83
    | 22 => 40
    | 23 => 83
    | 24 => 9
    | 25 => 33
    | 26 => 93
    | 27 => 83
    | 28 => 9
    | 29 => 8
    | 30 => 41
    | 31 => 38
    | 32 => 23
    | 33 => 45
    | 34 => 8
    | 35 => 51
    | 36 => 30
    | 37 => 75
    | 38 => 62
    | 39 => 9
    | 40 => 7
    | 41 => 41
    | 42 => 9
    | 43 => 202
    | 44 => 223
    | 45 => 184
    | 46 => 226
    | 47 => 8
    | 48 => 209
    | 49 => 24
    | 50 => 33
    | 51 => 6
    | 52 => 7
    | 53 => 15
    | 54 => 176
    | 55 => 69
    | 56 => 132
    | 57 => 41
    | 58 => 61
    | 59 => 61
    | 60 => 202
    | 61 => 1297
    | _ => 0

theorem coeff_cancel_416_L36 :
    ∀ j : Fin 63, (∑ i : Fin 62, (mults_416_L36 i : Int) * (refs_416_L36 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L36 :
    (∑ i : Fin 62, (mults_416_L36 i : Int) * (refs_416_L36 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf36_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_le_47_0 : x ⟨46, by decide⟩ ≤ 0)
    (h_ge_7_1 : (1 : Int) ≤ x ⟨6, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 62,
      (∑ j : Fin 63, (refs_416_L36 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L36 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨81, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨356, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨357, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨358, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨1, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨45, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨359, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨173, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨360, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨46, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨152, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨131, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨3, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨266, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨190, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨361, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨13, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨167, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨15, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨16, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨17, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨155, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨18, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨19, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨192, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨215, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨24, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨272, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨209, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨145, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨362, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨363, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨364, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨37, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨126, by decide⟩
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨20, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨21, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨22, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨25, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨30, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨31, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨32, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨41, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨44, by decide⟩]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_le_47_0]
    · simp only [refs_416_L36, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_7_1]
  exact farkas_leaf_unsat _ _ (mults_416_L36) coeff_cancel_416_L36 rhs_neg_416_L36 x hrows

-- leaf 37, path RR, Farkas rhs -4408
def refs_416_L37 : Fin 64 → RowRef 373 63
  | i => match i.val with
    | 0 => .occ ⟨356, by decide⟩
    | 1 => .occ ⟨357, by decide⟩
    | 2 => .occ ⟨358, by decide⟩
    | 3 => .occ ⟨43, by decide⟩
    | 4 => .occ ⟨44, by decide⟩
    | 5 => .occ ⟨166, by decide⟩
    | 6 => .occ ⟨248, by decide⟩
    | 7 => .occ ⟨112, by decide⟩
    | 8 => .occ ⟨365, by decide⟩
    | 9 => .occ ⟨85, by decide⟩
    | 10 => .occ ⟨190, by decide⟩
    | 11 => .occ ⟨366, by decide⟩
    | 12 => .occ ⟨367, by decide⟩
    | 13 => .occ ⟨281, by decide⟩
    | 14 => .occ ⟨5, by decide⟩
    | 15 => .occ ⟨368, by decide⟩
    | 16 => .occ ⟨237, by decide⟩
    | 17 => .occ ⟨11, by decide⟩
    | 18 => .occ ⟨326, by decide⟩
    | 19 => .occ ⟨167, by decide⟩
    | 20 => .occ ⟨50, by decide⟩
    | 21 => .occ ⟨20, by decide⟩
    | 22 => .occ ⟨284, by decide⟩
    | 23 => .occ ⟨369, by decide⟩
    | 24 => .occ ⟨331, by decide⟩
    | 25 => .occ ⟨25, by decide⟩
    | 26 => .occ ⟨27, by decide⟩
    | 27 => .occ ⟨225, by decide⟩
    | 28 => .occ ⟨263, by decide⟩
    | 29 => .occ ⟨304, by decide⟩
    | 30 => .occ ⟨56, by decide⟩
    | 31 => .occ ⟨291, by decide⟩
    | 32 => .occ ⟨334, by decide⟩
    | 33 => .occ ⟨171, by decide⟩
    | 34 => .occ ⟨362, by decide⟩
    | 35 => .occ ⟨370, by decide⟩
    | 36 => .occ ⟨108, by decide⟩
    | 37 => .occ ⟨371, by decide⟩
    | 38 => .occ ⟨372, by decide⟩
    | 39 => .occ ⟨33, by decide⟩
    | 40 => .occ ⟨36, by decide⟩
    | 41 => .occ ⟨279, by decide⟩
    | 42 => .sumGe
    | 43 => .nonneg ⟨2, by decide⟩
    | 44 => .nonneg ⟨4, by decide⟩
    | 45 => .nonneg ⟨7, by decide⟩
    | 46 => .nonneg ⟨10, by decide⟩
    | 47 => .nonneg ⟨12, by decide⟩
    | 48 => .nonneg ⟨16, by decide⟩
    | 49 => .nonneg ⟨18, by decide⟩
    | 50 => .nonneg ⟨23, by decide⟩
    | 51 => .nonneg ⟨24, by decide⟩
    | 52 => .nonneg ⟨28, by decide⟩
    | 53 => .nonneg ⟨33, by decide⟩
    | 54 => .nonneg ⟨34, by decide⟩
    | 55 => .nonneg ⟨39, by decide⟩
    | 56 => .nonneg ⟨40, by decide⟩
    | 57 => .nonneg ⟨42, by decide⟩
    | 58 => .nonneg ⟨43, by decide⟩
    | 59 => .nonneg ⟨55, by decide⟩
    | 60 => .nonneg ⟨59, by decide⟩
    | 61 => .nonneg ⟨61, by decide⟩
    | 62 => .branchGe ⟨6, by decide⟩ 1
    | 63 => .branchGe ⟨46, by decide⟩ 1
    | _ => .sumGe

def mults_416_L37 : Fin 64 → Nat
  | i => match i.val with
    | 0 => 1928
    | 1 => 3002
    | 2 => 2610
    | 3 => 434
    | 4 => 36
    | 5 => 154
    | 6 => 68
    | 7 => 3004
    | 8 => 336
    | 9 => 1402
    | 10 => 306
    | 11 => 2406
    | 12 => 3010
    | 13 => 98
    | 14 => 98
    | 15 => 828
    | 16 => 12
    | 17 => 174
    | 18 => 74
    | 19 => 134
    | 20 => 412
    | 21 => 332
    | 22 => 202
    | 23 => 1808
    | 24 => 307
    | 25 => 157
    | 26 => 70
    | 27 => 159
    | 28 => 371
    | 29 => 2364
    | 30 => 116
    | 31 => 28
    | 32 => 6
    | 33 => 303
    | 34 => 47
    | 35 => 125
    | 36 => 102
    | 37 => 2069
    | 38 => 301
    | 39 => 2508
    | 40 => 117
    | 41 => 426
    | 42 => 3210
    | 43 => 480
    | 44 => 30
    | 45 => 1820
    | 46 => 418
    | 47 => 116
    | 48 => 1244
    | 49 => 110
    | 50 => 152
    | 51 => 316
    | 52 => 30
    | 53 => 12
    | 54 => 308
    | 55 => 6918
    | 56 => 112
    | 57 => 380
    | 58 => 208
    | 59 => 232
    | 60 => 4
    | 61 => 700
    | 62 => 21070
    | 63 => 12930
    | _ => 0

theorem coeff_cancel_416_L37 :
    ∀ j : Fin 63, (∑ i : Fin 64, (mults_416_L37 i : Int) * (refs_416_L37 i).resolveCoeff S_416 j) = 0 := by
  decide

theorem rhs_neg_416_L37 :
    (∑ i : Fin 64, (mults_416_L37 i : Int) * (refs_416_L37 i).resolveRhs S_416) < 0 := by
  decide

theorem leaf37_infeasible_416 (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x)
    (h_ge_7_1 : (1 : Int) ≤ x ⟨6, by decide⟩)
    (h_ge_47_1 : (1 : Int) ≤ x ⟨46, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 64,
      (∑ j : Fin 63, (refs_416_L37 i).resolveCoeff S_416 j * x j) ≤
      (refs_416_L37 i).resolveRhs S_416 := by
    intro i; fin_cases i
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨356, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨357, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨358, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨43, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨44, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨166, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨248, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨112, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨365, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨85, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨190, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨366, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨367, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨281, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨5, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨368, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨237, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨11, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨326, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨167, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨50, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨20, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨284, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨369, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨331, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨25, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨27, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨225, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨263, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨304, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨56, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨291, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨334, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨171, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨362, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨370, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨108, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨371, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨372, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨33, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨36, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      exact hroot.hOcc ⟨279, by decide⟩
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hTotal]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨2, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨4, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨7, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨10, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨12, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨16, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨18, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨23, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨24, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨28, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨33, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨34, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨39, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨40, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨42, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨43, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨55, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨59, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [hroot.hNonneg ⟨61, by decide⟩]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_7_1]
    · simp only [refs_416_L37, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum, indicator_sum]
      linarith [h_ge_47_1]
  exact farkas_leaf_unsat _ _ (mults_416_L37) coeff_cancel_416_L37 rhs_neg_416_L37 x hrows

theorem orbit416_occupation_no_model (x : Fin 63 → Int)
    (hroot : S_416.RootHolds x) : False := by
  by_cases hbr_root_7_0 : x ⟨6, by decide⟩ ≤ 0
  ·
    by_cases hbr_L_14_0 : x ⟨13, by decide⟩ ≤ 0
    ·
      by_cases hbr_LL_30_0 : x ⟨29, by decide⟩ ≤ 0
      ·
        by_cases hbr_LLL_51_0 : x ⟨50, by decide⟩ ≤ 0
        ·
          by_cases hbr_LLLL_26_0 : x ⟨25, by decide⟩ ≤ 0
          ·
            by_cases hbr_LLLLL_55_0 : x ⟨54, by decide⟩ ≤ 0
            ·
              by_cases hbr_LLLLLL_46_0 : x ⟨45, by decide⟩ ≤ 0
              ·
                by_cases hbr_LLLLLLL_39_0 : x ⟨38, by decide⟩ ≤ 0
                ·
                  by_cases hbr_LLLLLLLL_48_0 : x ⟨47, by decide⟩ ≤ 0
                  ·
                    exact leaf0_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLLL_39_0 hbr_LLLLLL_46_0 hbr_LLLLLLLL_48_0 hbr_LLL_51_0 hbr_LLLLL_55_0
                  ·
                    have hbr_LLLLLLLL_48_0_ge : (1 : Int) ≤ x ⟨47, by decide⟩ := by omega
                    by_cases hbr_LLLLLLLLR_54_0 : x ⟨53, by decide⟩ ≤ 0
                    ·
                      by_cases hbr_LLLLLLLLRL_50_0 : x ⟨49, by decide⟩ ≤ 0
                      ·
                        exact leaf1_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLLL_39_0 hbr_LLLLLL_46_0 hbr_LLLLLLLLRL_50_0 hbr_LLL_51_0 hbr_LLLLLLLLR_54_0 hbr_LLLLL_55_0 hbr_LLLLLLLL_48_0_ge
                      ·
                        have hbr_LLLLLLLLRL_50_0_ge : (1 : Int) ≤ x ⟨49, by decide⟩ := by omega
                        exact leaf2_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLLL_39_0 hbr_LLLLLL_46_0 hbr_LLL_51_0 hbr_LLLLLLLLR_54_0 hbr_LLLLL_55_0 hbr_LLLLLLLL_48_0_ge hbr_LLLLLLLLRL_50_0_ge
                    ·
                      have hbr_LLLLLLLLR_54_0_ge : (1 : Int) ≤ x ⟨53, by decide⟩ := by omega
                      by_cases hbr_LLLLLLLLRR_60_0 : x ⟨59, by decide⟩ ≤ 0
                      ·
                        exact leaf3_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLLL_39_0 hbr_LLLLLL_46_0 hbr_LLL_51_0 hbr_LLLLL_55_0 hbr_LLLLLLLLRR_60_0 hbr_LLLLLLLL_48_0_ge hbr_LLLLLLLLR_54_0_ge
                      ·
                        have hbr_LLLLLLLLRR_60_0_ge : (1 : Int) ≤ x ⟨59, by decide⟩ := by omega
                        exact leaf4_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLLL_39_0 hbr_LLLLLL_46_0 hbr_LLL_51_0 hbr_LLLLL_55_0 hbr_LLLLLLLL_48_0_ge hbr_LLLLLLLLR_54_0_ge hbr_LLLLLLLLRR_60_0_ge
                ·
                  have hbr_LLLLLLL_39_0_ge : (1 : Int) ≤ x ⟨38, by decide⟩ := by omega
                  by_cases hbr_LLLLLLLR_47_0 : x ⟨46, by decide⟩ ≤ 0
                  ·
                    exact leaf5_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLL_46_0 hbr_LLLLLLLR_47_0 hbr_LLL_51_0 hbr_LLLLL_55_0 hbr_LLLLLLL_39_0_ge
                  ·
                    have hbr_LLLLLLLR_47_0_ge : (1 : Int) ≤ x ⟨46, by decide⟩ := by omega
                    exact leaf6_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLL_46_0 hbr_LLL_51_0 hbr_LLLLL_55_0 hbr_LLLLLLL_39_0_ge hbr_LLLLLLLR_47_0_ge
              ·
                have hbr_LLLLLL_46_0_ge : (1 : Int) ≤ x ⟨45, by decide⟩ := by omega
                exact leaf7_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLL_51_0 hbr_LLLLL_55_0 hbr_LLLLLL_46_0_ge
            ·
              have hbr_LLLLL_55_0_ge : (1 : Int) ≤ x ⟨54, by decide⟩ := by omega
              by_cases hbr_LLLLLR_50_0 : x ⟨49, by decide⟩ ≤ 0
              ·
                by_cases hbr_LLLLLRL_6_0 : x ⟨5, by decide⟩ ≤ 0
                ·
                  by_cases hbr_LLLLLRLL_22_0 : x ⟨21, by decide⟩ ≤ 0
                  ·
                    by_cases hbr_LLLLLRLLL_52_0 : x ⟨51, by decide⟩ ≤ 0
                    ·
                      by_cases hbr_LLLLLRLLLL_12_1 : x ⟨11, by decide⟩ ≤ 1
                      ·
                        by_cases hbr_LLLLLRLLLLL_2_0 : x ⟨1, by decide⟩ ≤ 0
                        ·
                          exact leaf8_infeasible_416 x hroot hbr_LLLLLRLLLLL_2_0 hbr_LLLLLRL_6_0 hbr_root_7_0 hbr_LLLLLRLLLL_12_1 hbr_L_14_0 hbr_LLLLLRLL_22_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLLL_52_0 hbr_LLLLL_55_0_ge
                        ·
                          have hbr_LLLLLRLLLLL_2_0_ge : (1 : Int) ≤ x ⟨1, by decide⟩ := by omega
                          exact leaf9_infeasible_416 x hroot hbr_LLLLLRL_6_0 hbr_root_7_0 hbr_LLLLLRLLLL_12_1 hbr_L_14_0 hbr_LLLLLRLL_22_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLLL_52_0 hbr_LLLLLRLLLLL_2_0_ge hbr_LLLLL_55_0_ge
                      ·
                        have hbr_LLLLLRLLLL_12_1_ge : (2 : Int) ≤ x ⟨11, by decide⟩ := by omega
                        exact leaf10_infeasible_416 x hroot hbr_LLLLLRL_6_0 hbr_root_7_0 hbr_L_14_0 hbr_LLLLLRLL_22_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLLL_52_0 hbr_LLLLLRLLLL_12_1_ge hbr_LLLLL_55_0_ge
                    ·
                      have hbr_LLLLLRLLL_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
                      exact leaf11_infeasible_416 x hroot hbr_LLLLLRL_6_0 hbr_root_7_0 hbr_L_14_0 hbr_LLLLLRLL_22_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLLL_52_0_ge hbr_LLLLL_55_0_ge
                  ·
                    have hbr_LLLLLRLL_22_0_ge : (1 : Int) ≤ x ⟨21, by decide⟩ := by omega
                    exact leaf12_infeasible_416 x hroot hbr_LLLLLRL_6_0 hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLL_22_0_ge hbr_LLLLL_55_0_ge
                ·
                  have hbr_LLLLLRL_6_0_ge : (1 : Int) ≤ x ⟨5, by decide⟩ := by omega
                  by_cases hbr_LLLLLRLR_1_2 : x ⟨0, by decide⟩ ≤ 2
                  ·
                    by_cases hbr_LLLLLRLRL_2_0 : x ⟨1, by decide⟩ ≤ 0
                    ·
                      exact leaf13_infeasible_416 x hroot hbr_LLLLLRLR_1_2 hbr_LLLLLRLRL_2_0 hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRL_6_0_ge hbr_LLLLL_55_0_ge
                    ·
                      have hbr_LLLLLRLRL_2_0_ge : (1 : Int) ≤ x ⟨1, by decide⟩ := by omega
                      exact leaf14_infeasible_416 x hroot hbr_LLLLLRLR_1_2 hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLRL_2_0_ge hbr_LLLLLRL_6_0_ge hbr_LLLLL_55_0_ge
                  ·
                    have hbr_LLLLLRLR_1_2_ge : (3 : Int) ≤ x ⟨0, by decide⟩ := by omega
                    exact leaf15_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLLLLR_50_0 hbr_LLL_51_0 hbr_LLLLLRLR_1_2_ge hbr_LLLLLRL_6_0_ge hbr_LLLLL_55_0_ge
              ·
                have hbr_LLLLLR_50_0_ge : (1 : Int) ≤ x ⟨49, by decide⟩ := by omega
                by_cases hbr_LLLLLRR_52_0 : x ⟨51, by decide⟩ ≤ 0
                ·
                  exact leaf16_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLL_51_0 hbr_LLLLLRR_52_0 hbr_LLLLLR_50_0_ge hbr_LLLLL_55_0_ge
                ·
                  have hbr_LLLLLRR_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
                  exact leaf17_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LLLL_26_0 hbr_LL_30_0 hbr_LLL_51_0 hbr_LLLLLR_50_0_ge hbr_LLLLLRR_52_0_ge hbr_LLLLL_55_0_ge
          ·
            have hbr_LLLL_26_0_ge : (1 : Int) ≤ x ⟨25, by decide⟩ := by omega
            exact leaf18_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LL_30_0 hbr_LLL_51_0 hbr_LLLL_26_0_ge
        ·
          have hbr_LLL_51_0_ge : (1 : Int) ≤ x ⟨50, by decide⟩ := by omega
          exact leaf19_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LL_30_0 hbr_LLL_51_0_ge
      ·
        have hbr_LL_30_0_ge : (1 : Int) ≤ x ⟨29, by decide⟩ := by omega
        exact leaf20_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0 hbr_LL_30_0_ge
    ·
      have hbr_L_14_0_ge : (1 : Int) ≤ x ⟨13, by decide⟩ := by omega
      by_cases hbr_LR_58_0 : x ⟨57, by decide⟩ ≤ 0
      ·
        by_cases hbr_LRL_18_0 : x ⟨17, by decide⟩ ≤ 0
        ·
          by_cases hbr_LRLL_59_0 : x ⟨58, by decide⟩ ≤ 0
          ·
            by_cases hbr_LRLLL_47_0 : x ⟨46, by decide⟩ ≤ 0
            ·
              by_cases hbr_LRLLLL_37_0 : x ⟨36, by decide⟩ ≤ 0
              ·
                exact leaf21_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LRLLLL_37_0 hbr_LRLLL_47_0 hbr_LR_58_0 hbr_LRLL_59_0 hbr_L_14_0_ge
              ·
                have hbr_LRLLLL_37_0_ge : (1 : Int) ≤ x ⟨36, by decide⟩ := by omega
                exact leaf22_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LRLLL_47_0 hbr_LR_58_0 hbr_LRLL_59_0 hbr_L_14_0_ge hbr_LRLLLL_37_0_ge
            ·
              have hbr_LRLLL_47_0_ge : (1 : Int) ≤ x ⟨46, by decide⟩ := by omega
              exact leaf23_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LR_58_0 hbr_LRLL_59_0 hbr_L_14_0_ge hbr_LRLLL_47_0_ge
          ·
            have hbr_LRLL_59_0_ge : (1 : Int) ≤ x ⟨58, by decide⟩ := by omega
            by_cases hbr_LRLLR_22_0 : x ⟨21, by decide⟩ ≤ 0
            ·
              by_cases hbr_LRLLRL_16_0 : x ⟨15, by decide⟩ ≤ 0
              ·
                by_cases hbr_LRLLRLL_52_0 : x ⟨51, by decide⟩ ≤ 0
                ·
                  exact leaf24_infeasible_416 x hroot hbr_root_7_0 hbr_LRLLRL_16_0 hbr_LRL_18_0 hbr_LRLLR_22_0 hbr_LRLLRLL_52_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRLL_59_0_ge
                ·
                  have hbr_LRLLRLL_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
                  exact leaf25_infeasible_416 x hroot hbr_root_7_0 hbr_LRLLRL_16_0 hbr_LRL_18_0 hbr_LRLLR_22_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRLLRLL_52_0_ge hbr_LRLL_59_0_ge
              ·
                have hbr_LRLLRL_16_0_ge : (1 : Int) ≤ x ⟨15, by decide⟩ := by omega
                exact leaf26_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LRLLR_22_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRLLRL_16_0_ge hbr_LRLL_59_0_ge
            ·
              have hbr_LRLLR_22_0_ge : (1 : Int) ≤ x ⟨21, by decide⟩ := by omega
              by_cases hbr_LRLLRR_52_0 : x ⟨51, by decide⟩ ≤ 0
              ·
                exact leaf27_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LRLLRR_52_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRLLR_22_0_ge hbr_LRLL_59_0_ge
              ·
                have hbr_LRLLRR_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
                exact leaf28_infeasible_416 x hroot hbr_root_7_0 hbr_LRL_18_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRLLR_22_0_ge hbr_LRLLRR_52_0_ge hbr_LRLL_59_0_ge
        ·
          have hbr_LRL_18_0_ge : (1 : Int) ≤ x ⟨17, by decide⟩ := by omega
          exact leaf29_infeasible_416 x hroot hbr_root_7_0 hbr_LR_58_0 hbr_L_14_0_ge hbr_LRL_18_0_ge
      ·
        have hbr_LR_58_0_ge : (1 : Int) ≤ x ⟨57, by decide⟩ := by omega
        by_cases hbr_LRR_56_0 : x ⟨55, by decide⟩ ≤ 0
        ·
          by_cases hbr_LRRL_12_1 : x ⟨11, by decide⟩ ≤ 1
          ·
            by_cases hbr_LRRLL_52_0 : x ⟨51, by decide⟩ ≤ 0
            ·
              exact leaf30_infeasible_416 x hroot hbr_root_7_0 hbr_LRRL_12_1 hbr_LRRLL_52_0 hbr_LRR_56_0 hbr_L_14_0_ge hbr_LR_58_0_ge
            ·
              have hbr_LRRLL_52_0_ge : (1 : Int) ≤ x ⟨51, by decide⟩ := by omega
              by_cases hbr_LRRLLR_53_0 : x ⟨52, by decide⟩ ≤ 0
              ·
                by_cases hbr_LRRLLRL_1_2 : x ⟨0, by decide⟩ ≤ 2
                ·
                  exact leaf31_infeasible_416 x hroot hbr_LRRLLRL_1_2 hbr_root_7_0 hbr_LRRL_12_1 hbr_LRRLLR_53_0 hbr_LRR_56_0 hbr_L_14_0_ge hbr_LRRLL_52_0_ge hbr_LR_58_0_ge
                ·
                  have hbr_LRRLLRL_1_2_ge : (3 : Int) ≤ x ⟨0, by decide⟩ := by omega
                  exact leaf32_infeasible_416 x hroot hbr_root_7_0 hbr_LRRL_12_1 hbr_LRRLLR_53_0 hbr_LRR_56_0 hbr_LRRLLRL_1_2_ge hbr_L_14_0_ge hbr_LRRLL_52_0_ge hbr_LR_58_0_ge
              ·
                have hbr_LRRLLR_53_0_ge : (1 : Int) ≤ x ⟨52, by decide⟩ := by omega
                exact leaf33_infeasible_416 x hroot hbr_root_7_0 hbr_LRRL_12_1 hbr_LRR_56_0 hbr_L_14_0_ge hbr_LRRLL_52_0_ge hbr_LRRLLR_53_0_ge hbr_LR_58_0_ge
          ·
            have hbr_LRRL_12_1_ge : (2 : Int) ≤ x ⟨11, by decide⟩ := by omega
            exact leaf34_infeasible_416 x hroot hbr_root_7_0 hbr_LRR_56_0 hbr_LRRL_12_1_ge hbr_L_14_0_ge hbr_LR_58_0_ge
        ·
          have hbr_LRR_56_0_ge : (1 : Int) ≤ x ⟨55, by decide⟩ := by omega
          exact leaf35_infeasible_416 x hroot hbr_root_7_0 hbr_L_14_0_ge hbr_LRR_56_0_ge hbr_LR_58_0_ge
  ·
    have hbr_root_7_0_ge : (1 : Int) ≤ x ⟨6, by decide⟩ := by omega
    by_cases hbr_R_47_0 : x ⟨46, by decide⟩ ≤ 0
    ·
      exact leaf36_infeasible_416 x hroot hbr_R_47_0 hbr_root_7_0_ge
    ·
      have hbr_R_47_0_ge : (1 : Int) ≤ x ⟨46, by decide⟩ := by omega
      exact leaf37_infeasible_416 x hroot hbr_root_7_0_ge hbr_R_47_0_ge

end QiushiMatmul
