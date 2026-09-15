
-- Auto-generated orbit 486 data module (computable block-dispatch)
-- 40 live vars, 169 occ rows, target=18, block_size=40

import Mathlib
import QiushiOccupationSoundness

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace QiushiMatmul
abbrev NLIVE_486 := 40
abbrev NOCC_486 := 169

private def occRow_486_0 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0)
private def occRow_486_1 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0)
private def occRow_486_2 (j : Fin 40) : Int := (if j.val = 8 then 1 else 0)
private def occRow_486_3 (j : Fin 40) : Int := (if j.val = 28 then 1 else 0)
private def occRow_486_4 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_5 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_6 (j : Fin 40) : Int := (if j.val = 39 then 1 else 0)
private def occRow_486_7 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0)
private def occRow_486_8 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0)
private def occRow_486_9 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 25 then 1 else 0)
private def occRow_486_10 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0)
private def occRow_486_11 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_12 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0)
private def occRow_486_13 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_14 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
private def occRow_486_15 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_16 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_17 (j : Fin 40) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_18 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_19 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_20 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_21 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0)
private def occRow_486_22 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_23 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_24 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_25 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_26 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_27 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_28 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_29 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_30 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_31 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_32 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_33 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_34 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_35 (j : Fin 40) : Int := (if j.val = 39 then 1 else 0)
private def occRow_486_36 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0)
private def occRow_486_37 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0)
private def occRow_486_38 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_39 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_40 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_41 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0)
private def occRow_486_42 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_43 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_44 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_45 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_46 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_47 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 29 then 1 else 0)
private def occRow_486_48 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_49 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_50 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_51 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_52 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_53 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_54 (j : Fin 40) : Int := (if j.val = 17 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_55 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0)
private def occRow_486_56 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0)
private def occRow_486_57 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0)
private def occRow_486_58 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_59 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_60 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_61 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_62 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_63 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_64 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_65 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_66 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_67 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_68 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_69 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_70 (j : Fin 40) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 27 then 1 else 0)
private def occRow_486_71 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_72 (j : Fin 40) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_73 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 25 then 1 else 0)
private def occRow_486_74 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0)
private def occRow_486_75 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0)
private def occRow_486_76 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_77 (j : Fin 40) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_78 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_79 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_80 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_81 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_82 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_83 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_84 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_85 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_86 (j : Fin 40) : Int := (if j.val = 28 then 1 else 0)
private def occRow_486_87 (j : Fin 40) : Int := (if j.val = 12 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_88 (j : Fin 40) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_89 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_90 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_91 (j : Fin 40) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_92 (j : Fin 40) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_93 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_94 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_95 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_96 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_97 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_98 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_99 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_100 (j : Fin 40) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_101 (j : Fin 40) : Int := (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_102 (j : Fin 40) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_103 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_104 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_105 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_106 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_107 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_108 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_109 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_110 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_111 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_112 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_113 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 1 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_114 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0)
private def occRow_486_115 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 33 then 1 else 0)
private def occRow_486_116 (j : Fin 40) : Int := (if j.val = 10 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_117 (j : Fin 40) : Int := (if j.val = 9 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_118 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_119 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_120 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_121 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_122 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_123 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_124 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 36 then 1 else 0)
private def occRow_486_125 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0)
private def occRow_486_126 (j : Fin 40) : Int := (if j.val = 13 then 1 else 0) + (if j.val = 26 then 1 else 0)
private def occRow_486_127 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 32 then 1 else 0)
private def occRow_486_128 (j : Fin 40) : Int := (if j.val = 18 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_129 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 21 then 1 else 0)
private def occRow_486_130 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 25 then 1 else 0)
private def occRow_486_131 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_132 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_133 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_134 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_135 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_136 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_137 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_138 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_139 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 37 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_140 (j : Fin 40) : Int := (if j.val = 8 then 1 else 0)
private def occRow_486_141 (j : Fin 40) : Int := (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_142 (j : Fin 40) : Int := (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 30 then 1 else 0)
private def occRow_486_143 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0)
private def occRow_486_144 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_145 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 25 then 1 else 0)
private def occRow_486_146 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 30 then 1 else 0)
private def occRow_486_147 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 31 then 1 else 0)
private def occRow_486_148 (j : Fin 40) : Int := (if j.val = 3 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 29 then 1 else 0)
private def occRow_486_149 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_150 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_151 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_152 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 2 then 1 else 0) + (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_153 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_154 (j : Fin 40) : Int := (if j.val = 24 then 1 else 0) + (if j.val = 27 then 1 else 0)
private def occRow_486_155 (j : Fin 40) : Int := (if j.val = 11 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_156 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 13 then 1 else 0)
private def occRow_486_157 (j : Fin 40) : Int := (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_158 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_159 (j : Fin 40) : Int := (if j.val = 7 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 35 then 1 else 0) + (if j.val = 38 then 1 else 0)
private def occRow_486_160 (j : Fin 40) : Int := (if j.val = 5 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 38 then 1 else 0) + (if j.val = 39 then 1 else 0)
private def occRow_486_161 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
private def occRow_486_162 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 26 then 1 else 0) + (if j.val = 27 then 1 else 0) + (if j.val = 28 then 1 else 0)
private def occRow_486_163 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 5 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 25 then 1 else 0) + (if j.val = 28 then 1 else 0)
private def occRow_486_164 (j : Fin 40) : Int := (if j.val = 0 then 1 else 0) + (if j.val = 11 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 14 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 33 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_165 (j : Fin 40) : Int := (if j.val = 1 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 18 then 1 else 0) + (if j.val = 23 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 32 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 37 then 1 else 0)
private def occRow_486_166 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 6 then 1 else 0) + (if j.val = 9 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 35 then 1 else 0)
private def occRow_486_167 (j : Fin 40) : Int := (if j.val = 4 then 1 else 0) + (if j.val = 7 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 16 then 1 else 0) + (if j.val = 20 then 1 else 0) + (if j.val = 21 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 28 then 1 else 0) + (if j.val = 30 then 1 else 0) + (if j.val = 34 then 1 else 0)
private def occRow_486_168 (j : Fin 40) : Int := (if j.val = 2 then 1 else 0) + (if j.val = 3 then 1 else 0) + (if j.val = 8 then 1 else 0) + (if j.val = 10 then 1 else 0) + (if j.val = 12 then 1 else 0) + (if j.val = 13 then 1 else 0) + (if j.val = 15 then 1 else 0) + (if j.val = 17 then 1 else 0) + (if j.val = 19 then 1 else 0) + (if j.val = 22 then 1 else 0) + (if j.val = 24 then 1 else 0) + (if j.val = 29 then 1 else 0) + (if j.val = 31 then 1 else 0) + (if j.val = 34 then 1 else 0) + (if j.val = 36 then 1 else 0) + (if j.val = 39 then 1 else 0)

private def occCoeffBlock_486_00 (off : Nat) (j : Fin 40) : Int :=
  match off with
  | 0 => occRow_486_0 j
  | 1 => occRow_486_1 j
  | 2 => occRow_486_2 j
  | 3 => occRow_486_3 j
  | 4 => occRow_486_4 j
  | 5 => occRow_486_5 j
  | 6 => occRow_486_6 j
  | 7 => occRow_486_7 j
  | 8 => occRow_486_8 j
  | 9 => occRow_486_9 j
  | 10 => occRow_486_10 j
  | 11 => occRow_486_11 j
  | 12 => occRow_486_12 j
  | 13 => occRow_486_13 j
  | 14 => occRow_486_14 j
  | 15 => occRow_486_15 j
  | 16 => occRow_486_16 j
  | 17 => occRow_486_17 j
  | 18 => occRow_486_18 j
  | 19 => occRow_486_19 j
  | 20 => occRow_486_20 j
  | 21 => occRow_486_21 j
  | 22 => occRow_486_22 j
  | 23 => occRow_486_23 j
  | 24 => occRow_486_24 j
  | 25 => occRow_486_25 j
  | 26 => occRow_486_26 j
  | 27 => occRow_486_27 j
  | 28 => occRow_486_28 j
  | 29 => occRow_486_29 j
  | 30 => occRow_486_30 j
  | 31 => occRow_486_31 j
  | 32 => occRow_486_32 j
  | 33 => occRow_486_33 j
  | 34 => occRow_486_34 j
  | 35 => occRow_486_35 j
  | 36 => occRow_486_36 j
  | 37 => occRow_486_37 j
  | 38 => occRow_486_38 j
  | 39 => occRow_486_39 j
  | _ => 0

private def occCoeffBlock_486_01 (off : Nat) (j : Fin 40) : Int :=
  match off with
  | 0 => occRow_486_40 j
  | 1 => occRow_486_41 j
  | 2 => occRow_486_42 j
  | 3 => occRow_486_43 j
  | 4 => occRow_486_44 j
  | 5 => occRow_486_45 j
  | 6 => occRow_486_46 j
  | 7 => occRow_486_47 j
  | 8 => occRow_486_48 j
  | 9 => occRow_486_49 j
  | 10 => occRow_486_50 j
  | 11 => occRow_486_51 j
  | 12 => occRow_486_52 j
  | 13 => occRow_486_53 j
  | 14 => occRow_486_54 j
  | 15 => occRow_486_55 j
  | 16 => occRow_486_56 j
  | 17 => occRow_486_57 j
  | 18 => occRow_486_58 j
  | 19 => occRow_486_59 j
  | 20 => occRow_486_60 j
  | 21 => occRow_486_61 j
  | 22 => occRow_486_62 j
  | 23 => occRow_486_63 j
  | 24 => occRow_486_64 j
  | 25 => occRow_486_65 j
  | 26 => occRow_486_66 j
  | 27 => occRow_486_67 j
  | 28 => occRow_486_68 j
  | 29 => occRow_486_69 j
  | 30 => occRow_486_70 j
  | 31 => occRow_486_71 j
  | 32 => occRow_486_72 j
  | 33 => occRow_486_73 j
  | 34 => occRow_486_74 j
  | 35 => occRow_486_75 j
  | 36 => occRow_486_76 j
  | 37 => occRow_486_77 j
  | 38 => occRow_486_78 j
  | 39 => occRow_486_79 j
  | _ => 0

private def occCoeffBlock_486_02 (off : Nat) (j : Fin 40) : Int :=
  match off with
  | 0 => occRow_486_80 j
  | 1 => occRow_486_81 j
  | 2 => occRow_486_82 j
  | 3 => occRow_486_83 j
  | 4 => occRow_486_84 j
  | 5 => occRow_486_85 j
  | 6 => occRow_486_86 j
  | 7 => occRow_486_87 j
  | 8 => occRow_486_88 j
  | 9 => occRow_486_89 j
  | 10 => occRow_486_90 j
  | 11 => occRow_486_91 j
  | 12 => occRow_486_92 j
  | 13 => occRow_486_93 j
  | 14 => occRow_486_94 j
  | 15 => occRow_486_95 j
  | 16 => occRow_486_96 j
  | 17 => occRow_486_97 j
  | 18 => occRow_486_98 j
  | 19 => occRow_486_99 j
  | 20 => occRow_486_100 j
  | 21 => occRow_486_101 j
  | 22 => occRow_486_102 j
  | 23 => occRow_486_103 j
  | 24 => occRow_486_104 j
  | 25 => occRow_486_105 j
  | 26 => occRow_486_106 j
  | 27 => occRow_486_107 j
  | 28 => occRow_486_108 j
  | 29 => occRow_486_109 j
  | 30 => occRow_486_110 j
  | 31 => occRow_486_111 j
  | 32 => occRow_486_112 j
  | 33 => occRow_486_113 j
  | 34 => occRow_486_114 j
  | 35 => occRow_486_115 j
  | 36 => occRow_486_116 j
  | 37 => occRow_486_117 j
  | 38 => occRow_486_118 j
  | 39 => occRow_486_119 j
  | _ => 0

private def occCoeffBlock_486_03 (off : Nat) (j : Fin 40) : Int :=
  match off with
  | 0 => occRow_486_120 j
  | 1 => occRow_486_121 j
  | 2 => occRow_486_122 j
  | 3 => occRow_486_123 j
  | 4 => occRow_486_124 j
  | 5 => occRow_486_125 j
  | 6 => occRow_486_126 j
  | 7 => occRow_486_127 j
  | 8 => occRow_486_128 j
  | 9 => occRow_486_129 j
  | 10 => occRow_486_130 j
  | 11 => occRow_486_131 j
  | 12 => occRow_486_132 j
  | 13 => occRow_486_133 j
  | 14 => occRow_486_134 j
  | 15 => occRow_486_135 j
  | 16 => occRow_486_136 j
  | 17 => occRow_486_137 j
  | 18 => occRow_486_138 j
  | 19 => occRow_486_139 j
  | 20 => occRow_486_140 j
  | 21 => occRow_486_141 j
  | 22 => occRow_486_142 j
  | 23 => occRow_486_143 j
  | 24 => occRow_486_144 j
  | 25 => occRow_486_145 j
  | 26 => occRow_486_146 j
  | 27 => occRow_486_147 j
  | 28 => occRow_486_148 j
  | 29 => occRow_486_149 j
  | 30 => occRow_486_150 j
  | 31 => occRow_486_151 j
  | 32 => occRow_486_152 j
  | 33 => occRow_486_153 j
  | 34 => occRow_486_154 j
  | 35 => occRow_486_155 j
  | 36 => occRow_486_156 j
  | 37 => occRow_486_157 j
  | 38 => occRow_486_158 j
  | 39 => occRow_486_159 j
  | _ => 0

private def occCoeffBlock_486_04 (off : Nat) (j : Fin 40) : Int :=
  match off with
  | 0 => occRow_486_160 j
  | 1 => occRow_486_161 j
  | 2 => occRow_486_162 j
  | 3 => occRow_486_163 j
  | 4 => occRow_486_164 j
  | 5 => occRow_486_165 j
  | 6 => occRow_486_166 j
  | 7 => occRow_486_167 j
  | 8 => occRow_486_168 j
  | _ => 0

def occCoeff_486 (i : Fin 169) (j : Fin 40) : Int :=
  match i.val / 40 with
  | 0 => occCoeffBlock_486_00 (i.val % 40) j
  | 1 => occCoeffBlock_486_01 (i.val % 40) j
  | 2 => occCoeffBlock_486_02 (i.val % 40) j
  | 3 => occCoeffBlock_486_03 (i.val % 40) j
  | 4 => occCoeffBlock_486_04 (i.val % 40) j
  | _ => 0

private def occRhsBlock_486_00 (off : Nat) : Int :=
  match off with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | 21 => 3
  | 22 => 3
  | 23 => 3
  | 24 => 3
  | 25 => 3
  | 26 => 6
  | 27 => 6
  | 28 => 6
  | 29 => 6
  | 30 => 6
  | 31 => 6
  | 32 => 6
  | 33 => 9
  | 34 => 9
  | 35 => 1
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 3
  | _ => 0

private def occRhsBlock_486_01 (off : Nat) : Int :=
  match off with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | 11 => 9
  | 12 => 9
  | 13 => 9
  | 14 => 1
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | 21 => 3
  | 22 => 3
  | 23 => 3
  | 24 => 3
  | 25 => 6
  | 26 => 6
  | 27 => 6
  | 28 => 9
  | 29 => 9
  | 30 => 1
  | 31 => 1
  | 32 => 1
  | 33 => 3
  | 34 => 3
  | 35 => 3
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 4
  | _ => 0

private def occRhsBlock_486_02 (off : Nat) : Int :=
  match off with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 9
  | 5 => 9
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 4
  | 14 => 6
  | 15 => 6
  | 16 => 6
  | 17 => 9
  | 18 => 9
  | 19 => 3
  | 20 => 3
  | 21 => 3
  | 22 => 3
  | 23 => 3
  | 24 => 6
  | 25 => 6
  | 26 => 6
  | 27 => 6
  | 28 => 9
  | 29 => 9
  | 30 => 9
  | 31 => 9
  | 32 => 9
  | 33 => 9
  | 34 => 3
  | 35 => 3
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 3
  | _ => 0

private def occRhsBlock_486_03 (off : Nat) : Int :=
  match off with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 9
  | 4 => 9
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 4
  | 15 => 6
  | 16 => 6
  | 17 => 6
  | 18 => 6
  | 19 => 9
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 3
  | 24 => 3
  | 25 => 4
  | 26 => 4
  | 27 => 4
  | 28 => 4
  | 29 => 6
  | 30 => 9
  | 31 => 9
  | 32 => 9
  | 33 => 9
  | 34 => 1
  | 35 => 1
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 3
  | _ => 0

private def occRhsBlock_486_04 (off : Nat) : Int :=
  match off with
  | 0 => 3
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 9
  | _ => 0

def occRhs_486 (i : Fin 169) : Int :=
  match i.val / 40 with
  | 0 => occRhsBlock_486_00 (i.val % 40)
  | 1 => occRhsBlock_486_01 (i.val % 40)
  | 2 => occRhsBlock_486_02 (i.val % 40)
  | 3 => occRhsBlock_486_03 (i.val % 40)
  | 4 => occRhsBlock_486_04 (i.val % 40)
  | _ => 0

def S_486 : OccSys 40 169 := {
  occCoeff := occCoeff_486,
  occRhs := occRhs_486,
  target := 18
}

end QiushiMatmul
