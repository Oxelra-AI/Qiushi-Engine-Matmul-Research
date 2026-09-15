import QiushiFrozenLabelCollision00
import QiushiFrozenLabelCollision01
import QiushiFrozenLabelCollision02
import QiushiFrozenLabelCollision03
import QiushiFrozenLabelCollision04
import QiushiFrozenLabelCollision05
import QiushiFrozenLabelCollision06
import QiushiFrozenLabelCollision07
import QiushiFrozenLabelCollision08
import QiushiFrozenLabelKeysData

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collisionPairs_no_overlap (i j : Fin 496) (hc : (i.val, j.val) ∈ collisionPairs)
    (W : Submodule F2 Mat3) (hi : frozenWangTable.OrbitImage i W)
    (hj : frozenWangTable.OrbitImage j W) : False := by
  simp only [collisionPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
  rcases hc with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35
  · obtain ⟨ha, hb⟩ := h00
    have hei : i = 129 := Fin.ext ha
    have hej : j = 133 := Fin.ext hb
    subst i j
    exact collision_pair_00 (planeIncidence_eq_of_overlap 6 129 133 W hi hj)
  · obtain ⟨ha, hb⟩ := h01
    have hei : i = 262 := Fin.ext ha
    have hej : j = 272 := Fin.ext hb
    subst i j
    exact collision_pair_01 (planeIncidence_eq_of_overlap 6 262 272 W hi hj)
  · obtain ⟨ha, hb⟩ := h02
    have hei : i = 264 := Fin.ext ha
    have hej : j = 266 := Fin.ext hb
    subst i j
    exact collision_pair_02 (planeIncidence_eq_of_overlap 1 264 266 W hi hj)
  · obtain ⟨ha, hb⟩ := h03
    have hei : i = 281 := Fin.ext ha
    have hej : j = 325 := Fin.ext hb
    subst i j
    exact collision_pair_03 (planeIncidence_eq_of_overlap 6 281 325 W hi hj)
  · obtain ⟨ha, hb⟩ := h04
    have hei : i = 282 := Fin.ext ha
    have hej : j = 326 := Fin.ext hb
    subst i j
    exact collision_pair_04 (planeIncidence_eq_of_overlap 6 282 326 W hi hj)
  · obtain ⟨ha, hb⟩ := h05
    have hei : i = 286 := Fin.ext ha
    have hej : j = 290 := Fin.ext hb
    subst i j
    exact collision_pair_05 (planeIncidence_eq_of_overlap 1 286 290 W hi hj)
  · obtain ⟨ha, hb⟩ := h06
    have hei : i = 289 := Fin.ext ha
    have hej : j = 360 := Fin.ext hb
    subst i j
    exact collision_pair_06 (planeIncidence_eq_of_overlap 1 289 360 W hi hj)
  · obtain ⟨ha, hb⟩ := h07
    have hei : i = 299 := Fin.ext ha
    have hej : j = 331 := Fin.ext hb
    subst i j
    exact collision_pair_07 (planeIncidence_eq_of_overlap 1 299 331 W hi hj)
  · obtain ⟨ha, hb⟩ := h08
    have hei : i = 312 := Fin.ext ha
    have hej : j = 352 := Fin.ext hb
    subst i j
    exact collision_pair_08 (planeIncidence_eq_of_overlap 6 312 352 W hi hj)
  · obtain ⟨ha, hb⟩ := h09
    have hei : i = 318 := Fin.ext ha
    have hej : j = 360 := Fin.ext hb
    subst i j
    exact collision_pair_09 (planeIncidence_eq_of_overlap 1 318 360 W hi hj)
  · obtain ⟨ha, hb⟩ := h10
    have hei : i = 320 := Fin.ext ha
    have hej : j = 322 := Fin.ext hb
    subst i j
    exact collision_pair_10 (planeIncidence_eq_of_overlap 6 320 322 W hi hj)
  · obtain ⟨ha, hb⟩ := h11
    have hei : i = 331 := Fin.ext ha
    have hej : j = 332 := Fin.ext hb
    subst i j
    exact collision_pair_11 (planeIncidence_eq_of_overlap 6 331 332 W hi hj)
  · obtain ⟨ha, hb⟩ := h12
    have hei : i = 352 := Fin.ext ha
    have hej : j = 355 := Fin.ext hb
    subst i j
    exact collision_pair_12 (planeIncidence_eq_of_overlap 6 352 355 W hi hj)
  · obtain ⟨ha, hb⟩ := h13
    have hei : i = 352 := Fin.ext ha
    have hej : j = 356 := Fin.ext hb
    subst i j
    exact collision_pair_13 (planeIncidence_eq_of_overlap 6 352 356 W hi hj)
  · obtain ⟨ha, hb⟩ := h14
    have hei : i = 353 := Fin.ext ha
    have hej : j = 360 := Fin.ext hb
    subst i j
    exact collision_pair_14 (planeIncidence_eq_of_overlap 6 353 360 W hi hj)
  · obtain ⟨ha, hb⟩ := h15
    have hei : i = 364 := Fin.ext ha
    have hej : j = 365 := Fin.ext hb
    subst i j
    exact collision_pair_15 (planeIncidence_eq_of_overlap 9 364 365 W hi hj)
  · obtain ⟨ha, hb⟩ := h16
    have hei : i = 364 := Fin.ext ha
    have hej : j = 373 := Fin.ext hb
    subst i j
    exact collision_pair_16 (planeIncidence_eq_of_overlap 6 364 373 W hi hj)
  · obtain ⟨ha, hb⟩ := h17
    have hei : i = 365 := Fin.ext ha
    have hej : j = 370 := Fin.ext hb
    subst i j
    exact collision_pair_17 (planeIncidence_eq_of_overlap 8 365 370 W hi hj)
  · obtain ⟨ha, hb⟩ := h18
    have hei : i = 370 := Fin.ext ha
    have hej : j = 373 := Fin.ext hb
    subst i j
    exact collision_pair_18 (planeIncidence_eq_of_overlap 6 370 373 W hi hj)
  · obtain ⟨ha, hb⟩ := h19
    have hei : i = 380 := Fin.ext ha
    have hej : j = 381 := Fin.ext hb
    subst i j
    exact collision_pair_19 (planeIncidence_eq_of_overlap 6 380 381 W hi hj)
  · obtain ⟨ha, hb⟩ := h20
    have hei : i = 381 := Fin.ext ha
    have hej : j = 382 := Fin.ext hb
    subst i j
    exact collision_pair_20 (planeIncidence_eq_of_overlap 6 381 382 W hi hj)
  · obtain ⟨ha, hb⟩ := h21
    have hei : i = 381 := Fin.ext ha
    have hej : j = 387 := Fin.ext hb
    subst i j
    exact collision_pair_21 (planeIncidence_eq_of_overlap 6 381 387 W hi hj)
  · obtain ⟨ha, hb⟩ := h22
    have hei : i = 381 := Fin.ext ha
    have hej : j = 388 := Fin.ext hb
    subst i j
    exact collision_pair_22 (planeIncidence_eq_of_overlap 6 381 388 W hi hj)
  · obtain ⟨ha, hb⟩ := h23
    have hei : i = 381 := Fin.ext ha
    have hej : j = 394 := Fin.ext hb
    subst i j
    exact collision_pair_23 (planeIncidence_eq_of_overlap 6 381 394 W hi hj)
  · obtain ⟨ha, hb⟩ := h24
    have hei : i = 381 := Fin.ext ha
    have hej : j = 399 := Fin.ext hb
    subst i j
    exact collision_pair_24 (planeIncidence_eq_of_overlap 6 381 399 W hi hj)
  · obtain ⟨ha, hb⟩ := h25
    have hei : i = 418 := Fin.ext ha
    have hej : j = 420 := Fin.ext hb
    subst i j
    exact collision_pair_25 (planeIncidence_eq_of_overlap 1 418 420 W hi hj)
  · obtain ⟨ha, hb⟩ := h26
    have hei : i = 418 := Fin.ext ha
    have hej : j = 425 := Fin.ext hb
    subst i j
    exact collision_pair_26 (planeIncidence_eq_of_overlap 7 418 425 W hi hj)
  · obtain ⟨ha, hb⟩ := h27
    have hei : i = 420 := Fin.ext ha
    have hej : j = 435 := Fin.ext hb
    subst i j
    exact collision_pair_27 (planeIncidence_eq_of_overlap 6 420 435 W hi hj)
  · obtain ⟨ha, hb⟩ := h28
    have hei : i = 420 := Fin.ext ha
    have hej : j = 437 := Fin.ext hb
    subst i j
    exact collision_pair_28 (planeIncidence_eq_of_overlap 1 420 437 W hi hj)
  · obtain ⟨ha, hb⟩ := h29
    have hei : i = 423 := Fin.ext ha
    have hej : j = 426 := Fin.ext hb
    subst i j
    exact collision_pair_29 (planeIncidence_eq_of_overlap 8 423 426 W hi hj)
  · obtain ⟨ha, hb⟩ := h30
    have hei : i = 425 := Fin.ext ha
    have hej : j = 435 := Fin.ext hb
    subst i j
    exact collision_pair_30 (planeIncidence_eq_of_overlap 6 425 435 W hi hj)
  · obtain ⟨ha, hb⟩ := h31
    have hei : i = 425 := Fin.ext ha
    have hej : j = 437 := Fin.ext hb
    subst i j
    exact collision_pair_31 (planeIncidence_eq_of_overlap 1 425 437 W hi hj)
  · obtain ⟨ha, hb⟩ := h32
    have hei : i = 426 := Fin.ext ha
    have hej : j = 439 := Fin.ext hb
    subst i j
    exact collision_pair_32 (planeIncidence_eq_of_overlap 1 426 439 W hi hj)
  · obtain ⟨ha, hb⟩ := h33
    have hei : i = 426 := Fin.ext ha
    have hej : j = 440 := Fin.ext hb
    subst i j
    exact collision_pair_33 (planeIncidence_eq_of_overlap 1 426 440 W hi hj)
  · obtain ⟨ha, hb⟩ := h34
    have hei : i = 460 := Fin.ext ha
    have hej : j = 463 := Fin.ext hb
    subst i j
    exact collision_pair_34 (planeIncidence_eq_of_overlap 9 460 463 W hi hj)
  · obtain ⟨ha, hb⟩ := h35
    have hei : i = 460 := Fin.ext ha
    have hej : j = 469 := Fin.ext hb
    subst i j
    exact collision_pair_35 (planeIncidence_eq_of_overlap 8 460 469 W hi hj)

end QiushiMatmul.FrozenLabel
