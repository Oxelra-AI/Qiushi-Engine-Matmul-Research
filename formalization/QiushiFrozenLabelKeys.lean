import QiushiFrozenLabelKeys00
import QiushiFrozenLabelKeys01
import QiushiFrozenLabelKeys02
import QiushiFrozenLabelKeys03
import QiushiFrozenLabelKeys04
import QiushiFrozenLabelKeys05
import QiushiFrozenLabelKeys06
import QiushiFrozenLabelKeys07
import QiushiFrozenLabelKeys08
import QiushiFrozenLabelKeys09
import QiushiFrozenLabelKeys10
import QiushiFrozenLabelKeys11
import QiushiFrozenLabelKeys12
import QiushiFrozenLabelKeys13
import QiushiFrozenLabelKeys14
import QiushiFrozenLabelKeys15
import QiushiFrozenLabelKeys16
import QiushiFrozenLabelKeys17
import QiushiFrozenLabelKeys18
import QiushiFrozenLabelKeys19
import QiushiFrozenLabelKeys20
import QiushiFrozenLabelKeys21
import QiushiFrozenLabelKeys22
import QiushiFrozenLabelKeys23
import QiushiFrozenLabelKeys24
import QiushiFrozenLabelKeys25
import QiushiFrozenLabelKeys26
import QiushiFrozenLabelKeys27
import QiushiFrozenLabelKeys28
import QiushiFrozenLabelKeys29
import QiushiFrozenLabelKeys30
import QiushiFrozenLabelKeys31
import QiushiFrozenLabelKeys32
import QiushiFrozenLabelKeys33
import QiushiFrozenLabelKeys34
import QiushiFrozenLabelKeys35
import QiushiFrozenLabelKeys36
import QiushiFrozenLabelKeys37
import QiushiFrozenLabelKeys38
import QiushiFrozenLabelSeparation

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem signatureFixture_correct (i : Fin 496) :
    refinedSignature (frozenWangBasis i) = signatureFixture i := by
  by_cases h0 : i.val < 8
  · let k : Fin 8 := ⟨i.val - 0, by omega⟩
    have he : (⟨0 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_00 k
  by_cases h1 : i.val < 16
  · let k : Fin 8 := ⟨i.val - 8, by omega⟩
    have he : (⟨8 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_01 k
  by_cases h2 : i.val < 24
  · let k : Fin 8 := ⟨i.val - 16, by omega⟩
    have he : (⟨16 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_02 k
  by_cases h3 : i.val < 32
  · let k : Fin 8 := ⟨i.val - 24, by omega⟩
    have he : (⟨24 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_03 k
  by_cases h4 : i.val < 40
  · let k : Fin 8 := ⟨i.val - 32, by omega⟩
    have he : (⟨32 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_04 k
  by_cases h5 : i.val < 48
  · let k : Fin 8 := ⟨i.val - 40, by omega⟩
    have he : (⟨40 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_05 k
  by_cases h6 : i.val < 56
  · let k : Fin 8 := ⟨i.val - 48, by omega⟩
    have he : (⟨48 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_06 k
  by_cases h7 : i.val < 64
  · let k : Fin 8 := ⟨i.val - 56, by omega⟩
    have he : (⟨56 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_07 k
  by_cases h8 : i.val < 72
  · let k : Fin 8 := ⟨i.val - 64, by omega⟩
    have he : (⟨64 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_08 k
  by_cases h9 : i.val < 80
  · let k : Fin 8 := ⟨i.val - 72, by omega⟩
    have he : (⟨72 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_09 k
  by_cases h10 : i.val < 88
  · let k : Fin 8 := ⟨i.val - 80, by omega⟩
    have he : (⟨80 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_10 k
  by_cases h11 : i.val < 96
  · let k : Fin 8 := ⟨i.val - 88, by omega⟩
    have he : (⟨88 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_11 k
  by_cases h12 : i.val < 104
  · let k : Fin 8 := ⟨i.val - 96, by omega⟩
    have he : (⟨96 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_12 k
  by_cases h13 : i.val < 112
  · let k : Fin 8 := ⟨i.val - 104, by omega⟩
    have he : (⟨104 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_13 k
  by_cases h14 : i.val < 120
  · let k : Fin 8 := ⟨i.val - 112, by omega⟩
    have he : (⟨112 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_14 k
  by_cases h15 : i.val < 128
  · let k : Fin 8 := ⟨i.val - 120, by omega⟩
    have he : (⟨120 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_15 k
  by_cases h16 : i.val < 144
  · let k : Fin 16 := ⟨i.val - 128, by omega⟩
    have he : (⟨128 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_16 k
  by_cases h17 : i.val < 160
  · let k : Fin 16 := ⟨i.val - 144, by omega⟩
    have he : (⟨144 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_17 k
  by_cases h18 : i.val < 176
  · let k : Fin 16 := ⟨i.val - 160, by omega⟩
    have he : (⟨160 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_18 k
  by_cases h19 : i.val < 192
  · let k : Fin 16 := ⟨i.val - 176, by omega⟩
    have he : (⟨176 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_19 k
  by_cases h20 : i.val < 208
  · let k : Fin 16 := ⟨i.val - 192, by omega⟩
    have he : (⟨192 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_20 k
  by_cases h21 : i.val < 224
  · let k : Fin 16 := ⟨i.val - 208, by omega⟩
    have he : (⟨208 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_21 k
  by_cases h22 : i.val < 240
  · let k : Fin 16 := ⟨i.val - 224, by omega⟩
    have he : (⟨224 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_22 k
  by_cases h23 : i.val < 256
  · let k : Fin 16 := ⟨i.val - 240, by omega⟩
    have he : (⟨240 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_23 k
  by_cases h24 : i.val < 272
  · let k : Fin 16 := ⟨i.val - 256, by omega⟩
    have he : (⟨256 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_24 k
  by_cases h25 : i.val < 288
  · let k : Fin 16 := ⟨i.val - 272, by omega⟩
    have he : (⟨272 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_25 k
  by_cases h26 : i.val < 304
  · let k : Fin 16 := ⟨i.val - 288, by omega⟩
    have he : (⟨288 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_26 k
  by_cases h27 : i.val < 320
  · let k : Fin 16 := ⟨i.val - 304, by omega⟩
    have he : (⟨304 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_27 k
  by_cases h28 : i.val < 336
  · let k : Fin 16 := ⟨i.val - 320, by omega⟩
    have he : (⟨320 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_28 k
  by_cases h29 : i.val < 352
  · let k : Fin 16 := ⟨i.val - 336, by omega⟩
    have he : (⟨336 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_29 k
  by_cases h30 : i.val < 368
  · let k : Fin 16 := ⟨i.val - 352, by omega⟩
    have he : (⟨352 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_30 k
  by_cases h31 : i.val < 384
  · let k : Fin 16 := ⟨i.val - 368, by omega⟩
    have he : (⟨368 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_31 k
  by_cases h32 : i.val < 400
  · let k : Fin 16 := ⟨i.val - 384, by omega⟩
    have he : (⟨384 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_32 k
  by_cases h33 : i.val < 416
  · let k : Fin 16 := ⟨i.val - 400, by omega⟩
    have he : (⟨400 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_33 k
  by_cases h34 : i.val < 432
  · let k : Fin 16 := ⟨i.val - 416, by omega⟩
    have he : (⟨416 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_34 k
  by_cases h35 : i.val < 448
  · let k : Fin 16 := ⟨i.val - 432, by omega⟩
    have he : (⟨432 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_35 k
  by_cases h36 : i.val < 464
  · let k : Fin 16 := ⟨i.val - 448, by omega⟩
    have he : (⟨448 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_36 k
  by_cases h37 : i.val < 480
  · let k : Fin 16 := ⟨i.val - 464, by omega⟩
    have he : (⟨464 + k.val, by omega⟩ : Fin 496) = i :=
      Fin.ext (by dsimp [k]; omega)
    simpa only [he] using signature_keys_37 k
  let k : Fin 16 := ⟨i.val - 480, by omega⟩
  have he : (⟨480 + k.val, by omega⟩ : Fin 496) = i :=
    Fin.ext (by dsimp [k]; omega)
  simpa only [he] using signature_keys_38 k

theorem different_label_overlap_candidate (i j : Fin 496)
    (hij : i.val < j.val) (hne : frozenWangLower i ≠ frozenWangLower j)
    (W : Submodule F2 Mat3) (hi : frozenWangTable.OrbitImage i W)
    (hj : frozenWangTable.OrbitImage j W) : (i.val, j.val) ∈ collisionPairs := by
  apply (signatureFixture_separates i j hij _).resolve_left hne
  rw [← signatureFixture_correct, ← signatureFixture_correct]
  exact refinedSignature_eq_of_overlap i j W hi hj

end QiushiMatmul.FrozenLabel
