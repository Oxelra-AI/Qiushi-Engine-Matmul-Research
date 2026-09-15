import QiushiCalibrationRows
import QiushiPlane484GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift484 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 32 else 0) +
    (if q.val.testBit 4 then 64 else 0) +
    (if q.val.testBit 5 then 128 else 0) +
    (if q.val.testBit 6 then 256 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label484 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 4 then 19 else 0)) (if n.val.testBit 3 then 10 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 5 then 8 else 0) +
    (if r.testBit 6 then 16 else 0) +
    (if r.testBit 7 then 32 else 0) +
    (if r.testBit 8 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate484 : ∀ a b : Fin 128,
    xorCode (lift484 a) (lift484 b) ∈ spanEnum [19, 10] ↔ a = b := by
  decide

theorem cover484 : ∀ c : Fin 512,
    xorCode c (lift484 (label484 c)) ∈ spanEnum [19, 10] := by
  decide

def coordinates484 : Coordinates plane484GenConfig.planeBasis where
  lift := lift484
  label := label484
  zero := by decide
  separate := separate484
  cover := cover484

theorem label484_correct (c : Fin 512) :
    coordinates484.quotientEquiv (label484 c) =
      plane484GenConfig.W.mkQ (codeMat c.val) :=
  coordinates484.label_correct c

end QiushiMatmul.CalibrationRows
