import QiushiCalibrationRows
import QiushiPlane490GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift490 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 16 else 0) +
    (if q.val.testBit 4 then 32 else 0) +
    (if q.val.testBit 5 then 64 else 0) +
    (if q.val.testBit 6 then 128 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label490 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 8 then 275 else 0)) (if n.val.testBit 3 then 10 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 4 then 8 else 0) +
    (if r.testBit 5 then 16 else 0) +
    (if r.testBit 6 then 32 else 0) +
    (if r.testBit 7 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate490 : ∀ a b : Fin 128,
    xorCode (lift490 a) (lift490 b) ∈ spanEnum [275, 10] ↔ a = b := by
  decide

theorem cover490 : ∀ c : Fin 512,
    xorCode c (lift490 (label490 c)) ∈ spanEnum [275, 10] := by
  decide

def coordinates490 : Coordinates plane490GenConfig.planeBasis where
  lift := lift490
  label := label490
  zero := by decide
  separate := separate490
  cover := cover490

theorem label490_correct (c : Fin 512) :
    coordinates490.quotientEquiv (label490 c) =
      plane490GenConfig.W.mkQ (codeMat c.val) :=
  coordinates490.label_correct c

end QiushiMatmul.CalibrationRows
