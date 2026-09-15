import QiushiCalibrationRows
import QiushiPlane489GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift489 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 16 else 0) +
    (if q.val.testBit 4 then 32 else 0) +
    (if q.val.testBit 5 then 64 else 0) +
    (if q.val.testBit 6 then 128 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label489 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 8 then 258 else 0)) (if n.val.testBit 3 then 10 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 4 then 8 else 0) +
    (if r.testBit 5 then 16 else 0) +
    (if r.testBit 6 then 32 else 0) +
    (if r.testBit 7 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate489 : ∀ a b : Fin 128,
    xorCode (lift489 a) (lift489 b) ∈ spanEnum [258, 10] ↔ a = b := by
  decide

theorem cover489 : ∀ c : Fin 512,
    xorCode c (lift489 (label489 c)) ∈ spanEnum [258, 10] := by
  decide

def coordinates489 : Coordinates plane489GenConfig.planeBasis where
  lift := lift489
  label := label489
  zero := by decide
  separate := separate489
  cover := cover489

theorem label489_correct (c : Fin 512) :
    coordinates489.quotientEquiv (label489 c) =
      plane489GenConfig.W.mkQ (codeMat c.val) :=
  coordinates489.label_correct c

end QiushiMatmul.CalibrationRows
