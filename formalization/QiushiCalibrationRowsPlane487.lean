import QiushiCalibrationRows
import QiushiPlane487GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift487 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 16 else 0) +
    (if q.val.testBit 4 then 32 else 0) +
    (if q.val.testBit 5 then 128 else 0) +
    (if q.val.testBit 6 then 256 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label487 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 6 then 84 else 0)) (if n.val.testBit 3 then 10 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 4 then 8 else 0) +
    (if r.testBit 5 then 16 else 0) +
    (if r.testBit 7 then 32 else 0) +
    (if r.testBit 8 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate487 : ∀ a b : Fin 128,
    xorCode (lift487 a) (lift487 b) ∈ spanEnum [84, 10] ↔ a = b := by
  decide

theorem cover487 : ∀ c : Fin 512,
    xorCode c (lift487 (label487 c)) ∈ spanEnum [84, 10] := by
  decide

def coordinates487 : Coordinates plane487GenConfig.planeBasis where
  lift := lift487
  label := label487
  zero := by decide
  separate := separate487
  cover := cover487

theorem label487_correct (c : Fin 512) :
    coordinates487.quotientEquiv (label487 c) =
      plane487GenConfig.W.mkQ (codeMat c.val) :=
  coordinates487.label_correct c

end QiushiMatmul.CalibrationRows
