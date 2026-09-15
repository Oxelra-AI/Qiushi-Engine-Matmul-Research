import QiushiCalibrationRows
import QiushiPlane485GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift485 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 32 else 0) +
    (if q.val.testBit 4 then 64 else 0) +
    (if q.val.testBit 5 then 128 else 0) +
    (if q.val.testBit 6 then 256 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label485 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 4 then 20 else 0)) (if n.val.testBit 3 then 10 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 5 then 8 else 0) +
    (if r.testBit 6 then 16 else 0) +
    (if r.testBit 7 then 32 else 0) +
    (if r.testBit 8 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate485 : ∀ a b : Fin 128,
    xorCode (lift485 a) (lift485 b) ∈ spanEnum [20, 10] ↔ a = b := by
  decide

theorem cover485 : ∀ c : Fin 512,
    xorCode c (lift485 (label485 c)) ∈ spanEnum [20, 10] := by
  decide

def coordinates485 : Coordinates plane485GenConfig.planeBasis where
  lift := lift485
  label := label485
  zero := by decide
  separate := separate485
  cover := cover485

theorem label485_correct (c : Fin 512) :
    coordinates485.quotientEquiv (label485 c) =
      plane485GenConfig.W.mkQ (codeMat c.val) :=
  coordinates485.label_correct c

end QiushiMatmul.CalibrationRows
