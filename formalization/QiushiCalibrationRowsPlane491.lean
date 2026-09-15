import QiushiCalibrationRows
import QiushiPlane491GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift491 (q : Fin 128) : Fin 512 :=
  ⟨((if q.val.testBit 0 then 1 else 0) +
    (if q.val.testBit 1 then 2 else 0) +
    (if q.val.testBit 2 then 4 else 0) +
    (if q.val.testBit 3 then 8 else 0) +
    (if q.val.testBit 4 then 16 else 0) +
    (if q.val.testBit 5 then 32 else 0) +
    (if q.val.testBit 6 then 256 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

def label491 (n : Fin 512) : Fin 128 :=
  let r := Nat.xor (Nat.xor (n.val) (if n.val.testBit 7 then 163 else 0)) (if n.val.testBit 6 then 84 else 0)
  ⟨((if r.testBit 0 then 1 else 0) +
    (if r.testBit 1 then 2 else 0) +
    (if r.testBit 2 then 4 else 0) +
    (if r.testBit 3 then 8 else 0) +
    (if r.testBit 4 then 16 else 0) +
    (if r.testBit 5 then 32 else 0) +
    (if r.testBit 8 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate491 : ∀ a b : Fin 128,
    xorCode (lift491 a) (lift491 b) ∈ spanEnum [163, 84] ↔ a = b := by
  decide

theorem cover491 : ∀ c : Fin 512,
    xorCode c (lift491 (label491 c)) ∈ spanEnum [163, 84] := by
  decide

def coordinates491 : Coordinates plane491GenConfig.planeBasis where
  lift := lift491
  label := label491
  zero := by decide
  separate := separate491
  cover := cover491

theorem label491_correct (c : Fin 512) :
    coordinates491.quotientEquiv (label491 c) =
      plane491GenConfig.W.mkQ (codeMat c.val) :=
  coordinates491.label_correct c

end QiushiMatmul.CalibrationRows
