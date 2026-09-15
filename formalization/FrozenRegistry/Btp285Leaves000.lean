import FrozenRegistry.Btp285Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane285BtpGenLeaf0000Refs : Fin 28 → RowRef 39 31 := ![.occ 5, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 26, .occ 27, .occ 29, .occ 30, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .sumGe, .nonneg 20, .nonneg 22, .nonneg 24, .nonneg 25]

def plane285BtpGenLeaf0000Mult : Fin 28 → Nat := ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1]

theorem plane285BtpGenLeaf0000 (x : Fin 31 → Int)
    (hroot : plane285BtpGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane285BtpGenLeaf0000Refs i).resolveCoeff plane285BtpGenOccSys j)
    (fun i => (plane285BtpGenLeaf0000Refs i).resolveRhs plane285BtpGenOccSys) plane285BtpGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane285BtpGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · change (∑ j, (-1 : Int) * x j) ≤ -plane285BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25

end QiushiMatmul
