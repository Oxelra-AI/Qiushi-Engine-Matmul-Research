import FrozenRegistry.Btp287Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane287BtpGenLeaf0000Refs : Fin 22 → RowRef 68 31 := ![.occ 1, .occ 2, .occ 3, .occ 4, .occ 7, .occ 8, .occ 11, .occ 14, .occ 15, .occ 20, .occ 23, .occ 26, .occ 29, .occ 31, .occ 32, .occ 51, .occ 56, .occ 62, .occ 64, .sumGe, .nonneg 9, .nonneg 10]

def plane287BtpGenLeaf0000Mult : Fin 22 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane287BtpGenLeaf0000 (x : Fin 31 → Int)
    (hroot : plane287BtpGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane287BtpGenLeaf0000Refs i).resolveCoeff plane287BtpGenOccSys j)
    (fun i => (plane287BtpGenLeaf0000Refs i).resolveRhs plane287BtpGenOccSys) plane287BtpGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane287BtpGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · change (∑ j, (-1 : Int) * x j) ≤ -plane287BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 31) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10

end QiushiMatmul
