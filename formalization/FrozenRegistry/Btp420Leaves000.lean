import FrozenRegistry.Btp420Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane420BtpGenLeaf0000Refs : Fin 64 → RowRef 63 63 := ![.occ 0, .occ 1, .occ 2, .occ 3, .occ 4, .occ 5, .occ 6, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 61, .occ 62, .sumGe]

def plane420BtpGenLeaf0000Mult : Fin 64 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane420BtpGenLeaf0000 (x : Fin 63 → Int)
    (hroot : plane420BtpGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane420BtpGenLeaf0000Refs i).resolveCoeff plane420BtpGenOccSys j)
    (fun i => (plane420BtpGenLeaf0000Refs i).resolveRhs plane420BtpGenOccSys) plane420BtpGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane420BtpGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · change (∑ j, (-1 : Int) * x j) ≤ -plane420BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
