import QiushiPlane434GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane434GenLeaf0000Refs : Fin 38 → RowRef 63 37 := ![.occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 61, .occ 62, .sumGe]

def plane434GenLeaf0000Mult : Fin 38 → Nat := ![17, 72, 23, 17, 40, 38, 57, 12, 50, 33, 16, 60, 7, 36, 9, 85, 25, 70, 46, 39, 68, 20, 24, 43, 14, 20, 14, 22, 12, 9, 21, 7, 7, 33, 9, 31, 44, 139]

theorem plane434GenLeaf0000 (x : Fin 37 → Int)
    (hroot : plane434GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane434GenLeaf0000Refs i).resolveCoeff plane434GenOccSys j)
    (fun i => (plane434GenLeaf0000Refs i).resolveRhs plane434GenOccSys) plane434GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane434GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane434GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
