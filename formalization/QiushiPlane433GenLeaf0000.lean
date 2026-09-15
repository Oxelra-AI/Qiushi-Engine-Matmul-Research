import QiushiPlane433GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane433GenLeaf0000Refs : Fin 32 → RowRef 63 31 := ![.occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 61, .occ 62, .sumGe]

def plane433GenLeaf0000Mult : Fin 32 → Nat := ![532, 579, 288, 130, 665, 165, 264, 443, 891, 203, 792, 271, 477, 403, 88, 142, 311, 122, 24, 165, 305, 189, 122, 47, 406, 609, 165, 71, 332, 34, 115, 1218]

theorem plane433GenLeaf0000 (x : Fin 31 → Int)
    (hroot : plane433GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane433GenLeaf0000Refs i).resolveCoeff plane433GenOccSys j)
    (fun i => (plane433GenLeaf0000Refs i).resolveRhs plane433GenOccSys) plane433GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane433GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane433GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
