import QiushiPlane483GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane483GenLeaf0000Refs : Fin 37 → RowRef 112 36 := ![.occ 76, .occ 77, .occ 78, .occ 79, .occ 80, .occ 81, .occ 82, .occ 83, .occ 84, .occ 85, .occ 86, .occ 87, .occ 88, .occ 89, .occ 90, .occ 91, .occ 92, .occ 93, .occ 94, .occ 95, .occ 96, .occ 97, .occ 98, .occ 99, .occ 100, .occ 101, .occ 102, .occ 103, .occ 104, .occ 105, .occ 106, .occ 107, .occ 108, .occ 109, .occ 110, .occ 111, .sumGe]

def plane483GenLeaf0000Mult : Fin 37 → Nat := ![11131, 13903, 8086, 6961, 24042, 38107, 11519, 1128, 5541, 3480, 7817, 45014, 15229, 4922, 49378, 6524, 32823, 12505, 11762, 34136, 14458, 4391, 11050, 13107, 8440, 11494, 8211, 1184, 12081, 12376, 12537, 26043, 12308, 17192, 16977, 9437, 108085]

theorem plane483GenLeaf0000 (x : Fin 36 → Int)
    (hroot : plane483GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane483GenLeaf0000Refs i).resolveCoeff plane483GenOccSys j)
    (fun i => (plane483GenLeaf0000Refs i).resolveRhs plane483GenOccSys) plane483GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane483GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · change (∑ j, (-1 : Int) * x j) ≤ -plane483GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
