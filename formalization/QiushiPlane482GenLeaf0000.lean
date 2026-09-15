import QiushiPlane482GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane482GenLeaf0000Refs : Fin 45 → RowRef 118 48 := ![.occ 74, .occ 75, .occ 76, .occ 77, .occ 78, .occ 79, .occ 80, .occ 81, .occ 82, .occ 83, .occ 84, .occ 85, .occ 86, .occ 87, .occ 88, .occ 89, .occ 90, .occ 91, .occ 92, .occ 93, .occ 94, .occ 95, .occ 96, .occ 97, .occ 98, .occ 99, .occ 100, .occ 101, .occ 102, .occ 103, .occ 104, .occ 105, .occ 106, .occ 107, .occ 108, .occ 109, .occ 110, .occ 111, .occ 112, .occ 113, .occ 114, .occ 115, .occ 116, .occ 117, .sumGe]

def plane482GenLeaf0000Mult : Fin 45 → Nat := ![100898, 56482, 13893, 56482, 67586, 13893, 93075, 43772, 72084, 103432, 62515, 58654, 14882, 122915, 99069, 113001, 99108, 38726, 98645, 33312, 143830, 66795, 132207, 69563, 63734, 167856, 48801, 34846, 85400, 76510, 85989, 146011, 81310, 87198, 106327, 78891, 68489, 66370, 101006, 25876, 80677, 145814, 136365, 137403, 686766]

theorem plane482GenLeaf0000 (x : Fin 48 → Int)
    (hroot : plane482GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane482GenLeaf0000Refs i).resolveCoeff plane482GenOccSys j)
    (fun i => (plane482GenLeaf0000Refs i).resolveRhs plane482GenOccSys) plane482GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane482GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
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
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · change (∑ j, (-1 : Int) * x j) ≤ -plane482GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
