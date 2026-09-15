import QiushiPlane481GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane481GenLeaf0000Refs : Fin 48 → RowRef 116 47 := ![.occ 69, .occ 70, .occ 71, .occ 72, .occ 73, .occ 74, .occ 75, .occ 76, .occ 77, .occ 78, .occ 79, .occ 80, .occ 81, .occ 82, .occ 83, .occ 84, .occ 85, .occ 86, .occ 87, .occ 88, .occ 89, .occ 90, .occ 91, .occ 92, .occ 93, .occ 94, .occ 95, .occ 96, .occ 97, .occ 98, .occ 99, .occ 100, .occ 101, .occ 102, .occ 103, .occ 104, .occ 105, .occ 106, .occ 107, .occ 108, .occ 109, .occ 110, .occ 111, .occ 112, .occ 113, .occ 114, .occ 115, .sumGe]

def plane481GenLeaf0000Mult : Fin 48 → Nat := ![1303730, 133253, 514830, 828200, 1699386, 507495, 460974, 2338456, 453386, 1801365, 627265, 2065428, 406797, 453597, 1360798, 1915118, 597655, 650726, 1048601, 1512528, 51055, 301076, 2349125, 647020, 2140550, 577219, 1367669, 1171500, 1025958, 1488169, 55821, 2142356, 960243, 435083, 363658, 2310474, 777138, 319183, 819350, 117990, 603419, 933011, 685506, 394870, 10185, 840785, 461325, 6872608]

theorem plane481GenLeaf0000 (x : Fin 47 → Int)
    (hroot : plane481GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane481GenLeaf0000Refs i).resolveCoeff plane481GenOccSys j)
    (fun i => (plane481GenLeaf0000Refs i).resolveRhs plane481GenOccSys) plane481GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane481GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane481GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
