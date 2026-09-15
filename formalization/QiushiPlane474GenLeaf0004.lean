import QiushiPlane474GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane474GenLeaf0004Refs : Fin 61 → RowRef 146 60 := ![.occ 16, .occ 17, .occ 18, .occ 19, .occ 25, .occ 28, .occ 29, .occ 35, .occ 36, .occ 37, .occ 46, .occ 48, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 58, .occ 62, .occ 63, .occ 64, .occ 68, .occ 70, .occ 73, .occ 76, .occ 77, .occ 80, .occ 82, .occ 85, .occ 89, .occ 91, .occ 92, .occ 95, .occ 96, .occ 99, .occ 100, .occ 102, .occ 107, .occ 115, .occ 123, .occ 129, .occ 130, .occ 131, .occ 138, .occ 139, .occ 140, .occ 144, .sumGe, .nonneg 0, .nonneg 9, .nonneg 15, .nonneg 17, .nonneg 28, .nonneg 38, .nonneg 40, .nonneg 42, .nonneg 45, .nonneg 52, .nonneg 54, .branchGe 44 (1)]

def plane474GenLeaf0004Mult : Fin 61 → Nat := ![132183, 87171, 91899, 128802, 14605, 31266, 30995, 62172, 61087, 81846, 49252, 25774, 52048, 62686, 52249, 63649, 190373, 16256, 77788, 39747, 38167, 83413, 208534, 25404, 71183, 52253, 87148, 54300, 26603, 41910, 36535, 58969, 50239, 2431, 5697, 21862, 18651, 49075, 52977, 5723, 12968, 57894, 8368, 14978, 56769, 20374, 962, 38608, 268478, 93599, 147320, 92492, 143571, 1637, 162118, 54193, 12714, 56134, 171577, 35433, 1150239]

theorem plane474GenLeaf0004 (x : Fin 60 → Int)
    (hroot : plane474GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane474GenLeaf0004Refs i).resolveCoeff plane474GenOccSys j)
    (fun i => (plane474GenLeaf0004Refs i).resolveRhs plane474GenOccSys) plane474GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane474GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · change (∑ j, (-1 : Int) * x j) ≤ -plane474GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (9 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (28 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (38 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (44 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
