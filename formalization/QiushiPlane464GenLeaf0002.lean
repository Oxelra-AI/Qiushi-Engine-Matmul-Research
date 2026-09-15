import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0002Refs : Fin 48 → RowRef 202 50 := ![.occ 17, .occ 18, .occ 19, .occ 21, .occ 24, .occ 26, .occ 28, .occ 29, .occ 35, .occ 37, .occ 38, .occ 42, .occ 49, .occ 53, .occ 54, .occ 65, .occ 66, .occ 77, .occ 78, .occ 79, .occ 80, .occ 87, .occ 88, .occ 93, .occ 104, .occ 106, .occ 107, .occ 141, .occ 147, .occ 152, .occ 159, .occ 162, .occ 164, .occ 175, .occ 178, .occ 179, .occ 183, .occ 194, .sumGe, .nonneg 0, .nonneg 26, .nonneg 27, .nonneg 29, .nonneg 32, .branchLe 1 (0), .branchLe 15 (0), .branchGe 5 (1), .branchGe 37 (1)]

def plane464GenLeaf0002Mult : Fin 48 → Nat := ![119, 119, 47, 155, 30, 94, 44, 135, 3, 35, 62, 75, 141, 39, 39, 9, 15, 46, 41, 17, 39, 30, 47, 30, 29, 14, 35, 156, 16, 44, 98, 15, 11, 17, 67, 16, 9, 15, 187, 90, 21, 44, 202, 73, 178, 187, 58, 1328]

theorem plane464GenLeaf0002 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0002Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0002Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 42
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 194
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
