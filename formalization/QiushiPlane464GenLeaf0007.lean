import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0007Refs : Fin 51 → RowRef 202 50 := ![.occ 13, .occ 14, .occ 25, .occ 27, .occ 39, .occ 41, .occ 47, .occ 57, .occ 60, .occ 61, .occ 67, .occ 76, .occ 80, .occ 81, .occ 87, .occ 89, .occ 92, .occ 95, .occ 102, .occ 114, .occ 116, .occ 120, .occ 122, .occ 124, .occ 134, .occ 145, .occ 147, .occ 148, .occ 154, .occ 161, .occ 163, .occ 169, .occ 170, .occ 177, .occ 186, .occ 187, .occ 190, .occ 200, .occ 201, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 11, .nonneg 12, .nonneg 13, .nonneg 32, .nonneg 43, .branchGe 1 (1), .branchLe 49 (0), .branchGe 40 (1)]

def plane464GenLeaf0007Mult : Fin 51 → Nat := ![69808, 5358, 25978, 96306, 10440, 2932, 56262, 82236, 8820, 19904, 31152, 210562, 192972, 96022, 150724, 26350, 30114, 101720, 10042, 9380, 9834, 45228, 10888, 5162, 13786, 12428, 79158, 17852, 17530, 11084, 12412, 42788, 69738, 11958, 12435, 9357, 10708, 41661, 46529, 232354, 542322, 77592, 37986, 1238, 88698, 9102, 129766, 94538, 224806, 132206, 929930]

theorem plane464GenLeaf0007 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0007Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0007Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 57
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 67
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (49 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
