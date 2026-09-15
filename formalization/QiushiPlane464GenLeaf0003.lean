import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0003Refs : Fin 51 → RowRef 202 50 := ![.occ 22, .occ 31, .occ 40, .occ 44, .occ 45, .occ 48, .occ 52, .occ 59, .occ 60, .occ 61, .occ 66, .occ 76, .occ 81, .occ 82, .occ 83, .occ 87, .occ 91, .occ 104, .occ 105, .occ 106, .occ 111, .occ 115, .occ 122, .occ 124, .occ 128, .occ 131, .occ 132, .occ 135, .occ 137, .occ 138, .occ 141, .occ 145, .occ 151, .occ 157, .occ 173, .occ 177, .occ 185, .occ 192, .occ 193, .occ 199, .sumGe, .nonneg 0, .nonneg 8, .nonneg 12, .nonneg 29, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 48, .branchLe 1 (0), .branchGe 15 (1)]

def plane464GenLeaf0003Mult : Fin 51 → Nat := ![3876, 15848, 110412, 3646, 39936, 190259, 8542, 111052, 33650, 90376, 15520, 36308, 34012, 19470, 42286, 18458, 108612, 16434, 31531, 20824, 100463, 87908, 4375, 70029, 57796, 18580, 14058, 40119, 9360, 9986, 17090, 45139, 3946, 120328, 8551, 17648, 37998, 1570, 30934, 10734, 194634, 14976, 20490, 60771, 16305, 48682, 53788, 37222, 45320, 104258, 1146596]

theorem plane464GenLeaf0003 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0003Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0003Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 31
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 157
  · exact hroot.hOcc 173
  · exact hroot.hOcc 177
  · exact hroot.hOcc 185
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
