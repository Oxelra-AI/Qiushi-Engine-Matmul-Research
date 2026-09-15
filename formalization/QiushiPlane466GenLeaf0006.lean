import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0006Refs : Fin 51 → RowRef 210 50 := ![.occ 13, .occ 14, .occ 22, .occ 37, .occ 43, .occ 48, .occ 54, .occ 60, .occ 61, .occ 62, .occ 64, .occ 66, .occ 101, .occ 102, .occ 103, .occ 106, .occ 111, .occ 114, .occ 121, .occ 122, .occ 123, .occ 129, .occ 133, .occ 144, .occ 149, .occ 150, .occ 170, .occ 171, .occ 172, .occ 180, .occ 181, .occ 184, .occ 187, .occ 188, .occ 199, .occ 201, .occ 205, .sumGe, .nonneg 18, .nonneg 29, .nonneg 32, .nonneg 33, .nonneg 35, .nonneg 36, .nonneg 39, .nonneg 43, .nonneg 45, .branchLe 24 (0), .branchGe 19 (1), .branchLe 30 (1), .branchGe 12 (1)]

def plane466GenLeaf0006Mult : Fin 51 → Nat := ![66250, 28094, 7412, 20764, 41018, 26153, 2345, 27462, 55078, 2647, 29406, 6386, 66924, 22330, 27091, 10204, 32123, 3151, 41711, 1955, 5265, 16186, 1500, 5063, 25414, 18302, 4389, 764, 28210, 4503, 13000, 4194, 7607, 6192, 3384, 14827, 19216, 86140, 48347, 3290, 11661, 7398, 37439, 10587, 6061, 26832, 20092, 53570, 83557, 75445, 353849]

theorem plane466GenLeaf0006 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0006Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0006Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 22
  · exact hroot.hOcc 37
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 54
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
