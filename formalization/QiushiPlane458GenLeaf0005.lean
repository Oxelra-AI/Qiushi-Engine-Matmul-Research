import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0005Refs : Fin 57 → RowRef 203 56 := ![.occ 14, .occ 22, .occ 29, .occ 30, .occ 46, .occ 48, .occ 65, .occ 66, .occ 72, .occ 74, .occ 75, .occ 78, .occ 79, .occ 83, .occ 85, .occ 86, .occ 95, .occ 98, .occ 99, .occ 105, .occ 106, .occ 109, .occ 111, .occ 112, .occ 114, .occ 120, .occ 124, .occ 142, .occ 144, .occ 146, .occ 153, .occ 154, .occ 155, .occ 157, .occ 181, .occ 192, .occ 193, .occ 194, .occ 200, .occ 201, .sumGe, .nonneg 6, .nonneg 8, .nonneg 12, .nonneg 14, .nonneg 19, .nonneg 20, .nonneg 25, .nonneg 39, .nonneg 50, .nonneg 52, .nonneg 53, .nonneg 55, .branchLe 46 (0), .branchGe 30 (1), .branchLe 10 (0), .branchGe 3 (1)]

def plane458GenLeaf0005Mult : Fin 57 → Nat := ![42262, 16419, 17681, 112501, 56513, 65865, 48054, 85955, 30408, 77027, 28662, 7038, 2363, 1470, 53056, 22814, 30977, 6214, 20120, 37219, 27299, 36683, 45916, 14383, 55409, 22064, 2223, 881, 7082, 26041, 35506, 12477, 2951, 1546, 17241, 16450, 17490, 16389, 9700, 13513, 112501, 32742, 16401, 9652, 3360, 43053, 1647, 24147, 80384, 16100, 36172, 81612, 78482, 112501, 256907, 85560, 276618]

theorem plane458GenLeaf0005 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0005Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0005Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 22
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 157
  · exact hroot.hOcc 181
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (14 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (19 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (39 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (50 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (10 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
