import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0001Refs : Fin 50 → RowRef 178 49 := ![.occ 15, .occ 17, .occ 18, .occ 20, .occ 25, .occ 26, .occ 29, .occ 32, .occ 35, .occ 39, .occ 44, .occ 55, .occ 60, .occ 61, .occ 66, .occ 68, .occ 77, .occ 78, .occ 82, .occ 85, .occ 86, .occ 87, .occ 92, .occ 95, .occ 97, .occ 99, .occ 103, .occ 104, .occ 112, .occ 119, .occ 129, .occ 132, .occ 139, .occ 142, .occ 152, .occ 153, .occ 160, .occ 162, .occ 164, .occ 165, .occ 170, .occ 173, .occ 175, .sumGe, .nonneg 18, .nonneg 31, .nonneg 39, .branchLe 3 (0), .branchLe 1 (0), .branchGe 4 (1)]

def plane457GenLeaf0001Mult : Fin 50 → Nat := ![10793, 2879, 4199, 8537, 25629, 4637, 5014, 14865, 23234, 5381, 13595, 218, 8997, 2773, 6890, 36373, 24593, 12540, 37611, 3423, 7590, 16001, 6366, 10769, 25769, 3412, 11302, 4208, 4028, 15692, 14045, 8538, 4491, 10905, 21451, 2318, 18257, 8838, 2207, 9984, 4317, 5508, 8648, 63530, 1147, 13940, 40354, 63530, 27157, 173801]

theorem plane457GenLeaf0001 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0001Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0001Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 55
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 112
  · exact hroot.hOcc 119
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
