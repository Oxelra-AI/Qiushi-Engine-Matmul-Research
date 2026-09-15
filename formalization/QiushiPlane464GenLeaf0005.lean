import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0005Refs : Fin 51 → RowRef 202 50 := ![.occ 23, .occ 35, .occ 41, .occ 50, .occ 58, .occ 61, .occ 66, .occ 67, .occ 68, .occ 70, .occ 75, .occ 76, .occ 79, .occ 81, .occ 93, .occ 94, .occ 96, .occ 98, .occ 101, .occ 109, .occ 110, .occ 113, .occ 129, .occ 132, .occ 133, .occ 134, .occ 141, .occ 153, .occ 157, .occ 167, .occ 168, .occ 177, .occ 186, .occ 187, .occ 189, .occ 191, .occ 193, .sumGe, .nonneg 0, .nonneg 10, .nonneg 13, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 43, .nonneg 46, .branchGe 1 (1), .branchLe 49 (0), .branchLe 40 (0), .branchLe 19 (0), .branchGe 18 (1)]

def plane464GenLeaf0005Mult : Fin 51 → Nat := ![4294, 3217, 17136, 1382, 5704, 12510, 14854, 1126, 1589, 169, 952, 9295, 4941, 2537, 555, 2228, 4294, 12559, 2774, 4402, 266, 1726, 5333, 7901, 4379, 1120, 5875, 11118, 2555, 994, 8634, 11620, 5046, 3118, 3217, 8406, 5848, 34365, 9010, 1442, 11444, 17315, 6143, 9087, 10533, 12844, 24206, 22745, 10233, 30121, 73885]

theorem plane464GenLeaf0005 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0005Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0005Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · exact hroot.hOcc 35
  · exact hroot.hOcc 41
  · exact hroot.hOcc 50
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 193
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (49 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (40 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
