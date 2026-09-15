import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0007Refs : Fin 57 → RowRef 203 56 := ![.occ 35, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 49, .occ 59, .occ 63, .occ 68, .occ 71, .occ 74, .occ 75, .occ 84, .occ 85, .occ 89, .occ 90, .occ 94, .occ 95, .occ 97, .occ 103, .occ 106, .occ 109, .occ 111, .occ 114, .occ 121, .occ 129, .occ 132, .occ 143, .occ 146, .occ 147, .occ 156, .occ 157, .occ 170, .occ 171, .occ 179, .occ 183, .occ 184, .occ 194, .occ 201, .sumGe, .nonneg 7, .nonneg 12, .nonneg 14, .nonneg 19, .nonneg 20, .nonneg 23, .nonneg 24, .nonneg 25, .nonneg 27, .nonneg 36, .nonneg 37, .nonneg 38, .nonneg 39, .nonneg 48, .branchGe 46 (1), .branchLe 10 (0)]

def plane458GenLeaf0007Mult : Fin 57 → Nat := ![11171, 21808, 30938, 36425, 20184, 2549, 13686, 2505, 36425, 28906, 7657, 8459, 5940, 1423, 7221, 4532, 24246, 6087, 7107, 17530, 9851, 2371, 6329, 782, 3255, 6655, 4436, 3049, 14272, 710, 10849, 11376, 7309, 7685, 8954, 4696, 7696, 6789, 3984, 7979, 40409, 2416, 18394, 6240, 937, 29131, 27799, 11113, 11304, 10362, 801, 29252, 6288, 14436, 21593, 266546, 23770]

theorem plane458GenLeaf0007 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0007Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0007Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 35
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 194
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (14 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (19 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (27 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (36 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (48 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (46 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (10 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
