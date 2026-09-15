import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0012Refs : Fin 64 → RowRef 304 63 := ![.occ 10, .occ 12, .occ 27, .occ 30, .occ 31, .occ 38, .occ 55, .occ 66, .occ 71, .occ 83, .occ 85, .occ 93, .occ 95, .occ 96, .occ 104, .occ 109, .occ 119, .occ 129, .occ 140, .occ 142, .occ 158, .occ 181, .occ 192, .occ 200, .occ 203, .occ 224, .occ 235, .occ 238, .occ 239, .occ 240, .occ 242, .occ 246, .occ 249, .occ 259, .occ 265, .occ 270, .occ 286, .occ 287, .occ 290, .occ 291, .occ 296, .occ 297, .occ 298, .occ 299, .sumGe, .nonneg 3, .nonneg 18, .nonneg 21, .nonneg 32, .nonneg 34, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 49, .nonneg 52, .nonneg 55, .nonneg 61, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchLe 16 (0), .branchLe 25 (0), .branchGe 22 (1)]

def plane471GenLeaf0012Mult : Fin 64 → Nat := ![63052, 16348, 2008, 45508, 4948, 74536, 107644, 38580, 71020, 82624, 96756, 15500, 13612, 28644, 3032, 76724, 11824, 31644, 5592, 7852, 17464, 8892, 26106, 2244, 1382, 67350, 8874, 23134, 11394, 4880, 31942, 6470, 36550, 1452, 1068, 31858, 9737, 36407, 12446, 17862, 5410, 23213, 8690, 1463, 163812, 70472, 129896, 2008, 37436, 6708, 98944, 7428, 61560, 15372, 25020, 62892, 15328, 87088, 34452, 39668, 35648, 62880, 61036, 783992]

theorem plane471GenLeaf0012 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0012Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0012Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 38
  · exact hroot.hOcc 55
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 119
  · exact hroot.hOcc 129
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 158
  · exact hroot.hOcc 181
  · exact hroot.hOcc 192
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 224
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 246
  · exact hroot.hOcc 249
  · exact hroot.hOcc 259
  · exact hroot.hOcc 265
  · exact hroot.hOcc 270
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
