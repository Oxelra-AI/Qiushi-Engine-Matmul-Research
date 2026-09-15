import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0005Refs : Fin 64 → RowRef 304 63 := ![.occ 3, .occ 5, .occ 31, .occ 42, .occ 45, .occ 50, .occ 51, .occ 64, .occ 66, .occ 82, .occ 83, .occ 93, .occ 95, .occ 96, .occ 104, .occ 106, .occ 109, .occ 114, .occ 118, .occ 119, .occ 132, .occ 139, .occ 140, .occ 141, .occ 155, .occ 159, .occ 188, .occ 201, .occ 204, .occ 217, .occ 220, .occ 224, .occ 228, .occ 231, .occ 241, .occ 242, .occ 264, .occ 271, .occ 272, .occ 284, .occ 286, .occ 290, .occ 295, .occ 298, .occ 299, .sumGe, .nonneg 10, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 36, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 47, .nonneg 49, .nonneg 51, .nonneg 62, .branchLe 48 (0), .branchGe 14 (1), .branchLe 4 (0), .branchLe 38 (0), .branchLe 19 (0), .branchLe 6 (0)]

def plane471GenLeaf0005Mult : Fin 64 → Nat := ![4168332, 1437210, 3746754, 3067696, 9816882, 485858, 10061452, 8553024, 2710646, 2929682, 545842, 848344, 6410784, 15430518, 3059716, 366358, 7923714, 1678892, 13379530, 4304098, 244496, 1744700, 3336068, 2444854, 2001898, 9988172, 9552147, 2690676, 2282348, 4865238, 1827912, 5203722, 254047, 2817383, 428263, 817675, 592290, 4523825, 9694198, 2536771, 5911223, 842212, 4160504, 5573199, 3266159, 31134338, 3664242, 8689874, 10018124, 11503518, 7194102, 18298608, 7371118, 83496, 2836982, 19948788, 15311606, 15583412, 23210624, 38723864, 30292126, 19649916, 22136480, 23145026]

theorem plane471GenLeaf0005 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0005Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0005Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 31
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 188
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 217
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 231
  · exact hroot.hOcc 241
  · exact hroot.hOcc 242
  · exact hroot.hOcc 264
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 284
  · exact hroot.hOcc 286
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (6 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
