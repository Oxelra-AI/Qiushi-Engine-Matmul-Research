import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0074Refs : Fin 48 → RowRef 668 48 := ![.occ 79, .occ 83, .occ 89, .occ 92, .occ 99, .occ 107, .occ 118, .occ 164, .occ 169, .occ 196, .occ 211, .occ 212, .occ 216, .occ 219, .occ 228, .occ 246, .occ 275, .occ 302, .occ 303, .occ 312, .occ 315, .occ 332, .occ 347, .occ 356, .occ 386, .occ 394, .occ 399, .occ 472, .occ 482, .occ 484, .occ 505, .occ 510, .occ 535, .occ 564, .occ 566, .occ 587, .occ 646, .occ 653, .occ 664, .sumGe, .nonneg 8, .nonneg 46, .branchGe 39 (1), .branchLe 7 (0), .branchGe 40 (1), .branchLe 13 (0), .branchLe 32 (0), .branchGe 33 (1)]

def plane487GenLeaf0074Mult : Fin 48 → Nat := ![10311, 2558, 87063, 105916, 17038, 9905, 665, 23799, 39104, 11544, 13007, 16862, 26097, 6855, 1330, 14430, 16771, 13672, 26290, 22706, 14126, 50700, 4396, 87699, 38813, 38813, 4757, 47544, 37857, 5321, 59615, 22116, 2167, 2578, 665, 5256, 12332, 32469, 8544, 128326, 25175, 8369, 181036, 64936, 383421, 90601, 14337, 357681]

theorem plane487GenLeaf0074 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0074Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0074Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0074Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0074Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 99
  · exact hroot.hOcc 107
  · exact hroot.hOcc 118
  · exact hroot.hOcc 164
  · exact hroot.hOcc 169
  · exact hroot.hOcc 196
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 228
  · exact hroot.hOcc 246
  · exact hroot.hOcc 275
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 472
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 505
  · exact hroot.hOcc 510
  · exact hroot.hOcc 535
  · exact hroot.hOcc 564
  · exact hroot.hOcc 566
  · exact hroot.hOcc 587
  · exact hroot.hOcc 646
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (46 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (32 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
