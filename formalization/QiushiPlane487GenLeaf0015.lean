import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0015Refs : Fin 49 → RowRef 668 48 := ![.occ 94, .occ 102, .occ 108, .occ 119, .occ 141, .occ 173, .occ 178, .occ 207, .occ 216, .occ 217, .occ 230, .occ 235, .occ 253, .occ 257, .occ 303, .occ 306, .occ 312, .occ 314, .occ 315, .occ 336, .occ 377, .occ 386, .occ 399, .occ 414, .occ 425, .occ 447, .occ 456, .occ 464, .occ 479, .occ 480, .occ 514, .occ 523, .occ 524, .occ 566, .occ 587, .occ 604, .occ 625, .occ 639, .occ 664, .occ 666, .sumGe, .nonneg 0, .nonneg 25, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 12 (1), .branchGe 3 (1), .branchGe 26 (1)]

def plane487GenLeaf0015Mult : Fin 49 → Nat := ![65890, 14788, 21724, 69758, 72283, 4310, 14158, 42532, 10730, 20890, 80595, 46370, 14646, 14446, 62881, 4879, 53452, 3291, 29815, 2274, 16021, 42734, 40680, 41833, 32714, 9501, 19193, 28404, 2255, 5028, 10574, 15325, 1848, 29547, 7004, 21376, 22866, 12236, 8107, 13403, 144022, 4250, 112053, 133660, 100804, 144022, 325202, 176607, 394881]

theorem plane487GenLeaf0015 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0015Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0015Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 108
  · exact hroot.hOcc 119
  · exact hroot.hOcc 141
  · exact hroot.hOcc 173
  · exact hroot.hOcc 178
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 230
  · exact hroot.hOcc 235
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 312
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 336
  · exact hroot.hOcc 377
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 414
  · exact hroot.hOcc 425
  · exact hroot.hOcc 447
  · exact hroot.hOcc 456
  · exact hroot.hOcc 464
  · exact hroot.hOcc 479
  · exact hroot.hOcc 480
  · exact hroot.hOcc 514
  · exact hroot.hOcc 523
  · exact hroot.hOcc 524
  · exact hroot.hOcc 566
  · exact hroot.hOcc 587
  · exact hroot.hOcc 604
  · exact hroot.hOcc 625
  · exact hroot.hOcc 639
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (26 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
