import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0003Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 89, .occ 106, .occ 109, .occ 153, .occ 178, .occ 231, .occ 246, .occ 253, .occ 256, .occ 263, .occ 270, .occ 288, .occ 297, .occ 303, .occ 347, .occ 356, .occ 380, .occ 386, .occ 387, .occ 391, .occ 399, .occ 409, .occ 426, .occ 488, .occ 511, .occ 521, .occ 539, .occ 546, .occ 572, .occ 577, .occ 581, .occ 590, .occ 609, .occ 625, .occ 653, .occ 662, .sumGe, .nonneg 0, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 38 (0), .branchGe 9 (1), .branchGe 33 (1)]

def plane487GenLeaf0003Mult : Fin 49 → Nat := ![22199, 73851, 38414, 4395, 2964, 16334, 17222, 65013, 9374, 6421, 47099, 20825, 13384, 23767, 13244, 15697, 45590, 15315, 6479, 4061, 7943, 8315, 4302, 11248, 7422, 4198, 1242, 40226, 58620, 5345, 2917, 3128, 26529, 6662, 1984, 110, 19867, 110131, 21974, 31534, 24537, 110131, 100574, 110131, 73294, 61590, 75704, 91351, 290809]

theorem plane487GenLeaf0003 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0003Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0003Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 153
  · exact hroot.hOcc 178
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 256
  · exact hroot.hOcc 263
  · exact hroot.hOcc 270
  · exact hroot.hOcc 288
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 409
  · exact hroot.hOcc 426
  · exact hroot.hOcc 488
  · exact hroot.hOcc 511
  · exact hroot.hOcc 521
  · exact hroot.hOcc 539
  · exact hroot.hOcc 546
  · exact hroot.hOcc 572
  · exact hroot.hOcc 577
  · exact hroot.hOcc 581
  · exact hroot.hOcc 590
  · exact hroot.hOcc 609
  · exact hroot.hOcc 625
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (38 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (9 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
