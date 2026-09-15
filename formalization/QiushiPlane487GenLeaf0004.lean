import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0004Refs : Fin 49 → RowRef 668 48 := ![.occ 79, .occ 83, .occ 101, .occ 103, .occ 159, .occ 223, .occ 225, .occ 227, .occ 240, .occ 246, .occ 269, .occ 287, .occ 297, .occ 303, .occ 308, .occ 310, .occ 315, .occ 317, .occ 324, .occ 334, .occ 347, .occ 381, .occ 386, .occ 390, .occ 391, .occ 412, .occ 470, .occ 494, .occ 501, .occ 507, .occ 520, .occ 546, .occ 579, .occ 638, .occ 653, .occ 658, .sumGe, .nonneg 7, .nonneg 8, .nonneg 30, .nonneg 40, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchLe 16 (0), .branchGe 38 (1)]

def plane487GenLeaf0004Mult : Fin 49 → Nat := ![15788, 10347, 50130, 350, 13067, 15820, 23873, 15459, 14396, 34766, 27851, 18654, 24902, 37667, 8177, 2979, 40667, 10907, 1002, 12553, 45935, 27195, 46244, 13532, 17304, 6766, 36005, 4393, 11283, 8482, 5673, 1394, 7198, 2504, 27959, 1997, 111473, 22708, 12553, 10109, 397, 46115, 31940, 94017, 111473, 66986, 3414, 111473, 210760]

theorem plane487GenLeaf0004 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0004Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0004Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 159
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 269
  · exact hroot.hOcc 287
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 310
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 324
  · exact hroot.hOcc 334
  · exact hroot.hOcc 347
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 412
  · exact hroot.hOcc 470
  · exact hroot.hOcc 494
  · exact hroot.hOcc 501
  · exact hroot.hOcc 507
  · exact hroot.hOcc 520
  · exact hroot.hOcc 546
  · exact hroot.hOcc 579
  · exact hroot.hOcc 638
  · exact hroot.hOcc 653
  · exact hroot.hOcc 658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (38 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
