import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0086Refs : Fin 49 → RowRef 668 48 := ![.occ 99, .occ 106, .occ 129, .occ 141, .occ 142, .occ 164, .occ 190, .occ 201, .occ 218, .occ 223, .occ 237, .occ 240, .occ 253, .occ 256, .occ 260, .occ 269, .occ 288, .occ 291, .occ 297, .occ 315, .occ 351, .occ 386, .occ 391, .occ 399, .occ 415, .occ 419, .occ 441, .occ 443, .occ 479, .occ 515, .occ 518, .occ 521, .occ 577, .occ 598, .occ 604, .occ 662, .occ 664, .occ 665, .occ 666, .sumGe, .nonneg 0, .nonneg 24, .nonneg 31, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchGe 3 (1), .branchLe 37 (0), .branchGe 17 (1)]

def plane487GenLeaf0086Mult : Fin 49 → Nat := ![10319, 7339, 15180, 22949, 6231, 5610, 3438, 28701, 48142, 12154, 16502, 21699, 25955, 20366, 6625, 12281, 152, 6079, 5068, 4310, 26386, 38053, 7480, 6856, 4983, 15191, 5193, 2920, 1553, 5298, 9583, 8316, 3652, 12336, 11820, 19634, 17899, 1460, 6874, 69841, 10256, 22808, 13539, 82403, 18326, 123450, 170542, 10638, 196061]

theorem plane487GenLeaf0086 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0086Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0086Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0086Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0086Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 106
  · exact hroot.hOcc 129
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 164
  · exact hroot.hOcc 190
  · exact hroot.hOcc 201
  · exact hroot.hOcc 218
  · exact hroot.hOcc 223
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 253
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 269
  · exact hroot.hOcc 288
  · exact hroot.hOcc 291
  · exact hroot.hOcc 297
  · exact hroot.hOcc 315
  · exact hroot.hOcc 351
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 415
  · exact hroot.hOcc 419
  · exact hroot.hOcc 441
  · exact hroot.hOcc 443
  · exact hroot.hOcc 479
  · exact hroot.hOcc 515
  · exact hroot.hOcc 518
  · exact hroot.hOcc 521
  · exact hroot.hOcc 577
  · exact hroot.hOcc 598
  · exact hroot.hOcc 604
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (24 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (37 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
