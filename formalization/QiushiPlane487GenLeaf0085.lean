import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0085Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 93, .occ 105, .occ 108, .occ 110, .occ 141, .occ 164, .occ 201, .occ 223, .occ 237, .occ 240, .occ 260, .occ 263, .occ 269, .occ 288, .occ 295, .occ 297, .occ 315, .occ 332, .occ 356, .occ 359, .occ 380, .occ 386, .occ 394, .occ 419, .occ 440, .occ 456, .occ 470, .occ 479, .occ 486, .occ 515, .occ 521, .occ 534, .occ 544, .occ 604, .occ 639, .occ 657, .occ 662, .occ 664, .sumGe, .nonneg 0, .nonneg 8, .nonneg 16, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchGe 3 (1), .branchLe 37 (0), .branchLe 17 (0)]

def plane487GenLeaf0085Mult : Fin 49 → Nat := ![49887, 13620, 182781, 105914, 109249, 146102, 79112, 27237, 54353, 29265, 40619, 99759, 3906, 64846, 7748, 3424, 66965, 48714, 98849, 41267, 9459, 6265, 1104, 13387, 54662, 30676, 15050, 28861, 15264, 1119, 65260, 21295, 37195, 19806, 6411, 17223, 52550, 1654, 12351, 203537, 26322, 13812, 15900, 383623, 89922, 528777, 721153, 147061, 162211]

theorem plane487GenLeaf0085 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0085Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0085Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0085Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0085Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 93
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 141
  · exact hroot.hOcc 164
  · exact hroot.hOcc 201
  · exact hroot.hOcc 223
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 260
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 288
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 356
  · exact hroot.hOcc 359
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 419
  · exact hroot.hOcc 440
  · exact hroot.hOcc 456
  · exact hroot.hOcc 470
  · exact hroot.hOcc 479
  · exact hroot.hOcc 486
  · exact hroot.hOcc 515
  · exact hroot.hOcc 521
  · exact hroot.hOcc 534
  · exact hroot.hOcc 544
  · exact hroot.hOcc 604
  · exact hroot.hOcc 639
  · exact hroot.hOcc 657
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (37 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (17 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul
