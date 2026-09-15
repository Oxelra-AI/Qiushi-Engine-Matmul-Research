import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0096Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 95, .occ 99, .occ 102, .occ 103, .occ 110, .occ 111, .occ 126, .occ 139, .occ 167, .occ 169, .occ 189, .occ 214, .occ 220, .occ 225, .occ 234, .occ 244, .occ 312, .occ 329, .occ 332, .occ 340, .occ 355, .occ 359, .occ 393, .occ 400, .occ 412, .occ 419, .occ 421, .occ 431, .occ 487, .occ 495, .occ 540, .occ 541, .occ 563, .occ 564, .occ 566, .occ 567, .occ 576, .occ 632, .occ 671, .occ 708, .occ 709, .sumGe, .nonneg 1, .nonneg 24, .nonneg 33, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchGe 2 (1)]

def plane491GenLeaf0096Mult : Fin 50 → Nat := ![21159, 26011, 86141, 65587, 52268, 26520, 7941, 64223, 56654, 4630, 15597, 20225, 15826, 61925, 7517, 39674, 256, 2182, 7338, 7773, 1479, 6402, 63371, 545, 8900, 17059, 925, 14226, 30677, 22174, 9717, 14489, 31979, 1521, 8767, 3760, 4103, 8028, 10123, 26822, 5079, 42798, 101599, 10123, 2024, 45408, 183727, 91882, 271845, 499786]

theorem plane491GenLeaf0096 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0096Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0096Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 126
  · exact hroot.hOcc 139
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 189
  · exact hroot.hOcc 214
  · exact hroot.hOcc 220
  · exact hroot.hOcc 225
  · exact hroot.hOcc 234
  · exact hroot.hOcc 244
  · exact hroot.hOcc 312
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 340
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 393
  · exact hroot.hOcc 400
  · exact hroot.hOcc 412
  · exact hroot.hOcc 419
  · exact hroot.hOcc 421
  · exact hroot.hOcc 431
  · exact hroot.hOcc 487
  · exact hroot.hOcc 495
  · exact hroot.hOcc 540
  · exact hroot.hOcc 541
  · exact hroot.hOcc 563
  · exact hroot.hOcc 564
  · exact hroot.hOcc 566
  · exact hroot.hOcc 567
  · exact hroot.hOcc 576
  · exact hroot.hOcc 632
  · exact hroot.hOcc 671
  · exact hroot.hOcc 708
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
