import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0106Refs : Fin 50 → RowRef 726 49 := ![.occ 81, .occ 98, .occ 104, .occ 105, .occ 110, .occ 112, .occ 116, .occ 118, .occ 214, .occ 219, .occ 243, .occ 260, .occ 267, .occ 275, .occ 292, .occ 304, .occ 305, .occ 319, .occ 351, .occ 355, .occ 363, .occ 367, .occ 372, .occ 393, .occ 402, .occ 404, .occ 430, .occ 431, .occ 495, .occ 531, .occ 559, .occ 575, .occ 580, .occ 582, .occ 585, .occ 622, .occ 662, .occ 664, .occ 687, .occ 691, .occ 723, .sumGe, .nonneg 37, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchGe 39 (1), .branchLe 27 (0), .branchLe 11 (0), .branchGe 4 (1)]

def plane491GenLeaf0106Mult : Fin 50 → Nat := ![224909, 16051, 162696, 144545, 34007, 668097, 235913, 584249, 11229, 96242, 58497, 97896, 227118, 383051, 283864, 6734, 55707, 33753, 23301, 102209, 189437, 170496, 129994, 89635, 165555, 551934, 10816, 359170, 353818, 189664, 7401, 214312, 51232, 75579, 124136, 245440, 65526, 221318, 39465, 157007, 14863, 878543, 139554, 1844170, 1919107, 878543, 626183, 392434, 779264, 1931755]

theorem plane491GenLeaf0106 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0106Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0106Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0106Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0106Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 243
  · exact hroot.hOcc 260
  · exact hroot.hOcc 267
  · exact hroot.hOcc 275
  · exact hroot.hOcc 292
  · exact hroot.hOcc 304
  · exact hroot.hOcc 305
  · exact hroot.hOcc 319
  · exact hroot.hOcc 351
  · exact hroot.hOcc 355
  · exact hroot.hOcc 363
  · exact hroot.hOcc 367
  · exact hroot.hOcc 372
  · exact hroot.hOcc 393
  · exact hroot.hOcc 402
  · exact hroot.hOcc 404
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 559
  · exact hroot.hOcc 575
  · exact hroot.hOcc 580
  · exact hroot.hOcc 582
  · exact hroot.hOcc 585
  · exact hroot.hOcc 622
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · exact hroot.hOcc 687
  · exact hroot.hOcc 691
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
