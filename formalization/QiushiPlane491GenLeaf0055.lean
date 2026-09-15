import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0055Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 85, .occ 94, .occ 100, .occ 106, .occ 116, .occ 119, .occ 138, .occ 151, .occ 161, .occ 166, .occ 219, .occ 232, .occ 234, .occ 244, .occ 257, .occ 260, .occ 305, .occ 329, .occ 360, .occ 363, .occ 370, .occ 382, .occ 389, .occ 421, .occ 424, .occ 434, .occ 446, .occ 489, .occ 504, .occ 509, .occ 529, .occ 573, .occ 603, .occ 634, .occ 642, .occ 653, .occ 675, .occ 691, .occ 715, .occ 722, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchGe 0 (1), .branchLe 39 (0)]

def plane491GenLeaf0055Mult : Fin 50 → Nat := ![198893, 163831, 66125, 20658, 172241, 275561, 39126, 11116, 121070, 59441, 44986, 148494, 35657, 135642, 16952, 50965, 36006, 57221, 1639, 16462, 255971, 179351, 41109, 62277, 51819, 38073, 188590, 98471, 7140, 6440, 13150, 82471, 82494, 28745, 21605, 32184, 63834, 106530, 3219, 13512, 41049, 45053, 358032, 241492, 275538, 1515496, 265490, 176286, 1190714, 344520]

theorem plane491GenLeaf0055 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0055Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0055Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0055Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0055Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 138
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 219
  · exact hroot.hOcc 232
  · exact hroot.hOcc 234
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 305
  · exact hroot.hOcc 329
  · exact hroot.hOcc 360
  · exact hroot.hOcc 363
  · exact hroot.hOcc 370
  · exact hroot.hOcc 382
  · exact hroot.hOcc 389
  · exact hroot.hOcc 421
  · exact hroot.hOcc 424
  · exact hroot.hOcc 434
  · exact hroot.hOcc 446
  · exact hroot.hOcc 489
  · exact hroot.hOcc 504
  · exact hroot.hOcc 509
  · exact hroot.hOcc 529
  · exact hroot.hOcc 573
  · exact hroot.hOcc 603
  · exact hroot.hOcc 634
  · exact hroot.hOcc 642
  · exact hroot.hOcc 653
  · exact hroot.hOcc 675
  · exact hroot.hOcc 691
  · exact hroot.hOcc 715
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
