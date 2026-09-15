import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0070Refs : Fin 49 → RowRef 726 49 := ![.occ 89, .occ 95, .occ 96, .occ 135, .occ 136, .occ 149, .occ 222, .occ 223, .occ 231, .occ 237, .occ 248, .occ 257, .occ 258, .occ 290, .occ 318, .occ 322, .occ 324, .occ 331, .occ 332, .occ 336, .occ 365, .occ 370, .occ 385, .occ 392, .occ 394, .occ 400, .occ 429, .occ 486, .occ 489, .occ 506, .occ 513, .occ 524, .occ 564, .occ 573, .occ 589, .occ 599, .occ 602, .occ 605, .occ 624, .occ 664, .occ 702, .occ 712, .sumGe, .nonneg 40, .branchLe 31 (0), .branchGe 16 (1), .branchGe 20 (1), .branchLe 38 (0), .branchLe 39 (0)]

def plane491GenLeaf0070Mult : Fin 49 → Nat := ![53560, 59000, 60287, 31523, 99822, 60509, 10975, 50443, 3875, 8997, 20385, 31873, 30068, 53441, 27155, 5643, 52138, 52304, 40287, 47371, 47694, 17446, 7944, 2526, 48690, 76343, 5420, 925, 19047, 50904, 5725, 19604, 4242, 18122, 19676, 19315, 30461, 14493, 5886, 39312, 7540, 47442, 192860, 5725, 188618, 812582, 200894, 148128, 173545]

theorem plane491GenLeaf0070 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0070Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0070Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0070Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0070Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 149
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 237
  · exact hroot.hOcc 248
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 290
  · exact hroot.hOcc 318
  · exact hroot.hOcc 322
  · exact hroot.hOcc 324
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 336
  · exact hroot.hOcc 365
  · exact hroot.hOcc 370
  · exact hroot.hOcc 385
  · exact hroot.hOcc 392
  · exact hroot.hOcc 394
  · exact hroot.hOcc 400
  · exact hroot.hOcc 429
  · exact hroot.hOcc 486
  · exact hroot.hOcc 489
  · exact hroot.hOcc 506
  · exact hroot.hOcc 513
  · exact hroot.hOcc 524
  · exact hroot.hOcc 564
  · exact hroot.hOcc 573
  · exact hroot.hOcc 589
  · exact hroot.hOcc 599
  · exact hroot.hOcc 602
  · exact hroot.hOcc 605
  · exact hroot.hOcc 624
  · exact hroot.hOcc 664
  · exact hroot.hOcc 702
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
