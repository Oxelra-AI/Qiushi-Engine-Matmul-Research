import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0012Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 105, .occ 122, .occ 124, .occ 128, .occ 210, .occ 212, .occ 213, .occ 221, .occ 237, .occ 255, .occ 260, .occ 329, .occ 331, .occ 332, .occ 341, .occ 342, .occ 372, .occ 377, .occ 403, .occ 410, .occ 463, .occ 493, .occ 506, .occ 509, .occ 531, .occ 533, .occ 537, .occ 540, .occ 541, .occ 549, .occ 552, .occ 558, .occ 573, .occ 576, .occ 631, .occ 691, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchGe 0 (1), .branchLe 3 (0), .branchGe 47 (1)]

def plane491GenLeaf0012Mult : Fin 50 → Nat := ![25238, 17679, 144, 1588, 274, 15763, 13270, 5989, 6802, 7675, 1812, 680, 2904, 1696, 1644, 7992, 6941, 497, 8544, 2876, 11152, 3413, 1847, 4877, 2291, 3612, 3042, 4526, 6316, 2587, 1414, 1883, 5947, 8885, 1365, 1611, 10578, 975, 27050, 19725, 8784, 19733, 13639, 21113, 21103, 18506, 36788, 80737, 18589, 81860]

theorem plane491GenLeaf0012 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0012Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0012Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 105
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 221
  · exact hroot.hOcc 237
  · exact hroot.hOcc 255
  · exact hroot.hOcc 260
  · exact hroot.hOcc 329
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 341
  · exact hroot.hOcc 342
  · exact hroot.hOcc 372
  · exact hroot.hOcc 377
  · exact hroot.hOcc 403
  · exact hroot.hOcc 410
  · exact hroot.hOcc 463
  · exact hroot.hOcc 493
  · exact hroot.hOcc 506
  · exact hroot.hOcc 509
  · exact hroot.hOcc 531
  · exact hroot.hOcc 533
  · exact hroot.hOcc 537
  · exact hroot.hOcc 540
  · exact hroot.hOcc 541
  · exact hroot.hOcc 549
  · exact hroot.hOcc 552
  · exact hroot.hOcc 558
  · exact hroot.hOcc 573
  · exact hroot.hOcc 576
  · exact hroot.hOcc 631
  · exact hroot.hOcc 691
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
