import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0008Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 93, .occ 109, .occ 111, .occ 155, .occ 195, .occ 218, .occ 234, .occ 249, .occ 257, .occ 303, .occ 346, .occ 354, .occ 364, .occ 375, .occ 416, .occ 447, .occ 449, .occ 467, .occ 468, .occ 484, .occ 489, .occ 491, .occ 519, .occ 522, .occ 599, .occ 603, .occ 653, .occ 664, .occ 682, .occ 694, .occ 699, .occ 711, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchLe 17 (0), .branchLe 22 (0), .branchLe 20 (0), .branchLe 42 (0)]

def plane490GenLeaf0008Mult : Fin 44 → Nat := ![39455, 39246, 28862, 27065, 21068, 31533, 7666, 11136, 6980, 37960, 403, 29341, 4288, 7223, 8783, 42721, 31187, 9935, 1333, 34692, 4881, 7144, 9932, 22177, 25822, 6141, 33319, 8263, 2356, 10265, 753, 1109, 1119, 11648, 104474, 102118, 80282, 91717, 104474, 122766, 79092, 104474, 94349, 95691]

theorem plane490GenLeaf0008 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0008Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0008Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 155
  · exact hroot.hOcc 195
  · exact hroot.hOcc 218
  · exact hroot.hOcc 234
  · exact hroot.hOcc 249
  · exact hroot.hOcc 257
  · exact hroot.hOcc 303
  · exact hroot.hOcc 346
  · exact hroot.hOcc 354
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 416
  · exact hroot.hOcc 447
  · exact hroot.hOcc 449
  · exact hroot.hOcc 467
  · exact hroot.hOcc 468
  · exact hroot.hOcc 484
  · exact hroot.hOcc 489
  · exact hroot.hOcc 491
  · exact hroot.hOcc 519
  · exact hroot.hOcc 522
  · exact hroot.hOcc 599
  · exact hroot.hOcc 603
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 682
  · exact hroot.hOcc 694
  · exact hroot.hOcc 699
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
