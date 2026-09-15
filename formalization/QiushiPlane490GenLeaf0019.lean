import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0019Refs : Fin 44 → RowRef 713 43 := ![.occ 94, .occ 95, .occ 112, .occ 114, .occ 117, .occ 169, .occ 181, .occ 186, .occ 236, .occ 249, .occ 252, .occ 283, .occ 340, .occ 354, .occ 362, .occ 373, .occ 375, .occ 376, .occ 444, .occ 445, .occ 447, .occ 467, .occ 489, .occ 494, .occ 520, .occ 599, .occ 605, .occ 653, .occ 659, .occ 665, .occ 666, .occ 675, .occ 711, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchLe 32 (0), .branchLe 3 (0), .branchLe 42 (0), .branchLe 20 (0), .branchGe 38 (1)]

def plane490GenLeaf0019Mult : Fin 44 → Nat := ![1541, 1280, 429, 906, 341, 642, 799, 364, 433, 824, 248, 481, 17, 959, 578, 454, 210, 323, 10, 788, 190, 38, 549, 379, 35, 694, 266, 54, 691, 38, 189, 149, 190, 2199, 2145, 2199, 2009, 3485, 338, 861, 1933, 1491, 1820, 4092]

theorem plane490GenLeaf0019 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0019Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0019Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 236
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 283
  · exact hroot.hOcc 340
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 373
  · exact hroot.hOcc 375
  · exact hroot.hOcc 376
  · exact hroot.hOcc 444
  · exact hroot.hOcc 445
  · exact hroot.hOcc 447
  · exact hroot.hOcc 467
  · exact hroot.hOcc 489
  · exact hroot.hOcc 494
  · exact hroot.hOcc 520
  · exact hroot.hOcc 599
  · exact hroot.hOcc 605
  · exact hroot.hOcc 653
  · exact hroot.hOcc 659
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · exact hroot.hOcc 675
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
