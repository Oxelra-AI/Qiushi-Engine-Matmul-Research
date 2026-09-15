import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0039Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 94, .occ 95, .occ 102, .occ 113, .occ 127, .occ 189, .occ 201, .occ 205, .occ 272, .occ 279, .occ 280, .occ 284, .occ 303, .occ 310, .occ 322, .occ 372, .occ 375, .occ 462, .occ 486, .occ 500, .occ 511, .occ 542, .occ 578, .occ 605, .occ 617, .occ 649, .occ 666, .occ 670, .occ 679, .occ 692, .occ 694, .occ 704, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 35 (0), .branchGe 5 (1), .branchLe 19 (0), .branchGe 39 (1), .branchGe 16 (1)]

def plane490GenLeaf0039Mult : Fin 44 → Nat := ![3, 242, 167, 224, 106, 94, 178, 84, 103, 42, 77, 42, 46, 60, 33, 71, 23, 56, 26, 31, 87, 26, 80, 38, 69, 35, 31, 22, 75, 12, 70, 11, 33, 33, 326, 326, 208, 131, 171, 269, 630, 281, 217, 1094]

theorem plane490GenLeaf0039 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0039Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0039Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 113
  · exact hroot.hOcc 127
  · exact hroot.hOcc 189
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 272
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 284
  · exact hroot.hOcc 303
  · exact hroot.hOcc 310
  · exact hroot.hOcc 322
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 462
  · exact hroot.hOcc 486
  · exact hroot.hOcc 500
  · exact hroot.hOcc 511
  · exact hroot.hOcc 542
  · exact hroot.hOcc 578
  · exact hroot.hOcc 605
  · exact hroot.hOcc 617
  · exact hroot.hOcc 649
  · exact hroot.hOcc 666
  · exact hroot.hOcc 670
  · exact hroot.hOcc 679
  · exact hroot.hOcc 692
  · exact hroot.hOcc 694
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
