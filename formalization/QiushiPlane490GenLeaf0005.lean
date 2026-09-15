import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0005Refs : Fin 44 → RowRef 713 43 := ![.occ 87, .occ 89, .occ 91, .occ 100, .occ 110, .occ 111, .occ 114, .occ 117, .occ 134, .occ 135, .occ 210, .occ 234, .occ 236, .occ 238, .occ 249, .occ 260, .occ 263, .occ 282, .occ 284, .occ 304, .occ 354, .occ 362, .occ 364, .occ 447, .occ 519, .occ 520, .occ 532, .occ 534, .occ 549, .occ 641, .occ 653, .occ 664, .occ 679, .occ 693, .occ 703, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchGe 19 (1), .branchLe 30 (0), .branchLe 25 (0)]

def plane490GenLeaf0005Mult : Fin 44 → Nat := ![806, 639, 952, 2646, 3136, 915, 50, 633, 3011, 1253, 757, 400, 1735, 682, 699, 1397, 341, 216, 2145, 884, 1485, 548, 645, 2267, 23, 503, 1320, 879, 480, 681, 476, 243, 914, 361, 391, 5380, 3664, 5164, 4466, 5380, 4250, 11904, 4036, 3895]

theorem plane490GenLeaf0005 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0005Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0005Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 210
  · exact hroot.hOcc 234
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 249
  · exact hroot.hOcc 260
  · exact hroot.hOcc 263
  · exact hroot.hOcc 282
  · exact hroot.hOcc 284
  · exact hroot.hOcc 304
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 447
  · exact hroot.hOcc 519
  · exact hroot.hOcc 520
  · exact hroot.hOcc 532
  · exact hroot.hOcc 534
  · exact hroot.hOcc 549
  · exact hroot.hOcc 641
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 679
  · exact hroot.hOcc 693
  · exact hroot.hOcc 703
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
