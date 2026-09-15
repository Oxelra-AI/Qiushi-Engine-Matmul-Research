import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0005Refs : Fin 44 → RowRef 1665 43 := ![.occ 128, .occ 129, .occ 133, .occ 134, .occ 138, .occ 139, .occ 141, .occ 142, .occ 286, .occ 314, .occ 563, .occ 564, .occ 566, .occ 678, .occ 758, .occ 771, .occ 772, .occ 955, .occ 1286, .occ 1340, .occ 1376, .occ 1433, .occ 1459, .occ 1489, .occ 1502, .occ 1618, .occ 1622, .occ 1626, .occ 1647, .occ 1651, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchGe 8 (1), .branchLe 9 (0), .branchGe 19 (1), .branchLe 28 (0)]

def plane484GenLeaf0005Mult : Fin 44 → Nat := ![1663, 2011, 1033, 367, 1039, 1552, 650, 174, 150, 1806, 2589, 497, 930, 546, 412, 510, 160, 376, 396, 384, 412, 706, 698, 1327, 788, 376, 322, 692, 1104, 171, 1259, 5484, 1102, 2014, 5162, 3678, 1870, 294, 5484, 5108, 7823, 3465, 8858, 5484]

theorem plane484GenLeaf0005 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0005Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0005Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 286
  · exact hroot.hOcc 314
  · exact hroot.hOcc 563
  · exact hroot.hOcc 564
  · exact hroot.hOcc 566
  · exact hroot.hOcc 678
  · exact hroot.hOcc 758
  · exact hroot.hOcc 771
  · exact hroot.hOcc 772
  · exact hroot.hOcc 955
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
