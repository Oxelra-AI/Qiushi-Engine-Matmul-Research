import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0176Refs : Fin 39 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 168, .occ 507, .occ 638, .occ 670, .occ 707, .occ 729, .occ 737, .occ 750, .occ 775, .occ 777, .occ 860, .occ 985, .occ 1174, .occ 1228, .occ 1240, .occ 1248, .occ 1255, .occ 1312, .occ 1375, .occ 1407, .occ 1421, .occ 1436, .occ 1471, .occ 1508, .occ 1557, .occ 1625, .occ 1628, .occ 1653, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 18 (1), .branchGe 42 (1), .branchLe 5 (0)]

def plane484GenLeaf0176Mult : Fin 39 → Nat := ![492, 102, 426, 93, 252, 68, 1085, 474, 444, 888, 102, 663, 209, 145, 116, 602, 496, 77, 131, 140, 57, 644, 9, 9, 760, 412, 218, 4, 120, 274, 1581, 1581, 1581, 4749, 1581, 1888, 4748, 2589, 1400]

theorem plane484GenLeaf0176 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0176Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0176Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0176Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0176Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 168
  · exact hroot.hOcc 507
  · exact hroot.hOcc 638
  · exact hroot.hOcc 670
  · exact hroot.hOcc 707
  · exact hroot.hOcc 729
  · exact hroot.hOcc 737
  · exact hroot.hOcc 750
  · exact hroot.hOcc 775
  · exact hroot.hOcc 777
  · exact hroot.hOcc 860
  · exact hroot.hOcc 985
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
