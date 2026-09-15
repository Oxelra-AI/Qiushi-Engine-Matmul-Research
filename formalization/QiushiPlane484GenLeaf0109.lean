import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0109Refs : Fin 40 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 175, .occ 198, .occ 203, .occ 204, .occ 209, .occ 356, .occ 399, .occ 615, .occ 653, .occ 662, .occ 720, .occ 860, .occ 902, .occ 921, .occ 1087, .occ 1136, .occ 1143, .occ 1145, .occ 1150, .occ 1231, .occ 1238, .occ 1288, .occ 1342, .occ 1368, .occ 1414, .occ 1477, .occ 1537, .occ 1653, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchLe 19 (0), .branchGe 34 (1), .branchGe 20 (1)]

def plane484GenLeaf0109Mult : Fin 40 → Nat := ![75, 12, 86, 48, 164, 57, 133, 5, 24, 34, 205, 141, 188, 57, 28, 24, 111, 31, 30, 18, 39, 17, 7, 33, 7, 7, 17, 14, 123, 104, 226, 82, 178, 91, 900, 1176, 72, 187, 565, 797]

theorem plane484GenLeaf0109 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0109Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0109Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 175
  · exact hroot.hOcc 198
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 209
  · exact hroot.hOcc 356
  · exact hroot.hOcc 399
  · exact hroot.hOcc 615
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 720
  · exact hroot.hOcc 860
  · exact hroot.hOcc 902
  · exact hroot.hOcc 921
  · exact hroot.hOcc 1087
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
