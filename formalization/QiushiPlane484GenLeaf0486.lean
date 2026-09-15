import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0486Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 133, .occ 135, .occ 141, .occ 142, .occ 175, .occ 537, .occ 575, .occ 952, .occ 1136, .occ 1143, .occ 1145, .occ 1158, .occ 1164, .occ 1168, .occ 1172, .occ 1206, .occ 1216, .occ 1317, .occ 1318, .occ 1330, .occ 1339, .occ 1431, .occ 1454, .occ 1458, .occ 1459, .occ 1564, .occ 1609, .occ 1652, .occ 1653, .occ 1655, .sumGe, .nonneg 16, .nonneg 21, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchGe 25 (1), .branchLe 2 (0), .branchLe 31 (0)]

def plane484GenLeaf0486Mult : Fin 44 → Nat := ![25296, 12250, 33360, 33884, 12772, 64101, 18935, 32568, 5686, 323, 10201, 17774, 1871, 7220, 2539, 12987, 4378, 2539, 3023, 7664, 2084, 6204, 348, 27275, 13811, 13058, 12125, 9899, 11622, 7397, 7902, 1510, 77891, 2842, 111014, 14992, 138218, 68132, 55200, 107433, 24362, 227912, 24362, 67992]

theorem plane484GenLeaf0486 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0486Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0486Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0486Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0486Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 537
  · exact hroot.hOcc 575
  · exact hroot.hOcc 952
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
