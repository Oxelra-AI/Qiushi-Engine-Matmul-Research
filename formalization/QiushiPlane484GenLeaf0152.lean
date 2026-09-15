import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0152Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 134, .occ 139, .occ 142, .occ 290, .occ 297, .occ 298, .occ 372, .occ 386, .occ 396, .occ 619, .occ 822, .occ 997, .occ 1136, .occ 1151, .occ 1159, .occ 1164, .occ 1215, .occ 1216, .occ 1243, .occ 1251, .occ 1268, .occ 1283, .occ 1302, .occ 1332, .occ 1353, .occ 1358, .occ 1380, .occ 1404, .occ 1419, .occ 1459, .occ 1471, .occ 1543, .occ 1625, .occ 1656, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchGe 16 (1)]

def plane484GenLeaf0152Mult : Fin 43 → Nat := ![2762, 380, 12684, 186, 4642, 7404, 16718, 4442, 4442, 1983, 360, 26742, 1803, 5782, 4593, 497, 6398, 1098, 1702, 6059, 1770, 334, 3727, 2352, 12008, 4837, 6625, 13924, 2440, 11983, 232, 4993, 4178, 2903, 6830, 33572, 26264, 29130, 106049, 33075, 13250, 106255, 100487]

theorem plane484GenLeaf0152 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0152Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0152Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0152Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0152Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 290
  · exact hroot.hOcc 297
  · exact hroot.hOcc 298
  · exact hroot.hOcc 372
  · exact hroot.hOcc 386
  · exact hroot.hOcc 396
  · exact hroot.hOcc 619
  · exact hroot.hOcc 822
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1332
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
