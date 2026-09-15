import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0434Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 140, .occ 142, .occ 179, .occ 378, .occ 416, .occ 691, .occ 858, .occ 961, .occ 1020, .occ 1046, .occ 1072, .occ 1158, .occ 1191, .occ 1200, .occ 1249, .occ 1250, .occ 1280, .occ 1282, .occ 1318, .occ 1336, .occ 1350, .occ 1358, .occ 1385, .occ 1409, .occ 1410, .occ 1454, .occ 1509, .occ 1609, .occ 1610, .occ 1615, .occ 1630, .sumGe, .nonneg 0, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchGe 40 (1), .branchGe 6 (1)]

def plane484GenLeaf0434Mult : Fin 43 → Nat := ![292618, 265592, 231426, 131112, 83660, 237478, 110054, 41040, 230360, 50353, 68626, 81336, 19116, 280204, 21030, 227016, 17726, 98581, 80082, 68344, 48451, 68344, 67833, 121654, 41389, 58701, 78241, 8105, 68344, 98624, 119654, 121654, 136294, 743998, 128904, 1664154, 383712, 455052, 743998, 743998, 743998, 757818, 1335020]

theorem plane484GenLeaf0434 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0434Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0434Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0434Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0434Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 179
  · exact hroot.hOcc 378
  · exact hroot.hOcc 416
  · exact hroot.hOcc 691
  · exact hroot.hOcc 858
  · exact hroot.hOcc 961
  · exact hroot.hOcc 1020
  · exact hroot.hOcc 1046
  · exact hroot.hOcc 1072
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1630
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
