import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0118Refs : Fin 50 → RowRef 726 49 := ![.occ 87, .occ 98, .occ 112, .occ 128, .occ 130, .occ 160, .occ 238, .occ 239, .occ 244, .occ 255, .occ 257, .occ 258, .occ 270, .occ 275, .occ 288, .occ 299, .occ 306, .occ 318, .occ 334, .occ 350, .occ 377, .occ 402, .occ 404, .occ 421, .occ 455, .occ 462, .occ 563, .occ 565, .occ 567, .occ 572, .occ 576, .occ 582, .occ 606, .occ 611, .occ 631, .occ 632, .occ 643, .occ 654, .occ 702, .occ 719, .sumGe, .nonneg 32, .nonneg 33, .nonneg 42, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchLe 13 (0), .branchGe 5 (1)]

def plane491GenLeaf0118Mult : Fin 50 → Nat := ![86505, 55107, 43986, 28352, 63069, 4697, 49711, 20005, 70663, 27940, 15482, 2392, 15920, 18247, 49908, 22733, 30691, 22362, 22955, 618, 16006, 34623, 19554, 12062, 608, 4008, 8811, 15066, 9400, 4451, 1806, 4379, 30744, 27940, 5860, 2027, 1835, 20274, 8073, 33269, 100438, 26138, 15870, 24403, 234539, 150537, 108506, 169454, 100438, 502119]

theorem plane491GenLeaf0118 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0118Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0118Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0118Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0118Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 160
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 270
  · exact hroot.hOcc 275
  · exact hroot.hOcc 288
  · exact hroot.hOcc 299
  · exact hroot.hOcc 306
  · exact hroot.hOcc 318
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 377
  · exact hroot.hOcc 402
  · exact hroot.hOcc 404
  · exact hroot.hOcc 421
  · exact hroot.hOcc 455
  · exact hroot.hOcc 462
  · exact hroot.hOcc 563
  · exact hroot.hOcc 565
  · exact hroot.hOcc 567
  · exact hroot.hOcc 572
  · exact hroot.hOcc 576
  · exact hroot.hOcc 582
  · exact hroot.hOcc 606
  · exact hroot.hOcc 611
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 643
  · exact hroot.hOcc 654
  · exact hroot.hOcc 702
  · exact hroot.hOcc 719
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (42 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
