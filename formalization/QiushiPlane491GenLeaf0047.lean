import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0047Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 100, .occ 106, .occ 107, .occ 110, .occ 113, .occ 116, .occ 119, .occ 150, .occ 161, .occ 230, .occ 231, .occ 244, .occ 293, .occ 305, .occ 324, .occ 329, .occ 335, .occ 338, .occ 359, .occ 365, .occ 370, .occ 394, .occ 409, .occ 424, .occ 431, .occ 470, .occ 539, .occ 590, .occ 622, .occ 626, .occ 642, .occ 664, .occ 665, .occ 700, .occ 704, .occ 710, .occ 711, .occ 725, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchLe 43 (0), .branchLe 6 (0), .branchLe 44 (0), .branchLe 7 (0)]

def plane491GenLeaf0047Mult : Fin 50 → Nat := ![119546, 266878, 1200635, 153682, 427509, 290761, 110073, 232047, 26491, 716868, 255754, 507810, 45591, 413024, 54544, 69403, 109204, 111214, 39637, 415408, 80527, 37217, 94884, 173332, 713103, 276657, 10867, 183641, 263853, 118755, 376882, 80047, 115449, 505306, 167953, 405922, 61121, 69858, 53762, 1572252, 299959, 1308157, 3234824, 1404299, 1382230, 1350537, 1035351, 1228352, 1140826, 1201049]

theorem plane491GenLeaf0047 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0047Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0047Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0047Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0047Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 150
  · exact hroot.hOcc 161
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 244
  · exact hroot.hOcc 293
  · exact hroot.hOcc 305
  · exact hroot.hOcc 324
  · exact hroot.hOcc 329
  · exact hroot.hOcc 335
  · exact hroot.hOcc 338
  · exact hroot.hOcc 359
  · exact hroot.hOcc 365
  · exact hroot.hOcc 370
  · exact hroot.hOcc 394
  · exact hroot.hOcc 409
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 470
  · exact hroot.hOcc 539
  · exact hroot.hOcc 590
  · exact hroot.hOcc 622
  · exact hroot.hOcc 626
  · exact hroot.hOcc 642
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · exact hroot.hOcc 700
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · exact hroot.hOcc 711
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul
