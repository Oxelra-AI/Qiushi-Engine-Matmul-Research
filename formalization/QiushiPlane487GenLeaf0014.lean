import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0014Refs : Fin 49 → RowRef 668 48 := ![.occ 97, .occ 104, .occ 105, .occ 112, .occ 115, .occ 118, .occ 119, .occ 122, .occ 156, .occ 205, .occ 216, .occ 223, .occ 240, .occ 249, .occ 250, .occ 253, .occ 257, .occ 297, .occ 315, .occ 316, .occ 322, .occ 352, .occ 356, .occ 374, .occ 379, .occ 386, .occ 387, .occ 389, .occ 399, .occ 425, .occ 464, .occ 465, .occ 470, .occ 479, .occ 570, .occ 604, .occ 611, .occ 635, .occ 639, .occ 651, .occ 664, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchGe 12 (1), .branchGe 3 (1), .branchLe 26 (0)]

def plane487GenLeaf0014Mult : Fin 49 → Nat := ![48391, 10742, 205010, 48374, 104677, 53565, 230822, 107284, 69534, 22286, 184561, 121448, 12553, 13762, 24780, 91864, 29302, 158955, 82113, 29479, 70965, 25645, 199881, 120398, 1329, 138153, 4411, 10602, 51668, 17400, 16057, 3946, 74812, 17129, 28922, 95177, 27542, 3536, 110375, 26023, 58412, 417986, 267633, 308521, 417986, 366318, 417441, 1144154, 400586]

theorem plane487GenLeaf0014 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0014Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0014Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 156
  · exact hroot.hOcc 205
  · exact hroot.hOcc 216
  · exact hroot.hOcc 223
  · exact hroot.hOcc 240
  · exact hroot.hOcc 249
  · exact hroot.hOcc 250
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 297
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 322
  · exact hroot.hOcc 352
  · exact hroot.hOcc 356
  · exact hroot.hOcc 374
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 389
  · exact hroot.hOcc 399
  · exact hroot.hOcc 425
  · exact hroot.hOcc 464
  · exact hroot.hOcc 465
  · exact hroot.hOcc 470
  · exact hroot.hOcc 479
  · exact hroot.hOcc 570
  · exact hroot.hOcc 604
  · exact hroot.hOcc 611
  · exact hroot.hOcc 635
  · exact hroot.hOcc 639
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (26 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
