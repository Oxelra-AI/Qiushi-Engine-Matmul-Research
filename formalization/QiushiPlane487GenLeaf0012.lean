import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0012Refs : Fin 46 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 85, .occ 86, .occ 90, .occ 100, .occ 118, .occ 119, .occ 204, .occ 217, .occ 240, .occ 253, .occ 270, .occ 303, .occ 315, .occ 340, .occ 343, .occ 347, .occ 349, .occ 353, .occ 359, .occ 380, .occ 386, .occ 387, .occ 390, .occ 398, .occ 399, .occ 402, .occ 411, .occ 470, .occ 523, .occ 577, .occ 589, .occ 604, .occ 609, .occ 643, .occ 650, .occ 651, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 12 (1), .branchLe 3 (0), .branchLe 24 (0), .branchGe 36 (1)]

def plane487GenLeaf0012Mult : Fin 46 → Nat := ![28, 640, 562, 931, 86, 275, 2248, 1364, 178, 226, 99, 682, 139, 1330, 457, 167, 116, 226, 421, 74, 414, 703, 174, 146, 814, 226, 1667, 4, 253, 909, 283, 179, 4, 507, 74, 80, 124, 283, 2427, 1274, 1687, 2223, 3589, 205, 2137, 5009]

theorem plane487GenLeaf0012 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0012Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0012Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 100
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 204
  · exact hroot.hOcc 217
  · exact hroot.hOcc 240
  · exact hroot.hOcc 253
  · exact hroot.hOcc 270
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 340
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 349
  · exact hroot.hOcc 353
  · exact hroot.hOcc 359
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 390
  · exact hroot.hOcc 398
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 411
  · exact hroot.hOcc 470
  · exact hroot.hOcc 523
  · exact hroot.hOcc 577
  · exact hroot.hOcc 589
  · exact hroot.hOcc 604
  · exact hroot.hOcc 609
  · exact hroot.hOcc 643
  · exact hroot.hOcc 650
  · exact hroot.hOcc 651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
