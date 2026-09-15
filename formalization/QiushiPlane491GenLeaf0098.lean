import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0098Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 98, .occ 112, .occ 116, .occ 118, .occ 137, .occ 200, .occ 219, .occ 230, .occ 234, .occ 257, .occ 258, .occ 275, .occ 299, .occ 307, .occ 318, .occ 329, .occ 332, .occ 341, .occ 350, .occ 363, .occ 365, .occ 368, .occ 400, .occ 404, .occ 421, .occ 422, .occ 431, .occ 435, .occ 449, .occ 501, .occ 529, .occ 531, .occ 534, .occ 543, .occ 565, .occ 606, .occ 640, .occ 662, .occ 671, .occ 691, .occ 722, .sumGe, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchLe 28 (0), .branchGe 0 (1)]

def plane491GenLeaf0098Mult : Fin 50 → Nat := ![177210, 170550, 60986, 128270, 9344, 83106, 32876, 17178, 3545, 14324, 18082, 95845, 16692, 22964, 7714, 44770, 64558, 63729, 26487, 6242, 31924, 8232, 62661, 33880, 103509, 4586, 36252, 8718, 118469, 76770, 17002, 5538, 22964, 52006, 22964, 8978, 17876, 40266, 50252, 25942, 21016, 71704, 135025, 302400, 505692, 398606, 206344, 221718, 250394, 550520]

theorem plane491GenLeaf0098 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0098Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0098Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 137
  · exact hroot.hOcc 200
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 234
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 299
  · exact hroot.hOcc 307
  · exact hroot.hOcc 318
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 341
  · exact hroot.hOcc 350
  · exact hroot.hOcc 363
  · exact hroot.hOcc 365
  · exact hroot.hOcc 368
  · exact hroot.hOcc 400
  · exact hroot.hOcc 404
  · exact hroot.hOcc 421
  · exact hroot.hOcc 422
  · exact hroot.hOcc 431
  · exact hroot.hOcc 435
  · exact hroot.hOcc 449
  · exact hroot.hOcc 501
  · exact hroot.hOcc 529
  · exact hroot.hOcc 531
  · exact hroot.hOcc 534
  · exact hroot.hOcc 543
  · exact hroot.hOcc 565
  · exact hroot.hOcc 606
  · exact hroot.hOcc 640
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 691
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
