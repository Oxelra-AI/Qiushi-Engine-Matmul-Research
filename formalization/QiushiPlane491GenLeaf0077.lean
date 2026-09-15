import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0077Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 85, .occ 98, .occ 102, .occ 118, .occ 121, .occ 170, .occ 171, .occ 178, .occ 219, .occ 234, .occ 312, .occ 315, .occ 320, .occ 323, .occ 332, .occ 393, .occ 402, .occ 418, .occ 423, .occ 482, .occ 487, .occ 490, .occ 501, .occ 505, .occ 512, .occ 517, .occ 525, .occ 526, .occ 534, .occ 548, .occ 582, .occ 621, .occ 662, .occ 687, .occ 704, .occ 711, .occ 714, .occ 721, .occ 722, .sumGe, .nonneg 36, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchGe 15 (1), .branchLe 48 (0), .branchGe 38 (1)]

def plane491GenLeaf0077Mult : Fin 50 → Nat := ![68163, 55874, 362606, 74078, 65199, 332719, 109098, 47582, 38785, 62573, 24425, 38536, 102082, 54400, 147952, 39276, 134019, 160, 33450, 26867, 11503, 28395, 71864, 120218, 16276, 3692, 63881, 24843, 20685, 1386, 71948, 27761, 145691, 59061, 67039, 18102, 64339, 65074, 24837, 1021, 401142, 140208, 1095331, 400121, 311279, 252169, 233047, 382134, 383040, 738732]

theorem plane491GenLeaf0077 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0077Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0077Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0077Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0077Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 98
  · exact hroot.hOcc 102
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 219
  · exact hroot.hOcc 234
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 320
  · exact hroot.hOcc 323
  · exact hroot.hOcc 332
  · exact hroot.hOcc 393
  · exact hroot.hOcc 402
  · exact hroot.hOcc 418
  · exact hroot.hOcc 423
  · exact hroot.hOcc 482
  · exact hroot.hOcc 487
  · exact hroot.hOcc 490
  · exact hroot.hOcc 501
  · exact hroot.hOcc 505
  · exact hroot.hOcc 512
  · exact hroot.hOcc 517
  · exact hroot.hOcc 525
  · exact hroot.hOcc 526
  · exact hroot.hOcc 534
  · exact hroot.hOcc 548
  · exact hroot.hOcc 582
  · exact hroot.hOcc 621
  · exact hroot.hOcc 662
  · exact hroot.hOcc 687
  · exact hroot.hOcc 704
  · exact hroot.hOcc 711
  · exact hroot.hOcc 714
  · exact hroot.hOcc 721
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (36 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (48 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
