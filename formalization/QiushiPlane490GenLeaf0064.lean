import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0064Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 115, .occ 117, .occ 151, .occ 184, .occ 195, .occ 196, .occ 235, .occ 238, .occ 244, .occ 247, .occ 274, .occ 280, .occ 295, .occ 302, .occ 306, .occ 322, .occ 336, .occ 375, .occ 461, .occ 462, .occ 468, .occ 471, .occ 482, .occ 498, .occ 525, .occ 541, .occ 542, .occ 575, .occ 635, .occ 677, .occ 690, .occ 700, .occ 706, .sumGe, .nonneg 17, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchLe 25 (0), .branchLe 18 (0), .branchLe 21 (0), .branchLe 11 (0)]

def plane490GenLeaf0064Mult : Fin 44 → Nat := ![174540, 364829, 73746, 37949, 66105, 75758, 16400, 324023, 122073, 64787, 41218, 95175, 124093, 71218, 179965, 87846, 155071, 103245, 126743, 77817, 111504, 85846, 101105, 143864, 73414, 656, 16242, 226429, 113905, 15489, 54547, 30978, 179630, 43640, 659317, 55279, 383370, 1156279, 588099, 990143, 383521, 615677, 571857, 567159]

theorem plane490GenLeaf0064 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0064Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0064Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0064Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0064Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 115
  · exact hroot.hOcc 117
  · exact hroot.hOcc 151
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 274
  · exact hroot.hOcc 280
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 306
  · exact hroot.hOcc 322
  · exact hroot.hOcc 336
  · exact hroot.hOcc 375
  · exact hroot.hOcc 461
  · exact hroot.hOcc 462
  · exact hroot.hOcc 468
  · exact hroot.hOcc 471
  · exact hroot.hOcc 482
  · exact hroot.hOcc 498
  · exact hroot.hOcc 525
  · exact hroot.hOcc 541
  · exact hroot.hOcc 542
  · exact hroot.hOcc 575
  · exact hroot.hOcc 635
  · exact hroot.hOcc 677
  · exact hroot.hOcc 690
  · exact hroot.hOcc 700
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
