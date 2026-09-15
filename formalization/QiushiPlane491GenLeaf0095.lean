import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0095Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 98, .occ 99, .occ 103, .occ 111, .occ 114, .occ 118, .occ 133, .occ 171, .occ 219, .occ 221, .occ 222, .occ 234, .occ 267, .occ 272, .occ 273, .occ 284, .occ 315, .occ 326, .occ 327, .occ 332, .occ 340, .occ 350, .occ 365, .occ 367, .occ 374, .occ 393, .occ 408, .occ 422, .occ 426, .occ 485, .occ 511, .occ 565, .occ 582, .occ 606, .occ 630, .occ 634, .occ 662, .occ 680, .occ 686, .occ 716, .occ 720, .occ 722, .sumGe, .nonneg 17, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchGe 7 (1)]

def plane491GenLeaf0095Mult : Fin 50 → Nat := ![104416, 82799, 113904, 58246, 6586, 43789, 114272, 60637, 25360, 4589, 26483, 33658, 15230, 31499, 17350, 10935, 30028, 4990, 55918, 20048, 26291, 18244, 65061, 1331, 49595, 45134, 27485, 5988, 24347, 48487, 17350, 8671, 11284, 41084, 10976, 16000, 10135, 1961, 40488, 8586, 5738, 34377, 1792, 144455, 1925, 367610, 98226, 334183, 124636, 521987]

theorem plane491GenLeaf0095 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0095Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0095Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0095Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0095Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 133
  · exact hroot.hOcc 171
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 222
  · exact hroot.hOcc 234
  · exact hroot.hOcc 267
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · exact hroot.hOcc 284
  · exact hroot.hOcc 315
  · exact hroot.hOcc 326
  · exact hroot.hOcc 327
  · exact hroot.hOcc 332
  · exact hroot.hOcc 340
  · exact hroot.hOcc 350
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 374
  · exact hroot.hOcc 393
  · exact hroot.hOcc 408
  · exact hroot.hOcc 422
  · exact hroot.hOcc 426
  · exact hroot.hOcc 485
  · exact hroot.hOcc 511
  · exact hroot.hOcc 565
  · exact hroot.hOcc 582
  · exact hroot.hOcc 606
  · exact hroot.hOcc 630
  · exact hroot.hOcc 634
  · exact hroot.hOcc 662
  · exact hroot.hOcc 680
  · exact hroot.hOcc 686
  · exact hroot.hOcc 716
  · exact hroot.hOcc 720
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
