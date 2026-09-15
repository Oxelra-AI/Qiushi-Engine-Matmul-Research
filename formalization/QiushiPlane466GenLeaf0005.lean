import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0005Refs : Fin 51 → RowRef 210 50 := ![.occ 38, .occ 41, .occ 50, .occ 56, .occ 62, .occ 63, .occ 64, .occ 67, .occ 71, .occ 83, .occ 84, .occ 87, .occ 97, .occ 98, .occ 100, .occ 101, .occ 102, .occ 103, .occ 106, .occ 111, .occ 113, .occ 114, .occ 117, .occ 125, .occ 130, .occ 133, .occ 156, .occ 163, .occ 165, .occ 167, .occ 172, .occ 177, .occ 183, .occ 191, .occ 196, .occ 201, .occ 202, .occ 209, .sumGe, .nonneg 0, .nonneg 14, .nonneg 31, .nonneg 35, .nonneg 38, .nonneg 41, .nonneg 46, .branchLe 24 (0), .branchGe 19 (1), .branchLe 30 (1), .branchLe 12 (0), .branchGe 21 (1)]

def plane466GenLeaf0005Mult : Fin 51 → Nat := ![41710, 25304, 15866, 97937, 14971, 28372, 6301, 62154, 1783, 11749, 21374, 45890, 17372, 11992, 19288, 23147, 70020, 32710, 16358, 24355, 13195, 29691, 49018, 28895, 11599, 42924, 11707, 8, 14165, 3062, 30372, 12152, 9833, 2176, 4790, 33292, 14215, 4944, 119680, 27414, 49410, 14540, 24519, 32993, 37927, 43314, 119680, 123580, 116618, 96525, 316732]

theorem plane466GenLeaf0005 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0005Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0005Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 50
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 71
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 156
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 172
  · exact hroot.hOcc 177
  · exact hroot.hOcc 183
  · exact hroot.hOcc 191
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (12 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
