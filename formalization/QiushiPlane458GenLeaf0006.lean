import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0006Refs : Fin 57 → RowRef 203 56 := ![.occ 10, .occ 11, .occ 15, .occ 20, .occ 23, .occ 25, .occ 30, .occ 48, .occ 56, .occ 58, .occ 66, .occ 73, .occ 74, .occ 75, .occ 82, .occ 84, .occ 91, .occ 95, .occ 102, .occ 106, .occ 110, .occ 111, .occ 114, .occ 115, .occ 120, .occ 123, .occ 124, .occ 125, .occ 129, .occ 137, .occ 140, .occ 151, .occ 152, .occ 154, .occ 157, .occ 161, .occ 168, .occ 180, .occ 186, .occ 187, .occ 196, .occ 198, .sumGe, .nonneg 19, .nonneg 20, .nonneg 22, .nonneg 23, .nonneg 25, .nonneg 29, .nonneg 36, .nonneg 38, .nonneg 45, .nonneg 52, .nonneg 53, .branchLe 46 (0), .branchGe 30 (1), .branchGe 10 (1)]

def plane458GenLeaf0006Mult : Fin 57 → Nat := ![20815, 4818, 14950, 18470, 3034, 19394, 1904, 1850, 17335, 16491, 4995, 7993, 9948, 6354, 2007, 1421, 822, 1493, 2301, 8152, 714, 12462, 9340, 889, 963, 1054, 574, 5105, 392, 351, 2261, 2961, 3455, 2658, 860, 2345, 6346, 5471, 1552, 8209, 2168, 1363, 20815, 11159, 11825, 13470, 768, 1256, 8595, 7141, 2573, 4014, 17164, 4541, 15344, 9441, 135525]

theorem plane458GenLeaf0006 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_46 : x 46 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0006Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0006Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 30
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 66
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 82
  · exact hroot.hOcc 84
  · exact hroot.hOcc 91
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 168
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (36 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (45 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (10 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
