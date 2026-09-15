import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0051Refs : Fin 43 → RowRef 713 43 := ![.occ 91, .occ 101, .occ 107, .occ 116, .occ 118, .occ 164, .occ 177, .occ 182, .occ 201, .occ 203, .occ 234, .occ 237, .occ 239, .occ 274, .occ 277, .occ 284, .occ 290, .occ 300, .occ 312, .occ 335, .occ 340, .occ 362, .occ 364, .occ 375, .occ 395, .occ 416, .occ 460, .occ 480, .occ 520, .occ 521, .occ 525, .occ 530, .occ 531, .occ 647, .sumGe, .nonneg 5, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchGe 39 (1), .branchLe 19 (0)]

def plane490GenLeaf0051Mult : Fin 43 → Nat := ![917, 793, 330, 1232, 953, 1676, 2953, 849, 1732, 96, 74, 1288, 2867, 24, 1556, 412, 849, 667, 543, 2536, 24, 1321, 464, 1583, 2179, 787, 1733, 1191, 519, 689, 354, 706, 91, 1334, 4600, 318, 3911, 3727, 354, 4045, 19407, 10563, 2867]

theorem plane490GenLeaf0051 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0051Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0051Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0051Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0051Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 101
  · exact hroot.hOcc 107
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 164
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 234
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 274
  · exact hroot.hOcc 277
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 300
  · exact hroot.hOcc 312
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 416
  · exact hroot.hOcc 460
  · exact hroot.hOcc 480
  · exact hroot.hOcc 520
  · exact hroot.hOcc 521
  · exact hroot.hOcc 525
  · exact hroot.hOcc 530
  · exact hroot.hOcc 531
  · exact hroot.hOcc 647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
