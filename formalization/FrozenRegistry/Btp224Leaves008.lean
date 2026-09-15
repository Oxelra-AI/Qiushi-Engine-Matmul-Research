import FrozenRegistry.Btp224Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0128Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0128Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0128 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0128Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0128Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0128Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0128Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0129Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0129Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0129 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (2 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0129Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0129Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0129Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0129Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0130Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0130Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0130 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0130Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0130Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0130Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0130Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0131Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0131Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0131 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0131Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0131Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0131Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0131Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0132Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0132Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0132 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0132Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0132Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0132Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0132Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0133Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0133Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0133 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0133Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0133Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0133Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0133Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0134Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (1), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0134Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0134 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0134Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0134Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0134Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0134Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0135Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0135Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0135 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0135Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0135Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0135Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0135Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0136Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0136Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0136 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (2 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0136Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0136Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0136Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0136Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0137Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0137Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0137 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0137Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0137Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0137Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0137Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0138Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0138Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0138 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0138Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0138Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0138Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0138Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0139Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane224BtpGenLeaf0139Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0139 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0139Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0139Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0139Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0139Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0140Refs : Fin 2 → RowRef 15 15 := ![.occ 3, .branchGe 3 (1)]

def plane224BtpGenLeaf0140Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0140 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0140Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0140Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0140Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0140Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0141Refs : Fin 2 → RowRef 15 15 := ![.occ 4, .branchGe 4 (3)]

def plane224BtpGenLeaf0141Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0141 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_4 : (3 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0141Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0141Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0141Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0141Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0142Refs : Fin 2 → RowRef 15 15 := ![.occ 5, .branchGe 5 (1)]

def plane224BtpGenLeaf0142Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0142 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0142Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0142Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0142Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0142Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0143Refs : Fin 2 → RowRef 15 15 := ![.occ 6, .branchGe 6 (1)]

def plane224BtpGenLeaf0143Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0143 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0143Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0143Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0143Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0143Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
