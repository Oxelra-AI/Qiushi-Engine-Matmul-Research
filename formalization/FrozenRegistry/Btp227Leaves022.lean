import FrozenRegistry.Btp227Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0352Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0352Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0352 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0352Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0352Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0352Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0352Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0353Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0353Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0353 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0353Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0353Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0353Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0353Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0354Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0354Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0354 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0354Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0354Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0354Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0354Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0355Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0355Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0355 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0355Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0355Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0355Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0355Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0356Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0356Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0356 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0356Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0356Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0356Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0356Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0357Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0357Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0357 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0357Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0357Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0357Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0357Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0358Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0358Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0358 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0358Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0358Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0358Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0358Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0359Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane227BtpGenLeaf0359Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0359 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0359Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0359Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0359Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0359Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0360Refs : Fin 2 → RowRef 15 15 := ![.occ 3, .branchGe 3 (1)]

def plane227BtpGenLeaf0360Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0360 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0360Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0360Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0360Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0360Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0361Refs : Fin 2 → RowRef 15 15 := ![.occ 4, .branchGe 4 (1)]

def plane227BtpGenLeaf0361Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0361 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0361Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0361Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0361Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0361Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0362Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0362Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0362 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0362Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0362Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0362Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0362Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0363Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0363Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0363 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0363Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0363Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0363Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0363Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0364Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0364Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0364 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0364Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0364Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0364Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0364Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0365Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0365Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0365 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0365Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0365Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0365Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0365Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0366Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0366Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0366 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0366Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0366Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0366Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0366Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0367Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (2), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0367Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0367 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0367Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0367Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0367Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0367Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
