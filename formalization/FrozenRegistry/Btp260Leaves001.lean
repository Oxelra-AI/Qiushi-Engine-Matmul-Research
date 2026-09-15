import FrozenRegistry.Btp260Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0016Refs : Fin 2 → RowRef 33 31 := ![.occ 0, .branchGe 0 (3)]

def plane260BtpGenLeaf0016Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0016 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0016Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0016Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0017Refs : Fin 2 → RowRef 33 31 := ![.occ 1, .branchGe 1 (1)]

def plane260BtpGenLeaf0017Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0017 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0017Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0017Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0018Refs : Fin 2 → RowRef 33 31 := ![.occ 2, .branchGe 2 (1)]

def plane260BtpGenLeaf0018Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0018 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0018Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0018Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0019Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (1), .branchLe 4 (1), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0019Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0019 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (1 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0019Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0019Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (15 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (18 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (20 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (21 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (22 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (23 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (24 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (27 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (28 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (29 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (30 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0020Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (1), .branchLe 4 (1), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0020Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0020 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (1 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0020Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0020Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (15 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (18 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (20 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (21 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (22 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (23 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (24 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (27 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (28 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (29 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (30 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0021Refs : Fin 4 → RowRef 33 31 := ![.occ 4, .branchGe 0 (2), .branchGe 3 (1), .branchGe 4 (1)]

def plane260BtpGenLeaf0021Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane260BtpGenLeaf0021 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0021Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0021Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0022Refs : Fin 2 → RowRef 33 31 := ![.occ 1, .branchGe 1 (1)]

def plane260BtpGenLeaf0022Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0022 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0022Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0022Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0023Refs : Fin 2 → RowRef 33 31 := ![.occ 2, .branchGe 2 (1)]

def plane260BtpGenLeaf0023Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0023 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0023Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0023Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0024Refs : Fin 2 → RowRef 33 31 := ![.occ 3, .branchGe 3 (2)]

def plane260BtpGenLeaf0024Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0024 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_3 : (2 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0024Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0024Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0025Refs : Fin 2 → RowRef 33 31 := ![.occ 5, .branchGe 4 (2)]

def plane260BtpGenLeaf0025Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0025 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_4 : (2 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0025Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0025Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0026Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0026Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0026 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
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
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0026Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0026Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (15 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (18 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (20 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (21 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (22 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (23 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (24 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (27 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (28 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (29 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (30 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0027Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0027Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0027 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
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
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0027Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0027Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (15 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (18 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (20 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (21 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (22 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (23 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (24 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (27 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (28 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (29 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (30 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0028Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0028Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0028 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
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
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0028Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0028Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (15 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (18 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (20 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (21 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (22 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (23 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (24 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (27 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (28 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (29 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (30 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0029Refs : Fin 2 → RowRef 33 31 := ![.occ 0, .branchGe 0 (3)]

def plane260BtpGenLeaf0029Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0029 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0029Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0029Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0030Refs : Fin 2 → RowRef 33 31 := ![.occ 1, .branchGe 1 (1)]

def plane260BtpGenLeaf0030Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0030 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0030Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0030Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0031Refs : Fin 2 → RowRef 33 31 := ![.occ 2, .branchGe 2 (1)]

def plane260BtpGenLeaf0031Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0031 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0031Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0031Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
