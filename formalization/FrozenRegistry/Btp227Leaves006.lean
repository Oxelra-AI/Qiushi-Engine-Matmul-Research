import FrozenRegistry.Btp227Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0096Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0096Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0096 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0096Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0096Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0097Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0097Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0097 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0097Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0097Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0098Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0098Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0098 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0098Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0098Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0099Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0099Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0099 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0099Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0099Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0100Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0100Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0100 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0100Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0100Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0101Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0101Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0101 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0101Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0101Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0102Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0102Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0102 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0102Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0102Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0103Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0103Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0103 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0103Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0103Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0104Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0104Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0104 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0104Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0104Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
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

def plane227BtpGenLeaf0105Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0105Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0105 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0105Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0105Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0106Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0106Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0106 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0106Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0106Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0106Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0106Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0107Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane227BtpGenLeaf0107Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0107 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0107Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0107Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0108Refs : Fin 2 → RowRef 15 15 := ![.occ 3, .branchGe 3 (1)]

def plane227BtpGenLeaf0108Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0108 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0108Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0108Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0109Refs : Fin 2 → RowRef 15 15 := ![.occ 4, .branchGe 4 (1)]

def plane227BtpGenLeaf0109Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0109 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0109Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0109Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0110Refs : Fin 2 → RowRef 15 15 := ![.occ 5, .branchGe 5 (3)]

def plane227BtpGenLeaf0110Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0110 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_5 : (3 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0110Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0110Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0111Refs : Fin 2 → RowRef 15 15 := ![.occ 6, .branchGe 6 (1)]

def plane227BtpGenLeaf0111Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0111 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0111Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0111Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
