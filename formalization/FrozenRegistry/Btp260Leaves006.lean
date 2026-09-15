import FrozenRegistry.Btp260Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0096Refs : Fin 32 → RowRef 33 31 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (1), .branchLe 4 (1), .branchLe 5 (1), .branchLe 6 (1), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane260BtpGenLeaf0096Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane260BtpGenLeaf0096 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (1 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (1 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0096Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0096Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane260BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_6
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

def plane260BtpGenLeaf0097Refs : Fin 4 → RowRef 33 31 := ![.occ 7, .branchGe 0 (2), .branchGe 5 (1), .branchGe 6 (1)]

def plane260BtpGenLeaf0097Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane260BtpGenLeaf0097 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0097Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0097Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (5 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (6 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0098Refs : Fin 2 → RowRef 33 31 := ![.occ 1, .branchGe 1 (1)]

def plane260BtpGenLeaf0098Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0098 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0098Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0098Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0099Refs : Fin 2 → RowRef 33 31 := ![.occ 2, .branchGe 2 (1)]

def plane260BtpGenLeaf0099Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0099 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0099Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0099Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0100Refs : Fin 2 → RowRef 33 31 := ![.occ 3, .branchGe 3 (2)]

def plane260BtpGenLeaf0100Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0100 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_3 : (2 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0100Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0100Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0101Refs : Fin 2 → RowRef 33 31 := ![.occ 5, .branchGe 4 (2)]

def plane260BtpGenLeaf0101Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0101 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_4 : (2 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0101Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0101Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0102Refs : Fin 2 → RowRef 33 31 := ![.occ 6, .branchGe 5 (2)]

def plane260BtpGenLeaf0102Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0102 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0102Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0102Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (5 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0103Refs : Fin 2 → RowRef 33 31 := ![.occ 8, .branchGe 6 (2)]

def plane260BtpGenLeaf0103Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0103 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_6 : (2 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0103Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0103Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (6 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0104Refs : Fin 2 → RowRef 33 31 := ![.occ 9, .branchGe 7 (1)]

def plane260BtpGenLeaf0104Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0104 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0104Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0104Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (7 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0105Refs : Fin 2 → RowRef 33 31 := ![.occ 10, .branchGe 8 (1)]

def plane260BtpGenLeaf0105Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0105 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0105Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0105Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (8 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0106Refs : Fin 2 → RowRef 33 31 := ![.occ 11, .branchGe 9 (1)]

def plane260BtpGenLeaf0106Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0106 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0106Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0106Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0106Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0106Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (9 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0107Refs : Fin 2 → RowRef 33 31 := ![.occ 12, .branchGe 10 (1)]

def plane260BtpGenLeaf0107Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0107 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0107Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0107Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (10 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0108Refs : Fin 2 → RowRef 33 31 := ![.occ 13, .branchGe 11 (1)]

def plane260BtpGenLeaf0108Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0108 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0108Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0108Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (11 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0109Refs : Fin 2 → RowRef 33 31 := ![.occ 14, .branchGe 12 (1)]

def plane260BtpGenLeaf0109Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0109 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0109Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0109Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (12 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0110Refs : Fin 2 → RowRef 33 31 := ![.occ 15, .branchGe 13 (1)]

def plane260BtpGenLeaf0110Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0110 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0110Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0110Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · change (∑ k, (if k = (13 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0111Refs : Fin 2 → RowRef 33 31 := ![.occ 16, .branchGe 14 (1)]

def plane260BtpGenLeaf0111Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0111 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0111Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0111Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · change (∑ k, (if k = (14 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
