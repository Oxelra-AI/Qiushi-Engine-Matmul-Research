import FrozenRegistry.Btp265Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0208Refs : Fin 32 → RowRef 31 31 := ![.sumGe, .branchLe 0 (3), .branchLe 1 (1), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (1), .branchLe 6 (1), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 17 (1), .branchLe 18 (0), .branchLe 19 (0), .branchLe 20 (0), .branchLe 21 (0), .branchLe 22 (0), .branchLe 23 (0), .branchLe 24 (0), .branchLe 25 (0), .branchLe 26 (0), .branchLe 27 (0), .branchLe 28 (0), .branchLe 29 (0), .branchLe 30 (0)]

def plane265BtpGenLeaf0208Mult : Fin 32 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane265BtpGenLeaf0208 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (3 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
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
    (hUB_17 : x 17 ≤ (1 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0208Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0208Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0208Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0208Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane265BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 31) then (1 : Int) else 0) * x k) ≤ (3 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 31) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
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
  · change (∑ k, (if k = (17 : Fin 31) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_17
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

def plane265BtpGenLeaf0209Refs : Fin 2 → RowRef 31 31 := ![.occ 0, .branchGe 0 (4)]

def plane265BtpGenLeaf0209Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0209 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_0 : (4 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0209Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0209Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0209Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0209Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(4 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0210Refs : Fin 2 → RowRef 31 31 := ![.occ 1, .branchGe 1 (2)]

def plane265BtpGenLeaf0210Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0210 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_1 : (2 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0210Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0210Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0210Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0210Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0211Refs : Fin 2 → RowRef 31 31 := ![.occ 2, .branchGe 2 (2)]

def plane265BtpGenLeaf0211Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0211 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_2 : (2 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0211Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0211Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0211Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0211Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0212Refs : Fin 2 → RowRef 31 31 := ![.occ 3, .branchGe 3 (1)]

def plane265BtpGenLeaf0212Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0212 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0212Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0212Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0212Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0212Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0213Refs : Fin 2 → RowRef 31 31 := ![.occ 4, .branchGe 4 (1)]

def plane265BtpGenLeaf0213Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0213 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0213Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0213Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0213Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0213Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0214Refs : Fin 2 → RowRef 31 31 := ![.occ 5, .branchGe 5 (2)]

def plane265BtpGenLeaf0214Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0214 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0214Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0214Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0214Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0214Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0215Refs : Fin 2 → RowRef 31 31 := ![.occ 6, .branchGe 6 (2)]

def plane265BtpGenLeaf0215Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0215 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_6 : (2 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0215Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0215Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0215Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0215Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0216Refs : Fin 2 → RowRef 31 31 := ![.occ 7, .branchGe 7 (1)]

def plane265BtpGenLeaf0216Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0216 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0216Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0216Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0216Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0216Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0217Refs : Fin 2 → RowRef 31 31 := ![.occ 8, .branchGe 8 (1)]

def plane265BtpGenLeaf0217Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0217 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0217Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0217Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0217Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0217Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0218Refs : Fin 2 → RowRef 31 31 := ![.occ 9, .branchGe 9 (1)]

def plane265BtpGenLeaf0218Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0218 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0218Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0218Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0218Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0218Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0219Refs : Fin 2 → RowRef 31 31 := ![.occ 10, .branchGe 10 (1)]

def plane265BtpGenLeaf0219Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0219 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0219Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0219Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0219Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0219Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0220Refs : Fin 2 → RowRef 31 31 := ![.occ 11, .branchGe 11 (1)]

def plane265BtpGenLeaf0220Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0220 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0220Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0220Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0220Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0220Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (11 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0221Refs : Fin 2 → RowRef 31 31 := ![.occ 12, .branchGe 12 (1)]

def plane265BtpGenLeaf0221Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0221 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0221Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0221Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0221Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0221Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (12 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0222Refs : Fin 2 → RowRef 31 31 := ![.occ 13, .branchGe 13 (1)]

def plane265BtpGenLeaf0222Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0222 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0222Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0222Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0222Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0222Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (13 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0223Refs : Fin 2 → RowRef 31 31 := ![.occ 14, .branchGe 14 (1)]

def plane265BtpGenLeaf0223Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0223 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0223Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0223Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0223Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0223Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (14 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
