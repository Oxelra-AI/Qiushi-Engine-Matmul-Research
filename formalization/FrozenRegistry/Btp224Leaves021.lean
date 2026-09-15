import FrozenRegistry.Btp224Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0336Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane224BtpGenLeaf0336Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0336 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0336Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0336Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0336Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0336Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0337Refs : Fin 2 → RowRef 15 15 := ![.occ 3, .branchGe 3 (1)]

def plane224BtpGenLeaf0337Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0337 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0337Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0337Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0337Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0337Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0338Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0338Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0338 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0338Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0338Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0338Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0338Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0339Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0339Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0339 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0339Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0339Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0339Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0339Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0340Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (1), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0340Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0340 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0340Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0340Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0340Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0340Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0341Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0341Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0341 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0341Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0341Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0341Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0341Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0342Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0342Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0342 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (2 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0342Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0342Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0342Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0342Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0343Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0343Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0343 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0343Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0343Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0343Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0343Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0344Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0344Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0344 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0344Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0344Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0344Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0344Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0345Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0345Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0345 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0345Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0345Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0345Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0345Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0346Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0346Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0346 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0346Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0346Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0346Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0346Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0347Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (1), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0347Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0347 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0347Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0347Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0347Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0347Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0348Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0348Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0348 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0348Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0348Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0348Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0348Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0349Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (1), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0349Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0349 (x : Fin 15 → Int)
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
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0349Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0349Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0349Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0349Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
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
  · change (∑ k, (if k = (11 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (12 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (13 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0350Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0350Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0350 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0350Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0350Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0350Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0350Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0351Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0351Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0351 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0351Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0351Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0351Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0351Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
