import FrozenRegistry.Btp224Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0272Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0272Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0272 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0272Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0272Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0272Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0272Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0273Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0273Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0273 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0273Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0273Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0273Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0273Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0274Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0274Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0274 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0274Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0274Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0274Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0274Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0275Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (1), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0275Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0275 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0275Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0275Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0275Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0275Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0276Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0276Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0276 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0276Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0276Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0276Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0276Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0277Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (1), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0277Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0277 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (2 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0277Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0277Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0277Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0277Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0278Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0278Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0278 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0278Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0278Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0278Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0278Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0279Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0279Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0279 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0279Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0279Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0279Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0279Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0280Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0280Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0280 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0280Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0280Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0280Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0280Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0281Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0281Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0281 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0281Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0281Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0281Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0281Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0282Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (1), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0282Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0282 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0282Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0282Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0282Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0282Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0283Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0283Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0283 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0283Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0283Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0283Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0283Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0284Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (2), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (2), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane224BtpGenLeaf0284Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane224BtpGenLeaf0284 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (2 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (2 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0284Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0284Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0284Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0284Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane224BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane224BtpGenLeaf0285Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (1)]

def plane224BtpGenLeaf0285Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0285 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0285Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0285Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0285Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0285Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0286Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (3)]

def plane224BtpGenLeaf0286Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0286 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_1 : (3 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0286Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0286Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0286Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0286Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0287Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane224BtpGenLeaf0287Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0287 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0287Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0287Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0287Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0287Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
