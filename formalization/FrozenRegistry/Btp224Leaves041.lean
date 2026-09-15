import FrozenRegistry.Btp224Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0656Refs : Fin 2 → RowRef 15 15 := ![.occ 7, .branchGe 7 (3)]

def plane224BtpGenLeaf0656Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0656 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_7 : (3 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0656Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0656Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0656Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0656Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0657Refs : Fin 2 → RowRef 15 15 := ![.occ 8, .branchGe 8 (1)]

def plane224BtpGenLeaf0657Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0657 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0657Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0657Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0657Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0657Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0658Refs : Fin 2 → RowRef 15 15 := ![.occ 9, .branchGe 9 (1)]

def plane224BtpGenLeaf0658Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0658 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0658Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0658Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0658Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0658Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0659Refs : Fin 2 → RowRef 15 15 := ![.occ 10, .branchGe 10 (1)]

def plane224BtpGenLeaf0659Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0659 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0659Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0659Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0659Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0659Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0660Refs : Fin 2 → RowRef 15 15 := ![.occ 11, .branchGe 11 (3)]

def plane224BtpGenLeaf0660Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0660 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_11 : (3 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0660Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0660Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0660Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0660Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (11 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0661Refs : Fin 2 → RowRef 15 15 := ![.occ 12, .branchGe 12 (1)]

def plane224BtpGenLeaf0661Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0661 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0661Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0661Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0661Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0661Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (12 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0662Refs : Fin 2 → RowRef 15 15 := ![.occ 13, .branchGe 13 (1)]

def plane224BtpGenLeaf0662Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0662 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0662Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0662Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0662Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0662Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (13 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane224BtpGenLeaf0663Refs : Fin 2 → RowRef 15 15 := ![.occ 14, .branchGe 14 (1)]

def plane224BtpGenLeaf0663Mult : Fin 2 → Nat := ![1, 1]

theorem plane224BtpGenLeaf0663 (x : Fin 15 → Int)
    (hroot : plane224BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane224BtpGenLeaf0663Refs i).resolveCoeff plane224BtpGenOccSys j)
    (fun i => (plane224BtpGenLeaf0663Refs i).resolveRhs plane224BtpGenOccSys) plane224BtpGenLeaf0663Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane224BtpGenLeaf0663Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (14 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
