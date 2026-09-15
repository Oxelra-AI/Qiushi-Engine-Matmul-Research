import FrozenRegistry.Btp227Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0160Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (2), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (2), .branchLe 6 (0), .branchLe 7 (2), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (0), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0160Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0160 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (2 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (2 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (2 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0160Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0160Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0160Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0160Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (5 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (7 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_7
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

def plane227BtpGenLeaf0161Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0161Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0161 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0161Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0161Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0161Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0161Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0162Refs : Fin 2 → RowRef 15 15 := ![.occ 1, .branchGe 1 (1)]

def plane227BtpGenLeaf0162Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0162 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0162Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0162Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0162Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0162Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0163Refs : Fin 2 → RowRef 15 15 := ![.occ 2, .branchGe 2 (3)]

def plane227BtpGenLeaf0163Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0163 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_2 : (3 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0163Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0163Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0163Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0163Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0164Refs : Fin 2 → RowRef 15 15 := ![.occ 3, .branchGe 3 (1)]

def plane227BtpGenLeaf0164Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0164 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0164Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0164Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0164Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0164Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0165Refs : Fin 2 → RowRef 15 15 := ![.occ 4, .branchGe 4 (1)]

def plane227BtpGenLeaf0165Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0165 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0165Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0165Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0165Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0165Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0166Refs : Fin 2 → RowRef 15 15 := ![.occ 5, .branchGe 5 (3)]

def plane227BtpGenLeaf0166Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0166 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_5 : (3 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0166Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0166Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0166Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0166Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0167Refs : Fin 2 → RowRef 15 15 := ![.occ 6, .branchGe 6 (1)]

def plane227BtpGenLeaf0167Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0167 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0167Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0167Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0167Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0167Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0168Refs : Fin 2 → RowRef 15 15 := ![.occ 7, .branchGe 7 (3)]

def plane227BtpGenLeaf0168Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0168 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_7 : (3 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0168Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0168Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0168Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0168Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0169Refs : Fin 2 → RowRef 15 15 := ![.occ 8, .branchGe 8 (1)]

def plane227BtpGenLeaf0169Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0169 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0169Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0169Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0169Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0169Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0170Refs : Fin 2 → RowRef 15 15 := ![.occ 9, .branchGe 9 (1)]

def plane227BtpGenLeaf0170Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0170 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0170Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0170Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0170Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0170Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0171Refs : Fin 2 → RowRef 15 15 := ![.occ 10, .branchGe 10 (1)]

def plane227BtpGenLeaf0171Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0171 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0171Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0171Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0171Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0171Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0172Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (0), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0172Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0172 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0172Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0172Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0172Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0172Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
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

def plane227BtpGenLeaf0173Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (1), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0173Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0173 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0173Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0173Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0173Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0173Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
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

def plane227BtpGenLeaf0174Refs : Fin 16 → RowRef 15 15 := ![.sumGe, .branchLe 0 (2), .branchLe 1 (0), .branchLe 2 (0), .branchLe 3 (0), .branchLe 4 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 10 (0), .branchLe 11 (1), .branchLe 12 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane227BtpGenLeaf0174Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane227BtpGenLeaf0174 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
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
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0174Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0174Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0174Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0174Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane227BtpGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 15) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (1 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (2 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (3 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 15) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
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

def plane227BtpGenLeaf0175Refs : Fin 2 → RowRef 15 15 := ![.occ 0, .branchGe 0 (3)]

def plane227BtpGenLeaf0175Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0175 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0175Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0175Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0175Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0175Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
