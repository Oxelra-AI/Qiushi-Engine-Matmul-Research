import FrozenRegistry.Btp265Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0096Refs : Fin 2 → RowRef 31 31 := ![.occ 0, .branchGe 0 (4)]

def plane265BtpGenLeaf0096Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0096 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_0 : (4 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0096Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0096Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · change (∑ k, (if k = (0 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(4 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0097Refs : Fin 2 → RowRef 31 31 := ![.occ 1, .branchGe 1 (2)]

def plane265BtpGenLeaf0097Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0097 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_1 : (2 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0097Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0097Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · change (∑ k, (if k = (1 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0098Refs : Fin 2 → RowRef 31 31 := ![.occ 2, .branchGe 2 (2)]

def plane265BtpGenLeaf0098Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0098 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_2 : (2 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0098Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0098Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · change (∑ k, (if k = (2 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0099Refs : Fin 2 → RowRef 31 31 := ![.occ 3, .branchGe 3 (1)]

def plane265BtpGenLeaf0099Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0099 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0099Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0099Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · change (∑ k, (if k = (3 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0100Refs : Fin 2 → RowRef 31 31 := ![.occ 4, .branchGe 4 (1)]

def plane265BtpGenLeaf0100Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0100 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0100Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0100Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0101Refs : Fin 2 → RowRef 31 31 := ![.occ 5, .branchGe 5 (2)]

def plane265BtpGenLeaf0101Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0101 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0101Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0101Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0102Refs : Fin 2 → RowRef 31 31 := ![.occ 6, .branchGe 6 (2)]

def plane265BtpGenLeaf0102Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0102 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_6 : (2 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0102Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0102Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0103Refs : Fin 2 → RowRef 31 31 := ![.occ 7, .branchGe 7 (1)]

def plane265BtpGenLeaf0103Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0103 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0103Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0103Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0104Refs : Fin 2 → RowRef 31 31 := ![.occ 8, .branchGe 8 (1)]

def plane265BtpGenLeaf0104Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0104 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0104Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0104Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0105Refs : Fin 2 → RowRef 31 31 := ![.occ 9, .branchGe 9 (1)]

def plane265BtpGenLeaf0105Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0105 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0105Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0105Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0106Refs : Fin 2 → RowRef 31 31 := ![.occ 10, .branchGe 10 (1)]

def plane265BtpGenLeaf0106Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0106 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0106Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0106Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0106Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0106Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0107Refs : Fin 2 → RowRef 31 31 := ![.occ 11, .branchGe 11 (1)]

def plane265BtpGenLeaf0107Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0107 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0107Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0107Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (11 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0108Refs : Fin 2 → RowRef 31 31 := ![.occ 12, .branchGe 12 (1)]

def plane265BtpGenLeaf0108Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0108 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0108Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0108Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (12 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0109Refs : Fin 2 → RowRef 31 31 := ![.occ 13, .branchGe 13 (1)]

def plane265BtpGenLeaf0109Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0109 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0109Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0109Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (13 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0110Refs : Fin 2 → RowRef 31 31 := ![.occ 14, .branchGe 14 (1)]

def plane265BtpGenLeaf0110Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0110 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0110Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0110Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (14 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0111Refs : Fin 2 → RowRef 31 31 := ![.occ 15, .branchGe 15 (1)]

def plane265BtpGenLeaf0111Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0111 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0111Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0111Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · change (∑ k, (if k = (15 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
