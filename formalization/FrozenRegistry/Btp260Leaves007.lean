import FrozenRegistry.Btp260Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0112Refs : Fin 2 → RowRef 33 31 := ![.occ 17, .branchGe 15 (1)]

def plane260BtpGenLeaf0112Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0112 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0112Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0112Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0112Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0112Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · change (∑ k, (if k = (15 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0113Refs : Fin 2 → RowRef 33 31 := ![.occ 18, .branchGe 16 (1)]

def plane260BtpGenLeaf0113Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0113 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0113Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0113Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0113Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0113Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · change (∑ k, (if k = (16 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0114Refs : Fin 2 → RowRef 33 31 := ![.occ 19, .branchGe 17 (1)]

def plane260BtpGenLeaf0114Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0114 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0114Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0114Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0114Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0114Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · change (∑ k, (if k = (17 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0115Refs : Fin 2 → RowRef 33 31 := ![.occ 20, .branchGe 18 (1)]

def plane260BtpGenLeaf0115Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0115 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0115Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0115Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0115Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0115Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · change (∑ k, (if k = (18 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0116Refs : Fin 2 → RowRef 33 31 := ![.occ 21, .branchGe 19 (1)]

def plane260BtpGenLeaf0116Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0116 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0116Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0116Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0116Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0116Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 21
  · change (∑ k, (if k = (19 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0117Refs : Fin 2 → RowRef 33 31 := ![.occ 22, .branchGe 20 (1)]

def plane260BtpGenLeaf0117Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0117 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0117Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0117Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0117Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0117Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · change (∑ k, (if k = (20 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0118Refs : Fin 2 → RowRef 33 31 := ![.occ 23, .branchGe 21 (1)]

def plane260BtpGenLeaf0118Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0118 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0118Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0118Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0118Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0118Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · change (∑ k, (if k = (21 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0119Refs : Fin 2 → RowRef 33 31 := ![.occ 24, .branchGe 22 (1)]

def plane260BtpGenLeaf0119Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0119 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0119Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0119Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0119Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0119Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 24
  · change (∑ k, (if k = (22 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0120Refs : Fin 2 → RowRef 33 31 := ![.occ 25, .branchGe 23 (1)]

def plane260BtpGenLeaf0120Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0120 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0120Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0120Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0120Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0120Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 25
  · change (∑ k, (if k = (23 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0121Refs : Fin 2 → RowRef 33 31 := ![.occ 26, .branchGe 24 (1)]

def plane260BtpGenLeaf0121Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0121 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0121Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0121Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0121Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0121Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 26
  · change (∑ k, (if k = (24 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0122Refs : Fin 2 → RowRef 33 31 := ![.occ 27, .branchGe 25 (1)]

def plane260BtpGenLeaf0122Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0122 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0122Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0122Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0122Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0122Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 27
  · change (∑ k, (if k = (25 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0123Refs : Fin 2 → RowRef 33 31 := ![.occ 28, .branchGe 26 (1)]

def plane260BtpGenLeaf0123Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0123 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0123Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0123Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0123Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0123Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 28
  · change (∑ k, (if k = (26 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0124Refs : Fin 2 → RowRef 33 31 := ![.occ 29, .branchGe 27 (1)]

def plane260BtpGenLeaf0124Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0124 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0124Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0124Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0124Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0124Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · change (∑ k, (if k = (27 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0125Refs : Fin 2 → RowRef 33 31 := ![.occ 30, .branchGe 28 (1)]

def plane260BtpGenLeaf0125Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0125 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0125Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0125Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0125Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0125Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · change (∑ k, (if k = (28 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0126Refs : Fin 2 → RowRef 33 31 := ![.occ 31, .branchGe 29 (1)]

def plane260BtpGenLeaf0126Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0126 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0126Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0126Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0126Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0126Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 31
  · change (∑ k, (if k = (29 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane260BtpGenLeaf0127Refs : Fin 2 → RowRef 33 31 := ![.occ 32, .branchGe 30 (1)]

def plane260BtpGenLeaf0127Mult : Fin 2 → Nat := ![1, 1]

theorem plane260BtpGenLeaf0127 (x : Fin 31 → Int)
    (hroot : plane260BtpGenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane260BtpGenLeaf0127Refs i).resolveCoeff plane260BtpGenOccSys j)
    (fun i => (plane260BtpGenLeaf0127Refs i).resolveRhs plane260BtpGenOccSys) plane260BtpGenLeaf0127Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane260BtpGenLeaf0127Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 32
  · change (∑ k, (if k = (30 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
