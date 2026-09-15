import FrozenRegistry.Btp227Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0512Refs : Fin 2 → RowRef 15 15 := ![.occ 7, .branchGe 7 (3)]

def plane227BtpGenLeaf0512Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0512 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_7 : (3 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0512Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0512Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0512Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0512Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0513Refs : Fin 2 → RowRef 15 15 := ![.occ 8, .branchGe 8 (1)]

def plane227BtpGenLeaf0513Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0513 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0513Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0513Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0513Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0513Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0514Refs : Fin 2 → RowRef 15 15 := ![.occ 9, .branchGe 9 (1)]

def plane227BtpGenLeaf0514Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0514 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0514Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0514Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0514Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0514Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0515Refs : Fin 2 → RowRef 15 15 := ![.occ 10, .branchGe 10 (1)]

def plane227BtpGenLeaf0515Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0515 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0515Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0515Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0515Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0515Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0516Refs : Fin 2 → RowRef 15 15 := ![.occ 11, .branchGe 11 (3)]

def plane227BtpGenLeaf0516Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0516 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_11 : (3 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0516Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0516Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0516Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0516Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (11 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0517Refs : Fin 2 → RowRef 15 15 := ![.occ 12, .branchGe 12 (1)]

def plane227BtpGenLeaf0517Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0517 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0517Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0517Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0517Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0517Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (12 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0518Refs : Fin 2 → RowRef 15 15 := ![.occ 13, .branchGe 13 (1)]

def plane227BtpGenLeaf0518Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0518 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0518Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0518Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0518Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0518Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (13 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane227BtpGenLeaf0519Refs : Fin 2 → RowRef 15 15 := ![.occ 14, .branchGe 14 (1)]

def plane227BtpGenLeaf0519Mult : Fin 2 → Nat := ![1, 1]

theorem plane227BtpGenLeaf0519 (x : Fin 15 → Int)
    (hroot : plane227BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane227BtpGenLeaf0519Refs i).resolveCoeff plane227BtpGenOccSys j)
    (fun i => (plane227BtpGenLeaf0519Refs i).resolveRhs plane227BtpGenOccSys) plane227BtpGenLeaf0519Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane227BtpGenLeaf0519Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (14 : Fin 15) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
