import FrozenRegistry.Btp265Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0464Refs : Fin 2 → RowRef 31 31 := ![.occ 20, .branchGe 20 (1)]

def plane265BtpGenLeaf0464Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0464 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0464Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0464Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0464Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0464Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · change (∑ k, (if k = (20 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0465Refs : Fin 2 → RowRef 31 31 := ![.occ 21, .branchGe 21 (1)]

def plane265BtpGenLeaf0465Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0465 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0465Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0465Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0465Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0465Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 21
  · change (∑ k, (if k = (21 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0466Refs : Fin 2 → RowRef 31 31 := ![.occ 22, .branchGe 22 (1)]

def plane265BtpGenLeaf0466Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0466 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0466Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0466Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0466Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0466Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · change (∑ k, (if k = (22 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0467Refs : Fin 2 → RowRef 31 31 := ![.occ 23, .branchGe 23 (1)]

def plane265BtpGenLeaf0467Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0467 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0467Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0467Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0467Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0467Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · change (∑ k, (if k = (23 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0468Refs : Fin 2 → RowRef 31 31 := ![.occ 24, .branchGe 24 (1)]

def plane265BtpGenLeaf0468Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0468 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0468Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0468Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0468Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0468Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 24
  · change (∑ k, (if k = (24 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0469Refs : Fin 2 → RowRef 31 31 := ![.occ 25, .branchGe 25 (1)]

def plane265BtpGenLeaf0469Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0469 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0469Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0469Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0469Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0469Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 25
  · change (∑ k, (if k = (25 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0470Refs : Fin 2 → RowRef 31 31 := ![.occ 26, .branchGe 26 (2)]

def plane265BtpGenLeaf0470Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0470 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_26 : (2 : Int) ≤ x 26)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0470Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0470Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0470Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0470Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 26
  · change (∑ k, (if k = (26 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0471Refs : Fin 2 → RowRef 31 31 := ![.occ 27, .branchGe 27 (1)]

def plane265BtpGenLeaf0471Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0471 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0471Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0471Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0471Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0471Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 27
  · change (∑ k, (if k = (27 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0472Refs : Fin 2 → RowRef 31 31 := ![.occ 28, .branchGe 28 (1)]

def plane265BtpGenLeaf0472Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0472 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0472Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0472Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0472Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0472Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 28
  · change (∑ k, (if k = (28 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0473Refs : Fin 2 → RowRef 31 31 := ![.occ 29, .branchGe 29 (1)]

def plane265BtpGenLeaf0473Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0473 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0473Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0473Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0473Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0473Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · change (∑ k, (if k = (29 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0474Refs : Fin 2 → RowRef 31 31 := ![.occ 30, .branchGe 30 (1)]

def plane265BtpGenLeaf0474Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0474 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0474Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0474Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0474Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0474Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · change (∑ k, (if k = (30 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
