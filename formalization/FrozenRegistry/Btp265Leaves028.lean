import FrozenRegistry.Btp265Data
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0448Refs : Fin 2 → RowRef 31 31 := ![.occ 4, .branchGe 4 (1)]

def plane265BtpGenLeaf0448Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0448 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0448Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0448Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0448Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0448Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · change (∑ k, (if k = (4 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0449Refs : Fin 2 → RowRef 31 31 := ![.occ 5, .branchGe 5 (2)]

def plane265BtpGenLeaf0449Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0449 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0449Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0449Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0449Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0449Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · change (∑ k, (if k = (5 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0450Refs : Fin 2 → RowRef 31 31 := ![.occ 6, .branchGe 6 (2)]

def plane265BtpGenLeaf0450Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0450 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_6 : (2 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0450Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0450Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0450Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0450Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · change (∑ k, (if k = (6 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0451Refs : Fin 2 → RowRef 31 31 := ![.occ 7, .branchGe 7 (1)]

def plane265BtpGenLeaf0451Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0451 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0451Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0451Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0451Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0451Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · change (∑ k, (if k = (7 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0452Refs : Fin 2 → RowRef 31 31 := ![.occ 8, .branchGe 8 (1)]

def plane265BtpGenLeaf0452Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0452 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0452Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0452Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0452Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0452Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · change (∑ k, (if k = (8 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0453Refs : Fin 2 → RowRef 31 31 := ![.occ 9, .branchGe 9 (1)]

def plane265BtpGenLeaf0453Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0453 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0453Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0453Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0453Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0453Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · change (∑ k, (if k = (9 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0454Refs : Fin 2 → RowRef 31 31 := ![.occ 10, .branchGe 10 (1)]

def plane265BtpGenLeaf0454Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0454 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0454Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0454Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0454Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0454Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · change (∑ k, (if k = (10 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0455Refs : Fin 2 → RowRef 31 31 := ![.occ 11, .branchGe 11 (1)]

def plane265BtpGenLeaf0455Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0455 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0455Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0455Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0455Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0455Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · change (∑ k, (if k = (11 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0456Refs : Fin 2 → RowRef 31 31 := ![.occ 12, .branchGe 12 (1)]

def plane265BtpGenLeaf0456Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0456 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0456Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0456Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0456Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0456Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ k, (if k = (12 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0457Refs : Fin 2 → RowRef 31 31 := ![.occ 13, .branchGe 13 (1)]

def plane265BtpGenLeaf0457Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0457 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0457Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0457Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0457Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0457Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · change (∑ k, (if k = (13 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0458Refs : Fin 2 → RowRef 31 31 := ![.occ 14, .branchGe 14 (1)]

def plane265BtpGenLeaf0458Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0458 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0458Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0458Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0458Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0458Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · change (∑ k, (if k = (14 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0459Refs : Fin 2 → RowRef 31 31 := ![.occ 15, .branchGe 15 (1)]

def plane265BtpGenLeaf0459Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0459 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0459Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0459Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0459Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0459Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · change (∑ k, (if k = (15 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0460Refs : Fin 2 → RowRef 31 31 := ![.occ 16, .branchGe 16 (1)]

def plane265BtpGenLeaf0460Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0460 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0460Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0460Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0460Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0460Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · change (∑ k, (if k = (16 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0461Refs : Fin 2 → RowRef 31 31 := ![.occ 17, .branchGe 17 (2)]

def plane265BtpGenLeaf0461Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0461 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_17 : (2 : Int) ≤ x 17)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0461Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0461Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0461Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0461Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · change (∑ k, (if k = (17 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0462Refs : Fin 2 → RowRef 31 31 := ![.occ 18, .branchGe 18 (1)]

def plane265BtpGenLeaf0462Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0462 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0462Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0462Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0462Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0462Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · change (∑ k, (if k = (18 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane265BtpGenLeaf0463Refs : Fin 2 → RowRef 31 31 := ![.occ 19, .branchGe 19 (1)]

def plane265BtpGenLeaf0463Mult : Fin 2 → Nat := ![1, 1]

theorem plane265BtpGenLeaf0463 (x : Fin 31 → Int)
    (hroot : plane265BtpGenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane265BtpGenLeaf0463Refs i).resolveCoeff plane265BtpGenOccSys j)
    (fun i => (plane265BtpGenLeaf0463Refs i).resolveRhs plane265BtpGenOccSys) plane265BtpGenLeaf0463Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane265BtpGenLeaf0463Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · change (∑ k, (if k = (19 : Fin 31) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
