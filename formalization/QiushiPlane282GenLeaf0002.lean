import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0002Refs : Fin 21 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 20, .occ 35, .occ 44, .occ 48, .occ 58, .occ 60, .occ 63, .occ 64, .occ 69, .occ 77, .occ 87, .occ 88, .occ 90, .sumGe, .branchLe 18 (0), .branchLe 19 (0), .branchLe 25 (0), .branchGe 9 (1), .branchLe 2 (1)]

def plane282GenLeaf0002Mult : Fin 21 → Nat := ![6, 8, 2, 2, 1, 3, 1, 3, 4, 1, 4, 6, 3, 4, 4, 12, 2, 6, 6, 6, 4]

theorem plane282GenLeaf0002 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_0 : x 0 ≤ (3 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0002Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0002Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 35
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 77
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (9 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
