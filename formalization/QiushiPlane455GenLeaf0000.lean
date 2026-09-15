import QiushiPlane455GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane455GenLeaf0000Refs : Fin 49 → RowRef 124 48 := ![.occ 17, .occ 21, .occ 23, .occ 25, .occ 26, .occ 35, .occ 37, .occ 39, .occ 41, .occ 42, .occ 43, .occ 44, .occ 46, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 55, .occ 60, .occ 62, .occ 64, .occ 66, .occ 68, .occ 72, .occ 74, .occ 77, .occ 85, .occ 88, .occ 90, .occ 92, .occ 94, .occ 100, .occ 101, .occ 102, .occ 105, .occ 106, .occ 108, .occ 110, .occ 113, .occ 118, .occ 120, .occ 123, .sumGe, .nonneg 22, .nonneg 28, .branchLe 14 (0), .branchLe 42 (0)]

def plane455GenLeaf0000Mult : Fin 49 → Nat := ![49932227, 5225807, 35486888, 28455004, 33898363, 16244790, 16076942, 10934003, 1467109, 21296704, 13706189, 27466395, 11901720, 12929346, 21287347, 22397700, 21040099, 15595037, 31394547, 5467560, 23185333, 20959757, 38960851, 15785826, 11232426, 22418630, 19078656, 10656080, 20803516, 11142803, 96683, 10599554, 2291229, 16910868, 585339, 13415797, 24315033, 14322609, 24067009, 14361772, 12641992, 18283413, 22351544, 3274452, 124056209, 26056729, 13865714, 124056209, 118490528]

theorem plane455GenLeaf0000 (x : Fin 48 → Int)
    (hroot : plane455GenOccSys.RootHolds x)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane455GenLeaf0000Refs i).resolveCoeff plane455GenOccSys j)
    (fun i => (plane455GenLeaf0000Refs i).resolveRhs plane455GenOccSys) plane455GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane455GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · change (∑ j, (-1 : Int) * x j) ≤ -plane455GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (42 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
