import QiushiPlane455GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane455GenLeaf0001Refs : Fin 49 → RowRef 124 48 := ![.occ 16, .occ 22, .occ 23, .occ 24, .occ 26, .occ 27, .occ 28, .occ 29, .occ 32, .occ 33, .occ 41, .occ 44, .occ 50, .occ 51, .occ 53, .occ 54, .occ 57, .occ 60, .occ 63, .occ 65, .occ 67, .occ 68, .occ 72, .occ 73, .occ 77, .occ 83, .occ 84, .occ 89, .occ 91, .occ 93, .occ 95, .occ 97, .occ 103, .occ 105, .occ 108, .occ 109, .occ 114, .occ 116, .occ 119, .occ 122, .occ 123, .sumGe, .nonneg 18, .nonneg 26, .nonneg 29, .nonneg 32, .nonneg 36, .branchLe 14 (0), .branchGe 42 (1)]

def plane455GenLeaf0001Mult : Fin 49 → Nat := ![104399, 19204, 44970, 21081, 61575, 207634, 227206, 143549, 27473, 41354, 38420, 42263, 127690, 65320, 14243, 45613, 162143, 56259, 121799, 63370, 74195, 62701, 34863, 82589, 98199, 56741, 54258, 29785, 57860, 86029, 30533, 37392, 51817, 65749, 50458, 98312, 6437, 17083, 50613, 17372, 26547, 351161, 98916, 247168, 24976, 87901, 101215, 344724, 1144073]

theorem plane455GenLeaf0001 (x : Fin 48 → Int)
    (hroot : plane455GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane455GenLeaf0001Refs i).resolveCoeff plane455GenOccSys j)
    (fun i => (plane455GenLeaf0001Refs i).resolveRhs plane455GenOccSys) plane455GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane455GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 77
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · change (∑ j, (-1 : Int) * x j) ≤ -plane455GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (26 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (42 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
