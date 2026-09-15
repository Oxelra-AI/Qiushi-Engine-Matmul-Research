import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0003Refs : Fin 59 → RowRef 202 58 := ![.occ 20, .occ 24, .occ 31, .occ 62, .occ 63, .occ 69, .occ 71, .occ 75, .occ 81, .occ 86, .occ 92, .occ 94, .occ 97, .occ 98, .occ 101, .occ 102, .occ 104, .occ 105, .occ 106, .occ 113, .occ 115, .occ 121, .occ 123, .occ 125, .occ 127, .occ 128, .occ 132, .occ 134, .occ 144, .occ 147, .occ 151, .occ 161, .occ 163, .occ 170, .occ 171, .occ 178, .occ 179, .occ 186, .occ 190, .occ 191, .occ 195, .occ 197, .occ 198, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 37, .nonneg 50, .nonneg 51, .nonneg 53, .nonneg 55, .nonneg 56, .branchGe 17 (1), .branchLe 9 (0), .branchLe 43 (0), .branchLe 20 (0), .branchLe 6 (0)]

def plane425GenLeaf0003Mult : Fin 59 → Nat := ![84864, 888, 91944, 1067222, 480386, 1028544, 90548, 188638, 122498, 41470, 811742, 437390, 29528, 27700, 217988, 1159176, 143326, 731516, 5606, 261388, 830850, 154048, 80815, 182360, 53949, 640350, 625892, 226770, 90904, 334760, 227635, 637734, 227994, 584440, 315132, 333294, 623272, 358307, 1269616, 507175, 614172, 233540, 146181, 3248208, 1058916, 169544, 1362428, 1167524, 312996, 18164, 219732, 181984, 317284, 1533444, 6688612, 2407040, 2129116, 2072912, 1807372]

theorem plane425GenLeaf0003 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0003Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0003Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · exact hroot.hOcc 24
  · exact hroot.hOcc 31
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 75
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (20 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (6 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
