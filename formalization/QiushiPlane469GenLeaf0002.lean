import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0002Refs : Fin 61 → RowRef 217 60 := ![.occ 15, .occ 24, .occ 28, .occ 41, .occ 43, .occ 48, .occ 57, .occ 58, .occ 69, .occ 72, .occ 74, .occ 81, .occ 82, .occ 83, .occ 84, .occ 91, .occ 93, .occ 94, .occ 96, .occ 99, .occ 110, .occ 111, .occ 116, .occ 120, .occ 122, .occ 128, .occ 129, .occ 139, .occ 140, .occ 141, .occ 142, .occ 144, .occ 151, .occ 153, .occ 159, .occ 161, .occ 164, .occ 179, .occ 180, .occ 182, .occ 183, .occ 184, .occ 190, .occ 196, .occ 199, .occ 207, .sumGe, .nonneg 3, .nonneg 10, .nonneg 17, .nonneg 32, .nonneg 41, .nonneg 46, .branchLe 34 (0), .branchLe 13 (0), .branchLe 8 (0), .branchLe 54 (0), .branchLe 40 (0), .branchLe 45 (0), .branchGe 5 (1), .branchGe 31 (1)]

def plane469GenLeaf0002Mult : Fin 61 → Nat := ![26708936, 5641444, 10981470, 4183546, 16324934, 19502812, 27433492, 14730950, 43452058, 2581898, 11014794, 6458010, 6023560, 20295270, 31347526, 16504246, 2383256, 4958210, 17729370, 4026264, 21437138, 15605286, 9146746, 8082598, 5051047, 15592094, 500705, 10019930, 1372155, 5375893, 12368486, 12355907, 6080972, 1905658, 2093817, 1296911, 1266824, 343017, 3162360, 5771550, 3664036, 5418424, 5078102, 14670322, 4935414, 13672698, 67144686, 19465518, 26056946, 28122930, 41938844, 27617924, 45659242, 34670734, 60426656, 51088732, 15501890, 67144686, 35689298, 79704702, 79359308]

theorem plane469GenLeaf0002 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0002Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0002Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 182
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 196
  · exact hroot.hOcc 199
  · exact hroot.hOcc 207
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (41 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (8 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (54 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (40 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (45 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (31 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
