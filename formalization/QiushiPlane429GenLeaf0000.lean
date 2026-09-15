import QiushiPlane429GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane429GenLeaf0000Refs : Fin 62 → RowRef 55 61 := ![.occ 2, .occ 3, .occ 4, .occ 5, .occ 6, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .sumGe, .nonneg 18, .nonneg 24, .nonneg 41, .nonneg 43, .nonneg 44, .nonneg 57, .nonneg 58, .nonneg 60]

def plane429GenLeaf0000Mult : Fin 62 → Nat := ![56626, 12276, 59104, 28664, 52878, 50594, 18974, 28038, 30480, 35416, 104568, 93116, 77772, 25560, 79812, 4976, 37562, 32406, 122434, 79546, 29716, 25822, 17158, 40404, 77631, 5054, 52050, 39399, 18450, 65884, 74440, 45038, 45614, 43948, 8952, 77776, 19704, 54017, 74304, 16955, 63472, 94698, 74998, 83180, 720, 19696, 16830, 13674, 36598, 26686, 20652, 4452, 4448, 197574, 73388, 12640, 15588, 24977, 38035, 57755, 35721, 32788]

theorem plane429GenLeaf0000 (x : Fin 61 → Int)
    (hroot : plane429GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane429GenLeaf0000Refs i).resolveCoeff plane429GenOccSys j)
    (fun i => (plane429GenLeaf0000Refs i).resolveRhs plane429GenOccSys) plane429GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane429GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · change (∑ j, (-1 : Int) * x j) ≤ -plane429GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (41 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (43 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (57 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (58 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (60 : Fin 61) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60

end QiushiMatmul
