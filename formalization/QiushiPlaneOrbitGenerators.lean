import QiushiPlaneOrbitCode

open Matrix
namespace QiushiMatmul.PlaneOrbit
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def leftMap (L : Mat3) : Mat3 →ₗ[F2] Mat3 where
  toFun X := L * X
  map_add' X Y := mul_add L X Y
  map_smul' c X := by simp only [mul_smul_comm, RingHom.id_apply]

def leftW (L : Mat3) (W : Space) : Space := W.map (leftMap L)

def rowMatrix (g : Fin 3) : Mat3 := codeMat (![266, 161, 275] g)

def genMap (g : Fin 4) : Mat3 →ₗ[F2] Mat3 :=
  if g.val = 3 then transposeLinearMap else leftMap (rowMatrix ⟨g.val % 3, Nat.mod_lt _ (by decide)⟩)

def genW (g : Fin 4) (W : Space) : Space := W.map (genMap g)

def genCode (g : Fin 4) (a : Nat) : Nat :=
  match g.val with
  | 0 => ((a >>> 3) &&& 7) ||| ((a &&& 7) <<< 3) ||| (a &&& 448)
  | 1 => (a &&& 7) ||| (((a >>> 6) &&& 7) <<< 3) ||| (((a >>> 3) &&& 7) <<< 6)
  | 2 => a ^^^ ((a >>> 3) &&& 7)
  | _ => transposeCode a

theorem rowMatrix_square : ∀ g : Fin 3, rowMatrix g * rowMatrix g = 1 := by
  decide +revert

theorem rowMatrix_det : ∀ g : Fin 3, (rowMatrix g).det ≠ 0 := by
  decide +revert

theorem genCode_bound : ∀ g : Fin 4, ∀ a : Fin 512, genCode g a.val < 512 := by
  decide +revert

theorem genCode_semantics : ∀ g : Fin 4, ∀ a : Fin 512,
    codeMat (genCode g a.val) = genMap g (codeMat a.val) := by
  decide +revert

theorem genMap_involution (g : Fin 4) (M : Mat3) :
    genMap g (genMap g M) = M := by
  unfold genMap
  split
  · exact Matrix.transpose_transpose M
  · change rowMatrix _ * (rowMatrix _ * M) = M
    rw [← mul_assoc, rowMatrix_square, one_mul]

theorem genW_involution (g : Fin 4) (W : Space) : genW g (genW g W) = W := by
  rw [genW, genW, ← Submodule.map_comp]
  have he : (genMap g).comp (genMap g) = LinearMap.id := by
    ext M i j
    exact congrFun (congrFun (genMap_involution g M) i) j
  rw [he, Submodule.map_id]

theorem leftW_one (W : Space) : leftW 1 W = W := by
  have h : leftMap 1 = LinearMap.id := by ext; simp [leftMap]
  simp [leftW, h]

theorem leftW_mul (L R : Mat3) (W : Space) :
    leftW (L * R) W = leftW L (leftW R W) := by
  rw [leftW, leftW, leftW, ← Submodule.map_comp]
  congr 1
  ext M i j
  exact congrFun (congrFun (mul_assoc L R M) i) j

def rowWord : List (Fin 3) → Mat3
  | [] => 1
  | g :: gs => rowMatrix g * rowWord gs

def GeneratorClosed (S : Set Space) : Prop :=
  ∀ g W, W ∈ S → genW g W ∈ S

theorem word_closed {S : Set Space} (hS : GeneratorClosed S) (w : List (Fin 3))
    (W : Space) (hW : W ∈ S) : leftW (rowWord w) W ∈ S := by
  induction w with
  | nil => simpa [rowWord, leftW_one] using hW
  | cons g gs ih =>
    rw [rowWord, leftW_mul]
    have h := hS ⟨g.val, by omega⟩ _ ih
    have hg : g.val ≠ 3 := by omega
    simpa [genW, genMap, leftW, hg, Nat.mod_eq_of_lt g.isLt] using h

end QiushiMatmul.PlaneOrbit
