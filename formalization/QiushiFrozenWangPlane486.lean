import QiushiFiniteBlocks
import QiushiFrozenWangPlane486Source000
import QiushiFrozenWangPlane486Source001
import QiushiFrozenWangPlane486Source002
import QiushiFrozenWangPlane486Source003
import QiushiFrozenWangPlane486Source004
import QiushiFrozenWangPlane486Source005
import QiushiFrozenWangPlane486Source006
import QiushiFrozenWangPlane486Source007
import QiushiFrozenWangPlane486Source008
import QiushiFrozenWangPlane486Dead000
import QiushiFrozenWangPlane486Dead001
import QiushiFrozenWangPlane486Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane486_source : ∀ i : Fin plane486GenConfig.nOcc,
    plane486GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane486GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486_sourceBlock000
  | ⟨1, _⟩ => exact plane486_sourceBlock001
  | ⟨2, _⟩ => exact plane486_sourceBlock002
  | ⟨3, _⟩ => exact plane486_sourceBlock003
  | ⟨4, _⟩ => exact plane486_sourceBlock004
  | ⟨5, _⟩ => exact plane486_sourceBlock005
  | ⟨6, _⟩ => exact plane486_sourceBlock006
  | ⟨7, _⟩ => exact plane486_sourceBlock007
  | ⟨8, _⟩ => exact plane486_sourceBlock008
  | ⟨k + 9, h⟩ => omega

theorem plane486_dead : ∀ i : Fin plane486GenConfig.nDead,
    plane486GenConfig.target ≤ frozenWangTable.L0 (plane486GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486_deadBlock000
  | ⟨1, _⟩ => exact plane486_deadBlock001
  | ⟨2, _⟩ => exact plane486_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
