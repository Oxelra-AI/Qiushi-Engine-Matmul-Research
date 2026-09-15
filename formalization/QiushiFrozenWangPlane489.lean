import QiushiFiniteBlocks
import QiushiFrozenWangPlane489Source000
import QiushiFrozenWangPlane489Source001
import QiushiFrozenWangPlane489Source002
import QiushiFrozenWangPlane489Source003
import QiushiFrozenWangPlane489Source004
import QiushiFrozenWangPlane489Source005
import QiushiFrozenWangPlane489Source006
import QiushiFrozenWangPlane489Source007
import QiushiFrozenWangPlane489Source008
import QiushiFrozenWangPlane489Source009
import QiushiFrozenWangPlane489Source010
import QiushiFrozenWangPlane489Source011
import QiushiFrozenWangPlane489Dead000
import QiushiFrozenWangPlane489Dead001
import QiushiFrozenWangPlane489Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane489_source : ∀ i : Fin plane489GenConfig.nOcc,
    plane489GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane489GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 12) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489_sourceBlock000
  | ⟨1, _⟩ => exact plane489_sourceBlock001
  | ⟨2, _⟩ => exact plane489_sourceBlock002
  | ⟨3, _⟩ => exact plane489_sourceBlock003
  | ⟨4, _⟩ => exact plane489_sourceBlock004
  | ⟨5, _⟩ => exact plane489_sourceBlock005
  | ⟨6, _⟩ => exact plane489_sourceBlock006
  | ⟨7, _⟩ => exact plane489_sourceBlock007
  | ⟨8, _⟩ => exact plane489_sourceBlock008
  | ⟨9, _⟩ => exact plane489_sourceBlock009
  | ⟨10, _⟩ => exact plane489_sourceBlock010
  | ⟨11, _⟩ => exact plane489_sourceBlock011
  | ⟨k + 12, h⟩ => omega

theorem plane489_dead : ∀ i : Fin plane489GenConfig.nDead,
    plane489GenConfig.target ≤ frozenWangTable.L0 (plane489GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489_deadBlock000
  | ⟨1, _⟩ => exact plane489_deadBlock001
  | ⟨2, _⟩ => exact plane489_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
