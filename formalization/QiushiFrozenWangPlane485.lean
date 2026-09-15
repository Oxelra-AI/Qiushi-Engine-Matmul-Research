import QiushiFiniteBlocks
import QiushiFrozenWangPlane485Source000
import QiushiFrozenWangPlane485Source001
import QiushiFrozenWangPlane485Source002
import QiushiFrozenWangPlane485Source003
import QiushiFrozenWangPlane485Source004
import QiushiFrozenWangPlane485Source005
import QiushiFrozenWangPlane485Source006
import QiushiFrozenWangPlane485Source007
import QiushiFrozenWangPlane485Source008
import QiushiFrozenWangPlane485Source009
import QiushiFrozenWangPlane485Source010
import QiushiFrozenWangPlane485Source011
import QiushiFrozenWangPlane485Source012
import QiushiFrozenWangPlane485Source013
import QiushiFrozenWangPlane485Dead000
import QiushiFrozenWangPlane485Dead001
import QiushiFrozenWangPlane485Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane485_source : ∀ i : Fin plane485GenConfig.nOcc,
    plane485GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane485GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 14) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485_sourceBlock000
  | ⟨1, _⟩ => exact plane485_sourceBlock001
  | ⟨2, _⟩ => exact plane485_sourceBlock002
  | ⟨3, _⟩ => exact plane485_sourceBlock003
  | ⟨4, _⟩ => exact plane485_sourceBlock004
  | ⟨5, _⟩ => exact plane485_sourceBlock005
  | ⟨6, _⟩ => exact plane485_sourceBlock006
  | ⟨7, _⟩ => exact plane485_sourceBlock007
  | ⟨8, _⟩ => exact plane485_sourceBlock008
  | ⟨9, _⟩ => exact plane485_sourceBlock009
  | ⟨10, _⟩ => exact plane485_sourceBlock010
  | ⟨11, _⟩ => exact plane485_sourceBlock011
  | ⟨12, _⟩ => exact plane485_sourceBlock012
  | ⟨13, _⟩ => exact plane485_sourceBlock013
  | ⟨k + 14, h⟩ => omega

theorem plane485_dead : ∀ i : Fin plane485GenConfig.nDead,
    plane485GenConfig.target ≤ frozenWangTable.L0 (plane485GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485_deadBlock000
  | ⟨1, _⟩ => exact plane485_deadBlock001
  | ⟨2, _⟩ => exact plane485_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
