import QiushiFiniteBlocks
import QiushiFrozenWangPlane488Source000
import QiushiFrozenWangPlane488Source001
import QiushiFrozenWangPlane488Source002
import QiushiFrozenWangPlane488Source003
import QiushiFrozenWangPlane488Source004
import QiushiFrozenWangPlane488Source005
import QiushiFrozenWangPlane488Source006
import QiushiFrozenWangPlane488Source007
import QiushiFrozenWangPlane488Source008
import QiushiFrozenWangPlane488Source009
import QiushiFrozenWangPlane488Source010
import QiushiFrozenWangPlane488Source011
import QiushiFrozenWangPlane488Source012
import QiushiFrozenWangPlane488Dead000
import QiushiFrozenWangPlane488Dead001
import QiushiFrozenWangPlane488Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source : ∀ i : Fin plane488GenConfig.nOcc,
    plane488GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane488GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 13) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488_sourceBlock000
  | ⟨1, _⟩ => exact plane488_sourceBlock001
  | ⟨2, _⟩ => exact plane488_sourceBlock002
  | ⟨3, _⟩ => exact plane488_sourceBlock003
  | ⟨4, _⟩ => exact plane488_sourceBlock004
  | ⟨5, _⟩ => exact plane488_sourceBlock005
  | ⟨6, _⟩ => exact plane488_sourceBlock006
  | ⟨7, _⟩ => exact plane488_sourceBlock007
  | ⟨8, _⟩ => exact plane488_sourceBlock008
  | ⟨9, _⟩ => exact plane488_sourceBlock009
  | ⟨10, _⟩ => exact plane488_sourceBlock010
  | ⟨11, _⟩ => exact plane488_sourceBlock011
  | ⟨12, _⟩ => exact plane488_sourceBlock012
  | ⟨k + 13, h⟩ => omega

theorem plane488_dead : ∀ i : Fin plane488GenConfig.nDead,
    plane488GenConfig.target ≤ frozenWangTable.L0 (plane488GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488_deadBlock000
  | ⟨1, _⟩ => exact plane488_deadBlock001
  | ⟨2, _⟩ => exact plane488_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
