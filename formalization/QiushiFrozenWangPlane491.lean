import QiushiFiniteBlocks
import QiushiFrozenWangPlane491Source000
import QiushiFrozenWangPlane491Source001
import QiushiFrozenWangPlane491Source002
import QiushiFrozenWangPlane491Source003
import QiushiFrozenWangPlane491Source004
import QiushiFrozenWangPlane491Source005
import QiushiFrozenWangPlane491Source006
import QiushiFrozenWangPlane491Source007
import QiushiFrozenWangPlane491Source008
import QiushiFrozenWangPlane491Source009
import QiushiFrozenWangPlane491Source010
import QiushiFrozenWangPlane491Source011
import QiushiFrozenWangPlane491Source012
import QiushiFrozenWangPlane491Source013
import QiushiFrozenWangPlane491Source014
import QiushiFrozenWangPlane491Source015
import QiushiFrozenWangPlane491Source016
import QiushiFrozenWangPlane491Source017
import QiushiFrozenWangPlane491Source018
import QiushiFrozenWangPlane491Source019
import QiushiFrozenWangPlane491Source020
import QiushiFrozenWangPlane491Source021
import QiushiFrozenWangPlane491Source022
import QiushiFrozenWangPlane491Dead000
import QiushiFrozenWangPlane491Dead001
import QiushiFrozenWangPlane491Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane491_source : ∀ i : Fin plane491GenConfig.nOcc,
    plane491GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane491GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491_sourceBlock000
  | ⟨1, _⟩ => exact plane491_sourceBlock001
  | ⟨2, _⟩ => exact plane491_sourceBlock002
  | ⟨3, _⟩ => exact plane491_sourceBlock003
  | ⟨4, _⟩ => exact plane491_sourceBlock004
  | ⟨5, _⟩ => exact plane491_sourceBlock005
  | ⟨6, _⟩ => exact plane491_sourceBlock006
  | ⟨7, _⟩ => exact plane491_sourceBlock007
  | ⟨8, _⟩ => exact plane491_sourceBlock008
  | ⟨9, _⟩ => exact plane491_sourceBlock009
  | ⟨10, _⟩ => exact plane491_sourceBlock010
  | ⟨11, _⟩ => exact plane491_sourceBlock011
  | ⟨12, _⟩ => exact plane491_sourceBlock012
  | ⟨13, _⟩ => exact plane491_sourceBlock013
  | ⟨14, _⟩ => exact plane491_sourceBlock014
  | ⟨15, _⟩ => exact plane491_sourceBlock015
  | ⟨16, _⟩ => exact plane491_sourceBlock016
  | ⟨17, _⟩ => exact plane491_sourceBlock017
  | ⟨18, _⟩ => exact plane491_sourceBlock018
  | ⟨19, _⟩ => exact plane491_sourceBlock019
  | ⟨20, _⟩ => exact plane491_sourceBlock020
  | ⟨21, _⟩ => exact plane491_sourceBlock021
  | ⟨22, _⟩ => exact plane491_sourceBlock022
  | ⟨k + 23, h⟩ => omega

theorem plane491_dead : ∀ i : Fin plane491GenConfig.nDead,
    plane491GenConfig.target ≤ frozenWangTable.L0 (plane491GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491_deadBlock000
  | ⟨1, _⟩ => exact plane491_deadBlock001
  | ⟨2, _⟩ => exact plane491_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
