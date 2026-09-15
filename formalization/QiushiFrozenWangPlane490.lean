import QiushiFiniteBlocks
import QiushiFrozenWangPlane490Source000
import QiushiFrozenWangPlane490Source001
import QiushiFrozenWangPlane490Source002
import QiushiFrozenWangPlane490Source003
import QiushiFrozenWangPlane490Source004
import QiushiFrozenWangPlane490Source005
import QiushiFrozenWangPlane490Source006
import QiushiFrozenWangPlane490Source007
import QiushiFrozenWangPlane490Source008
import QiushiFrozenWangPlane490Source009
import QiushiFrozenWangPlane490Source010
import QiushiFrozenWangPlane490Source011
import QiushiFrozenWangPlane490Source012
import QiushiFrozenWangPlane490Source013
import QiushiFrozenWangPlane490Source014
import QiushiFrozenWangPlane490Source015
import QiushiFrozenWangPlane490Source016
import QiushiFrozenWangPlane490Source017
import QiushiFrozenWangPlane490Source018
import QiushiFrozenWangPlane490Source019
import QiushiFrozenWangPlane490Source020
import QiushiFrozenWangPlane490Source021
import QiushiFrozenWangPlane490Source022
import QiushiFrozenWangPlane490Dead000
import QiushiFrozenWangPlane490Dead001
import QiushiFrozenWangPlane490Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source : ∀ i : Fin plane490GenConfig.nOcc,
    plane490GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane490GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490_sourceBlock000
  | ⟨1, _⟩ => exact plane490_sourceBlock001
  | ⟨2, _⟩ => exact plane490_sourceBlock002
  | ⟨3, _⟩ => exact plane490_sourceBlock003
  | ⟨4, _⟩ => exact plane490_sourceBlock004
  | ⟨5, _⟩ => exact plane490_sourceBlock005
  | ⟨6, _⟩ => exact plane490_sourceBlock006
  | ⟨7, _⟩ => exact plane490_sourceBlock007
  | ⟨8, _⟩ => exact plane490_sourceBlock008
  | ⟨9, _⟩ => exact plane490_sourceBlock009
  | ⟨10, _⟩ => exact plane490_sourceBlock010
  | ⟨11, _⟩ => exact plane490_sourceBlock011
  | ⟨12, _⟩ => exact plane490_sourceBlock012
  | ⟨13, _⟩ => exact plane490_sourceBlock013
  | ⟨14, _⟩ => exact plane490_sourceBlock014
  | ⟨15, _⟩ => exact plane490_sourceBlock015
  | ⟨16, _⟩ => exact plane490_sourceBlock016
  | ⟨17, _⟩ => exact plane490_sourceBlock017
  | ⟨18, _⟩ => exact plane490_sourceBlock018
  | ⟨19, _⟩ => exact plane490_sourceBlock019
  | ⟨20, _⟩ => exact plane490_sourceBlock020
  | ⟨21, _⟩ => exact plane490_sourceBlock021
  | ⟨22, _⟩ => exact plane490_sourceBlock022
  | ⟨k + 23, h⟩ => omega

theorem plane490_dead : ∀ i : Fin plane490GenConfig.nDead,
    plane490GenConfig.target ≤ frozenWangTable.L0 (plane490GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490_deadBlock000
  | ⟨1, _⟩ => exact plane490_deadBlock001
  | ⟨2, _⟩ => exact plane490_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
