import QiushiFiniteBlocks
import QiushiFrozenWangPlane487Source000
import QiushiFrozenWangPlane487Source001
import QiushiFrozenWangPlane487Source002
import QiushiFrozenWangPlane487Source003
import QiushiFrozenWangPlane487Source004
import QiushiFrozenWangPlane487Source005
import QiushiFrozenWangPlane487Source006
import QiushiFrozenWangPlane487Source007
import QiushiFrozenWangPlane487Source008
import QiushiFrozenWangPlane487Source009
import QiushiFrozenWangPlane487Source010
import QiushiFrozenWangPlane487Source011
import QiushiFrozenWangPlane487Source012
import QiushiFrozenWangPlane487Source013
import QiushiFrozenWangPlane487Source014
import QiushiFrozenWangPlane487Source015
import QiushiFrozenWangPlane487Source016
import QiushiFrozenWangPlane487Source017
import QiushiFrozenWangPlane487Source018
import QiushiFrozenWangPlane487Source019
import QiushiFrozenWangPlane487Source020
import QiushiFrozenWangPlane487Dead000
import QiushiFrozenWangPlane487Dead001
import QiushiFrozenWangPlane487Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane487_source : ∀ i : Fin plane487GenConfig.nOcc,
    plane487GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane487GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 21) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487_sourceBlock000
  | ⟨1, _⟩ => exact plane487_sourceBlock001
  | ⟨2, _⟩ => exact plane487_sourceBlock002
  | ⟨3, _⟩ => exact plane487_sourceBlock003
  | ⟨4, _⟩ => exact plane487_sourceBlock004
  | ⟨5, _⟩ => exact plane487_sourceBlock005
  | ⟨6, _⟩ => exact plane487_sourceBlock006
  | ⟨7, _⟩ => exact plane487_sourceBlock007
  | ⟨8, _⟩ => exact plane487_sourceBlock008
  | ⟨9, _⟩ => exact plane487_sourceBlock009
  | ⟨10, _⟩ => exact plane487_sourceBlock010
  | ⟨11, _⟩ => exact plane487_sourceBlock011
  | ⟨12, _⟩ => exact plane487_sourceBlock012
  | ⟨13, _⟩ => exact plane487_sourceBlock013
  | ⟨14, _⟩ => exact plane487_sourceBlock014
  | ⟨15, _⟩ => exact plane487_sourceBlock015
  | ⟨16, _⟩ => exact plane487_sourceBlock016
  | ⟨17, _⟩ => exact plane487_sourceBlock017
  | ⟨18, _⟩ => exact plane487_sourceBlock018
  | ⟨19, _⟩ => exact plane487_sourceBlock019
  | ⟨20, _⟩ => exact plane487_sourceBlock020
  | ⟨k + 21, h⟩ => omega

theorem plane487_dead : ∀ i : Fin plane487GenConfig.nDead,
    plane487GenConfig.target ≤ frozenWangTable.L0 (plane487GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487_deadBlock000
  | ⟨1, _⟩ => exact plane487_deadBlock001
  | ⟨2, _⟩ => exact plane487_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
