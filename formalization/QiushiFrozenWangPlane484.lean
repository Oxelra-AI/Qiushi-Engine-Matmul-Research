import QiushiFiniteBlocks
import QiushiFrozenWangPlane484Source000
import QiushiFrozenWangPlane484Source001
import QiushiFrozenWangPlane484Source002
import QiushiFrozenWangPlane484Source003
import QiushiFrozenWangPlane484Source004
import QiushiFrozenWangPlane484Source005
import QiushiFrozenWangPlane484Source006
import QiushiFrozenWangPlane484Source007
import QiushiFrozenWangPlane484Source008
import QiushiFrozenWangPlane484Source009
import QiushiFrozenWangPlane484Source010
import QiushiFrozenWangPlane484Source011
import QiushiFrozenWangPlane484Source012
import QiushiFrozenWangPlane484Source013
import QiushiFrozenWangPlane484Source014
import QiushiFrozenWangPlane484Source015
import QiushiFrozenWangPlane484Source016
import QiushiFrozenWangPlane484Source017
import QiushiFrozenWangPlane484Source018
import QiushiFrozenWangPlane484Source019
import QiushiFrozenWangPlane484Source020
import QiushiFrozenWangPlane484Source021
import QiushiFrozenWangPlane484Source022
import QiushiFrozenWangPlane484Source023
import QiushiFrozenWangPlane484Source024
import QiushiFrozenWangPlane484Source025
import QiushiFrozenWangPlane484Source026
import QiushiFrozenWangPlane484Source027
import QiushiFrozenWangPlane484Source028
import QiushiFrozenWangPlane484Source029
import QiushiFrozenWangPlane484Source030
import QiushiFrozenWangPlane484Source031
import QiushiFrozenWangPlane484Source032
import QiushiFrozenWangPlane484Source033
import QiushiFrozenWangPlane484Source034
import QiushiFrozenWangPlane484Source035
import QiushiFrozenWangPlane484Source036
import QiushiFrozenWangPlane484Source037
import QiushiFrozenWangPlane484Source038
import QiushiFrozenWangPlane484Source039
import QiushiFrozenWangPlane484Source040
import QiushiFrozenWangPlane484Source041
import QiushiFrozenWangPlane484Source042
import QiushiFrozenWangPlane484Source043
import QiushiFrozenWangPlane484Source044
import QiushiFrozenWangPlane484Source045
import QiushiFrozenWangPlane484Source046
import QiushiFrozenWangPlane484Source047
import QiushiFrozenWangPlane484Source048
import QiushiFrozenWangPlane484Source049
import QiushiFrozenWangPlane484Source050
import QiushiFrozenWangPlane484Source051
import QiushiFrozenWangPlane484Source052
import QiushiFrozenWangPlane484Dead000
import QiushiFrozenWangPlane484Dead001
import QiushiFrozenWangPlane484Dead002

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane484_source : ∀ i : Fin plane484GenConfig.nOcc,
    plane484GenConfig.sourceLb i ≤ frozenWangTable.L0 (plane484GenConfig.sourceU i) := by
  apply forall_fin_of_blocks (blocks := 53) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484_sourceBlock000
  | ⟨1, _⟩ => exact plane484_sourceBlock001
  | ⟨2, _⟩ => exact plane484_sourceBlock002
  | ⟨3, _⟩ => exact plane484_sourceBlock003
  | ⟨4, _⟩ => exact plane484_sourceBlock004
  | ⟨5, _⟩ => exact plane484_sourceBlock005
  | ⟨6, _⟩ => exact plane484_sourceBlock006
  | ⟨7, _⟩ => exact plane484_sourceBlock007
  | ⟨8, _⟩ => exact plane484_sourceBlock008
  | ⟨9, _⟩ => exact plane484_sourceBlock009
  | ⟨10, _⟩ => exact plane484_sourceBlock010
  | ⟨11, _⟩ => exact plane484_sourceBlock011
  | ⟨12, _⟩ => exact plane484_sourceBlock012
  | ⟨13, _⟩ => exact plane484_sourceBlock013
  | ⟨14, _⟩ => exact plane484_sourceBlock014
  | ⟨15, _⟩ => exact plane484_sourceBlock015
  | ⟨16, _⟩ => exact plane484_sourceBlock016
  | ⟨17, _⟩ => exact plane484_sourceBlock017
  | ⟨18, _⟩ => exact plane484_sourceBlock018
  | ⟨19, _⟩ => exact plane484_sourceBlock019
  | ⟨20, _⟩ => exact plane484_sourceBlock020
  | ⟨21, _⟩ => exact plane484_sourceBlock021
  | ⟨22, _⟩ => exact plane484_sourceBlock022
  | ⟨23, _⟩ => exact plane484_sourceBlock023
  | ⟨24, _⟩ => exact plane484_sourceBlock024
  | ⟨25, _⟩ => exact plane484_sourceBlock025
  | ⟨26, _⟩ => exact plane484_sourceBlock026
  | ⟨27, _⟩ => exact plane484_sourceBlock027
  | ⟨28, _⟩ => exact plane484_sourceBlock028
  | ⟨29, _⟩ => exact plane484_sourceBlock029
  | ⟨30, _⟩ => exact plane484_sourceBlock030
  | ⟨31, _⟩ => exact plane484_sourceBlock031
  | ⟨32, _⟩ => exact plane484_sourceBlock032
  | ⟨33, _⟩ => exact plane484_sourceBlock033
  | ⟨34, _⟩ => exact plane484_sourceBlock034
  | ⟨35, _⟩ => exact plane484_sourceBlock035
  | ⟨36, _⟩ => exact plane484_sourceBlock036
  | ⟨37, _⟩ => exact plane484_sourceBlock037
  | ⟨38, _⟩ => exact plane484_sourceBlock038
  | ⟨39, _⟩ => exact plane484_sourceBlock039
  | ⟨40, _⟩ => exact plane484_sourceBlock040
  | ⟨41, _⟩ => exact plane484_sourceBlock041
  | ⟨42, _⟩ => exact plane484_sourceBlock042
  | ⟨43, _⟩ => exact plane484_sourceBlock043
  | ⟨44, _⟩ => exact plane484_sourceBlock044
  | ⟨45, _⟩ => exact plane484_sourceBlock045
  | ⟨46, _⟩ => exact plane484_sourceBlock046
  | ⟨47, _⟩ => exact plane484_sourceBlock047
  | ⟨48, _⟩ => exact plane484_sourceBlock048
  | ⟨49, _⟩ => exact plane484_sourceBlock049
  | ⟨50, _⟩ => exact plane484_sourceBlock050
  | ⟨51, _⟩ => exact plane484_sourceBlock051
  | ⟨52, _⟩ => exact plane484_sourceBlock052
  | ⟨k + 53, h⟩ => omega

theorem plane484_dead : ∀ i : Fin plane484GenConfig.nDead,
    plane484GenConfig.target ≤ frozenWangTable.L0 (plane484GenConfig.deadU i) := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484_deadBlock000
  | ⟨1, _⟩ => exact plane484_deadBlock001
  | ⟨2, _⟩ => exact plane484_deadBlock002
  | ⟨k + 3, h⟩ => omega


end QiushiMatmul.FrozenWang
