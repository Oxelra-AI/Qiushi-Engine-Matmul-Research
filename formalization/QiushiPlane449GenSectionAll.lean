import QiushiPlane449GenSectionBlock0
import QiushiPlane449GenSectionBlock1
import QiushiPlane449GenSectionBlock2
import QiushiPlane449GenSectionBlock3
import QiushiPlane449GenSectionBlock4
import QiushiPlane449GenSectionBlock5
import QiushiPlane449GenSectionBlock6
import QiushiPlane449GenSectionBlock7
import QiushiPlane449GenSectionBlock8
import QiushiPlane449GenSectionBlock9
import QiushiPlane449GenSectionBlock10
import QiushiPlane449GenSectionBlock11
import QiushiPlane449GenSectionBlock12
import QiushiPlane449GenSectionBlock13
import QiushiPlane449GenSectionBlock14
import QiushiPlane449GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenSectionAll : forall i, plane449GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane449GenSectionBlock0
  | ⟨1, _⟩ => exact plane449GenSectionBlock1
  | ⟨2, _⟩ => exact plane449GenSectionBlock2
  | ⟨3, _⟩ => exact plane449GenSectionBlock3
  | ⟨4, _⟩ => exact plane449GenSectionBlock4
  | ⟨5, _⟩ => exact plane449GenSectionBlock5
  | ⟨6, _⟩ => exact plane449GenSectionBlock6
  | ⟨7, _⟩ => exact plane449GenSectionBlock7
  | ⟨8, _⟩ => exact plane449GenSectionBlock8
  | ⟨9, _⟩ => exact plane449GenSectionBlock9
  | ⟨10, _⟩ => exact plane449GenSectionBlock10
  | ⟨11, _⟩ => exact plane449GenSectionBlock11
  | ⟨12, _⟩ => exact plane449GenSectionBlock12
  | ⟨13, _⟩ => exact plane449GenSectionBlock13
  | ⟨14, _⟩ => exact plane449GenSectionBlock14
  | ⟨15, _⟩ => exact plane449GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
