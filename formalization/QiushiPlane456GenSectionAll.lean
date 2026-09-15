import QiushiPlane456GenSectionBlock0
import QiushiPlane456GenSectionBlock1
import QiushiPlane456GenSectionBlock2
import QiushiPlane456GenSectionBlock3
import QiushiPlane456GenSectionBlock4
import QiushiPlane456GenSectionBlock5
import QiushiPlane456GenSectionBlock6
import QiushiPlane456GenSectionBlock7
import QiushiPlane456GenSectionBlock8
import QiushiPlane456GenSectionBlock9
import QiushiPlane456GenSectionBlock10
import QiushiPlane456GenSectionBlock11
import QiushiPlane456GenSectionBlock12
import QiushiPlane456GenSectionBlock13
import QiushiPlane456GenSectionBlock14
import QiushiPlane456GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenSectionAll : forall i, plane456GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456GenSectionBlock0
  | ⟨1, _⟩ => exact plane456GenSectionBlock1
  | ⟨2, _⟩ => exact plane456GenSectionBlock2
  | ⟨3, _⟩ => exact plane456GenSectionBlock3
  | ⟨4, _⟩ => exact plane456GenSectionBlock4
  | ⟨5, _⟩ => exact plane456GenSectionBlock5
  | ⟨6, _⟩ => exact plane456GenSectionBlock6
  | ⟨7, _⟩ => exact plane456GenSectionBlock7
  | ⟨8, _⟩ => exact plane456GenSectionBlock8
  | ⟨9, _⟩ => exact plane456GenSectionBlock9
  | ⟨10, _⟩ => exact plane456GenSectionBlock10
  | ⟨11, _⟩ => exact plane456GenSectionBlock11
  | ⟨12, _⟩ => exact plane456GenSectionBlock12
  | ⟨13, _⟩ => exact plane456GenSectionBlock13
  | ⟨14, _⟩ => exact plane456GenSectionBlock14
  | ⟨15, _⟩ => exact plane456GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
