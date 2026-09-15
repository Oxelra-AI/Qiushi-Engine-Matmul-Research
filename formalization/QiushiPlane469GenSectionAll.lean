import QiushiPlane469GenSectionBlock0
import QiushiPlane469GenSectionBlock1
import QiushiPlane469GenSectionBlock2
import QiushiPlane469GenSectionBlock3
import QiushiPlane469GenSectionBlock4
import QiushiPlane469GenSectionBlock5
import QiushiPlane469GenSectionBlock6
import QiushiPlane469GenSectionBlock7
import QiushiPlane469GenSectionBlock8
import QiushiPlane469GenSectionBlock9
import QiushiPlane469GenSectionBlock10
import QiushiPlane469GenSectionBlock11
import QiushiPlane469GenSectionBlock12
import QiushiPlane469GenSectionBlock13
import QiushiPlane469GenSectionBlock14
import QiushiPlane469GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenSectionAll : forall i, plane469GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane469GenSectionBlock0
  | ⟨1, _⟩ => exact plane469GenSectionBlock1
  | ⟨2, _⟩ => exact plane469GenSectionBlock2
  | ⟨3, _⟩ => exact plane469GenSectionBlock3
  | ⟨4, _⟩ => exact plane469GenSectionBlock4
  | ⟨5, _⟩ => exact plane469GenSectionBlock5
  | ⟨6, _⟩ => exact plane469GenSectionBlock6
  | ⟨7, _⟩ => exact plane469GenSectionBlock7
  | ⟨8, _⟩ => exact plane469GenSectionBlock8
  | ⟨9, _⟩ => exact plane469GenSectionBlock9
  | ⟨10, _⟩ => exact plane469GenSectionBlock10
  | ⟨11, _⟩ => exact plane469GenSectionBlock11
  | ⟨12, _⟩ => exact plane469GenSectionBlock12
  | ⟨13, _⟩ => exact plane469GenSectionBlock13
  | ⟨14, _⟩ => exact plane469GenSectionBlock14
  | ⟨15, _⟩ => exact plane469GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
