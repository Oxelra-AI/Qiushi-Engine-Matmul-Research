import QiushiPlane315GenSectionBlock0
import QiushiPlane315GenSectionBlock1
import QiushiPlane315GenSectionBlock2
import QiushiPlane315GenSectionBlock3
import QiushiPlane315GenSectionBlock4
import QiushiPlane315GenSectionBlock5
import QiushiPlane315GenSectionBlock6
import QiushiPlane315GenSectionBlock7
import QiushiPlane315GenSectionBlock8
import QiushiPlane315GenSectionBlock9
import QiushiPlane315GenSectionBlock10
import QiushiPlane315GenSectionBlock11
import QiushiPlane315GenSectionBlock12
import QiushiPlane315GenSectionBlock13
import QiushiPlane315GenSectionBlock14
import QiushiPlane315GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenSectionAll : forall i, plane315GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane315GenSectionBlock0
  | ⟨1, _⟩ => exact plane315GenSectionBlock1
  | ⟨2, _⟩ => exact plane315GenSectionBlock2
  | ⟨3, _⟩ => exact plane315GenSectionBlock3
  | ⟨4, _⟩ => exact plane315GenSectionBlock4
  | ⟨5, _⟩ => exact plane315GenSectionBlock5
  | ⟨6, _⟩ => exact plane315GenSectionBlock6
  | ⟨7, _⟩ => exact plane315GenSectionBlock7
  | ⟨8, _⟩ => exact plane315GenSectionBlock8
  | ⟨9, _⟩ => exact plane315GenSectionBlock9
  | ⟨10, _⟩ => exact plane315GenSectionBlock10
  | ⟨11, _⟩ => exact plane315GenSectionBlock11
  | ⟨12, _⟩ => exact plane315GenSectionBlock12
  | ⟨13, _⟩ => exact plane315GenSectionBlock13
  | ⟨14, _⟩ => exact plane315GenSectionBlock14
  | ⟨15, _⟩ => exact plane315GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
