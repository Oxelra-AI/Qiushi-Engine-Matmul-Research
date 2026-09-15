import QiushiPlane425GenSectionBlock0
import QiushiPlane425GenSectionBlock1
import QiushiPlane425GenSectionBlock2
import QiushiPlane425GenSectionBlock3
import QiushiPlane425GenSectionBlock4
import QiushiPlane425GenSectionBlock5
import QiushiPlane425GenSectionBlock6
import QiushiPlane425GenSectionBlock7
import QiushiPlane425GenSectionBlock8
import QiushiPlane425GenSectionBlock9
import QiushiPlane425GenSectionBlock10
import QiushiPlane425GenSectionBlock11
import QiushiPlane425GenSectionBlock12
import QiushiPlane425GenSectionBlock13
import QiushiPlane425GenSectionBlock14
import QiushiPlane425GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenSectionAll : forall i, plane425GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane425GenSectionBlock0
  | ⟨1, _⟩ => exact plane425GenSectionBlock1
  | ⟨2, _⟩ => exact plane425GenSectionBlock2
  | ⟨3, _⟩ => exact plane425GenSectionBlock3
  | ⟨4, _⟩ => exact plane425GenSectionBlock4
  | ⟨5, _⟩ => exact plane425GenSectionBlock5
  | ⟨6, _⟩ => exact plane425GenSectionBlock6
  | ⟨7, _⟩ => exact plane425GenSectionBlock7
  | ⟨8, _⟩ => exact plane425GenSectionBlock8
  | ⟨9, _⟩ => exact plane425GenSectionBlock9
  | ⟨10, _⟩ => exact plane425GenSectionBlock10
  | ⟨11, _⟩ => exact plane425GenSectionBlock11
  | ⟨12, _⟩ => exact plane425GenSectionBlock12
  | ⟨13, _⟩ => exact plane425GenSectionBlock13
  | ⟨14, _⟩ => exact plane425GenSectionBlock14
  | ⟨15, _⟩ => exact plane425GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
