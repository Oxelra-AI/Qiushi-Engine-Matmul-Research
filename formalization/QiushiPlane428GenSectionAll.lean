import QiushiPlane428GenSectionBlock0
import QiushiPlane428GenSectionBlock1
import QiushiPlane428GenSectionBlock2
import QiushiPlane428GenSectionBlock3
import QiushiPlane428GenSectionBlock4
import QiushiPlane428GenSectionBlock5
import QiushiPlane428GenSectionBlock6
import QiushiPlane428GenSectionBlock7
import QiushiPlane428GenSectionBlock8
import QiushiPlane428GenSectionBlock9
import QiushiPlane428GenSectionBlock10
import QiushiPlane428GenSectionBlock11
import QiushiPlane428GenSectionBlock12
import QiushiPlane428GenSectionBlock13
import QiushiPlane428GenSectionBlock14
import QiushiPlane428GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenSectionAll : forall i, plane428GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane428GenSectionBlock0
  | ⟨1, _⟩ => exact plane428GenSectionBlock1
  | ⟨2, _⟩ => exact plane428GenSectionBlock2
  | ⟨3, _⟩ => exact plane428GenSectionBlock3
  | ⟨4, _⟩ => exact plane428GenSectionBlock4
  | ⟨5, _⟩ => exact plane428GenSectionBlock5
  | ⟨6, _⟩ => exact plane428GenSectionBlock6
  | ⟨7, _⟩ => exact plane428GenSectionBlock7
  | ⟨8, _⟩ => exact plane428GenSectionBlock8
  | ⟨9, _⟩ => exact plane428GenSectionBlock9
  | ⟨10, _⟩ => exact plane428GenSectionBlock10
  | ⟨11, _⟩ => exact plane428GenSectionBlock11
  | ⟨12, _⟩ => exact plane428GenSectionBlock12
  | ⟨13, _⟩ => exact plane428GenSectionBlock13
  | ⟨14, _⟩ => exact plane428GenSectionBlock14
  | ⟨15, _⟩ => exact plane428GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
