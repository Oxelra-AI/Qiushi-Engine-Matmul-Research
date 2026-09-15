import QiushiPlane487GenSectionBlock0
import QiushiPlane487GenSectionBlock1
import QiushiPlane487GenSectionBlock2
import QiushiPlane487GenSectionBlock3
import QiushiPlane487GenSectionBlock4
import QiushiPlane487GenSectionBlock5
import QiushiPlane487GenSectionBlock6
import QiushiPlane487GenSectionBlock7
import QiushiPlane487GenSectionBlock8
import QiushiPlane487GenSectionBlock9
import QiushiPlane487GenSectionBlock10
import QiushiPlane487GenSectionBlock11
import QiushiPlane487GenSectionBlock12
import QiushiPlane487GenSectionBlock13
import QiushiPlane487GenSectionBlock14
import QiushiPlane487GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenSectionAll : forall i, plane487GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487GenSectionBlock0
  | ⟨1, _⟩ => exact plane487GenSectionBlock1
  | ⟨2, _⟩ => exact plane487GenSectionBlock2
  | ⟨3, _⟩ => exact plane487GenSectionBlock3
  | ⟨4, _⟩ => exact plane487GenSectionBlock4
  | ⟨5, _⟩ => exact plane487GenSectionBlock5
  | ⟨6, _⟩ => exact plane487GenSectionBlock6
  | ⟨7, _⟩ => exact plane487GenSectionBlock7
  | ⟨8, _⟩ => exact plane487GenSectionBlock8
  | ⟨9, _⟩ => exact plane487GenSectionBlock9
  | ⟨10, _⟩ => exact plane487GenSectionBlock10
  | ⟨11, _⟩ => exact plane487GenSectionBlock11
  | ⟨12, _⟩ => exact plane487GenSectionBlock12
  | ⟨13, _⟩ => exact plane487GenSectionBlock13
  | ⟨14, _⟩ => exact plane487GenSectionBlock14
  | ⟨15, _⟩ => exact plane487GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
