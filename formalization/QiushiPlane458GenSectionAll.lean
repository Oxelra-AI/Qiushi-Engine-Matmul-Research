import QiushiPlane458GenSectionBlock0
import QiushiPlane458GenSectionBlock1
import QiushiPlane458GenSectionBlock2
import QiushiPlane458GenSectionBlock3
import QiushiPlane458GenSectionBlock4
import QiushiPlane458GenSectionBlock5
import QiushiPlane458GenSectionBlock6
import QiushiPlane458GenSectionBlock7
import QiushiPlane458GenSectionBlock8
import QiushiPlane458GenSectionBlock9
import QiushiPlane458GenSectionBlock10
import QiushiPlane458GenSectionBlock11
import QiushiPlane458GenSectionBlock12
import QiushiPlane458GenSectionBlock13
import QiushiPlane458GenSectionBlock14
import QiushiPlane458GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenSectionAll : forall i, plane458GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane458GenSectionBlock0
  | ⟨1, _⟩ => exact plane458GenSectionBlock1
  | ⟨2, _⟩ => exact plane458GenSectionBlock2
  | ⟨3, _⟩ => exact plane458GenSectionBlock3
  | ⟨4, _⟩ => exact plane458GenSectionBlock4
  | ⟨5, _⟩ => exact plane458GenSectionBlock5
  | ⟨6, _⟩ => exact plane458GenSectionBlock6
  | ⟨7, _⟩ => exact plane458GenSectionBlock7
  | ⟨8, _⟩ => exact plane458GenSectionBlock8
  | ⟨9, _⟩ => exact plane458GenSectionBlock9
  | ⟨10, _⟩ => exact plane458GenSectionBlock10
  | ⟨11, _⟩ => exact plane458GenSectionBlock11
  | ⟨12, _⟩ => exact plane458GenSectionBlock12
  | ⟨13, _⟩ => exact plane458GenSectionBlock13
  | ⟨14, _⟩ => exact plane458GenSectionBlock14
  | ⟨15, _⟩ => exact plane458GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
