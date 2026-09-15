import QiushiPlane269GenSectionBlock0
import QiushiPlane269GenSectionBlock1
import QiushiPlane269GenSectionBlock2
import QiushiPlane269GenSectionBlock3
import QiushiPlane269GenSectionBlock4
import QiushiPlane269GenSectionBlock5
import QiushiPlane269GenSectionBlock6
import QiushiPlane269GenSectionBlock7
import QiushiPlane269GenSectionBlock8
import QiushiPlane269GenSectionBlock9
import QiushiPlane269GenSectionBlock10
import QiushiPlane269GenSectionBlock11
import QiushiPlane269GenSectionBlock12
import QiushiPlane269GenSectionBlock13
import QiushiPlane269GenSectionBlock14
import QiushiPlane269GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane269GenSectionAll : forall i, plane269GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane269GenSectionBlock0
  | ⟨1, _⟩ => exact plane269GenSectionBlock1
  | ⟨2, _⟩ => exact plane269GenSectionBlock2
  | ⟨3, _⟩ => exact plane269GenSectionBlock3
  | ⟨4, _⟩ => exact plane269GenSectionBlock4
  | ⟨5, _⟩ => exact plane269GenSectionBlock5
  | ⟨6, _⟩ => exact plane269GenSectionBlock6
  | ⟨7, _⟩ => exact plane269GenSectionBlock7
  | ⟨8, _⟩ => exact plane269GenSectionBlock8
  | ⟨9, _⟩ => exact plane269GenSectionBlock9
  | ⟨10, _⟩ => exact plane269GenSectionBlock10
  | ⟨11, _⟩ => exact plane269GenSectionBlock11
  | ⟨12, _⟩ => exact plane269GenSectionBlock12
  | ⟨13, _⟩ => exact plane269GenSectionBlock13
  | ⟨14, _⟩ => exact plane269GenSectionBlock14
  | ⟨15, _⟩ => exact plane269GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
