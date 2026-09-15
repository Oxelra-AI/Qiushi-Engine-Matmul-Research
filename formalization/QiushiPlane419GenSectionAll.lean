import QiushiPlane419GenSectionBlock0
import QiushiPlane419GenSectionBlock1
import QiushiPlane419GenSectionBlock2
import QiushiPlane419GenSectionBlock3
import QiushiPlane419GenSectionBlock4
import QiushiPlane419GenSectionBlock5
import QiushiPlane419GenSectionBlock6
import QiushiPlane419GenSectionBlock7
import QiushiPlane419GenSectionBlock8
import QiushiPlane419GenSectionBlock9
import QiushiPlane419GenSectionBlock10
import QiushiPlane419GenSectionBlock11
import QiushiPlane419GenSectionBlock12
import QiushiPlane419GenSectionBlock13
import QiushiPlane419GenSectionBlock14
import QiushiPlane419GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenSectionAll : forall i, plane419GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane419GenSectionBlock0
  | ⟨1, _⟩ => exact plane419GenSectionBlock1
  | ⟨2, _⟩ => exact plane419GenSectionBlock2
  | ⟨3, _⟩ => exact plane419GenSectionBlock3
  | ⟨4, _⟩ => exact plane419GenSectionBlock4
  | ⟨5, _⟩ => exact plane419GenSectionBlock5
  | ⟨6, _⟩ => exact plane419GenSectionBlock6
  | ⟨7, _⟩ => exact plane419GenSectionBlock7
  | ⟨8, _⟩ => exact plane419GenSectionBlock8
  | ⟨9, _⟩ => exact plane419GenSectionBlock9
  | ⟨10, _⟩ => exact plane419GenSectionBlock10
  | ⟨11, _⟩ => exact plane419GenSectionBlock11
  | ⟨12, _⟩ => exact plane419GenSectionBlock12
  | ⟨13, _⟩ => exact plane419GenSectionBlock13
  | ⟨14, _⟩ => exact plane419GenSectionBlock14
  | ⟨15, _⟩ => exact plane419GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
