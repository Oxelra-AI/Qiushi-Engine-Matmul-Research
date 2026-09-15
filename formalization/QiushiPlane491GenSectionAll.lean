import QiushiPlane491GenSectionBlock0
import QiushiPlane491GenSectionBlock1
import QiushiPlane491GenSectionBlock2
import QiushiPlane491GenSectionBlock3
import QiushiPlane491GenSectionBlock4
import QiushiPlane491GenSectionBlock5
import QiushiPlane491GenSectionBlock6
import QiushiPlane491GenSectionBlock7
import QiushiPlane491GenSectionBlock8
import QiushiPlane491GenSectionBlock9
import QiushiPlane491GenSectionBlock10
import QiushiPlane491GenSectionBlock11
import QiushiPlane491GenSectionBlock12
import QiushiPlane491GenSectionBlock13
import QiushiPlane491GenSectionBlock14
import QiushiPlane491GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenSectionAll : forall i, plane491GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491GenSectionBlock0
  | ⟨1, _⟩ => exact plane491GenSectionBlock1
  | ⟨2, _⟩ => exact plane491GenSectionBlock2
  | ⟨3, _⟩ => exact plane491GenSectionBlock3
  | ⟨4, _⟩ => exact plane491GenSectionBlock4
  | ⟨5, _⟩ => exact plane491GenSectionBlock5
  | ⟨6, _⟩ => exact plane491GenSectionBlock6
  | ⟨7, _⟩ => exact plane491GenSectionBlock7
  | ⟨8, _⟩ => exact plane491GenSectionBlock8
  | ⟨9, _⟩ => exact plane491GenSectionBlock9
  | ⟨10, _⟩ => exact plane491GenSectionBlock10
  | ⟨11, _⟩ => exact plane491GenSectionBlock11
  | ⟨12, _⟩ => exact plane491GenSectionBlock12
  | ⟨13, _⟩ => exact plane491GenSectionBlock13
  | ⟨14, _⟩ => exact plane491GenSectionBlock14
  | ⟨15, _⟩ => exact plane491GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
