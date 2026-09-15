import QiushiPlane457GenSectionBlock0
import QiushiPlane457GenSectionBlock1
import QiushiPlane457GenSectionBlock2
import QiushiPlane457GenSectionBlock3
import QiushiPlane457GenSectionBlock4
import QiushiPlane457GenSectionBlock5
import QiushiPlane457GenSectionBlock6
import QiushiPlane457GenSectionBlock7
import QiushiPlane457GenSectionBlock8
import QiushiPlane457GenSectionBlock9
import QiushiPlane457GenSectionBlock10
import QiushiPlane457GenSectionBlock11
import QiushiPlane457GenSectionBlock12
import QiushiPlane457GenSectionBlock13
import QiushiPlane457GenSectionBlock14
import QiushiPlane457GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenSectionAll : forall i, plane457GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane457GenSectionBlock0
  | ⟨1, _⟩ => exact plane457GenSectionBlock1
  | ⟨2, _⟩ => exact plane457GenSectionBlock2
  | ⟨3, _⟩ => exact plane457GenSectionBlock3
  | ⟨4, _⟩ => exact plane457GenSectionBlock4
  | ⟨5, _⟩ => exact plane457GenSectionBlock5
  | ⟨6, _⟩ => exact plane457GenSectionBlock6
  | ⟨7, _⟩ => exact plane457GenSectionBlock7
  | ⟨8, _⟩ => exact plane457GenSectionBlock8
  | ⟨9, _⟩ => exact plane457GenSectionBlock9
  | ⟨10, _⟩ => exact plane457GenSectionBlock10
  | ⟨11, _⟩ => exact plane457GenSectionBlock11
  | ⟨12, _⟩ => exact plane457GenSectionBlock12
  | ⟨13, _⟩ => exact plane457GenSectionBlock13
  | ⟨14, _⟩ => exact plane457GenSectionBlock14
  | ⟨15, _⟩ => exact plane457GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
