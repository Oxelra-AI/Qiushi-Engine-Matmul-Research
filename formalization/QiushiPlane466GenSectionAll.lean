import QiushiPlane466GenSectionBlock0
import QiushiPlane466GenSectionBlock1
import QiushiPlane466GenSectionBlock2
import QiushiPlane466GenSectionBlock3
import QiushiPlane466GenSectionBlock4
import QiushiPlane466GenSectionBlock5
import QiushiPlane466GenSectionBlock6
import QiushiPlane466GenSectionBlock7
import QiushiPlane466GenSectionBlock8
import QiushiPlane466GenSectionBlock9
import QiushiPlane466GenSectionBlock10
import QiushiPlane466GenSectionBlock11
import QiushiPlane466GenSectionBlock12
import QiushiPlane466GenSectionBlock13
import QiushiPlane466GenSectionBlock14
import QiushiPlane466GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenSectionAll : forall i, plane466GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane466GenSectionBlock0
  | ⟨1, _⟩ => exact plane466GenSectionBlock1
  | ⟨2, _⟩ => exact plane466GenSectionBlock2
  | ⟨3, _⟩ => exact plane466GenSectionBlock3
  | ⟨4, _⟩ => exact plane466GenSectionBlock4
  | ⟨5, _⟩ => exact plane466GenSectionBlock5
  | ⟨6, _⟩ => exact plane466GenSectionBlock6
  | ⟨7, _⟩ => exact plane466GenSectionBlock7
  | ⟨8, _⟩ => exact plane466GenSectionBlock8
  | ⟨9, _⟩ => exact plane466GenSectionBlock9
  | ⟨10, _⟩ => exact plane466GenSectionBlock10
  | ⟨11, _⟩ => exact plane466GenSectionBlock11
  | ⟨12, _⟩ => exact plane466GenSectionBlock12
  | ⟨13, _⟩ => exact plane466GenSectionBlock13
  | ⟨14, _⟩ => exact plane466GenSectionBlock14
  | ⟨15, _⟩ => exact plane466GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
