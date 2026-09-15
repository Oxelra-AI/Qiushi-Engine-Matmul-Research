import QiushiPlane477GenSectionBlock0
import QiushiPlane477GenSectionBlock1
import QiushiPlane477GenSectionBlock2
import QiushiPlane477GenSectionBlock3
import QiushiPlane477GenSectionBlock4
import QiushiPlane477GenSectionBlock5
import QiushiPlane477GenSectionBlock6
import QiushiPlane477GenSectionBlock7
import QiushiPlane477GenSectionBlock8
import QiushiPlane477GenSectionBlock9
import QiushiPlane477GenSectionBlock10
import QiushiPlane477GenSectionBlock11
import QiushiPlane477GenSectionBlock12
import QiushiPlane477GenSectionBlock13
import QiushiPlane477GenSectionBlock14
import QiushiPlane477GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane477GenSectionAll : forall i, plane477GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane477GenSectionBlock0
  | ⟨1, _⟩ => exact plane477GenSectionBlock1
  | ⟨2, _⟩ => exact plane477GenSectionBlock2
  | ⟨3, _⟩ => exact plane477GenSectionBlock3
  | ⟨4, _⟩ => exact plane477GenSectionBlock4
  | ⟨5, _⟩ => exact plane477GenSectionBlock5
  | ⟨6, _⟩ => exact plane477GenSectionBlock6
  | ⟨7, _⟩ => exact plane477GenSectionBlock7
  | ⟨8, _⟩ => exact plane477GenSectionBlock8
  | ⟨9, _⟩ => exact plane477GenSectionBlock9
  | ⟨10, _⟩ => exact plane477GenSectionBlock10
  | ⟨11, _⟩ => exact plane477GenSectionBlock11
  | ⟨12, _⟩ => exact plane477GenSectionBlock12
  | ⟨13, _⟩ => exact plane477GenSectionBlock13
  | ⟨14, _⟩ => exact plane477GenSectionBlock14
  | ⟨15, _⟩ => exact plane477GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
