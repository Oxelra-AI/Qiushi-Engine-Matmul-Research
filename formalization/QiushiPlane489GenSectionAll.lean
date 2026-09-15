import QiushiPlane489GenSectionBlock0
import QiushiPlane489GenSectionBlock1
import QiushiPlane489GenSectionBlock2
import QiushiPlane489GenSectionBlock3
import QiushiPlane489GenSectionBlock4
import QiushiPlane489GenSectionBlock5
import QiushiPlane489GenSectionBlock6
import QiushiPlane489GenSectionBlock7
import QiushiPlane489GenSectionBlock8
import QiushiPlane489GenSectionBlock9
import QiushiPlane489GenSectionBlock10
import QiushiPlane489GenSectionBlock11
import QiushiPlane489GenSectionBlock12
import QiushiPlane489GenSectionBlock13
import QiushiPlane489GenSectionBlock14
import QiushiPlane489GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenSectionAll : forall i, plane489GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489GenSectionBlock0
  | ⟨1, _⟩ => exact plane489GenSectionBlock1
  | ⟨2, _⟩ => exact plane489GenSectionBlock2
  | ⟨3, _⟩ => exact plane489GenSectionBlock3
  | ⟨4, _⟩ => exact plane489GenSectionBlock4
  | ⟨5, _⟩ => exact plane489GenSectionBlock5
  | ⟨6, _⟩ => exact plane489GenSectionBlock6
  | ⟨7, _⟩ => exact plane489GenSectionBlock7
  | ⟨8, _⟩ => exact plane489GenSectionBlock8
  | ⟨9, _⟩ => exact plane489GenSectionBlock9
  | ⟨10, _⟩ => exact plane489GenSectionBlock10
  | ⟨11, _⟩ => exact plane489GenSectionBlock11
  | ⟨12, _⟩ => exact plane489GenSectionBlock12
  | ⟨13, _⟩ => exact plane489GenSectionBlock13
  | ⟨14, _⟩ => exact plane489GenSectionBlock14
  | ⟨15, _⟩ => exact plane489GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
