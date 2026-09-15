import QiushiPlane464GenSectionBlock0
import QiushiPlane464GenSectionBlock1
import QiushiPlane464GenSectionBlock2
import QiushiPlane464GenSectionBlock3
import QiushiPlane464GenSectionBlock4
import QiushiPlane464GenSectionBlock5
import QiushiPlane464GenSectionBlock6
import QiushiPlane464GenSectionBlock7
import QiushiPlane464GenSectionBlock8
import QiushiPlane464GenSectionBlock9
import QiushiPlane464GenSectionBlock10
import QiushiPlane464GenSectionBlock11
import QiushiPlane464GenSectionBlock12
import QiushiPlane464GenSectionBlock13
import QiushiPlane464GenSectionBlock14
import QiushiPlane464GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenSectionAll : forall i, plane464GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane464GenSectionBlock0
  | ⟨1, _⟩ => exact plane464GenSectionBlock1
  | ⟨2, _⟩ => exact plane464GenSectionBlock2
  | ⟨3, _⟩ => exact plane464GenSectionBlock3
  | ⟨4, _⟩ => exact plane464GenSectionBlock4
  | ⟨5, _⟩ => exact plane464GenSectionBlock5
  | ⟨6, _⟩ => exact plane464GenSectionBlock6
  | ⟨7, _⟩ => exact plane464GenSectionBlock7
  | ⟨8, _⟩ => exact plane464GenSectionBlock8
  | ⟨9, _⟩ => exact plane464GenSectionBlock9
  | ⟨10, _⟩ => exact plane464GenSectionBlock10
  | ⟨11, _⟩ => exact plane464GenSectionBlock11
  | ⟨12, _⟩ => exact plane464GenSectionBlock12
  | ⟨13, _⟩ => exact plane464GenSectionBlock13
  | ⟨14, _⟩ => exact plane464GenSectionBlock14
  | ⟨15, _⟩ => exact plane464GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
