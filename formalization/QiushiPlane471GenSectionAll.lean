import QiushiPlane471GenSectionBlock0
import QiushiPlane471GenSectionBlock1
import QiushiPlane471GenSectionBlock2
import QiushiPlane471GenSectionBlock3
import QiushiPlane471GenSectionBlock4
import QiushiPlane471GenSectionBlock5
import QiushiPlane471GenSectionBlock6
import QiushiPlane471GenSectionBlock7
import QiushiPlane471GenSectionBlock8
import QiushiPlane471GenSectionBlock9
import QiushiPlane471GenSectionBlock10
import QiushiPlane471GenSectionBlock11
import QiushiPlane471GenSectionBlock12
import QiushiPlane471GenSectionBlock13
import QiushiPlane471GenSectionBlock14
import QiushiPlane471GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenSectionAll : forall i, plane471GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471GenSectionBlock0
  | ⟨1, _⟩ => exact plane471GenSectionBlock1
  | ⟨2, _⟩ => exact plane471GenSectionBlock2
  | ⟨3, _⟩ => exact plane471GenSectionBlock3
  | ⟨4, _⟩ => exact plane471GenSectionBlock4
  | ⟨5, _⟩ => exact plane471GenSectionBlock5
  | ⟨6, _⟩ => exact plane471GenSectionBlock6
  | ⟨7, _⟩ => exact plane471GenSectionBlock7
  | ⟨8, _⟩ => exact plane471GenSectionBlock8
  | ⟨9, _⟩ => exact plane471GenSectionBlock9
  | ⟨10, _⟩ => exact plane471GenSectionBlock10
  | ⟨11, _⟩ => exact plane471GenSectionBlock11
  | ⟨12, _⟩ => exact plane471GenSectionBlock12
  | ⟨13, _⟩ => exact plane471GenSectionBlock13
  | ⟨14, _⟩ => exact plane471GenSectionBlock14
  | ⟨15, _⟩ => exact plane471GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
