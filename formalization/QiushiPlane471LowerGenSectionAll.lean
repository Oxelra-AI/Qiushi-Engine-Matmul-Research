import QiushiPlane471LowerGenSectionBlock0
import QiushiPlane471LowerGenSectionBlock1
import QiushiPlane471LowerGenSectionBlock2
import QiushiPlane471LowerGenSectionBlock3
import QiushiPlane471LowerGenSectionBlock4
import QiushiPlane471LowerGenSectionBlock5
import QiushiPlane471LowerGenSectionBlock6
import QiushiPlane471LowerGenSectionBlock7
import QiushiPlane471LowerGenSectionBlock8
import QiushiPlane471LowerGenSectionBlock9
import QiushiPlane471LowerGenSectionBlock10
import QiushiPlane471LowerGenSectionBlock11
import QiushiPlane471LowerGenSectionBlock12
import QiushiPlane471LowerGenSectionBlock13
import QiushiPlane471LowerGenSectionBlock14
import QiushiPlane471LowerGenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenSectionAll : forall i, plane471LowerGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471LowerGenSectionBlock0
  | ⟨1, _⟩ => exact plane471LowerGenSectionBlock1
  | ⟨2, _⟩ => exact plane471LowerGenSectionBlock2
  | ⟨3, _⟩ => exact plane471LowerGenSectionBlock3
  | ⟨4, _⟩ => exact plane471LowerGenSectionBlock4
  | ⟨5, _⟩ => exact plane471LowerGenSectionBlock5
  | ⟨6, _⟩ => exact plane471LowerGenSectionBlock6
  | ⟨7, _⟩ => exact plane471LowerGenSectionBlock7
  | ⟨8, _⟩ => exact plane471LowerGenSectionBlock8
  | ⟨9, _⟩ => exact plane471LowerGenSectionBlock9
  | ⟨10, _⟩ => exact plane471LowerGenSectionBlock10
  | ⟨11, _⟩ => exact plane471LowerGenSectionBlock11
  | ⟨12, _⟩ => exact plane471LowerGenSectionBlock12
  | ⟨13, _⟩ => exact plane471LowerGenSectionBlock13
  | ⟨14, _⟩ => exact plane471LowerGenSectionBlock14
  | ⟨15, _⟩ => exact plane471LowerGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
