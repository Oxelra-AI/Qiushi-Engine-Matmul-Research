import QiushiPlane463LowerGenSectionBlock0
import QiushiPlane463LowerGenSectionBlock1
import QiushiPlane463LowerGenSectionBlock2
import QiushiPlane463LowerGenSectionBlock3
import QiushiPlane463LowerGenSectionBlock4
import QiushiPlane463LowerGenSectionBlock5
import QiushiPlane463LowerGenSectionBlock6
import QiushiPlane463LowerGenSectionBlock7
import QiushiPlane463LowerGenSectionBlock8
import QiushiPlane463LowerGenSectionBlock9
import QiushiPlane463LowerGenSectionBlock10
import QiushiPlane463LowerGenSectionBlock11
import QiushiPlane463LowerGenSectionBlock12
import QiushiPlane463LowerGenSectionBlock13
import QiushiPlane463LowerGenSectionBlock14
import QiushiPlane463LowerGenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenSectionAll : forall i, plane463LowerGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463LowerGenSectionBlock0
  | ⟨1, _⟩ => exact plane463LowerGenSectionBlock1
  | ⟨2, _⟩ => exact plane463LowerGenSectionBlock2
  | ⟨3, _⟩ => exact plane463LowerGenSectionBlock3
  | ⟨4, _⟩ => exact plane463LowerGenSectionBlock4
  | ⟨5, _⟩ => exact plane463LowerGenSectionBlock5
  | ⟨6, _⟩ => exact plane463LowerGenSectionBlock6
  | ⟨7, _⟩ => exact plane463LowerGenSectionBlock7
  | ⟨8, _⟩ => exact plane463LowerGenSectionBlock8
  | ⟨9, _⟩ => exact plane463LowerGenSectionBlock9
  | ⟨10, _⟩ => exact plane463LowerGenSectionBlock10
  | ⟨11, _⟩ => exact plane463LowerGenSectionBlock11
  | ⟨12, _⟩ => exact plane463LowerGenSectionBlock12
  | ⟨13, _⟩ => exact plane463LowerGenSectionBlock13
  | ⟨14, _⟩ => exact plane463LowerGenSectionBlock14
  | ⟨15, _⟩ => exact plane463LowerGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
