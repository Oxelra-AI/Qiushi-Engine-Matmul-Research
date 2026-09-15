import QiushiPlane456LowerGenSectionBlock0
import QiushiPlane456LowerGenSectionBlock1
import QiushiPlane456LowerGenSectionBlock2
import QiushiPlane456LowerGenSectionBlock3
import QiushiPlane456LowerGenSectionBlock4
import QiushiPlane456LowerGenSectionBlock5
import QiushiPlane456LowerGenSectionBlock6
import QiushiPlane456LowerGenSectionBlock7
import QiushiPlane456LowerGenSectionBlock8
import QiushiPlane456LowerGenSectionBlock9
import QiushiPlane456LowerGenSectionBlock10
import QiushiPlane456LowerGenSectionBlock11
import QiushiPlane456LowerGenSectionBlock12
import QiushiPlane456LowerGenSectionBlock13
import QiushiPlane456LowerGenSectionBlock14
import QiushiPlane456LowerGenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456LowerGenSectionAll : forall i, plane456LowerGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456LowerGenSectionBlock0
  | ⟨1, _⟩ => exact plane456LowerGenSectionBlock1
  | ⟨2, _⟩ => exact plane456LowerGenSectionBlock2
  | ⟨3, _⟩ => exact plane456LowerGenSectionBlock3
  | ⟨4, _⟩ => exact plane456LowerGenSectionBlock4
  | ⟨5, _⟩ => exact plane456LowerGenSectionBlock5
  | ⟨6, _⟩ => exact plane456LowerGenSectionBlock6
  | ⟨7, _⟩ => exact plane456LowerGenSectionBlock7
  | ⟨8, _⟩ => exact plane456LowerGenSectionBlock8
  | ⟨9, _⟩ => exact plane456LowerGenSectionBlock9
  | ⟨10, _⟩ => exact plane456LowerGenSectionBlock10
  | ⟨11, _⟩ => exact plane456LowerGenSectionBlock11
  | ⟨12, _⟩ => exact plane456LowerGenSectionBlock12
  | ⟨13, _⟩ => exact plane456LowerGenSectionBlock13
  | ⟨14, _⟩ => exact plane456LowerGenSectionBlock14
  | ⟨15, _⟩ => exact plane456LowerGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
