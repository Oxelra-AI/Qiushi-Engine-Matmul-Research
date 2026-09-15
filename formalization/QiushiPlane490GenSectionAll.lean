import QiushiPlane490GenSectionBlock0
import QiushiPlane490GenSectionBlock1
import QiushiPlane490GenSectionBlock2
import QiushiPlane490GenSectionBlock3
import QiushiPlane490GenSectionBlock4
import QiushiPlane490GenSectionBlock5
import QiushiPlane490GenSectionBlock6
import QiushiPlane490GenSectionBlock7
import QiushiPlane490GenSectionBlock8
import QiushiPlane490GenSectionBlock9
import QiushiPlane490GenSectionBlock10
import QiushiPlane490GenSectionBlock11
import QiushiPlane490GenSectionBlock12
import QiushiPlane490GenSectionBlock13
import QiushiPlane490GenSectionBlock14
import QiushiPlane490GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenSectionAll : forall i, plane490GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490GenSectionBlock0
  | ⟨1, _⟩ => exact plane490GenSectionBlock1
  | ⟨2, _⟩ => exact plane490GenSectionBlock2
  | ⟨3, _⟩ => exact plane490GenSectionBlock3
  | ⟨4, _⟩ => exact plane490GenSectionBlock4
  | ⟨5, _⟩ => exact plane490GenSectionBlock5
  | ⟨6, _⟩ => exact plane490GenSectionBlock6
  | ⟨7, _⟩ => exact plane490GenSectionBlock7
  | ⟨8, _⟩ => exact plane490GenSectionBlock8
  | ⟨9, _⟩ => exact plane490GenSectionBlock9
  | ⟨10, _⟩ => exact plane490GenSectionBlock10
  | ⟨11, _⟩ => exact plane490GenSectionBlock11
  | ⟨12, _⟩ => exact plane490GenSectionBlock12
  | ⟨13, _⟩ => exact plane490GenSectionBlock13
  | ⟨14, _⟩ => exact plane490GenSectionBlock14
  | ⟨15, _⟩ => exact plane490GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
