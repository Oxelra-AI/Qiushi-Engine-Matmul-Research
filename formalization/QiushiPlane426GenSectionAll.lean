import QiushiPlane426GenSectionBlock0
import QiushiPlane426GenSectionBlock1
import QiushiPlane426GenSectionBlock2
import QiushiPlane426GenSectionBlock3
import QiushiPlane426GenSectionBlock4
import QiushiPlane426GenSectionBlock5
import QiushiPlane426GenSectionBlock6
import QiushiPlane426GenSectionBlock7
import QiushiPlane426GenSectionBlock8
import QiushiPlane426GenSectionBlock9
import QiushiPlane426GenSectionBlock10
import QiushiPlane426GenSectionBlock11
import QiushiPlane426GenSectionBlock12
import QiushiPlane426GenSectionBlock13
import QiushiPlane426GenSectionBlock14
import QiushiPlane426GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenSectionAll : forall i, plane426GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane426GenSectionBlock0
  | ⟨1, _⟩ => exact plane426GenSectionBlock1
  | ⟨2, _⟩ => exact plane426GenSectionBlock2
  | ⟨3, _⟩ => exact plane426GenSectionBlock3
  | ⟨4, _⟩ => exact plane426GenSectionBlock4
  | ⟨5, _⟩ => exact plane426GenSectionBlock5
  | ⟨6, _⟩ => exact plane426GenSectionBlock6
  | ⟨7, _⟩ => exact plane426GenSectionBlock7
  | ⟨8, _⟩ => exact plane426GenSectionBlock8
  | ⟨9, _⟩ => exact plane426GenSectionBlock9
  | ⟨10, _⟩ => exact plane426GenSectionBlock10
  | ⟨11, _⟩ => exact plane426GenSectionBlock11
  | ⟨12, _⟩ => exact plane426GenSectionBlock12
  | ⟨13, _⟩ => exact plane426GenSectionBlock13
  | ⟨14, _⟩ => exact plane426GenSectionBlock14
  | ⟨15, _⟩ => exact plane426GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
