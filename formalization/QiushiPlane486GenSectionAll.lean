import QiushiPlane486GenSectionBlock0
import QiushiPlane486GenSectionBlock1
import QiushiPlane486GenSectionBlock2
import QiushiPlane486GenSectionBlock3
import QiushiPlane486GenSectionBlock4
import QiushiPlane486GenSectionBlock5
import QiushiPlane486GenSectionBlock6
import QiushiPlane486GenSectionBlock7
import QiushiPlane486GenSectionBlock8
import QiushiPlane486GenSectionBlock9
import QiushiPlane486GenSectionBlock10
import QiushiPlane486GenSectionBlock11
import QiushiPlane486GenSectionBlock12
import QiushiPlane486GenSectionBlock13
import QiushiPlane486GenSectionBlock14
import QiushiPlane486GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenSectionAll : forall i, plane486GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486GenSectionBlock0
  | ⟨1, _⟩ => exact plane486GenSectionBlock1
  | ⟨2, _⟩ => exact plane486GenSectionBlock2
  | ⟨3, _⟩ => exact plane486GenSectionBlock3
  | ⟨4, _⟩ => exact plane486GenSectionBlock4
  | ⟨5, _⟩ => exact plane486GenSectionBlock5
  | ⟨6, _⟩ => exact plane486GenSectionBlock6
  | ⟨7, _⟩ => exact plane486GenSectionBlock7
  | ⟨8, _⟩ => exact plane486GenSectionBlock8
  | ⟨9, _⟩ => exact plane486GenSectionBlock9
  | ⟨10, _⟩ => exact plane486GenSectionBlock10
  | ⟨11, _⟩ => exact plane486GenSectionBlock11
  | ⟨12, _⟩ => exact plane486GenSectionBlock12
  | ⟨13, _⟩ => exact plane486GenSectionBlock13
  | ⟨14, _⟩ => exact plane486GenSectionBlock14
  | ⟨15, _⟩ => exact plane486GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
