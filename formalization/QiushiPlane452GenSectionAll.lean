import QiushiPlane452GenSectionBlock0
import QiushiPlane452GenSectionBlock1
import QiushiPlane452GenSectionBlock2
import QiushiPlane452GenSectionBlock3
import QiushiPlane452GenSectionBlock4
import QiushiPlane452GenSectionBlock5
import QiushiPlane452GenSectionBlock6
import QiushiPlane452GenSectionBlock7
import QiushiPlane452GenSectionBlock8
import QiushiPlane452GenSectionBlock9
import QiushiPlane452GenSectionBlock10
import QiushiPlane452GenSectionBlock11
import QiushiPlane452GenSectionBlock12
import QiushiPlane452GenSectionBlock13
import QiushiPlane452GenSectionBlock14
import QiushiPlane452GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenSectionAll : forall i, plane452GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane452GenSectionBlock0
  | ⟨1, _⟩ => exact plane452GenSectionBlock1
  | ⟨2, _⟩ => exact plane452GenSectionBlock2
  | ⟨3, _⟩ => exact plane452GenSectionBlock3
  | ⟨4, _⟩ => exact plane452GenSectionBlock4
  | ⟨5, _⟩ => exact plane452GenSectionBlock5
  | ⟨6, _⟩ => exact plane452GenSectionBlock6
  | ⟨7, _⟩ => exact plane452GenSectionBlock7
  | ⟨8, _⟩ => exact plane452GenSectionBlock8
  | ⟨9, _⟩ => exact plane452GenSectionBlock9
  | ⟨10, _⟩ => exact plane452GenSectionBlock10
  | ⟨11, _⟩ => exact plane452GenSectionBlock11
  | ⟨12, _⟩ => exact plane452GenSectionBlock12
  | ⟨13, _⟩ => exact plane452GenSectionBlock13
  | ⟨14, _⟩ => exact plane452GenSectionBlock14
  | ⟨15, _⟩ => exact plane452GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
