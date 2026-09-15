import QiushiPlane267GenSectionBlock0
import QiushiPlane267GenSectionBlock1
import QiushiPlane267GenSectionBlock2
import QiushiPlane267GenSectionBlock3
import QiushiPlane267GenSectionBlock4
import QiushiPlane267GenSectionBlock5
import QiushiPlane267GenSectionBlock6
import QiushiPlane267GenSectionBlock7
import QiushiPlane267GenSectionBlock8
import QiushiPlane267GenSectionBlock9
import QiushiPlane267GenSectionBlock10
import QiushiPlane267GenSectionBlock11
import QiushiPlane267GenSectionBlock12
import QiushiPlane267GenSectionBlock13
import QiushiPlane267GenSectionBlock14
import QiushiPlane267GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane267GenSectionAll : forall i, plane267GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane267GenSectionBlock0
  | ⟨1, _⟩ => exact plane267GenSectionBlock1
  | ⟨2, _⟩ => exact plane267GenSectionBlock2
  | ⟨3, _⟩ => exact plane267GenSectionBlock3
  | ⟨4, _⟩ => exact plane267GenSectionBlock4
  | ⟨5, _⟩ => exact plane267GenSectionBlock5
  | ⟨6, _⟩ => exact plane267GenSectionBlock6
  | ⟨7, _⟩ => exact plane267GenSectionBlock7
  | ⟨8, _⟩ => exact plane267GenSectionBlock8
  | ⟨9, _⟩ => exact plane267GenSectionBlock9
  | ⟨10, _⟩ => exact plane267GenSectionBlock10
  | ⟨11, _⟩ => exact plane267GenSectionBlock11
  | ⟨12, _⟩ => exact plane267GenSectionBlock12
  | ⟨13, _⟩ => exact plane267GenSectionBlock13
  | ⟨14, _⟩ => exact plane267GenSectionBlock14
  | ⟨15, _⟩ => exact plane267GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
