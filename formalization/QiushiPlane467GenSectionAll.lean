import QiushiPlane467GenSectionBlock0
import QiushiPlane467GenSectionBlock1
import QiushiPlane467GenSectionBlock2
import QiushiPlane467GenSectionBlock3
import QiushiPlane467GenSectionBlock4
import QiushiPlane467GenSectionBlock5
import QiushiPlane467GenSectionBlock6
import QiushiPlane467GenSectionBlock7
import QiushiPlane467GenSectionBlock8
import QiushiPlane467GenSectionBlock9
import QiushiPlane467GenSectionBlock10
import QiushiPlane467GenSectionBlock11
import QiushiPlane467GenSectionBlock12
import QiushiPlane467GenSectionBlock13
import QiushiPlane467GenSectionBlock14
import QiushiPlane467GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenSectionAll : forall i, plane467GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane467GenSectionBlock0
  | ⟨1, _⟩ => exact plane467GenSectionBlock1
  | ⟨2, _⟩ => exact plane467GenSectionBlock2
  | ⟨3, _⟩ => exact plane467GenSectionBlock3
  | ⟨4, _⟩ => exact plane467GenSectionBlock4
  | ⟨5, _⟩ => exact plane467GenSectionBlock5
  | ⟨6, _⟩ => exact plane467GenSectionBlock6
  | ⟨7, _⟩ => exact plane467GenSectionBlock7
  | ⟨8, _⟩ => exact plane467GenSectionBlock8
  | ⟨9, _⟩ => exact plane467GenSectionBlock9
  | ⟨10, _⟩ => exact plane467GenSectionBlock10
  | ⟨11, _⟩ => exact plane467GenSectionBlock11
  | ⟨12, _⟩ => exact plane467GenSectionBlock12
  | ⟨13, _⟩ => exact plane467GenSectionBlock13
  | ⟨14, _⟩ => exact plane467GenSectionBlock14
  | ⟨15, _⟩ => exact plane467GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
