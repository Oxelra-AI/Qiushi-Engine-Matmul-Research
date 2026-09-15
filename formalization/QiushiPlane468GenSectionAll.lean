import QiushiPlane468GenSectionBlock0
import QiushiPlane468GenSectionBlock1
import QiushiPlane468GenSectionBlock2
import QiushiPlane468GenSectionBlock3
import QiushiPlane468GenSectionBlock4
import QiushiPlane468GenSectionBlock5
import QiushiPlane468GenSectionBlock6
import QiushiPlane468GenSectionBlock7
import QiushiPlane468GenSectionBlock8
import QiushiPlane468GenSectionBlock9
import QiushiPlane468GenSectionBlock10
import QiushiPlane468GenSectionBlock11
import QiushiPlane468GenSectionBlock12
import QiushiPlane468GenSectionBlock13
import QiushiPlane468GenSectionBlock14
import QiushiPlane468GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenSectionAll : forall i, plane468GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane468GenSectionBlock0
  | ⟨1, _⟩ => exact plane468GenSectionBlock1
  | ⟨2, _⟩ => exact plane468GenSectionBlock2
  | ⟨3, _⟩ => exact plane468GenSectionBlock3
  | ⟨4, _⟩ => exact plane468GenSectionBlock4
  | ⟨5, _⟩ => exact plane468GenSectionBlock5
  | ⟨6, _⟩ => exact plane468GenSectionBlock6
  | ⟨7, _⟩ => exact plane468GenSectionBlock7
  | ⟨8, _⟩ => exact plane468GenSectionBlock8
  | ⟨9, _⟩ => exact plane468GenSectionBlock9
  | ⟨10, _⟩ => exact plane468GenSectionBlock10
  | ⟨11, _⟩ => exact plane468GenSectionBlock11
  | ⟨12, _⟩ => exact plane468GenSectionBlock12
  | ⟨13, _⟩ => exact plane468GenSectionBlock13
  | ⟨14, _⟩ => exact plane468GenSectionBlock14
  | ⟨15, _⟩ => exact plane468GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
