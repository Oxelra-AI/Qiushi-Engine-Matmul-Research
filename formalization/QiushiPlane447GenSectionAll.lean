import QiushiPlane447GenSectionBlock0
import QiushiPlane447GenSectionBlock1
import QiushiPlane447GenSectionBlock2
import QiushiPlane447GenSectionBlock3
import QiushiPlane447GenSectionBlock4
import QiushiPlane447GenSectionBlock5
import QiushiPlane447GenSectionBlock6
import QiushiPlane447GenSectionBlock7
import QiushiPlane447GenSectionBlock8
import QiushiPlane447GenSectionBlock9
import QiushiPlane447GenSectionBlock10
import QiushiPlane447GenSectionBlock11
import QiushiPlane447GenSectionBlock12
import QiushiPlane447GenSectionBlock13
import QiushiPlane447GenSectionBlock14
import QiushiPlane447GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenSectionAll : forall i, plane447GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane447GenSectionBlock0
  | ⟨1, _⟩ => exact plane447GenSectionBlock1
  | ⟨2, _⟩ => exact plane447GenSectionBlock2
  | ⟨3, _⟩ => exact plane447GenSectionBlock3
  | ⟨4, _⟩ => exact plane447GenSectionBlock4
  | ⟨5, _⟩ => exact plane447GenSectionBlock5
  | ⟨6, _⟩ => exact plane447GenSectionBlock6
  | ⟨7, _⟩ => exact plane447GenSectionBlock7
  | ⟨8, _⟩ => exact plane447GenSectionBlock8
  | ⟨9, _⟩ => exact plane447GenSectionBlock9
  | ⟨10, _⟩ => exact plane447GenSectionBlock10
  | ⟨11, _⟩ => exact plane447GenSectionBlock11
  | ⟨12, _⟩ => exact plane447GenSectionBlock12
  | ⟨13, _⟩ => exact plane447GenSectionBlock13
  | ⟨14, _⟩ => exact plane447GenSectionBlock14
  | ⟨15, _⟩ => exact plane447GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
