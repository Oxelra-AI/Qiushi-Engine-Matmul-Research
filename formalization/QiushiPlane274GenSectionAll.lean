import QiushiPlane274GenSectionBlock0
import QiushiPlane274GenSectionBlock1
import QiushiPlane274GenSectionBlock2
import QiushiPlane274GenSectionBlock3
import QiushiPlane274GenSectionBlock4
import QiushiPlane274GenSectionBlock5
import QiushiPlane274GenSectionBlock6
import QiushiPlane274GenSectionBlock7
import QiushiPlane274GenSectionBlock8
import QiushiPlane274GenSectionBlock9
import QiushiPlane274GenSectionBlock10
import QiushiPlane274GenSectionBlock11
import QiushiPlane274GenSectionBlock12
import QiushiPlane274GenSectionBlock13
import QiushiPlane274GenSectionBlock14
import QiushiPlane274GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenSectionAll : forall i, plane274GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane274GenSectionBlock0
  | ⟨1, _⟩ => exact plane274GenSectionBlock1
  | ⟨2, _⟩ => exact plane274GenSectionBlock2
  | ⟨3, _⟩ => exact plane274GenSectionBlock3
  | ⟨4, _⟩ => exact plane274GenSectionBlock4
  | ⟨5, _⟩ => exact plane274GenSectionBlock5
  | ⟨6, _⟩ => exact plane274GenSectionBlock6
  | ⟨7, _⟩ => exact plane274GenSectionBlock7
  | ⟨8, _⟩ => exact plane274GenSectionBlock8
  | ⟨9, _⟩ => exact plane274GenSectionBlock9
  | ⟨10, _⟩ => exact plane274GenSectionBlock10
  | ⟨11, _⟩ => exact plane274GenSectionBlock11
  | ⟨12, _⟩ => exact plane274GenSectionBlock12
  | ⟨13, _⟩ => exact plane274GenSectionBlock13
  | ⟨14, _⟩ => exact plane274GenSectionBlock14
  | ⟨15, _⟩ => exact plane274GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
