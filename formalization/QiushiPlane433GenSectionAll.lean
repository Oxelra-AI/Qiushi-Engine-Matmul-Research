import QiushiPlane433GenSectionBlock0
import QiushiPlane433GenSectionBlock1
import QiushiPlane433GenSectionBlock2
import QiushiPlane433GenSectionBlock3
import QiushiPlane433GenSectionBlock4
import QiushiPlane433GenSectionBlock5
import QiushiPlane433GenSectionBlock6
import QiushiPlane433GenSectionBlock7
import QiushiPlane433GenSectionBlock8
import QiushiPlane433GenSectionBlock9
import QiushiPlane433GenSectionBlock10
import QiushiPlane433GenSectionBlock11
import QiushiPlane433GenSectionBlock12
import QiushiPlane433GenSectionBlock13
import QiushiPlane433GenSectionBlock14
import QiushiPlane433GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenSectionAll : forall i, plane433GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane433GenSectionBlock0
  | ⟨1, _⟩ => exact plane433GenSectionBlock1
  | ⟨2, _⟩ => exact plane433GenSectionBlock2
  | ⟨3, _⟩ => exact plane433GenSectionBlock3
  | ⟨4, _⟩ => exact plane433GenSectionBlock4
  | ⟨5, _⟩ => exact plane433GenSectionBlock5
  | ⟨6, _⟩ => exact plane433GenSectionBlock6
  | ⟨7, _⟩ => exact plane433GenSectionBlock7
  | ⟨8, _⟩ => exact plane433GenSectionBlock8
  | ⟨9, _⟩ => exact plane433GenSectionBlock9
  | ⟨10, _⟩ => exact plane433GenSectionBlock10
  | ⟨11, _⟩ => exact plane433GenSectionBlock11
  | ⟨12, _⟩ => exact plane433GenSectionBlock12
  | ⟨13, _⟩ => exact plane433GenSectionBlock13
  | ⟨14, _⟩ => exact plane433GenSectionBlock14
  | ⟨15, _⟩ => exact plane433GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
