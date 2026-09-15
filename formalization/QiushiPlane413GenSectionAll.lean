import QiushiPlane413GenSectionBlock0
import QiushiPlane413GenSectionBlock1
import QiushiPlane413GenSectionBlock2
import QiushiPlane413GenSectionBlock3
import QiushiPlane413GenSectionBlock4
import QiushiPlane413GenSectionBlock5
import QiushiPlane413GenSectionBlock6
import QiushiPlane413GenSectionBlock7
import QiushiPlane413GenSectionBlock8
import QiushiPlane413GenSectionBlock9
import QiushiPlane413GenSectionBlock10
import QiushiPlane413GenSectionBlock11
import QiushiPlane413GenSectionBlock12
import QiushiPlane413GenSectionBlock13
import QiushiPlane413GenSectionBlock14
import QiushiPlane413GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenSectionAll : forall i, plane413GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane413GenSectionBlock0
  | ⟨1, _⟩ => exact plane413GenSectionBlock1
  | ⟨2, _⟩ => exact plane413GenSectionBlock2
  | ⟨3, _⟩ => exact plane413GenSectionBlock3
  | ⟨4, _⟩ => exact plane413GenSectionBlock4
  | ⟨5, _⟩ => exact plane413GenSectionBlock5
  | ⟨6, _⟩ => exact plane413GenSectionBlock6
  | ⟨7, _⟩ => exact plane413GenSectionBlock7
  | ⟨8, _⟩ => exact plane413GenSectionBlock8
  | ⟨9, _⟩ => exact plane413GenSectionBlock9
  | ⟨10, _⟩ => exact plane413GenSectionBlock10
  | ⟨11, _⟩ => exact plane413GenSectionBlock11
  | ⟨12, _⟩ => exact plane413GenSectionBlock12
  | ⟨13, _⟩ => exact plane413GenSectionBlock13
  | ⟨14, _⟩ => exact plane413GenSectionBlock14
  | ⟨15, _⟩ => exact plane413GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
