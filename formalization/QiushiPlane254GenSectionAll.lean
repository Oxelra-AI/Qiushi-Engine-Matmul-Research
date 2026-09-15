import QiushiPlane254GenSectionBlock0
import QiushiPlane254GenSectionBlock1
import QiushiPlane254GenSectionBlock2
import QiushiPlane254GenSectionBlock3
import QiushiPlane254GenSectionBlock4
import QiushiPlane254GenSectionBlock5
import QiushiPlane254GenSectionBlock6
import QiushiPlane254GenSectionBlock7
import QiushiPlane254GenSectionBlock8
import QiushiPlane254GenSectionBlock9
import QiushiPlane254GenSectionBlock10
import QiushiPlane254GenSectionBlock11
import QiushiPlane254GenSectionBlock12
import QiushiPlane254GenSectionBlock13
import QiushiPlane254GenSectionBlock14
import QiushiPlane254GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane254GenSectionAll : forall i, plane254GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane254GenSectionBlock0
  | ⟨1, _⟩ => exact plane254GenSectionBlock1
  | ⟨2, _⟩ => exact plane254GenSectionBlock2
  | ⟨3, _⟩ => exact plane254GenSectionBlock3
  | ⟨4, _⟩ => exact plane254GenSectionBlock4
  | ⟨5, _⟩ => exact plane254GenSectionBlock5
  | ⟨6, _⟩ => exact plane254GenSectionBlock6
  | ⟨7, _⟩ => exact plane254GenSectionBlock7
  | ⟨8, _⟩ => exact plane254GenSectionBlock8
  | ⟨9, _⟩ => exact plane254GenSectionBlock9
  | ⟨10, _⟩ => exact plane254GenSectionBlock10
  | ⟨11, _⟩ => exact plane254GenSectionBlock11
  | ⟨12, _⟩ => exact plane254GenSectionBlock12
  | ⟨13, _⟩ => exact plane254GenSectionBlock13
  | ⟨14, _⟩ => exact plane254GenSectionBlock14
  | ⟨15, _⟩ => exact plane254GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
