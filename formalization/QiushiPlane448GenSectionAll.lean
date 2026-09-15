import QiushiPlane448GenSectionBlock0
import QiushiPlane448GenSectionBlock1
import QiushiPlane448GenSectionBlock2
import QiushiPlane448GenSectionBlock3
import QiushiPlane448GenSectionBlock4
import QiushiPlane448GenSectionBlock5
import QiushiPlane448GenSectionBlock6
import QiushiPlane448GenSectionBlock7
import QiushiPlane448GenSectionBlock8
import QiushiPlane448GenSectionBlock9
import QiushiPlane448GenSectionBlock10
import QiushiPlane448GenSectionBlock11
import QiushiPlane448GenSectionBlock12
import QiushiPlane448GenSectionBlock13
import QiushiPlane448GenSectionBlock14
import QiushiPlane448GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane448GenSectionAll : forall i, plane448GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane448GenSectionBlock0
  | ⟨1, _⟩ => exact plane448GenSectionBlock1
  | ⟨2, _⟩ => exact plane448GenSectionBlock2
  | ⟨3, _⟩ => exact plane448GenSectionBlock3
  | ⟨4, _⟩ => exact plane448GenSectionBlock4
  | ⟨5, _⟩ => exact plane448GenSectionBlock5
  | ⟨6, _⟩ => exact plane448GenSectionBlock6
  | ⟨7, _⟩ => exact plane448GenSectionBlock7
  | ⟨8, _⟩ => exact plane448GenSectionBlock8
  | ⟨9, _⟩ => exact plane448GenSectionBlock9
  | ⟨10, _⟩ => exact plane448GenSectionBlock10
  | ⟨11, _⟩ => exact plane448GenSectionBlock11
  | ⟨12, _⟩ => exact plane448GenSectionBlock12
  | ⟨13, _⟩ => exact plane448GenSectionBlock13
  | ⟨14, _⟩ => exact plane448GenSectionBlock14
  | ⟨15, _⟩ => exact plane448GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
