import QiushiPlane459GenSectionBlock0
import QiushiPlane459GenSectionBlock1
import QiushiPlane459GenSectionBlock2
import QiushiPlane459GenSectionBlock3
import QiushiPlane459GenSectionBlock4
import QiushiPlane459GenSectionBlock5
import QiushiPlane459GenSectionBlock6
import QiushiPlane459GenSectionBlock7
import QiushiPlane459GenSectionBlock8
import QiushiPlane459GenSectionBlock9
import QiushiPlane459GenSectionBlock10
import QiushiPlane459GenSectionBlock11
import QiushiPlane459GenSectionBlock12
import QiushiPlane459GenSectionBlock13
import QiushiPlane459GenSectionBlock14
import QiushiPlane459GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenSectionAll : forall i, plane459GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane459GenSectionBlock0
  | ⟨1, _⟩ => exact plane459GenSectionBlock1
  | ⟨2, _⟩ => exact plane459GenSectionBlock2
  | ⟨3, _⟩ => exact plane459GenSectionBlock3
  | ⟨4, _⟩ => exact plane459GenSectionBlock4
  | ⟨5, _⟩ => exact plane459GenSectionBlock5
  | ⟨6, _⟩ => exact plane459GenSectionBlock6
  | ⟨7, _⟩ => exact plane459GenSectionBlock7
  | ⟨8, _⟩ => exact plane459GenSectionBlock8
  | ⟨9, _⟩ => exact plane459GenSectionBlock9
  | ⟨10, _⟩ => exact plane459GenSectionBlock10
  | ⟨11, _⟩ => exact plane459GenSectionBlock11
  | ⟨12, _⟩ => exact plane459GenSectionBlock12
  | ⟨13, _⟩ => exact plane459GenSectionBlock13
  | ⟨14, _⟩ => exact plane459GenSectionBlock14
  | ⟨15, _⟩ => exact plane459GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
