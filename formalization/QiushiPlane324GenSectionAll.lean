import QiushiPlane324GenSectionBlock0
import QiushiPlane324GenSectionBlock1
import QiushiPlane324GenSectionBlock2
import QiushiPlane324GenSectionBlock3
import QiushiPlane324GenSectionBlock4
import QiushiPlane324GenSectionBlock5
import QiushiPlane324GenSectionBlock6
import QiushiPlane324GenSectionBlock7
import QiushiPlane324GenSectionBlock8
import QiushiPlane324GenSectionBlock9
import QiushiPlane324GenSectionBlock10
import QiushiPlane324GenSectionBlock11
import QiushiPlane324GenSectionBlock12
import QiushiPlane324GenSectionBlock13
import QiushiPlane324GenSectionBlock14
import QiushiPlane324GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane324GenSectionAll : forall i, plane324GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane324GenSectionBlock0
  | ⟨1, _⟩ => exact plane324GenSectionBlock1
  | ⟨2, _⟩ => exact plane324GenSectionBlock2
  | ⟨3, _⟩ => exact plane324GenSectionBlock3
  | ⟨4, _⟩ => exact plane324GenSectionBlock4
  | ⟨5, _⟩ => exact plane324GenSectionBlock5
  | ⟨6, _⟩ => exact plane324GenSectionBlock6
  | ⟨7, _⟩ => exact plane324GenSectionBlock7
  | ⟨8, _⟩ => exact plane324GenSectionBlock8
  | ⟨9, _⟩ => exact plane324GenSectionBlock9
  | ⟨10, _⟩ => exact plane324GenSectionBlock10
  | ⟨11, _⟩ => exact plane324GenSectionBlock11
  | ⟨12, _⟩ => exact plane324GenSectionBlock12
  | ⟨13, _⟩ => exact plane324GenSectionBlock13
  | ⟨14, _⟩ => exact plane324GenSectionBlock14
  | ⟨15, _⟩ => exact plane324GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
