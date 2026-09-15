import QiushiPlane475GenSectionBlock0
import QiushiPlane475GenSectionBlock1
import QiushiPlane475GenSectionBlock2
import QiushiPlane475GenSectionBlock3
import QiushiPlane475GenSectionBlock4
import QiushiPlane475GenSectionBlock5
import QiushiPlane475GenSectionBlock6
import QiushiPlane475GenSectionBlock7
import QiushiPlane475GenSectionBlock8
import QiushiPlane475GenSectionBlock9
import QiushiPlane475GenSectionBlock10
import QiushiPlane475GenSectionBlock11
import QiushiPlane475GenSectionBlock12
import QiushiPlane475GenSectionBlock13
import QiushiPlane475GenSectionBlock14
import QiushiPlane475GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane475GenSectionAll : forall i, plane475GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane475GenSectionBlock0
  | ⟨1, _⟩ => exact plane475GenSectionBlock1
  | ⟨2, _⟩ => exact plane475GenSectionBlock2
  | ⟨3, _⟩ => exact plane475GenSectionBlock3
  | ⟨4, _⟩ => exact plane475GenSectionBlock4
  | ⟨5, _⟩ => exact plane475GenSectionBlock5
  | ⟨6, _⟩ => exact plane475GenSectionBlock6
  | ⟨7, _⟩ => exact plane475GenSectionBlock7
  | ⟨8, _⟩ => exact plane475GenSectionBlock8
  | ⟨9, _⟩ => exact plane475GenSectionBlock9
  | ⟨10, _⟩ => exact plane475GenSectionBlock10
  | ⟨11, _⟩ => exact plane475GenSectionBlock11
  | ⟨12, _⟩ => exact plane475GenSectionBlock12
  | ⟨13, _⟩ => exact plane475GenSectionBlock13
  | ⟨14, _⟩ => exact plane475GenSectionBlock14
  | ⟨15, _⟩ => exact plane475GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
